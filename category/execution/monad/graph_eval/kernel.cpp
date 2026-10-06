// Copyright (C) 2026 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "category/execution/monad/graph_eval/config.hpp"
#include <category/execution/monad/graph_eval/kernel.hpp>
#include <iree/hal/allocator.h>
#include <iree/hal/buffer.h>
#include <iree/hal/buffer_view.h>
#include <iree/runtime/call.h>
#include <iree/runtime/instance.h>
#include <iree/runtime/session.h>
#include <iree/vm/bytecode/module.h>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

//
// IREE kernels
//

// kernels.mlir, compiled ahead of time by the build; see
// category/execution/CMakeLists.txt.
// #embed is C23, an extension in C++.
#ifdef __clang__
    #pragma clang diagnostic push
    #pragma clang diagnostic ignored "-Wc23-extensions"
#elif defined __GNUC__
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wpedantic"
#endif
alignas(64) constexpr unsigned char KERNELS_VMFB[] = {
#embed MONAD_GRAPH_EVAL_KERNELS_VMFB
};
#ifdef __clang__
    #pragma clang diagnostic pop
#elif defined __GNUC__
    #pragma GCC diagnostic pop
#endif

// IREE failures (out of memory, ...) are local to this node rather than a
// property of the transaction, so abort instead of returning an error that
// would make execution diverge from other nodes
void check_ok(iree_status_t status)
{
    if (MONAD_UNLIKELY(!iree_status_is_ok(status))) {
        char message[4096];
        iree_host_size_t length = 0;
        if (!iree_status_format(status, sizeof(message), message, &length)) {
            MONAD_ABORT_PRINTF(
                "IREE runtime error: %s",
                iree_status_code_string(iree_status_code(status)));
        }
        MONAD_ABORT_PRINTF(
            "IREE runtime error: %.*s", static_cast<int>(length), message);
    }
}

struct IREERuntime
{
    iree_runtime_instance_t *instance;
    iree_hal_device_t *device;
    iree_vm_module_t *kernels;
};

// Shared by all threads' sessions. Created on first use and never destroyed.
IREERuntime const &iree_runtime()
{
    static IREERuntime const runtime = [] {
        iree_runtime_instance_options_t options;
        iree_runtime_instance_options_initialize(&options);
        iree_runtime_instance_options_use_all_available_drivers(&options);
        IREERuntime runtime{};
        check_ok(iree_runtime_instance_create(
            &options, iree_allocator_system(), &runtime.instance));
        check_ok(iree_runtime_instance_try_create_default_device(
            runtime.instance,
            iree_make_cstring_view("local-sync"),
            &runtime.device));
        // Modules are thread-safe; only their per-session state is not.
        // KERNELS_VMFB is static, so it outlives the module.
        check_ok(iree_vm_bytecode_module_create(
            iree_runtime_instance_vm_instance(runtime.instance),
            IREE_VM_BYTECODE_MODULE_FLAG_NONE,
            iree_make_const_byte_span(KERNELS_VMFB, sizeof(KERNELS_VMFB)),
            iree_allocator_null(),
            iree_runtime_instance_host_allocator(runtime.instance),
            &runtime.kernels));
        return runtime;
    }();
    return runtime;
}

struct SessionDeleter
{
    void operator()(iree_runtime_session_t *const session) const
    {
        iree_runtime_session_release(session);
    }
};

// Each thread gets its own session. These are created lazily on first use and
// released by the SessionDeleter destructor when the thread exits.
iree_runtime_session_t *thread_session()
{
    thread_local std::unique_ptr<iree_runtime_session_t, SessionDeleter> const
        session{[] {
            IREERuntime const &rt = iree_runtime();
            iree_runtime_session_options_t options;
            iree_runtime_session_options_initialize(&options);
            iree_runtime_session_t *created = nullptr;
            check_ok(iree_runtime_session_create_with_device(
                rt.instance,
                &options,
                rt.device,
                iree_runtime_instance_host_allocator(rt.instance),
                &created));
            check_ok(iree_runtime_session_append_module(created, rt.kernels));
            return created;
        }()};
    return session.get();
}

iree_hal_element_type_t dtype_to_iree(Dtype dtype)
{
    switch (dtype) {
    case Dtype::int8:
        return IREE_HAL_ELEMENT_TYPE_INT_8;
    case Dtype::uint8:
        return IREE_HAL_ELEMENT_TYPE_UINT_8;
    case Dtype::int16:
        return IREE_HAL_ELEMENT_TYPE_INT_16;
    case Dtype::uint16:
        return IREE_HAL_ELEMENT_TYPE_UINT_16;
    case Dtype::int32:
        return IREE_HAL_ELEMENT_TYPE_INT_32;
    case Dtype::uint32:
        return IREE_HAL_ELEMENT_TYPE_UINT_32;
    case Dtype::int64:
        return IREE_HAL_ELEMENT_TYPE_INT_64;
    case Dtype::uint64:
        return IREE_HAL_ELEMENT_TYPE_UINT_64;
    }
    MONAD_ABORT();
}

// Import a Tensor as an IREE buffer
iree_hal_buffer_view_t *
import_tensor(iree_runtime_session_t *const session, Tensor &tensor)
{
    iree_hal_buffer_params_t params{};
    params.type = IREE_HAL_MEMORY_TYPE_DEVICE_LOCAL;
    params.access = IREE_HAL_MEMORY_ACCESS_ALL;
    params.usage = IREE_HAL_BUFFER_USAGE_DEFAULT;

    iree_hal_external_buffer_t bufdesc{};
    bufdesc.flags = IREE_HAL_EXTERNAL_BUFFER_FLAG_NONE;
    // Beware: here we assume that iree_hal_element_dense_byte_count(dtype) =
    // dtype_size(dtype)
    bufdesc.size = tensor.type().size_bytes();
    bufdesc.type = IREE_HAL_EXTERNAL_BUFFER_TYPE_HOST_ALLOCATION;
    // TODO: remove this const_cast
    bufdesc.handle.host_allocation.ptr = (tensor.data());

    iree_hal_buffer_t *buffer = nullptr;
    check_ok(iree_hal_allocator_import_buffer(
        iree_runtime_session_device_allocator(session),
        params,
        &bufdesc,
        iree_hal_buffer_release_callback_null(),
        &buffer));

    iree_hal_buffer_view_t *view = nullptr;
    std::array<iree_hal_dim_t, 8> shape;
    for (auto i = 0; i < tensor.type().shape.rank; i++) {
        // TODO: this would not be necessary if Tensor stored dimensions as
        // unsigned long
        shape[static_cast<size_t>(i)] =
            tensor.type().shape.dimensions[static_cast<size_t>(i)];
    }
    iree_hal_element_type_t dtype = dtype_to_iree(tensor.type().dtype);
    iree_status_t status = iree_hal_buffer_view_create(
        buffer,
        tensor.type().shape.rank,
        shape.data(),
        dtype,
        IREE_HAL_ENCODING_TYPE_DENSE_ROW_MAJOR,
        iree_runtime_session_host_allocator(session),
        &view);

    // There is no need to keep the buffer around, since the created view holds
    // its own data.
    // TODO: do we even need the buffer?
    iree_hal_buffer_release(buffer);
    check_ok(status);
    return view;
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

void Kernel::operator()(std::vector<Tensor> &inputs, Tensor &output) const
{
    iree_runtime_session_t *const session = thread_session();

    iree_runtime_call_t call;
    check_ok(iree_runtime_call_initialize_by_name(
        session, iree_make_cstring_view(kernel_name_), &call));

    for (auto &input : inputs) {
        auto *const view = import_tensor(session, input);
        check_ok(iree_runtime_call_inputs_push_back_buffer_view(&call, view));
        iree_hal_buffer_view_release(view);
    }

    auto *const out_view = import_tensor(session, output);
    check_ok(iree_runtime_call_inputs_push_back_buffer_view(&call, out_view));

    check_ok(iree_runtime_call_invoke(&call, 0));

    iree_hal_buffer_view_t *result = nullptr;
    check_ok(iree_runtime_call_outputs_pop_front_buffer_view(&call, &result));
    // The result must alias `out`; otherwise `out` would silently be left
    // without it
    MONAD_ASSERT(
        iree_hal_buffer_allocated_buffer(iree_hal_buffer_view_buffer(result)) ==
            iree_hal_buffer_allocated_buffer(
                iree_hal_buffer_view_buffer(out_view)),
        "kernel did not write its result into the output tensor");

    iree_hal_buffer_view_release(result);
    iree_hal_buffer_view_release(out_view);

    iree_runtime_call_deinitialize(&call);
}

MONAD_GRAPH_EVAL_NAMESPACE_END
