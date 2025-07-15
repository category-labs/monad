#pragma once

#include <monad/vm/compiler/ir/basic_blocks.hpp>
#include <monad/vm/compiler/ir/x86/types.hpp>
#include <monad/vm/compiler/ir/x86/virtual_stack.hpp>
#include <monad/vm/runtime/detail.hpp>
#include <monad/vm/runtime/types.hpp>

#include <asmjit/x86.h>
#include <asmjit/x86/x86assembler.h>

namespace monad::vm::compiler::native
{
    class Emitter
    {
    public:
        struct Error : std::runtime_error
        {
            explicit Error(std::string const &msg);
            explicit Error(char const *msg);
        };

        struct EmitErrorHandler : asmjit::ErrorHandler
        {
            void handleError(
                asmjit::Error, char const *message,
                asmjit::BaseEmitter *) override;
        };

        enum class LocationType
        {
            StackOffset,
            Literal,
            AvxReg,
            GeneralReg
        };

        template <typename Int = int32_t>
        static bool is_uint64_bounded(uint64_t);

        template <typename Int = int32_t>
        static bool is_literal_bounded(Literal const &);

        static char const *location_type_to_string(LocationType);

        template <size_t N>
        struct RoSubdata
        {
            static_assert(std::popcount(N) == 1);
            static_assert(N <= 32);

            using Data = std::array<uint8_t, N>;

            struct DataHash
            {
                size_t operator()(Data const &x) const;
            };

            std::unordered_map<Data, int32_t, DataHash> offmap;
        };

        class RoData
        {
        public:
            explicit RoData(asmjit::Label);

            asmjit::Label const &label() const;

            std::vector<runtime::uint256_t> const &data() const;

            asmjit::x86::Mem add_literal(Literal const &);

            template <typename F>
            asmjit::x86::Mem add_external_function(F);

            asmjit::x86::Mem add32(runtime::uint256_t const &);
            asmjit::x86::Mem add16(uint64_t, uint64_t);
            asmjit::x86::Mem add8(uint64_t);
            asmjit::x86::Mem add4(uint32_t);

        private:
            template <size_t N>
            asmjit::x86::Mem add(std::array<uint8_t, N> const &);

            asmjit::Label label_;
            int32_t partial_index_{};
            int32_t partial_sub_index_{32};
            std::vector<runtime::uint256_t> data_;
            RoSubdata<32> sub32_;
            RoSubdata<16> sub16_;
            RoSubdata<8> sub8_;
            RoSubdata<4> sub4_;
        };

        using Gpq256 = std::array<asmjit::x86::Gpq, 4>;
        using Imm256 = std::array<asmjit::Imm, 4>;

        using Operand =
            std::variant<Gpq256, Imm256, asmjit::x86::Ymm, asmjit::x86::Mem>;

        template <typename L, typename R>
        using GeneralBinInstr = std::array<
            asmjit::Error (asmjit::x86::Assembler::*)(L const &, R const &), 4>;

        template <typename R>
        using AvxBinInstr = asmjit::Error (
            asmjit::x86::EmitterExplicitT<asmjit::x86::Assembler>::*)(
            asmjit::x86::Vec const &, asmjit::x86::Vec const &, R const &);

        static constexpr auto MAX_RUNTIME_ARGS = 12;

        class RuntimeImpl
        {
        public:
            template <typename... Args>
            RuntimeImpl(
                Emitter *e, int32_t remaining_base_gas, bool spill_avx,
                void (*f)(Args...))
                : em_{e}
                , remaining_base_gas_{remaining_base_gas}
                , spill_avx_{spill_avx}
                , runtime_fun_{reinterpret_cast<void *>(f)}
                , arg_count_{sizeof...(Args)}
                , context_arg_{runtime::detail::context_arg_t<
                      Args...>::context_arg}
                , result_arg_{runtime::detail::result_arg_t<
                      Args...>::result_arg}
                , remaining_gas_arg_{runtime::detail::remaining_gas_arg_t<
                      Args...>::remaining_gas_arg}
            {
            }

            RuntimeImpl &pass(StackElemRef &&);

            void call_impl();

            size_t implicit_arg_count();
            size_t explicit_arg_count();
            bool spill_avx_regs();

        protected:
            using RuntimeArg =
                std::variant<asmjit::x86::Gpq, asmjit::Imm, asmjit::x86::Mem>;

            void mov_arg(size_t arg_index, RuntimeArg &&arg);
            void mov_reg_arg(asmjit::x86::Gpq const &, RuntimeArg &&arg);
            void mov_stack_arg(int32_t sp_offset, RuntimeArg &&arg);

            Emitter *em_;
            std::vector<StackElemRef> explicit_args_;
            int32_t remaining_base_gas_;
            bool spill_avx_;
            void *runtime_fun_;
            size_t arg_count_;
            std::optional<size_t> context_arg_;
            std::optional<size_t> result_arg_;
            std::optional<size_t> remaining_gas_arg_;
        };

        template <typename... Args>
        class Runtime : public RuntimeImpl
        {
        public:
            Runtime(
                Emitter *e, int32_t remaining_base_gas, bool spill_avx,
                void (*f)(Args...))
                : RuntimeImpl(e, remaining_base_gas, spill_avx, f)
            {
            }

            Runtime(Emitter *e, bool spill_avx, void (*f)(Args...))
                : Runtime(e, 0, spill_avx, f)
            {
            }

            void call()
            {
                em_->call_runtime_impl(*this);
            }
        };

        friend class RuntimeImpl;
        template <typename... Args>
        friend class Runtime;

        ////////// Initialization and de-initialization //////////

        Emitter(
            asmjit::JitRuntime const &, uint64_t bytecode_size,
            CompilerConfig const & = {});

        ~Emitter();

        entrypoint_t finish_contract(asmjit::JitRuntime &);

        ////////// Debug functionality //////////

        void runtime_print_gas_remaining(std::string const &msg);
        void runtime_print_input_stack(std::string const &msg);
        void runtime_store_input_stack(uint64_t);
        void runtime_print_top2(std::string const &msg);
        void breakpoint();
        void checked_debug_comment(std::string const &msg);
        void swap_general_regs(StackElem &, StackElem &);
        void swap_general_reg_indices(GeneralReg, uint8_t, uint8_t);

        ////////// Core emit functionality //////////

        [[noreturn]] void fail_with_error(asmjit::Error);
        Stack &get_stack();
        size_t estimate_size();
        void add_jump_dest(byte_offset);
        [[nodiscard]]
        bool begin_new_block(basic_blocks::Block const &);
        void gas_decrement_no_check(int32_t);
        void gas_decrement_check_non_negative(int32_t);
        void spill_caller_save_regs(bool spill_avx);
        void spill_all_caller_save_general_regs();
        void spill_avx_reg_range(uint8_t start);
        void spill_all_avx_regs();
        [[nodiscard]] std::pair<StackElemRef, AvxRegReserv> alloc_avx_reg();
        void insert_avx_reg_without_reserv(StackElem &);
        [[nodiscard]] AvxRegReserv insert_avx_reg(StackElemRef);
        [[nodiscard]] std::pair<StackElemRef, GeneralRegReserv>
        alloc_general_reg();
        [[nodiscard]] GeneralRegReserv insert_general_reg(StackElemRef);

        template <typename... LiveSet>
        [[nodiscard]] StackElemRef
        release_general_reg(StackElem &, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        [[nodiscard]] StackElemRef
        release_general_reg(StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        void release_volatile_general_reg(std::tuple<LiveSet...> const &);

        void discharge_deferred_comparison(); // Leaves eflags unchanged

        ////////// Move functionality //////////

        void mov_stack_index_to_avx_reg(int32_t stack_index);
        void mov_stack_index_to_general_reg(int32_t stack_index);
        void mov_stack_index_to_stack_offset(int32_t stack_index);

        ////////// EVM instructions //////////

        void push(uint256_t const &);
        void pop();
        void dup(uint8_t dup_index);
        void swap(uint8_t swap_index);

        void lt();
        void gt();
        void slt();
        void sgt();
        void sub();
        void add();
        void byte();
        void signextend();
        void shl();
        void shr();
        void sar();

        void and_();
        void or_();
        void xor_();
        void eq();

        void iszero();
        void not_();

        void gas(int32_t remaining_base_gas);

        void address();
        void caller();
        void callvalue();
        void calldatasize();
        void returndatasize();
        void msize();
        void codesize();
        void origin();
        void gasprice();
        void gaslimit();
        void coinbase();
        void timestamp();
        void number();
        void prevrandao();
        void chainid();
        void basefee();
        void blobbasefee();

        void calldataload();
        void mload();
        void mstore();
        void mstore8();

        // Revision dependent instructions
        template <evmc_revision rev>
        void mul(int32_t remaining_base_gas)
        {
            if (mul_optimized()) {
                return;
            }
            call_runtime(remaining_base_gas, false, runtime::mul);
        }

        template <evmc_revision rev>
        void udiv(int32_t remaining_base_gas)
        {
            if (div_optimized<false>()) {
                return;
            }
            call_runtime(remaining_base_gas, true, runtime::udiv);
        }

        template <evmc_revision rev>
        void sdiv(int32_t remaining_base_gas)
        {
            if (div_optimized<true>()) {
                return;
            }
            call_runtime(remaining_base_gas, true, runtime::sdiv);
        }

        template <evmc_revision rev>
        void umod(int32_t remaining_base_gas)
        {
            if (mod_optimized<false>()) {
                return;
            }
            call_runtime(remaining_base_gas, true, runtime::umod);
        }

        template <evmc_revision rev>
        void smod(int32_t remaining_base_gas)
        {
            if (mod_optimized<true>()) {
                return;
            }
            call_runtime(remaining_base_gas, true, runtime::smod);
        }

        bool addmod_opt();

        template <evmc_revision rev>
        void addmod(int32_t remaining_base_gas)
        {
            if (addmod_opt()) {
                return;
            }
            call_runtime(remaining_base_gas, true, runtime::addmod);
        }

        bool mulmod_opt();

        template <evmc_revision rev>
        void mulmod(int32_t remaining_base_gas)
        {
            if (mulmod_opt()) {
                return;
            }
            call_runtime(remaining_base_gas, true, runtime::mulmod);
        }

        template <evmc_revision rev>
        void exp(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::exp<rev>);
        }

        template <evmc_revision rev>
        void sha3(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::sha3);
        }

        template <evmc_revision rev>
        void balance(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::balance<rev>);
        }

        template <evmc_revision rev>
        void calldatacopy(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::calldatacopy);
        }

        template <evmc_revision rev>
        void codecopy(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::codecopy);
        }

        template <evmc_revision rev>
        void extcodesize(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::extcodesize<rev>);
        }

        template <evmc_revision rev>
        void extcodecopy(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::extcodecopy<rev>);
        }

        template <evmc_revision rev>
        void returndatacopy(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::returndatacopy);
        }

        template <evmc_revision rev>
        void extcodehash(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::extcodehash<rev>);
        }

        template <evmc_revision rev>
        void blockhash(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::blockhash);
        }

        template <evmc_revision rev>
        void selfbalance(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::selfbalance);
        }

        template <evmc_revision rev>
        void blobhash(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::blobhash);
        }

        template <evmc_revision rev>
        void sload(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::sload<rev>);
        }

        template <evmc_revision rev>
        void sstore(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::sstore<rev>);
        }

        template <evmc_revision rev>
        void tload(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::tload);
        }

        template <evmc_revision rev>
        void tstore(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::tstore);
        }

        template <evmc_revision rev>
        void mcopy(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::mcopy);
        }

        template <evmc_revision rev>
        void log0(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::log0);
        }

        template <evmc_revision rev>
        void log1(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::log1);
        }

        template <evmc_revision rev>
        void log2(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::log2);
        }

        template <evmc_revision rev>
        void log3(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::log3);
        }

        template <evmc_revision rev>
        void log4(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::log4);
        }

        template <evmc_revision rev>
        void create(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::create<rev>);
        }

        template <evmc_revision rev>
        void call(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::call<rev>);
        }

        template <evmc_revision rev>
        void callcode(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::callcode<rev>);
        }

        template <evmc_revision rev>
        void delegatecall(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::delegatecall<rev>);
        }

        template <evmc_revision rev>
        void create2(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::create2<rev>);
        }

        template <evmc_revision rev>
        void staticcall(int32_t remaining_base_gas)
        {
            call_runtime(remaining_base_gas, true, runtime::staticcall<rev>);
        }

        template <evmc_revision rev>
        void selfdestruct(int32_t remaining_base_gas)
        {
            runtime_store_input_stack(bytecode_size_);
            call_runtime(remaining_base_gas, true, runtime::selfdestruct<rev>);
        }

        template <typename... Args>
        void call_runtime(
            int32_t remaining_base_gas, bool spill_avx, void (*f)(Args...))
        {
            Runtime<Args...>(this, remaining_base_gas, spill_avx, f).call();
        }

        // Terminators invalidate emitter until `begin_new_block` is called.
        void jump();
        void jumpi(basic_blocks::Block const &fallthrough);
        void fallthrough();
        void stop();
        void invalid_instruction();
        void return_();
        void revert();

    private:
        ////////// Private initialization and de-initialization //////////

        asmjit::CodeHolder *
        init_code_holder(asmjit::JitRuntime const &, char const *);
        void contract_prologue();
        void contract_epilogue();

        ////////// Private debug functionality //////////

        void unchecked_debug_comment(std::string const &msg);

        ////////// Private core emit functionality //////////

        template <typename... LiveSet, size_t... Is>
        bool is_live(
            StackElem const &, std::tuple<LiveSet...> const &,
            std::index_sequence<Is...>);

        template <typename... LiveSet>
        bool is_live(StackElem const &, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        bool is_live(StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet, size_t... Is>
        bool is_live(
            GeneralReg, std::tuple<LiveSet...> const &,
            std::index_sequence<Is...>);

        template <typename... LiveSet>
        bool is_live(GeneralReg, std::tuple<LiveSet...> const &);

        bool block_prologue(basic_blocks::Block const &);
        template <bool preserve_eflags>
        void adjust_by_stack_delta();
        void write_to_final_stack_offsets();

        void discharge_deferred_comparison(StackElem *, Comparison);

        Gpq256 &general_reg_to_gpq256(GeneralReg);

        template <typename... LiveSet>
        unsigned get_stack_elem_general_order_index(
            StackElemRef, std::tuple<LiveSet...> const &);

        template <asmjit::x86::Gpq gpq>
        uint8_t volatile_gpq_index();

        ////////// Private move functionality //////////

        template <bool remember_intermediate, bool assume_aligned>
        void mov_literal_to_mem(StackElemRef, asmjit::x86::Mem const &);

        template <bool assume_aligned>
        void mov_literal_to_mem(Literal const &, asmjit::x86::Mem const &);

        void mov_general_reg_to_mem(GeneralReg, asmjit::x86::Mem const &);

        template <bool remember_intermediate>
        void
        mov_stack_elem_to_unaligned_mem(StackElemRef, asmjit::x86::Mem const &);

        void mov_general_reg_to_gpq256(GeneralReg, Gpq256 const &);
        void mov_literal_to_gpq256(Literal const &, Gpq256 const &);
        void mov_mem_to_gpq256(asmjit::x86::Mem, Gpq256 const &);
        void mov_stack_offset_to_gpq256(StackOffset, Gpq256 const &);
        template <bool remember_intermediate>
        void mov_stack_elem_to_gpq256(StackElemRef, Gpq256 const &);

        void mov_literal_to_ymm(Literal const &, asmjit::x86::Ymm const &);

        void mov_stack_elem_to_avx_reg(StackElemRef);
        void mov_stack_elem_to_general_reg(StackElemRef);
        void
        mov_stack_elem_to_general_reg(StackElemRef, int32_t preferred_offset);
        void mov_stack_elem_to_stack_offset(StackElemRef);
        void
        mov_stack_elem_to_stack_offset(StackElemRef, int32_t preferred_offset);

        void mov_general_reg_to_avx_reg(StackElemRef);
        void mov_literal_to_avx_reg(StackElemRef);
        void mov_stack_offset_to_avx_reg(StackElemRef);

        void mov_avx_reg_to_stack_offset(StackElemRef);
        void
        mov_avx_reg_to_stack_offset(StackElemRef, int32_t preferred_offset);
        void mov_general_reg_to_stack_offset(StackElem &);
        void mov_general_reg_to_stack_offset(StackElemRef);
        void
        mov_general_reg_to_stack_offset(StackElem &, int32_t preferred_offset);
        void
        mov_general_reg_to_stack_offset(StackElemRef, int32_t preferred_offset);
        void mov_literal_to_stack_offset(StackElemRef);
        void
        mov_literal_to_stack_offset(StackElemRef, int32_t preferred_offset);

        void mov_avx_reg_to_general_reg(StackElemRef);
        void mov_avx_reg_to_general_reg(StackElemRef, int32_t preferred_offset);
        void mov_literal_to_general_reg(StackElemRef);
        void mov_stack_offset_to_general_reg(StackElemRef);

        StackElem *revertible_mov_stack_offset_to_general_reg(StackElemRef);

        void bswap_to_ymm(
            std::variant<asmjit::x86::Ymm, asmjit::x86::Mem> src,
            asmjit::x86::Ymm dst);
        void mov_mem_be_to_avx_reg(asmjit::x86::Mem, StackElemRef);
        void mov_mem_be_to_general_reg(asmjit::x86::Mem, StackElemRef);
        StackElemRef read_mem_be(asmjit::x86::Mem);
        void mov_stack_elem_to_mem_be(StackElemRef, asmjit::x86::Mem);

        ////////// Private EVM instruction utilities //////////

        template <typename... LiveSet>
        StackElemRef negate(StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        StackElemRef
        sub(StackElemRef, StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        StackElemRef
        add(StackElemRef, StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        StackElemRef
        shl(StackElemRef, StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        StackElemRef
        shr(StackElemRef, StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        StackElemRef
        sar(StackElemRef, StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        StackElemRef
        and_(StackElemRef, StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        StackElemRef
        or_(StackElemRef, StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        StackElemRef
        xor_(StackElemRef, StackElemRef, std::tuple<LiveSet...> const &);

        std::variant<Comparison, StackElemRef> iszero(StackElemRef);
        void push_iszero(StackElemRef);

        std::optional<Comparison> issigned(StackElemRef);

        StackElemRef negate_by_sub(StackElemRef);
        void negate_gpq256(Gpq256 const &);

        template <uint8_t bits, typename... LiveSet>
        std::variant<std::monostate, asmjit::x86::Gpq, uint64_t>
        is_bounded_by_bits(
            StackElemRef, asmjit::Label const &skip_label,
            std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        std::optional<asmjit::x86::Mem> touch_memory(
            StackElemRef offset, int32_t read_size,
            std::tuple<LiveSet...> const &);

        void call_runtime_impl(RuntimeImpl &rt);

        void status_code(runtime::StatusCode);
        void error_block(asmjit::Label &, runtime::StatusCode);
        void return_with_status_code(runtime::StatusCode);

        static constexpr size_t div64_ceil(size_t x)
        {
            return (x >> 6) + ((x & 63) != 0);
        }

        class MulEmitter
        {
        public:
            using RightMulArg =
                std::variant<uint256_t, asmjit::x86::Mem, Gpq256>;

            MulEmitter(
                size_t bit_size, Emitter &em, Operand const &left,
                RightMulArg const &right, asmjit::x86::Gpq const *dst,
                asmjit::x86::Gpq const *tmp);

            void emit();

        private:
            void init_mul_dst(size_t sub_size, asmjit::x86::Gpq *);
            template <bool Has32Bit>
            void mul_sequence(size_t sub_size, asmjit::x86::Gpq const *);
            template <bool Has32Bit>
            void update_dst(size_t sub_size, asmjit::x86::Gpq const *);
            template <bool Has32Bit>
            void compose(size_t sub_size, asmjit::x86::Gpq *);
            template <bool Has32Bit>
            void emit_loop();

            size_t bit_size_;
            Emitter &em_;
            Operand const &left_;
            RightMulArg const &right_;
            asmjit::x86::Gpq const *dst_;
            asmjit::x86::Gpq const *tmp_;
            bool is_dst_initialized_;
        };

        friend class MulEmitter;

        template <typename LeftOpType>
        void mulx(
            asmjit::x86::Gpq dst1, asmjit::x86::Gpq dst2, LeftOpType left,
            asmjit::x86::Gpq right);
        template <bool Is32Bit, typename LeftOpType>
        void imul_by_gpq(
            asmjit::x86::Gpq dst, LeftOpType left, asmjit::x86::Gpq right);
        template <bool Is32Bit, typename LeftOpType>
        void
        imul_by_int32(asmjit::x86::Gpq dst, LeftOpType left, int32_t right);
        template <bool Is32Bit, typename LeftOpType>
        void imul_by_rax_or_int32(
            asmjit::x86::Gpq dst, LeftOpType left, std::optional<int32_t>);
        void mul_with_bit_size_by_rax(
            size_t bit_size, asmjit::x86::Gpq const *dst, Operand const &left,
            std::optional<int32_t> value_of_rax);
        template <bool Has32Bit>
        void mul_with_bit_size_and_has_32_bit_by_rax(
            size_t bit_size, asmjit::x86::Gpq const *dst, Operand const &left,
            std::optional<int32_t> value_of_rax);
        template <typename... LiveSet>
        StackElemRef mul_with_bit_size(
            size_t bit_size, StackElemRef, MulEmitter::RightMulArg,
            std::tuple<LiveSet...> const &);
        bool mul_optimized();

        template <typename... LiveSet>
        StackElemRef sdiv_by_sar(
            StackElemRef, uint256_t const &shift,
            std::tuple<LiveSet...> const &);
        template <bool is_sdiv>
        bool div_optimized();

        template <typename... LiveSet>
        StackElemRef mod_by_mask(
            StackElemRef, uint256_t const &mask,
            std::tuple<LiveSet...> const &);
        template <typename... LiveSet>
        StackElemRef smod_by_mask(
            StackElemRef, uint256_t const &mask,
            std::tuple<LiveSet...> const &);
        template <bool is_smod>
        bool mod_optimized();

        template <typename... LiveSet>
        void jump_stack_elem_dest(StackElemRef, std::tuple<LiveSet...> const &);
        uint256_t literal_jump_dest_operand(StackElemRef);
        asmjit::Label const &jump_dest_label(uint256_t const &);
        void jump_literal_dest(uint256_t const &);
        template <typename... LiveSet>
        std::pair<Operand, std::optional<StackElem *>>
        non_literal_jump_dest_operand(
            StackElemRef const &, std::tuple<LiveSet...> const &);
        void jump_non_literal_dest(
            StackElemRef, Operand const &, std::optional<StackElem *>);
        void conditional_jmp(asmjit::Label const &, Comparison);
        Comparison jumpi_comparison(StackElemRef cond, StackElemRef dest);
        void jumpi_spill_fallthrough_stack();
        void jumpi_keep_fallthrough_stack();

        void read_context_address(int32_t offset);
        void read_context_word(int32_t offset);
        void read_context_uint32_to_word(int32_t offset);
        void read_context_uint64_to_word(int32_t offset);

        void lt(StackElemRef dst, StackElemRef src);
        void slt(StackElemRef dst, StackElemRef src);

        void byte_literal_ix(uint256_t const &ix, StackOffset src);
        void
        byte_general_reg_or_stack_offset_ix(StackElemRef ix, StackOffset src);

        template <typename... LiveSet>
        void cmp_stack_elem_to_uint16(
            StackElemRef, uint16_t, std::tuple<LiveSet...> const &);

        void signextend_literal_ix(uint256_t const &ix, StackElemRef src);
        template <typename... LiveSet>
        void signextend_stack_elem_ix(
            StackElemRef ix, StackElemRef src, std::tuple<LiveSet...> const &);

        enum class ShiftType
        {
            SHL,
            SHR,
            SAR
        };

        template <ShiftType shift_type, typename... LiveSet>
        StackElemRef shift_by_stack_elem(
            StackElemRef shift, StackElemRef, std::tuple<LiveSet...> const &);

        template <ShiftType shift_type, typename... LiveSet>
        void setup_shift_stack(
            StackElemRef, int32_t additional_byte_count,
            std::tuple<LiveSet...> const &);

        template <ShiftType shift_type, typename... LiveSet>
        StackElemRef shift_by_literal(
            uint256_t const &shift, StackElemRef,
            std::tuple<LiveSet...> const &);

        template <ShiftType shift_type, typename... LiveSet>
        StackElemRef shift_by_general_reg_or_stack_offset(
            StackElemRef shift, StackElemRef, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        std::tuple<StackElemRef, LocationType, StackElemRef, LocationType>
        prepare_general_dest_and_source(
            bool commutative, StackElemRef dst, StackElemRef src,
            std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        std::tuple<StackElemRef, LocationType, StackElemRef, LocationType>
        get_general_dest_and_source(
            bool commutative, StackElemRef dst, StackElemRef src,
            std::tuple<LiveSet...> const &);

        Operand get_operand(
            StackElemRef, LocationType, bool always_add_literal = false);

        template <
            GeneralBinInstr<asmjit::x86::Gp, asmjit::x86::Gp> GG,
            GeneralBinInstr<asmjit::x86::Gp, asmjit::x86::Mem> GM,
            GeneralBinInstr<asmjit::x86::Gp, asmjit::Imm> GI,
            GeneralBinInstr<asmjit::x86::Mem, asmjit::x86::Gp> MG,
            GeneralBinInstr<asmjit::x86::Mem, asmjit::Imm> MI>
        void general_bin_instr(
            StackElemRef dst, LocationType dst_loc, StackElemRef src,
            LocationType src_loc,
            std::function<bool(size_t, uint64_t)> is_no_operation);

        template <typename... LiveSet>
        std::tuple<StackElemRef, StackElemRef, LocationType> get_una_arguments(
            bool is_dst_mutated, StackElemRef dst,
            std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        std::tuple<StackElemRef, LocationType, StackElemRef, LocationType>
        prepare_avx_or_general_arguments_commutative(
            StackElemRef dst, StackElemRef src, std::tuple<LiveSet...> const &);

        template <typename... LiveSet>
        std::tuple<
            StackElemRef, StackElemRef, LocationType, StackElemRef,
            LocationType>
        get_avx_or_general_arguments_commutative(
            StackElemRef dst, StackElemRef src, std::tuple<LiveSet...> const &);

        template <
            GeneralBinInstr<asmjit::x86::Gp, asmjit::x86::Gp> GG,
            GeneralBinInstr<asmjit::x86::Gp, asmjit::x86::Mem> GM,
            GeneralBinInstr<asmjit::x86::Gp, asmjit::Imm> GI,
            GeneralBinInstr<asmjit::x86::Mem, asmjit::x86::Gp> MG,
            GeneralBinInstr<asmjit::x86::Mem, asmjit::Imm> MI,
            AvxBinInstr<asmjit::x86::Vec> VV, AvxBinInstr<asmjit::x86::Mem> VM>
        void avx_or_general_bin_instr(
            StackElemRef dst, StackElemRef left, LocationType left_loc,
            StackElemRef right, LocationType right_loc,
            std::function<bool(size_t, uint64_t)> is_no_operation);

        template <typename... LiveSet>
        std::tuple<
            StackElemRef, Emitter::LocationType, StackElemRef,
            Emitter::LocationType>
        prepare_mod2_bin_dest_and_source(
            StackElemRef dst, StackElemRef src, size_t exp,
            std::tuple<LiveSet...> const &live);
        template <typename... LiveSet>
        std::tuple<
            StackElemRef, Emitter::LocationType, StackElemRef,
            Emitter::LocationType>
        get_mod2_bin_dest_and_source(
            StackElemRef dst_in, StackElemRef src_in, size_t exp,
            std::tuple<LiveSet...> const &live);
        void mov_stack_elem_to_general_reg_mod2(StackElemRef elem, size_t exp);
        void
        mov_stack_offset_to_general_reg_mod2(StackElemRef elem, size_t exp);
        void mov_literal_to_general_reg_mod2(StackElemRef elem, size_t exp);
        void add_mod2(StackElemRef left, StackElemRef right, size_t exp);
        void mul_mod2(StackElemRef left, StackElemRef right, size_t exp);

        using ModOpType = uint256_t (*)(
            uint256_t const &, uint256_t const &, uint256_t const &);
        using ModOpByMaskType =
            void (Emitter::*)(StackElemRef, StackElemRef, size_t exp);
        template <
            ModOpType ModOp, uint64_t Unit, uint64_t Absorb,
            ModOpByMaskType ModOpByMask>
        bool modop_optimized();

        ////////// Fields //////////

        // Order of fields is significant.
        EmitErrorHandler error_handler_;
        asmjit::CodeHolder code_holder_;
        asmjit::FileLogger debug_logger_;
        bool runtime_debug_trace_;
        asmjit::x86::Assembler as_;
        asmjit::Label epilogue_label_;
        asmjit::Label error_label_;
        asmjit::Label jump_table_label_;
        Stack stack_;
        bool keep_stack_in_next_block_;
        std::array<Gpq256, 3> gpq256_regs_;
        uint64_t bytecode_size_;
        std::unordered_map<byte_offset, asmjit::Label> jump_dests_;
        RoData rodata_;
        std::vector<std::tuple<asmjit::Label, Gpq256, asmjit::Label>>
            byte_out_of_bounds_handlers_;
        std::vector<std::tuple<asmjit::Label, asmjit::x86::Mem, asmjit::Label>>
            load_bounded_le_handlers_;
        std::vector<std::pair<asmjit::Label, std::string>> debug_messages_;
    };
}
