#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/account_fmt.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/spmc_stream.h>

#include <CLI/CLI.hpp>

#include <quill/Fmt.h>
#include <quill/Quill.h>

#include <algorithm>
#include <signal.h>
#include <span>

namespace fmt = fmtquill::v10;

sig_atomic_t volatile stop;

void signal_handler(int)
{
    stop = 1;
}

int main(int const argc, char const *argv[])
{
    using namespace monad;
    CLI::App cli{"replay_ethereum"};
    cli.option_defaults()->always_capture_default();

    std::string name;
    cli.add_option("--name", name, "shared memory name")->required();

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        return cli.exit(e);
    }
    catch (CLI::RequiredError const &e) {
        return cli.exit(e);
    }

    quill::start(true);

    auto *stream = spmc_stream_create(name.c_str(), false);
    while (stream == nullptr) {
        stream = spmc_stream_create(name.c_str(), false);
    }

    LOG_INFO("listening for events from shm {}", name);

    struct Context
    {
        unsigned long long seq = 0;
        size_t size;
        char buf[SPMC_STREAM_MAX_PAYLOAD_SIZE];
    } ctx;

    auto const handler = [](unsigned long long const seq,
                            void const volatile *const buf,
                            size_t const size,
                            void *const context) {
        MONAD_ASSERT(size > 0);
        auto &ctx = *reinterpret_cast<Context *>(context);
        ctx.seq = seq;
        ctx.size = size;
        for (size_t i = 0;
             i < std::min(size, (size_t)SPMC_STREAM_MAX_PAYLOAD_SIZE);
             ++i) {
            ctx.buf[i] = reinterpret_cast<char const volatile *>(buf)[i];
        }
    };

    stop = 0;
    unsigned long long seq = 0;
    bool skip = false;
    while (stop == 0) {
        auto const res = spmc_stream_pop(stream, handler, (void *)&ctx);
        if (res == EAGAIN || res == ECANCELED) {
            continue;
        }
        if ((seq + 2) != ctx.seq) {
            MONAD_ASSERT(ctx.seq > seq);
            LOG_WARNING("gap expected {} got {}", seq + 2, ctx.seq);
            seq = ctx.seq;
            skip = true;
            continue;
        }
        seq = ctx.seq;
        if (ctx.buf[0] == 'A') {
            skip = false;
            if (ctx.size == (sizeof(Address) + 1)) {
                LOG_INFO(
                    "addr={} DELETED",
                    *reinterpret_cast<Address const *>(ctx.buf + 1));
            }
            else {
                MONAD_ASSERT(
                    ctx.size == (sizeof(Address) + sizeof(Account) + 1));
                LOG_INFO(
                    "addr={} {}",
                    *reinterpret_cast<Address const *>(ctx.buf + 1),
                    *reinterpret_cast<Account const *>(
                        ctx.buf + 1 + sizeof(Address)));
            }
        }
        else if (!skip) {
            MONAD_ASSERT(ctx.buf[0] == 'S');
            MONAD_ASSERT(((ctx.size - 1) % (sizeof(bytes32_t) * 2)) == 0);
            auto const nstorage = (ctx.size - 1) / (sizeof(bytes32_t) * 2);
            auto const *const sbuf =
                reinterpret_cast<bytes32_t const *>(ctx.buf + 1);
            for (size_t i = 0; i < nstorage; ++i) {
                auto const &val = sbuf[i * 2 + 1];
                if (val == bytes32_t{}) {
                    LOG_INFO("\t {}=DELETED", sbuf[i * 2]);
                }
                else {
                    LOG_INFO("\t {}={}", sbuf[i * 2], val);
                }
            }
        }
    }
    spmc_stream_destroy(stream);
}
