#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/event/append_only_log_emitter.hpp>

#include <evmc/hex.hpp>

using std::ios;

MONAD_NAMESPACE_BEGIN

namespace
{

    constexpr auto EVENT_SIZE =
        static_cast<std::streamoff>(sizeof(monad_execution_event));
}

AppendOnlyLogEmitter::AppendOnlyLogEmitter(std::filesystem::path const &path)
{
    cursor_.open(path, std::ios::binary);
    MONAD_ASSERT(cursor_);
}

std::optional<AppendOnlyLogEmitter::Event> AppendOnlyLogEmitter::next_event()
{
    monad_execution_event ev;
    auto const pos = cursor_.tellg();
    if (MONAD_LIKELY(cursor_.read(
            reinterpret_cast<char *>(&ev), sizeof(monad_execution_event)))) {
        return Event{
            .kind = ev.kind,
            .filename =
                evmc::hex(byte_string_view{std::bit_cast<bytes32_t>(ev.id)})};
    }
    else {
        // execution got ahead
        cursor_.clear();
        cursor_.seekg(pos);
        return {};
    }
}

bool AppendOnlyLogEmitter::rewind_to_event(
    monad_execution_event const &rewind_ev)
{
    cursor_.seekg(0, ios::end);
    auto const size_on_start = cursor_.tellg();
    cursor_.seekg(0, ios::beg);

    if (size_on_start >= EVENT_SIZE) {
        auto const pos = (size_on_start / EVENT_SIZE) * EVENT_SIZE - EVENT_SIZE;
        cursor_.seekg(pos);
        while (cursor_) {
            monad_execution_event ev;
            if (!cursor_.read(
                    reinterpret_cast<char *>(&ev),
                    sizeof(monad_execution_event))) {
                MONAD_ASSERT(false);
            }

            if (std::bit_cast<bytes32_t>(ev.id) ==
                    std::bit_cast<bytes32_t>(rewind_ev.id) &&
                ev.kind == rewind_ev.kind) {
                cursor_.seekg(-EVENT_SIZE, ios::cur);

                return true;
            }

            cursor_.seekg(-2 * EVENT_SIZE, ios::cur);
        }
    }
    cursor_.clear();
    cursor_.seekg(0, ios::beg);

    return false;
}

MONAD_NAMESPACE_END
