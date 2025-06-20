// Copyright (C) 2025 Category Labs, Inc.
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

#include "command.hpp"
#include "file.hpp"
#include "iterator.hpp"
#include "options.hpp"
#include "stream.hpp"

#include <bit>
#include <cstdint>
#include <memory>
#include <print>
#include <span>
#include <string>

#include <openssl/evp.h>
#include <openssl/types.h>

#include <category/core/hex.hpp>

namespace
{

struct State
{
    EVP_MD_CTX *hash_ctx;
    DigestCommandOptions const *options;
};

EVP_MD const *g_sha256_md;

std::string digest_init(StreamObserver *so)
{
    if (g_sha256_md == nullptr) {
        g_sha256_md = EVP_sha256();
    }
    std::unique_ptr state = std::make_unique<State>();
    state->hash_ctx = EVP_MD_CTX_create();
    if (EVP_DigestInit_ex(state->hash_ctx, g_sha256_md, nullptr) != 1) {
        return "EVP_DigestInit_ex failed";
    }
    state->options = so->command->get_options<DigestCommandOptions>();
    so->state = state.release();
    return {};
}

std::string digest_iter_init(StreamObserver *, EventIterator *)
{
    return {};
}

StreamUpdateResult
digest_update(StreamObserver *so, EventIterator *iter, StreamEvent *e)
{
    State *const state = so->get_state<State>();
    DigestCommandOptions const *options = state->options;

    if (e->iter_result != EventIteratorResult::Success) {
        return StreamUpdateResult::Abort;
    }

    // Compute the digest of the payload first; we might set the
    // payload_buf_offset to zero to better compare against snapshots, which
    // might have a different buffer layout order, and clearing it early will
    // break monad_event_payload_check
    EVP_DigestUpdate(state->hash_ctx, e->payload, e->event.payload_size);
    if (!iter->check_payload(&e->event)) {
        stream_warnx_f(
            so,
            "event {} payload lost! OFFSET: {}, WINDOW_START: {}",
            e->event.seqno,
            e->event.payload_buf_offset,
            iter->ring.mapped_event_ring->get_buffer_window_start());
        return StreamUpdateResult::Abort;
    }
    if (options->erase_timestamps) {
        e->event.record_epoch_nanos = 0;
    }
    if (options->erase_payload_offset) {
        e->event.payload_buf_offset = 0;
    }
    uint8_t resid_mask = options->erase_content_ext_mask;
    while (resid_mask != 0) {
        auto const to_clear = std::countr_zero(resid_mask);
        e->event.content_ext[to_clear] = 0;
        resid_mask &= ~static_cast<uint8_t>(1U << to_clear);
    }
    EVP_DigestUpdate(state->hash_ctx, &e->event, sizeof e->event);

    return StreamUpdateResult::Ok;
}

void digest_finish(StreamObserver *so, StreamUpdateResult)
{
    using monad::as_hex;
    uint8_t event_digest[32];

    State *const state = so->get_state<State>();
    OutputFile const *out = so->command->output;

    EVP_DigestFinal_ex(state->hash_ctx, event_digest, nullptr);
    EVP_MD_CTX_destroy(state->hash_ctx);
    std::println(
        out->file,
        "{} message digest: {:}",
        so->get_event_source().describe(),
        as_hex(std::as_bytes(std::span{event_digest})));

    delete state;
}

} // End of anonymous namespace

StreamObserverOps const digest_ops = {
    .init = digest_init,
    .iter_init = digest_iter_init,
    .update = digest_update,
    .finish = digest_finish,
};
