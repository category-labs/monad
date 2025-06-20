#include "parse.hpp"
#include "command.hpp"

#include <algorithm>
#include <cctype>
#include <charconv>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <expected>
#include <format>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>

#include <category/core/assert.h>
#include <category/core/event/evcap_file.h>
#include <category/core/event/event_def.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

namespace
{

template <std::integral I>
std::string parse_integer_token(std::string_view tok, I &value)
{
    char const *scan = tok.data();
    char const *const end = scan + tok.length();
    auto const [ptr, errc] = std::from_chars(scan, end, value);
    if (int const ec = static_cast<int>(errc)) {
        return std::format(
            "invalid integer token {}: {} [{}]", tok, strerror(ec), ec);
    }
    if (ptr != end) {
        return std::format("invalid integer token {}", tok);
    }
    return {};
}

std::string parse_section_param(EventSourceQuery *q, std::string_view value)
{
    std::optional<uint64_t> offset;

    if (std::ranges::all_of(value, [](char c) { return std::isdigit(c); })) {
        // The value is an integer token; this has an unspecified seek origin,
        // and is left to be interpreted in the "natural" way by the command
        std::string err = parse_integer_token(value, offset.emplace());
        if (!err.empty()) {
            return err;
        }
        CaptureSectionSpec &css = q->section.emplace();
        css.origin = CaptureSectionSpec::SeekOrigin::Unspecified;
        css.offset = offset;
        return {};
    }

    // The value is expected to have the format `<origin>[.<offset>]`
    auto const dot_index = value.find('.');
    if (dot_index != std::string_view::npos) {
        std::string_view const offset_token = value.substr(dot_index + 1);
        std::string const err =
            parse_integer_token(offset_token, offset.emplace());
        if (!err.empty()) {
            return std::format(
                "parse error in section offset {} in {}: {}",
                offset_token,
                value,
                err);
        }
        // Reseat `value` to be just the <origin>
        value = value.substr(0, dot_index);
    }

    // <origin> is one of the following:
    //
    //   1. The word "abs" (absolute); `offset` must be present and is the
    //      literal index of the corresponding section in the section table
    //
    //   2. The name of a section descriptor type; `offset` is relative
    //      address of the section, when iterating over section descriptors
    //      of that type only, e.g., `EVENT_BUNDLE.0` names the first event
    //      bundle section
    //
    //   3. The name of a content type; `offset` is the relative address of
    //      the section, when iterating over event bundle sections having
    //      that content type
    if (value == "abs") {
        if (!offset) {
            return "'abs' section address must be followed by "
                   "`.<section-index>`";
        }
        CaptureSectionSpec &css = q->section.emplace();
        css.origin = CaptureSectionSpec::SeekOrigin::Absolute;
        css.offset = offset;
        return {};
    }

    for (uint16_t t = 0; t < MONAD_EVCAP_SECTION_COUNT; ++t) {
        if (value == g_monad_evcap_section_names[t]) {
            CaptureSectionSpec &css = q->section.emplace();
            css.origin = CaptureSectionSpec::SeekOrigin::SectionType;
            css.section_type = static_cast<monad_evcap_section_type>(t);
            css.offset = offset;
            return {};
        }
    }

    for (uint16_t t = 0; t < MONAD_EVENT_CONTENT_TYPE_COUNT; ++t) {
        if (value == g_monad_event_content_type_names[t]) {
            CaptureSectionSpec &css = q->section.emplace();
            css.origin = CaptureSectionSpec::SeekOrigin::ContentType;
            css.content_type = static_cast<monad_event_content_type>(t);
            css.offset = offset;
            return {};
        }
    }

    return std::format("could not parse `{}` as a section base", value);
}

std::string parse_block_label_param(EventSourceQuery *q, std::string_view value)
{
    constexpr size_t MinHashLength = 4;
    BlockLabel &block_label = q->block.emplace();
    if (value.starts_with("0x")) {
        uint8_t byte;
        char const *p = value.data() + 2;
        char const *const end = value.data() + value.length();
        while (p + 1 < end && std::sscanf(p, "%2hhx", &byte) == 1) {
            block_label.block_id.push_back(byte);
            p += 2;
        }
        if (block_label.block_id.size() < MinHashLength) {
            return std::format(
                "block_id prefix must be at least {} bytes long, found short "
                "id `{}`",
                MinHashLength,
                value);
        }
        block_label.type = BlockLabel::Type::BlockId;
        return {};
    }
    else {
        block_label.type = BlockLabel::Type::BlockNumber;
        std::string err = parse_integer_token(value, block_label.block_number);
        if (!err.empty()) {
            return err;
        }
        if (block_label.block_number == 0) {
            return "0 is not a valid block number";
        }
        return {};
    }
}

std::string
parse_consensus_event_param(EventSourceQuery *q, std::string_view value)
{
    if (value.empty()) {
        return "consensus event spec cannot be empty";
    }
    if (value.length() != 1) {
        return std::format(
            "expected single letter consensus event code, found {}", value);
    }
    switch (std::tolower(value[0])) {
    case 'e':
        [[fallthrough]];
    case 'p':
        q->consensus_event = MONAD_EXEC_BLOCK_START;
        break;
    case 'f':
        q->consensus_event = MONAD_EXEC_BLOCK_FINALIZED;
        break;
    case 'q':
        q->consensus_event = MONAD_EXEC_BLOCK_QC;
        break;
    case 'v':
        q->consensus_event = MONAD_EXEC_BLOCK_VERIFIED;
        break;
    case 'r':
        q->consensus_event = MONAD_EXEC_NONE;
        break;
    default:
        return std::format(
            "'{:c}' is a recognized consensus event code", value[0]);
    }
    return {};
}

std::string parse_count_param(EventSourceQuery *q, std::string_view value)
{
    if (value != "*") {
        return parse_integer_token(value, q->count.emplace());
    }
    return {};
}

struct QueryParamTableEntry
{
    std::string_view name;
    char abbreviation;
    std::string (*parse_param_fn)(EventSourceQuery *, std::string_view);
};

constexpr QueryParamTableEntry QueryParamTable[] = {
    {
        .name = "section",
        .abbreviation = 's',
        .parse_param_fn = parse_section_param,
    },
    {
        .name = "block",
        .abbreviation = 'b',
        .parse_param_fn = parse_block_label_param,
    },
    {
        .name = "exec",
        .abbreviation = 'e',
        .parse_param_fn = parse_consensus_event_param,
    },
    {
        .name = "count",
        .abbreviation = 'c',
        .parse_param_fn = parse_count_param,
    },
};

} // anonymous namespace

// parse_event_source_spec
//
// Grammar:
//
//    <event-source-spec> ::=
//        [<input-name> ':'] <event-source-file> ['?' [<event-source-query>]]
//
//  The only required component, <event-source-file>, can be one of four things:
//
//  1. a path to a regular file; this can either be an event ring file (live,
//     abandoned, or compressed snapshot) or an event capture file
//
//  2. a path to a finalized block archive directory
//
//  3. the name of an event ring type (e.g., `exec` or `test`)
//
//  4. the label of a "named input" created by the -i,--input option; this
//     allows multiple subcommands to easily reference the same file path, e.g.:
//
//        monad-event-cli -i foo:/very/long/path dump -e foo info foo
//
// The optional [<name> ':'] component introduces a new named input at the same
// time is it defines a source specification; the named input refers only to
// the file, and not the trailing source query
//
// The optional ['?' [<event-source-query]] is used to select part of an event
// ring file, capture file, or archive, based on certain filter conditions
std::expected<EventSourceSpecComponents, std::string>
parse_event_source_spec(std::string_view event_source_spec)
{
    EventSourceSpecComponents comp{};
    if (empty(event_source_spec)) {
        return comp;
    }

    // Find the query string if it is present
    auto const question_index = event_source_spec.find('?');
    if (question_index != std::string_view::npos) {
        comp.event_source_query = event_source_spec.substr(question_index + 1);
        event_source_spec = event_source_spec.substr(0, question_index);
    }

    // <event-source-spec> can introduce a new named input
    auto const colon_index = event_source_spec.find(':');
    if (colon_index != std::string_view::npos) {
        comp.named_input = event_source_spec.substr(0, colon_index);
        comp.event_source_file = event_source_spec.substr(colon_index + 1);
    }
    else {
        comp.event_source_file = event_source_spec;
    }

    return comp;
}

// Grammar:
//
//    <event-source-query> ::= [<param>] ([','] <param>)*
//    <param> ::= <name> '=' <value>
//
// Recognized names, their single-character abbreviated form, and the expected
// value domains:
//
//    name      | abr | value domain
//    --------- | --- | ------------
//    section   |  s  | event capture section specification
//    block     |  b  | block label, either number or (partial) hash32 ID
//    exec      |  e  | consensus event code (exec event content only)
//    count     |  c  | number of subsequent sections / blocks (or '*')
std::expected<EventSourceQuery, std::string>
parse_event_source_query(std::string_view query)
{
    EventSourceQuery q{};

    for (auto param : std::views::split(query, ',')) {
        if (param.empty()) {
            continue; // Allow empty parameters
        }
        char const *const data = std::ranges::data(param);
        char const *const equal = std::ranges::find(param, '=');
        if (equal == std::ranges::end(param)) {
            return std::unexpected(
                std::format("query parameter `{}` has no '=' token", param));
        }
        std::string_view const name{data, static_cast<size_t>(equal - data)};
        std::string_view const value{equal + 1, param.size() - name.size() - 1};
        if (name.empty()) {
            return std::unexpected("found empty parameter in query");
        }
        bool found = false;
        for (QueryParamTableEntry const &e : QueryParamTable) {
            if (name == e.name || std::tolower(name[0]) == e.abbreviation) {
                std::string const error = e.parse_param_fn(&q, value);
                if (!error.empty()) {
                    return std::unexpected(std::format(
                        "error parsing query attribute `{}={}`: {}",
                        name,
                        value,
                        error));
                }
                found = true;
            }
        }
        if (!found) {
            return std::unexpected(
                std::format("{} is not a valid query parameter", name));
        }
    }

    return q;
}
