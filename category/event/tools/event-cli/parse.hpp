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

#pragma once

#include <expected>
#include <string>
#include <string_view>

struct EventSourceQuery;

// Represents the tokenized form of an <event-source-spec>, without fully
// parsing the <event-source-query> or resolving anything
struct EventSourceSpecComponents
{
    std::string named_input;
    std::string event_source_file;
    std::string event_source_query;
};

std::expected<EventSourceSpecComponents, std::string>
parse_event_source_spec(std::string_view event_source_spec);

std::expected<EventSourceQuery, std::string>
parse_event_source_query(std::string_view query);
