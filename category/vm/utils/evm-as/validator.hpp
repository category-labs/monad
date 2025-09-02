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

#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/utils/evm-as/builder.hpp>
#include <category/vm/utils/evm-as/instruction.hpp>
#include <category/vm/utils/evm-as/resolver.hpp>

#include <evmc/evmc.h>

#include <limits>
#include <set>
#include <variant>
#include <vector>

namespace monad::vm::utils::evm_as
{
    struct ValidationError
    {
        size_t offset;
        std::string msg;
    };
}

namespace monad::vm::utils::evm_as::internal
{
    using namespace monad::vm::utils::evm_as;

    // The initial version of the validator is somewhat simple and will
    // reject many programs that are fine. It provides a quick way to
    // check some common errors. If the validator proves to be useful,
    // then we can improve its precision, e.g. by building the basic
    // block structure and doing a control flow analysis.
    template <Traits traits, bool collect_errors>
    struct EvmDebugValidator
    {

        explicit EvmDebugValidator(std::vector<ValidationError> &errors)
            : errors(errors)
            , vstack_size(0)
            , pos(0)
        {
        }

        bool validate(EvmBuilder<traits> const &eb)
        {
            // Validate labels
            std::set<std::string> labels{};
            size_t i = 0;
            for (auto const &ins : eb) {
                pos = i++;
                std::visit(
                    Cases{
                        [this](PushLabelI const &push) {
                            check_label(push.label);
                        },
                        [&labels, this](JumpdestI const &jumpdest) {
                            check_label(jumpdest.label);
                            auto const [it, inserted] =
                                labels.insert(jumpdest.label);
                            // Is the label already defined?
                            if (!inserted) {
                                error(
                                    pos,
                                    std::format(
                                        "Multiply defined label '{}'",
                                        jumpdest.label));
                            }
                        },
                        [](auto const &) {}},
                    ins);
            }

            i = 0;
            for (auto const &ins : eb) {
                pos = i++;
                std::visit(
                    Cases{
                        [&labels, this](PushLabelI const &push) {
                            auto it = labels.find(push.label);
                            if (it == labels.end()) {
                                error(
                                    pos,
                                    std::format(
                                        "Undefined label '{}'", push.label));
                            }
                        },
                        [](auto const &) {}},
                    ins);
            }

            // Validate stack
            i = 0;
            for (auto const &ins : eb) {
                pos = i++;
                if (!std::visit(*this, ins)) {
                    // Stop accumulating errors on stack{over,under}flow
                    break;
                }
            }
            return result;
        }

        bool operator()(PlainI const &plain)
        {
            auto const &info = compiler::opcode_table<traits>[plain.opcode];
            if (vstack_size < info.min_stack) {
                error(pos, "Stack underflow");
                return false;
            }

            vstack_size = (vstack_size - info.min_stack) + info.stack_increase;

            return check_stackoverflow();
        }

        bool operator()(PushI const &)
        {
            vstack_size += 1;
            return check_stackoverflow();
        }

        bool operator()(PushLabelI const &)
        {
            vstack_size += 1;
            return check_stackoverflow();
        }

        bool operator()(InvalidI const &invalid)
        {
            if (invalid.has_name()) {
                error(
                    pos, std::format("Invalid instruction '{}'", invalid.name));
            }
            else {
                error(pos, "Invalid instruction");
            }
            return true;
        }

        bool operator()(auto const &)
        {
            return true;
        }

    private:
        bool check_stackoverflow()
        {
            if (vstack_size > 1024) {
                error(pos, "Stack overflow");
                return false;
            }
            return true;
        }

        bool check_label(std::string const &label)
        {
            // TODO: check that the string contains only alphanums.
            if (label == "") {
                error(pos, "Empty label");
                return false;
            }
            return true;
        }

        void error(size_t pos, std::string &&msg)
        {
            result = false;
            if constexpr (collect_errors) {
                errors.emplace_back(ValidationError{pos, std::move(msg)});
            }
            else {
                (void)pos;
                (void)msg;
            }
        }

        std::vector<ValidationError> &errors;
        size_t vstack_size = 0;
        size_t pos = 0;
        bool result = true;
    };

}

namespace monad::vm::utils::evm_as
{
    template <Traits traits>
    bool
    validate(EvmBuilder<traits> const &eb, std::vector<ValidationError> &errors)
    {
        internal::EvmDebugValidator<traits, true> v(errors);
        return v.validate(eb);
    }

    template <Traits traits>
    bool validate(EvmBuilder<traits> const &eb)
    {
        std::vector<ValidationError> errors;
        internal::EvmDebugValidator<traits, false> v(errors);
        return v.validate(eb);
    }
}
