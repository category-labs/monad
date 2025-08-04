#pragma once

#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>
#include <category/vm/evm/opcodes.hpp>
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
    template <evmc_revision Rev, bool collect_errors>
    struct EvmDebugValidator
    {

        explicit EvmDebugValidator(std::vector<ValidationError> &errors)
            : errors(errors)
            , vstack_size(0)
            , pos(0)
        {
        }

        bool validate(EvmBuilder<Rev> const &eb)
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
                                    std::move(std::format(
                                        "Multiply defined label '{}'",
                                        jumpdest.label)));
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
                                    std::move(std::format(
                                        "Undefined label '{}'", push.label)));
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
            auto const &info = compiler::opcode_table<Rev>[plain.opcode];
            if (vstack_size < info.min_stack) {
                error(pos, std::move("Stack underflow"));
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
                    pos,
                    std::move(
                        std::format("Invalid instruction '{}'", invalid.name)));
            }
            else {
                error(pos, std::move("Invalid instruction"));
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
                error(pos, std::move("Stack overflow"));
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
    template <evmc_revision Rev>
    bool
    validate(EvmBuilder<Rev> const &eb, std::vector<ValidationError> &errors)
    {
        internal::EvmDebugValidator<Rev, true> v(errors);
        return v.validate(eb);
    }

    template <evmc_revision Rev>
    bool validate(EvmBuilder<Rev> const &eb)
    {
        std::vector<ValidationError> errors;
        internal::EvmDebugValidator<Rev, false> v(errors);
        return v.validate(eb);
    }
}
