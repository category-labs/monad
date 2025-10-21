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

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/utils/rc_ptr.hpp>

#include <evmc/evmc.hpp>

#include <compare>
#include <cstdint>
#include <optional>
#include <queue>
#include <set>
#include <variant>
#include <vector>

namespace monad::vm::compiler::native
{
    constexpr std::uint8_t AVX_REG_COUNT = 16;
    constexpr std::uint8_t GENERAL_REG_COUNT = 3;
    constexpr std::uint8_t CALLEE_SAVE_GENERAL_REG_ID = 0;

    struct Literal
    {
        uint256_t value;
    };

    bool operator==(Literal const &a, Literal const &b);

    struct StackOffset
    {
        std::int32_t offset;
    };

    bool operator==(StackOffset const &a, StackOffset const &b);

    struct AvxReg
    {
        std::uint8_t reg;
    };

    std::strong_ordering operator<=>(AvxReg const &a, AvxReg const &b);

    bool operator==(AvxReg const &a, AvxReg const &b);

    struct GeneralReg
    {
        std::uint8_t reg;
    };

    std::strong_ordering operator<=>(GeneralReg const &a, GeneralReg const &b);

    bool operator==(GeneralReg const &a, GeneralReg const &b);

    extern std::array<AvxReg, AVX_REG_COUNT> ALL_AVX_REGS;
    extern std::array<GeneralReg, GENERAL_REG_COUNT> ALL_GENERAL_REGS;

    class Stack;
    class StackElem;

    // Custom memory management of reference counted `StackElem`:
    struct StackElemDeleter;

    enum class Comparison
    {
        Below,
        AboveEqual,
        Above,
        BelowEqual,
        Less,
        GreaterEqual,
        Greater,
        LessEqual,
        Equal,
        NotEqual,
    };

    constexpr Comparison negate_comparison(Comparison c)
    {
        using enum Comparison;
        switch (c) {
        case Below:
            return AboveEqual;
        case AboveEqual:
            return Below;
        case Above:
            return BelowEqual;
        case BelowEqual:
            return Above;
        case Less:
            return GreaterEqual;
        case GreaterEqual:
            return Less;
        case Greater:
            return LessEqual;
        case LessEqual:
            return Greater;
        case Equal:
            return NotEqual;
        case NotEqual:
            return Equal;
        }

        std::unreachable();
    }

    struct DeferredComparison
    {
        DeferredComparison()
            : stack_elem{}
            , negated_stack_elem{}
            , comparison_{Comparison::Below}
        {
        }

        DeferredComparison(DeferredComparison const &) = default;
        DeferredComparison &operator=(DeferredComparison const &) = default;

        StackElem *stack_elem;
        StackElem *negated_stack_elem;

        Comparison comparison() const noexcept
        {
            MONAD_VM_DEBUG_ASSERT(stack_elem || negated_stack_elem);
            return comparison_;
        }

        void set(StackElem *const elem, Comparison const c) noexcept
        {
            MONAD_VM_DEBUG_ASSERT(!stack_elem && !negated_stack_elem);
            stack_elem = elem;
            comparison_ = c;
        }

    private:
        Comparison comparison_;
    };

    struct OperandLocations
    {
        std::optional<Literal> literal;
        std::optional<StackOffset> stack_offset;
        std::optional<AvxReg> avx_reg;
        std::optional<GeneralReg> general_reg;
        bool is_deferred_comparison;

        bool operator==(OperandLocations const &other) const
        {
            return literal == other.literal &&
                   stack_offset == other.stack_offset &&
                   avx_reg == other.avx_reg &&
                   general_reg == other.general_reg &&
                   is_deferred_comparison == other.is_deferred_comparison;
        }
    };

    /**
     * A stack element. It can store its word value in up to 4 locations at the
     * same time. The 4 locations are: `StackOffset`, `AvxReg`, `GeneralReg`,
     * `Literal`. It is important to note that holding a reference to
     * `StackElem` does not guarantee that the registers in the `StackElem` will
     * remain part of the `StackElem`. The `StackElem` is part of the stack, so
     * mutating the stack can mutate the `StackElem`. If a register in
     * `StackElem` has not been reserved with `AvxRegReserv` or
     * `GeneralRegReserv`, the stack is allowed to allocate the registers in for
     * other purposes. Make sure to reserve the registers you want to keep in
     * the `StackElem`. See `GeneralRegReserv` and `AvxRegReserv`.
     */
    class StackElem
    {
        friend class Stack;
        friend struct StackElemDeleter;

    public:
        explicit StackElem(Stack *);
        StackElem(StackElem const &) = delete;
        StackElem &operator=(StackElem const &) = delete;
        ~StackElem();

        std::int32_t preferred_stack_offset() const;

        std::optional<StackOffset> const &stack_offset() const
        {
            return stack_offset_;
        }

        std::optional<AvxReg> const &avx_reg() const
        {
            return avx_reg_;
        }

        std::optional<GeneralReg> const &general_reg() const
        {
            return general_reg_;
        }

        std::optional<Literal> const &literal() const
        {
            return literal_;
        }

        std::set<std::int32_t> const &stack_indices() const
        {
            return stack_indices_;
        }

        bool is_on_stack() const
        {
            return !stack_indices_.empty();
        }

        bool is_deferred_comparison() const;

        // Remember to match this with a call to `unreserve_avx_reg`.
        void reserve_avx_reg()
        {
            ++reserve_avx_reg_count_;
        }

        // Remember to match this with a call to `unreserve_general_reg`.
        void reserve_general_reg()
        {
            ++reserve_general_reg_count_;
        }

        void unreserve_avx_reg()
        {
            --reserve_avx_reg_count_;
        }

        void unreserve_general_reg()
        {
            --reserve_general_reg_count_;
        }

    private:
        void deferred_comparison(Comparison);
        void deferred_comparison();
        void negated_deferred_comparison();
        void discharge_deferred_comparison();
        void discharge_negated_deferred_comparison();

        void insert_literal(Literal);
        void insert_stack_offset(StackOffset);
        void insert_avx_reg();
        void insert_general_reg();

        void free_avx_reg();
        void free_general_reg();
        void free_stack_offset();

        void remove_avx_reg();
        void remove_general_reg();
        void remove_stack_offset();
        void remove_literal();

        Stack &stack_;
        std::set<std::int32_t> stack_indices_;
        std::uint32_t reserve_avx_reg_count_;
        std::uint32_t reserve_general_reg_count_;
        std::optional<StackOffset> stack_offset_;
        std::optional<AvxReg> avx_reg_;
        std::optional<GeneralReg> general_reg_;
        std::optional<Literal> literal_;
    };

    using StackElemRef = utils::RcPtr<StackElem, StackElemDeleter>;

    /**
     * An AVX register reservation. Can be used to ensure that the optional
     * AVX register in a `StackElem` will not be deallocated as long as the
     * `AvxRegReserv` object is alive.
     */
    class AvxRegReserv
    {
    public:
        explicit AvxRegReserv(StackElemRef e)
            : stack_elem_{std::move(e)}
        {
            stack_elem_->reserve_avx_reg();
        }

        AvxRegReserv(AvxRegReserv const &r)
            : AvxRegReserv{r.stack_elem_}
        {
        }

        AvxRegReserv &operator=(AvxRegReserv const &r)
        {
            stack_elem_->unreserve_avx_reg();
            stack_elem_ = r.stack_elem_;
            stack_elem_->reserve_avx_reg();
            return *this;
        }

        ~AvxRegReserv()
        {
            stack_elem_->unreserve_avx_reg();
        }

    private:
        StackElemRef stack_elem_;
    };

    /**
     * A general register reservation. Can be used to ensure that the optional
     * general register in a `StackElemRef` will not be deallocated as long as
     * the `GeneralRegReserv` object is alive. Be careful to never reserve more
     * than three different general purpose registers at the same time. Note
     * moreover that if three different general purpose registers are reserved
     * at the same time, it is not possible for the stack to spill or allocate
     * general registers. If only two or less general purpose registers are
     * reserved, then the stack will be able to use the remainig general
     * register.
     */
    class GeneralRegReserv
    {
    public:
        explicit GeneralRegReserv(StackElemRef e)
            : stack_elem_{std::move(e)}
        {
            stack_elem_->reserve_general_reg();
        }

        GeneralRegReserv(GeneralRegReserv const &r)
            : GeneralRegReserv{r.stack_elem_}
        {
        }

        GeneralRegReserv &operator=(GeneralRegReserv const &r)
        {
            stack_elem_->unreserve_general_reg();
            stack_elem_ = r.stack_elem_;
            stack_elem_->reserve_general_reg();
            return *this;
        }

        ~GeneralRegReserv()
        {
            stack_elem_->unreserve_general_reg();
        }

    private:
        StackElemRef stack_elem_;
    };

    class RegReserv
    {
    public:
        explicit RegReserv(StackElemRef e)
            : avx_reserv{e}
            , general_reserv{std::move(e)}
        {
        }

    private:
        AvxRegReserv avx_reserv;
        GeneralRegReserv general_reserv;
    };

    using AvxRegQueue =
        std::priority_queue<AvxReg, std::vector<AvxReg>, std::greater<>>;

    using GeneralRegQueue = std::priority_queue<
        GeneralReg, std::vector<GeneralReg>, std::greater<>>;

    /**
     * A `Stack` manages a virtual representation of the EVM stack, specialized
     * for the resources available on AVX2 x86 machines.
     *
     * This virtual representation can be interpreted by a code-generating
     * component to emit x86 code for an EVM basic block; no code is generated
     * by the stack itself when operations are performed. Instead, the wrapping
     * code is responsible for emitting code that _performs_ the concrete
     * operations corresponding to the virtual ones.
     */
    class Stack
    {
        friend class StackElem;
        friend struct StackElemDeleter;

    public:
        /*
         * A fresh stack. Need to call `begin_new_block` before the
         * the stack is ready to generate code for a basic block.
         */
        Stack();

        /*
         * A stack prepared for code generation of given basic block.
         */
        explicit Stack(basic_blocks::Block const &);

        ~Stack();

        /**
         * Prepare stack for code generation of the given block
         * with an initial stack state for the block.
         */
        void begin_new_block(basic_blocks::Block const &);

        /**
         * Prepare stack for code generation of the given block
         * and adapt the current stack state for the block.
         */
        void continue_block(basic_blocks::Block const &);

        /**
         * Obtain a reference to an item on the stack. Negative indices
         * refer to stack elements before the basic block's stack frame
         * and non-negative indices refer to stack elements on the basic
         * block's stack frame.
         */
        StackElemRef get(std::int32_t index);

        /**
         * Obtain a reference to the top item of the stack.
         */
        StackElemRef top();

        /**
         * Pop the top element from the stack.
         */
        StackElemRef pop();

        /**
         * Push a stack element onto the top of the stack, updating book-keeping
         * information.
         */
        void push(StackElemRef);

        /**
         * Push a deferred comparison onto the top of the stack, updating
         * book-keeping information.
         */
        void push_deferred_comparison(Comparison);

        /**
         * If given stack elem is deferred comparison, then negate it.
         * Returns null if the stack elem is not a deferred comparison.
         */
        StackElemRef negate_if_deferred_comparison(StackElemRef);

        /**
         * Push a literal onto the top of the stack, updating book-keeping
         * information.
         */
        void push_literal(uint256_t const &);

        /**
         * Push a duplicate of the specified stack element to the top of the
         * stack.
         */
        void dup(std::int32_t stack_index);

        /**
         * Swap the top element of the stack with the one at the specified
         * index.
         */
        void swap(std::int32_t swap_index);

        /**
         * Clear deferred comparison and insert a stack offset to the
         * corresponding stack elements. Returns the old `DeferredComparison`
         * containing the stack elements.
         * WARNING. Be careful about keeping the `DeferredComparison` object
         * alive, because if it outlives its stack elements, then the stack
         * element pointers in `DeferredComparison` becomes dangling pointers.
         * Note that it is always safe if the `DeferredComparison` object never
         * leaves its scope and no elements are removed from the stack while the
         * `DeferredComparison` is live.
         */
        DeferredComparison discharge_deferred_comparison();

        /**
         * Get current deferred comparison. Same warning here as
         * `discharge_deferred_comparison`.
         */
        DeferredComparison peek_deferred_comparison()
        {
            return deferred_comparison_;
        }

        /**
         * Whether there is a deferred comparison stack element.
         */
        bool has_deferred_comparison_at(std::int32_t stack_index) const;
        bool has_deferred_comparison() const;

        /**
         * Build a stack element with the given literal.
         */
        StackElemRef alloc_literal(Literal);

        /**
         * Find an available physical stack offset that can be used to spill the
         * virtual stack item at this index, and mark that physical index as
         * allocated. Returns a stack element holding the offset.
         */
        StackElemRef alloc_stack_offset(std::int32_t stack_index);

        /**
         * Allocate an AVX register.
         * If the optional StackOffset has a value, then make sure
         * to emit mov instruction from the AVX register to stack offset.
         */
        [[nodiscard]]
        std::tuple<StackElemRef, AvxRegReserv, std::optional<StackOffset>>
        alloc_avx_reg();

        /**
         * Allocate general register.
         * If the optional StackOffset has a value, then make sure
         * to emit mov instruction from the general register to stack offset.
         */
        [[nodiscard]]
        std::tuple<StackElemRef, GeneralRegReserv, std::optional<StackOffset>>
        alloc_general_reg();

        /**
         * Find a stack offset for the given stack element. The given
         * `preferred_offset` will be used as offset if it is available.
         */
        void insert_stack_offset(StackElemRef, std::int32_t preferred_offset);
        void insert_stack_offset(StackElem &, std::int32_t preferred_offset);

        /**
         * Find a stack offset for the given stack element.
         */
        void insert_stack_offset(StackElemRef);
        void insert_stack_offset(StackElem &);

        /**
         * Remove stack offset from `elem` and return a new stack element
         * containing the stack offset register.
         */
        StackElemRef release_stack_offset(StackElemRef elem);

        /**
         * Find an AVX register for the given stack element.
         * If the optional StackOffset has a value, then make sure
         * to emit mov instruction from the AVX register to stack offset.
         */
        [[nodiscard]]
        std::pair<AvxRegReserv, std::optional<StackOffset>>
            insert_avx_reg(StackElemRef);
        [[nodiscard]]
        std::optional<StackOffset> insert_avx_reg_without_reserv(StackElem &);

        /**
         * Find a stack element holding an AVX register from the stack,
         * which can be spilled from the stack element. It is required
         * that at least one stack element is holding an avx register
         * which can be spilled.
         */
        StackElem *find_stack_elem_for_avx_reg_spill();

        /**
         * Find an AVX register from the stack and spill it by adding it to
         * the set `free_avx_regs_`.
         * If a non-null stack element is returned, then make sure to emit
         * mov instruction from the spilled AVX register to the stack element's
         * stack offset. The stack offset which is guaranteed to be a location
         * of the stack element.
         */
        [[nodiscard]]
        StackElem *spill_avx_reg();
        [[nodiscard]]
        StackElem *spill_avx_reg(StackElemRef);
        [[nodiscard]]
        StackElem *spill_avx_reg(StackElem *);

        /**
         * Remove general register from `elem` and return a new stack element
         * containing the general register.
         */
        StackElemRef release_general_reg(StackElem &elem);
        StackElemRef release_general_reg(StackElemRef elem);

        /**
         * Move the general register in `src` to `dst`. It is required that
         * `src` does not need to spill its value to another location, even
         * if general register is the only location.
         */
        void move_general_reg(StackElem &src, StackElem &dst);

        /**
         * Swap the general registers in the stack elements. It is
         * required that both of the stack elements are having
         * general register locations.
         */
        void swap_general_regs(StackElem &, StackElem &);

        /**
         * Remove the general register. It is required that the
         * `StackElem` does not need to spill its value to another
         * location, even if general register is the only location.
         */
        void remove_general_reg(StackElem &);

        /**
         * Remove the stack offset. It is required that the
         * `StackElem` does not need to spill its value to another
         * location, even if stack offset is the only location.
         */
        void remove_stack_offset(StackElem &);

        /**
         * Remove stack offset location from the given stack element. It is
         * required and checked that the stack elements holds its value in
         * another location.
         */
        void spill_stack_offset(StackElemRef);

        /**
         * Remove literal location from the given stack element. It is
         * required and checked that the stack elements holds its value in
         * another location.
         */
        void spill_literal(StackElemRef);

        /**
         * Find an general register from the stack and spill it by adding it to
         * the set `free_general_regs_`.
         * If a non-null stack element is returned, then make sure to emit mov
         * instruction from the spilled general register to the stack element's
         * stack offset. The stack offset which is guaranteed to be a location
         * of the stack element.
         */
        [[nodiscard]]
        StackElem *spill_general_reg();
        [[nodiscard]]
        StackElem *spill_general_reg(StackElemRef);
        [[nodiscard]]
        StackElem *spill_general_reg(StackElem *);

        /**
         * The number of stack elements that are not located in the stack
         * offset coinciding with its stack index.
         */
        size_t missing_spill_count();

        /**
         * Find a general register for the given stack element.
         * If the optional StackOffset has a value, then make sure
         * to emit mov instruction from the general register to stack offset.
         */
        [[nodiscard]]
        std::pair<GeneralRegReserv, std::optional<StackOffset>>
            insert_general_reg(StackElemRef);

        /**
         * Remove AVX register from `elem` and return a new stack element
         * containing the AVX register.
         */
        StackElemRef release_avx_reg(StackElemRef elem);

        /**
         * Move the avx register in `src` to `dst`. It is required that
         * `src` does not need to spill its value to another location, even
         * if general register is the only location.
         */
        void move_avx_reg(StackElem &src, StackElem &dst);

        /**
         * Spill all caller save general registers to persistent storage.
         * Returns `(GeneralReg, StackOffset)` pairs which can be used to
         * emit the code for moving the registers to physical stack memory.
         * If spill of both caller save general registers and AVX registers
         * is needed, then call `spill_all_caller_save_general_regs` first.
         * This is an optimization in the case where a stack value is both
         * in caller save general register and AVX register, because
         * calling `spill_all_avx_regs` afterwards will use faster AVX
         * instructions for moving to physical stack memory.
         */
        [[nodiscard]]
        std::vector<std::pair<GeneralReg, StackOffset>>
        spill_all_caller_save_general_regs();

        /**
         * Spill all AVX registers to persistent storage.
         * Returns `(AvxReg, StackOffset)` pairs which can be used to emit
         * the code for moving the registers to physical stack memory.
         * See the `spill_all_caller_save_general_regs` documentation for
         * an optimization trick when both caller save general registers
         * and AVX registers need to be spilled.
         */
        [[nodiscard]]
        std::vector<std::pair<AvxReg, StackOffset>> spill_all_avx_regs();

        /**
         * Spill the AVX registers with reg ID in the inclusive range
         * [`first`, `15`] to persistent storage.
         * Returns `(AvxReg, StackOffset)` pairs which can be used to emit
         * the code for moving the registers to physical stack memory.
         * See the `spill_all_caller_save_general_regs` documentation for
         * an optimization trick when both caller save general registers
         * and AVX registers need to be spilled.
         */
        [[nodiscard]]
        std::vector<std::pair<AvxReg, StackOffset>>
        spill_avx_reg_range(uint8_t first);

        /** Set of available stack offsets. */
        std::set<std::int32_t> const &available_stack_offsets();

        /** Whether there is a free avx register. */
        bool has_free_avx_reg()
        {
            return !free_avx_regs_.empty();
        }

        /** Whether there is a free general register. */
        bool has_free_general_reg()
        {
            return !free_general_regs_.empty();
        }

        /** Null or the stack element holding the general reg. */
        StackElem *general_reg_stack_elem(GeneralReg r)
        {
            return general_reg_stack_elems_[r.reg];
        }

        /** Whether the given general register is currently on the stack. */
        bool is_general_reg_on_stack(GeneralReg);

        /**
         * The relative size of the stack at the *lowest* point during execution
         * of a block.
         */
        std::int32_t min_delta() const
        {
            return min_delta_;
        }

        /**
         * The relative size of the stack at the *highest* point during
         * execution of a block.
         */
        std::int32_t max_delta() const
        {
            return max_delta_;
        }

        /**
         * The difference between the final and initial stack sizes during
         * execution of a block.
         */
        std::int32_t delta() const
        {
            return delta_;
        }

        /**
         * Whether `min_delta` decreased after last call to one of
         * `begin_new_block` or `continue_block`.
         */
        bool did_min_delta_decrease() const
        {
            return did_min_delta_decrease_;
        }

        /**
         * Whether `max_delta` increased after last call to one of
         * `begin_new_block` or `continue_block`.
         */
        bool did_max_delta_increase() const
        {
            return did_max_delta_increase_;
        }

        /**
         * Index of the top element on the stack. The returned value is only
         * a valid index if the stack is not empty.
         */
        std::int32_t top_index() const
        {
            return top_index_;
        }

        std::int32_t bottom_index() const
        {
            return -static_cast<std::int32_t>(negative_elems_.size()) -
                   1; // minus 1 because 1-indexed
        }

        OperandLocations get_stack_elem_locations(std::int32_t index)
        {
            StackElemRef const elem = at(index);
            return {
                elem->literal(),
                elem->stack_offset(),
                elem->avx_reg(),
                elem->general_reg(),
                elem->is_deferred_comparison()};
        }

    private:
        /** Allocate a new stack element. */
        StackElemRef new_stack_elem();

        /**
         * Obtain a mutable reference to an item on the stack, correctly
         * handling negative values to reference input stack elements.
         */
        StackElemRef &at(std::int32_t index);

        /**
         * Identify a stack offset that can be used to spill the specified stack
         * item.
         *
         * If there's nothing currently in the physical stack slot corresponding
         * to that item, it can be spilled to its "proper" location. Otherwise,
         * if there's a collision, we need to use another available slot to
         * relocate this item to.
         */
        StackOffset
        find_available_stack_offset(std::int32_t preferred_offset) const;

        // Linked list of stack element RC objects, using `ref_count`
        // for "next" pointer:
        utils::RcObject<StackElem> *free_rc_objects_;
        std::int32_t top_index_;
        std::int32_t min_delta_;
        std::int32_t max_delta_;
        std::int32_t delta_;
        bool did_min_delta_decrease_;
        bool did_max_delta_increase_;
        std::set<std::int32_t> available_stack_offsets_;
        AvxRegQueue free_avx_regs_;
        GeneralRegQueue free_general_regs_;
        // The `avx_reg_stack_elems_` contains all the stack elements with AVX
        // registers. The array is maintained by `StackElem`. Entries are
        // `nullptr` when there is no stack element holding the corresponding
        // register.
        std::array<StackElem *, AVX_REG_COUNT> avx_reg_stack_elems_;
        // The `general_reg_stack_elems_` is analogous to
        // `avx_reg_stack_elems_`.
        std::array<StackElem *, GENERAL_REG_COUNT> general_reg_stack_elems_;
        DeferredComparison deferred_comparison_;
        // Make sure stack element vectors are last, so that the stack
        // destructor will destroy them last.
        std::vector<StackElemRef> negative_elems_;
        std::vector<StackElemRef> positive_elems_;
    };

    struct StackElemDeleter
    {
        static void destroy(utils::RcObject<StackElem> *x)
        {
            static_assert(sizeof(std::size_t) == sizeof(void *));
            x->ref_count = reinterpret_cast<std::size_t>(
                x->object.stack_.free_rc_objects_);
            x->object.stack_.free_rc_objects_ = x;
        }

        static void deallocate(utils::RcObject<StackElem> *)
        {
            // nop
        }
    };
}
