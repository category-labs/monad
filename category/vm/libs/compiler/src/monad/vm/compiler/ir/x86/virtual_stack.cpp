#include <monad/vm/compiler/ir/basic_blocks.hpp>
#include <monad/vm/compiler/ir/x86/virtual_stack.hpp>
#include <monad/vm/compiler/types.hpp>
#include <monad/vm/core/assert.h>
#include <monad/vm/utils/rc_ptr.hpp>

#include <algorithm>
#include <array>
#include <compare>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using namespace monad::vm::compiler;

namespace monad::vm::compiler::native
{
    bool operator==(Literal const &a, Literal const &b)
    {
        return a.value == b.value;
    }

    bool operator==(StackOffset const &a, StackOffset const &b)
    {
        return a.offset == b.offset;
    }

    std::strong_ordering operator<=>(AvxReg const &a, AvxReg const &b)
    {
        return a.reg <=> b.reg;
    }

    bool operator==(AvxReg const &a, AvxReg const &b)
    {
        return a.reg == b.reg;
    }

    std::strong_ordering operator<=>(GeneralReg const &a, GeneralReg const &b)
    {
        return a.reg <=> b.reg;
    }

    bool operator==(GeneralReg const &a, GeneralReg const &b)
    {
        return a.reg == b.reg;
    }

    static_assert(AVX_REG_COUNT == 16);
    std::array<AvxReg, AVX_REG_COUNT> ALL_AVX_REGS = {
        AvxReg(0),
        AvxReg(1),
        AvxReg(2),
        AvxReg(3),
        AvxReg(4),
        AvxReg(5),
        AvxReg(6),
        AvxReg(7),
        AvxReg(8),
        AvxReg(9),
        AvxReg(10),
        AvxReg(11),
        AvxReg(12),
        AvxReg(13),
        AvxReg(14),
        AvxReg(15)};

    static_assert(GENERAL_REG_COUNT == 3);
    std::array<GeneralReg, GENERAL_REG_COUNT> ALL_GENERAL_REGS = {
        GeneralReg(0), GeneralReg(1), GeneralReg(2)};

    StackElem::StackElem(Stack *s)
        : stack_{*s}
        , reserve_avx_reg_count_{}
        , reserve_general_reg_count_{}
    {
    }

    std::int32_t StackElem::preferred_stack_offset() const
    {
        return stack_indices_.begin() == stack_indices_.end()
                   ? stack_.min_delta_
                   : *stack_indices_.begin();
    }

    void StackElem::deferred_comparison(Comparison c)
    {
        MONAD_VM_ASSERT(stack_.deferred_comparison_.stack_elem == nullptr);
        MONAD_VM_DEBUG_ASSERT(
            !stack_offset_ && !avx_reg_ && !general_reg_ && !literal_);
        stack_.deferred_comparison_.set(this, c);
    }

    void StackElem::deferred_comparison()
    {
        MONAD_VM_ASSERT(!stack_.deferred_comparison_.stack_elem);
        MONAD_VM_ASSERT(stack_.deferred_comparison_.negated_stack_elem);
        MONAD_VM_DEBUG_ASSERT(
            stack_.deferred_comparison_.negated_stack_elem != this);
        MONAD_VM_DEBUG_ASSERT(
            !stack_offset_ && !avx_reg_ && !general_reg_ && !literal_);
        stack_.deferred_comparison_.stack_elem = this;
    }

    void StackElem::negated_deferred_comparison()
    {
        MONAD_VM_ASSERT(!stack_.deferred_comparison_.negated_stack_elem);
        MONAD_VM_ASSERT(stack_.deferred_comparison_.stack_elem);
        MONAD_VM_DEBUG_ASSERT(stack_.deferred_comparison_.stack_elem != this);
        MONAD_VM_DEBUG_ASSERT(
            !stack_offset_ && !avx_reg_ && !general_reg_ && !literal_);
        stack_.deferred_comparison_.negated_stack_elem = this;
    }

    void StackElem::discharge_deferred_comparison()
    {
        MONAD_VM_DEBUG_ASSERT(
            !stack_offset_ && !avx_reg_ && !general_reg_ && !literal_);
        MONAD_VM_DEBUG_ASSERT(stack_.deferred_comparison_.stack_elem == this);
        stack_.deferred_comparison_.stack_elem = nullptr;
    }

    void StackElem::discharge_negated_deferred_comparison()
    {
        MONAD_VM_DEBUG_ASSERT(
            !stack_offset_ && !avx_reg_ && !general_reg_ && !literal_);
        MONAD_VM_DEBUG_ASSERT(
            stack_.deferred_comparison_.negated_stack_elem == this);
        stack_.deferred_comparison_.negated_stack_elem = nullptr;
    }

    void StackElem::insert_literal(Literal x)
    {
        MONAD_VM_ASSERT(!literal_.has_value());
        literal_ = x;
    }

    void StackElem::insert_stack_offset(StackOffset x)
    {
        MONAD_VM_ASSERT(!stack_offset_.has_value());
        stack_offset_ = x;
        auto removed = stack_.available_stack_offsets_.erase(x.offset);
        MONAD_VM_ASSERT(removed == 1);
    }

    void StackElem::insert_avx_reg()
    {
        MONAD_VM_ASSERT(!avx_reg_.has_value());
        auto x = stack_.free_avx_regs_.top();
        avx_reg_ = x;
        stack_.free_avx_regs_.pop();
        MONAD_VM_ASSERT(stack_.avx_reg_stack_elems_[x.reg] == nullptr);
        stack_.avx_reg_stack_elems_[x.reg] = this;
    }

    void StackElem::insert_general_reg()
    {
        auto reg = stack_.free_general_regs_.top();
        stack_.free_general_regs_.pop();
        MONAD_VM_ASSERT(!general_reg_.has_value());
        MONAD_VM_ASSERT(stack_.general_reg_stack_elems_[reg.reg] == nullptr);
        general_reg_ = reg;
        stack_.general_reg_stack_elems_[reg.reg] = this;
    }

    void StackElem::free_avx_reg()
    {
        MONAD_VM_ASSERT(avx_reg_.has_value());
        stack_.free_avx_regs_.push(*avx_reg_);
        auto reg = avx_reg_->reg;
        MONAD_VM_ASSERT(stack_.avx_reg_stack_elems_[reg] == this);
        stack_.avx_reg_stack_elems_[reg] = nullptr;
    }

    void StackElem::free_general_reg()
    {
        MONAD_VM_ASSERT(general_reg_.has_value());
        stack_.free_general_regs_.push(*general_reg_);
        auto reg = general_reg_->reg;
        MONAD_VM_ASSERT(stack_.general_reg_stack_elems_[reg] == this);
        stack_.general_reg_stack_elems_[reg] = nullptr;
    }

    void StackElem::free_stack_offset()
    {
        MONAD_VM_ASSERT(stack_offset_.has_value());
        auto [_, inserted] =
            stack_.available_stack_offsets_.insert(stack_offset_->offset);
        MONAD_VM_ASSERT(inserted);
    }

    void StackElem::remove_avx_reg()
    {
        free_avx_reg();
        avx_reg_ = std::nullopt;
    }

    void StackElem::remove_general_reg()
    {
        free_general_reg();
        general_reg_ = std::nullopt;
    }

    void StackElem::remove_stack_offset()
    {
        free_stack_offset();
        stack_offset_ = std::nullopt;
    }

    void StackElem::remove_literal()
    {
        literal_ = std::nullopt;
    }

    StackElem::~StackElem()
    {
        if (stack_offset_.has_value()) {
            free_stack_offset();
        }
        if (avx_reg_.has_value()) {
            free_avx_reg();
        }
        if (general_reg_.has_value()) {
            free_general_reg();
        }
        if (stack_.deferred_comparison_.stack_elem == this) {
            discharge_deferred_comparison();
        }
        if (stack_.deferred_comparison_.negated_stack_elem == this) {
            discharge_negated_deferred_comparison();
        }
    }

    Stack::Stack()
        : free_rc_objects_{}
    {
    }

    Stack::Stack(basic_blocks::Block const &block)
        : Stack()
    {
        begin_new_block(block);
    }

    Stack::~Stack()
    {
        // Clear to free stack elements on the stack before
        // loading `free_rc_objects_`:
        negative_elems_.clear();
        positive_elems_.clear();
        auto *rco = free_rc_objects_;
        if (rco) {
            do {
                utils::RcObject<StackElem> *x = rco;
                static_assert(sizeof(std::size_t) == sizeof(void *));
                rco = reinterpret_cast<decltype(x)>(x->ref_count);
                utils::RcObject<StackElem>::default_deallocate(x);
            }
            while (rco);
        }
    }

    void Stack::begin_new_block(basic_blocks::Block const &block)
    {
        positive_elems_.clear();
        negative_elems_.clear();
        deferred_comparison_ = DeferredComparison{};
        general_reg_stack_elems_.fill(nullptr);
        avx_reg_stack_elems_.fill(nullptr);
        free_general_regs_ =
            GeneralRegQueue{ALL_GENERAL_REGS.begin(), ALL_GENERAL_REGS.end()};
        free_avx_regs_ = AvxRegQueue{ALL_AVX_REGS.begin(), ALL_AVX_REGS.end()};
        available_stack_offsets_.clear();
        top_index_ = -1;

        auto const [new_min_delta, new_delta, new_max_delta] =
            block.stack_deltas();

        negative_elems_.reserve(static_cast<std::size_t>(-new_min_delta));
        for (auto i = -1; i >= new_min_delta; --i) {
            StackElemRef e = new_stack_elem();
            e->stack_offset_ = StackOffset{i};
            e->stack_indices_.insert(i);
            negative_elems_.push_back(std::move(e));
        }
        positive_elems_.resize(static_cast<std::size_t>(new_max_delta));
        auto it = available_stack_offsets_.end();
        for (auto i = 0; i < new_max_delta; ++i) {
            it = available_stack_offsets_.insert(it, i);
        }

        did_min_delta_decrease_ = new_min_delta < 0;
        did_max_delta_increase_ = new_max_delta > 0;
        min_delta_ = new_min_delta;
        delta_ = new_delta;
        max_delta_ = new_max_delta;
    }

    void Stack::continue_block(basic_blocks::Block const &block)
    {
        auto const [pre_min_delta, pre_delta, pre_max_delta] =
            block.stack_deltas();
        auto new_min_delta = std::min(delta_ + pre_min_delta, min_delta_);
        auto new_delta = delta_ + pre_delta;
        auto new_max_delta = std::max(delta_ + pre_max_delta, max_delta_);

        negative_elems_.reserve(static_cast<std::size_t>(-new_min_delta));
        for (auto i = min_delta_ - 1; i >= new_min_delta; --i) {
            StackElemRef e = new_stack_elem();
            e->stack_offset_ = StackOffset{i};
            e->stack_indices_.insert(i);
            negative_elems_.push_back(std::move(e));
        }

        positive_elems_.resize(static_cast<std::size_t>(new_max_delta));
        auto it = available_stack_offsets_.end();
        for (auto i = max_delta_; i < new_max_delta; ++i) {
            it = available_stack_offsets_.insert(it, i);
        }

        did_min_delta_decrease_ = new_min_delta < min_delta_;
        did_max_delta_increase_ = new_max_delta > max_delta_;
        min_delta_ = new_min_delta;
        delta_ = new_delta;
        max_delta_ = new_max_delta;
    }

    StackElemRef Stack::new_stack_elem()
    {
        return StackElemRef::make(
            [this]() {
                if (free_rc_objects_) {
                    utils::RcObject<StackElem> *x = free_rc_objects_;
                    static_assert(sizeof(std::size_t) == sizeof(void *));
                    free_rc_objects_ =
                        reinterpret_cast<decltype(x)>(x->ref_count);
                    return x;
                }
                else {
                    auto *x = utils::RcObject<StackElem>::default_allocate();
                    return x;
                }
            },
            this);
    }

    StackElemRef Stack::get(std::int32_t index)
    {
        MONAD_VM_ASSERT(index <= top_index_);
        return at(index);
    }

    StackElemRef &Stack::at(std::int32_t index)
    {
        if (index < 0) {
            auto i = static_cast<std::size_t>(-index - 1);
            MONAD_VM_ASSERT(i < negative_elems_.size());
            return negative_elems_[i];
        }
        else {
            auto i = static_cast<std::size_t>(index);
            MONAD_VM_ASSERT(i < positive_elems_.size());
            return positive_elems_[i];
        }
    }

    StackElemRef Stack::top()
    {
        return at(top_index_);
    }

    StackElemRef Stack::pop()
    {
        auto &e = at(top_index_);

        auto rem = e->stack_indices_.erase(top_index_);
        MONAD_VM_DEBUG_ASSERT(rem == 1);

        // Note that it's valid for stack indices to become negative here.
        top_index_ -= 1;

        return std::move(e); // Move to prevent increment reference count
    }

    void Stack::push(StackElemRef e)
    {
        top_index_ += 1;
        auto [_, ins] = e->stack_indices_.insert(top_index_);
        MONAD_VM_DEBUG_ASSERT(ins);
        at(top_index_) = std::move(e);
    }

    void Stack::push_deferred_comparison(Comparison c)
    {
        top_index_ += 1;
        auto e = new_stack_elem();
        e->stack_indices_.insert(top_index_);
        e->deferred_comparison(c);
        at(top_index_) = std::move(e);
    }

    bool Stack::negate_top_deferred_comparison()
    {
        auto e = get(top_index_);
        auto &dc = deferred_comparison_;
        if (dc.stack_elem == e.get()) {
            pop();
            if (dc.negated_stack_elem) {
                auto i = dc.negated_stack_elem->stack_indices_.begin();
                MONAD_VM_DEBUG_ASSERT(
                    i != dc.negated_stack_elem->stack_indices_.end());
                push(at(*i));
            }
            else {
                auto d = new_stack_elem();
                d->negated_deferred_comparison();
                push(std::move(d));
            }
            return true;
        }
        else if (dc.negated_stack_elem == e.get()) {
            pop();
            if (dc.stack_elem) {
                auto i = dc.stack_elem->stack_indices_.begin();
                MONAD_VM_DEBUG_ASSERT(i != dc.stack_elem->stack_indices_.end());
                push(at(*i));
            }
            else {
                auto d = new_stack_elem();
                d->deferred_comparison();
                push(std::move(d));
            }
            return true;
        }
        return false;
    }

    void Stack::push_literal(uint256_t const &x)
    {
        top_index_ += 1;
        auto e = alloc_literal(Literal{x});
        e->stack_indices_.insert(top_index_);
        at(top_index_) = std::move(e);
    }

    void Stack::dup(std::int32_t stack_index)
    {
        MONAD_VM_ASSERT(stack_index <= top_index_);
        push(at(stack_index));
    }

    void Stack::swap(std::int32_t swap_index)
    {
        MONAD_VM_ASSERT(swap_index < top_index_);

        auto t = top();
        auto &e = at(swap_index);

        auto rem_t = t->stack_indices_.erase(top_index_);
        MONAD_VM_DEBUG_ASSERT(rem_t == 1);

        auto rem_e = e->stack_indices_.erase(swap_index);
        MONAD_VM_DEBUG_ASSERT(rem_e == 1);

        auto ins_t = t->stack_indices_.insert(swap_index);
        MONAD_VM_DEBUG_ASSERT(ins_t.second);

        auto ins_e = e->stack_indices_.insert(top_index_);
        MONAD_VM_DEBUG_ASSERT(ins_e.second);

        at(top_index_) = std::move(e);
        e = std::move(t);
    }

    DeferredComparison Stack::discharge_deferred_comparison()
    {
        DeferredComparison dc{deferred_comparison_};
        if (dc.stack_elem) {
            dc.stack_elem->discharge_deferred_comparison();
        }
        if (dc.negated_stack_elem) {
            dc.negated_stack_elem->discharge_negated_deferred_comparison();
        }
        return dc;
    }

    bool Stack::has_deferred_comparison() const
    {
        return deferred_comparison_.stack_elem != nullptr ||
               deferred_comparison_.negated_stack_elem != nullptr;
    }

    bool Stack::has_deferred_comparison_at(std::int32_t stack_index) const
    {
        auto const &dc = deferred_comparison_;
        if (dc.stack_elem &&
            dc.stack_elem->stack_indices_.contains(stack_index)) {
            return true;
        }
        if (dc.negated_stack_elem &&
            dc.negated_stack_elem->stack_indices_.contains(stack_index)) {
            return true;
        }
        return false;
    }

    StackOffset Stack::find_available_stack_offset(std::int32_t preferred) const
    {
        if (available_stack_offsets_.contains(preferred)) {
            return {preferred};
        }
        MONAD_VM_ASSERT(!available_stack_offsets_.empty());
        return {*available_stack_offsets_.begin()};
    }

    StackElem *Stack::find_stack_elem_for_avx_reg_spill()
    {
        MONAD_VM_ASSERT(free_avx_regs_.empty());
        for (std::uint8_t i = 0; i < AVX_REG_COUNT; ++i) {
            auto *e = avx_reg_stack_elems_[i];
            if (e == nullptr || e->reserve_avx_reg_count_ != 0) {
                continue;
            }
            return e;
        }
        MONAD_VM_ASSERT(false);
    }

    StackElem *Stack::spill_avx_reg()
    {
        return spill_avx_reg(find_stack_elem_for_avx_reg_spill());
    }

    StackElem *Stack::spill_avx_reg(StackElemRef e)
    {
        return spill_avx_reg(e.get());
    }

    StackElem *Stack::spill_avx_reg(StackElem *e)
    {
        e->remove_avx_reg();
        if (e->stack_offset_.has_value() || e->general_reg_.has_value() ||
            e->literal_.has_value()) {
            return nullptr;
        }
        std::int32_t const preferred = e->preferred_stack_offset();
        StackOffset const offset = find_available_stack_offset(preferred);
        e->insert_stack_offset(offset);
        return e;
    }

    void Stack::spill_stack_offset(StackElemRef e)
    {
        MONAD_VM_ASSERT(
            e->avx_reg_.has_value() || e->general_reg_.has_value() ||
            e->literal_.has_value());
        e->remove_stack_offset();
    }

    void Stack::spill_literal(StackElemRef e)
    {
        MONAD_VM_ASSERT(
            e->avx_reg_.has_value() || e->general_reg_.has_value() ||
            e->stack_offset_.has_value());
        e->remove_literal();
    }

    StackElem *Stack::spill_general_reg()
    {
        MONAD_VM_ASSERT(free_general_regs_.empty());
        std::uint8_t best_index = 0;
        std::int8_t best_score = -1;
        for (std::uint8_t i = 0; i < GENERAL_REG_COUNT; ++i) {
            auto *e = general_reg_stack_elems_[i];
            if (e == nullptr || e->reserve_general_reg_count_ != 0) {
                continue;
            }
            std::int8_t score = 0;
            if (e->stack_offset_.has_value()) {
                score |= 0b100;
            }
            if (e->literal_.has_value()) {
                score |= 0b10;
            }
            if (e->avx_reg_.has_value()) {
                score |= 0b1;
            }
            if (score > best_score) {
                best_score = score;
                best_index = i;
            }
        }

        MONAD_VM_ASSERT(best_score >= 0);

        return spill_general_reg(general_reg_stack_elems_[best_index]);
    }

    StackElem *Stack::spill_general_reg(StackElemRef e)
    {
        return spill_general_reg(e.get());
    }

    StackElem *Stack::spill_general_reg(StackElem *e)
    {
        e->remove_general_reg();
        if (e->stack_offset_.has_value() || e->avx_reg_.has_value() ||
            e->literal_.has_value()) {
            return nullptr;
        }
        std::int32_t const preferred = e->preferred_stack_offset();
        StackOffset const offset = find_available_stack_offset(preferred);
        e->insert_stack_offset(offset);
        return e;
    }

    size_t Stack::missing_spill_count()
    {
        size_t count = 0;
        for (int32_t stack_ix = 0; stack_ix <= top_index_; ++stack_ix) {
            size_t const i = static_cast<size_t>(stack_ix);
            count += !positive_elems_[i]->stack_offset() ||
                     positive_elems_[i]->stack_offset()->offset != stack_ix;
        }
        uint32_t i = static_cast<uint32_t>(negative_elems_.size());
        while (i-- > 0) {
            int32_t const stack_ix = -static_cast<int32_t>(i) - 1;
            if (stack_ix > top_index_) {
                break;
            }
            count += !negative_elems_[i]->stack_offset() ||
                     negative_elems_[i]->stack_offset()->offset != stack_ix;
        }
        return count;
    }

    std::vector<std::pair<GeneralReg, StackOffset>>
    Stack::spill_all_caller_save_general_regs()
    {
        static_assert(CALLEE_SAVE_GENERAL_REG_ID == 0);
        std::vector<std::pair<GeneralReg, StackOffset>> ret;
        for (std::uint8_t i = 1; i < GENERAL_REG_COUNT; ++i) {
            auto *e = general_reg_stack_elems_[i];
            if (e == nullptr) {
                continue;
            }
            MONAD_VM_ASSERT(e->reserve_general_reg_count_ == 0);
            GeneralReg const reg = *e->general_reg_;
            e->remove_general_reg();
            if (!e->stack_offset_.has_value() && !e->avx_reg_.has_value() &&
                !e->literal_.has_value()) {
                std::int32_t const preferred = e->preferred_stack_offset();
                StackOffset const offset =
                    find_available_stack_offset(preferred);
                e->insert_stack_offset(offset);
                ret.emplace_back(reg, offset);
            }
        }
        return ret;
    }

    std::vector<std::pair<AvxReg, StackOffset>> Stack::spill_all_avx_regs()
    {
        return spill_avx_reg_range(0);
    }

    std::vector<std::pair<AvxReg, StackOffset>>
    Stack::spill_avx_reg_range(uint8_t first)
    {
        std::vector<std::pair<AvxReg, StackOffset>> ret;
        for (std::uint8_t i = first; i < 16; ++i) {
            auto *e = avx_reg_stack_elems_[i];
            if (e == nullptr) {
                continue;
            }
            MONAD_VM_ASSERT(e->reserve_avx_reg_count_ == 0);
            AvxReg const reg = *e->avx_reg_;
            e->remove_avx_reg();
            if (!e->stack_offset_.has_value() && !e->general_reg_.has_value() &&
                !e->literal_.has_value()) {
                std::int32_t const preferred = e->preferred_stack_offset();
                StackOffset const offset =
                    find_available_stack_offset(preferred);
                e->insert_stack_offset(offset);
                ret.emplace_back(reg, offset);
            }
        }
        return ret;
    }

    std::set<std::int32_t> const &Stack::available_stack_offsets()
    {
        return available_stack_offsets_;
    }

    void Stack::insert_stack_offset(StackElemRef e, std::int32_t preferred)
    {
        insert_stack_offset(*e, preferred);
    }

    void Stack::insert_stack_offset(StackElemRef e)
    {
        insert_stack_offset(*e);
    }

    void Stack::insert_stack_offset(StackElem &e, std::int32_t preferred)
    {
        if (e.stack_offset_.has_value()) {
            return;
        }
        auto offset = find_available_stack_offset(preferred);
        e.insert_stack_offset(offset);
    }

    void Stack::insert_stack_offset(StackElem &e)
    {
        std::int32_t const preferred = e.preferred_stack_offset();
        insert_stack_offset(e, preferred);
    }

    std::pair<AvxRegReserv, std::optional<StackOffset>>
    Stack::insert_avx_reg(StackElemRef e)
    {
        if (e->avx_reg_.has_value()) {
            return {AvxRegReserv{e}, std::nullopt};
        }
        StackElem *spill_elem =
            free_avx_regs_.empty() ? spill_avx_reg() : nullptr;
        std::optional<StackOffset> const spill_offset =
            spill_elem ? spill_elem->stack_offset_ : std::nullopt;
        e->insert_avx_reg();
        return {AvxRegReserv{e}, spill_offset};
    }

    std::optional<StackOffset>
    Stack::insert_avx_reg_without_reserv(StackElem &e)
    {
        if (e.avx_reg_.has_value()) {
            return std::nullopt;
        }
        StackElem *spill_elem =
            free_avx_regs_.empty() ? spill_avx_reg() : nullptr;
        std::optional<StackOffset> const spill_offset =
            spill_elem ? spill_elem->stack_offset_ : std::nullopt;
        e.insert_avx_reg();
        return spill_offset;
    }

    std::pair<GeneralRegReserv, std::optional<StackOffset>>
    Stack::insert_general_reg(StackElemRef e)
    {
        if (e->general_reg_.has_value()) {
            return {GeneralRegReserv{e}, std::nullopt};
        }
        StackElem *spill_elem =
            free_general_regs_.empty() ? spill_general_reg() : nullptr;
        std::optional<StackOffset> const spill_offset =
            spill_elem ? spill_elem->stack_offset_ : std::nullopt;
        e->insert_general_reg();
        return {GeneralRegReserv{e}, spill_offset};
    }

    StackElemRef Stack::alloc_literal(Literal lit)
    {
        auto e = new_stack_elem();
        e->insert_literal(lit);
        return e;
    }

    StackElemRef Stack::alloc_stack_offset(std::int32_t preferred)
    {
        auto e = new_stack_elem();
        insert_stack_offset(*e, preferred);
        return e;
    }

    std::tuple<StackElemRef, AvxRegReserv, std::optional<StackOffset>>
    Stack::alloc_avx_reg()
    {
        auto e = new_stack_elem();
        auto [reserv, spill] = insert_avx_reg(e);
        return {std::move(e), reserv, spill};
    }

    std::tuple<StackElemRef, GeneralRegReserv, std::optional<StackOffset>>
    Stack::alloc_general_reg()
    {
        auto e = new_stack_elem();
        auto [reserv, spill] = insert_general_reg(e);
        return {std::move(e), reserv, spill};
    }

    StackElemRef Stack::release_stack_offset(StackElemRef elem)
    {
        auto dst = new_stack_elem();
        dst->stack_offset_ = elem->stack_offset_;
        elem->stack_offset_ = std::nullopt;
        return dst;
    }

    StackElemRef Stack::release_avx_reg(StackElemRef elem)
    {
        auto dst = new_stack_elem();
        move_avx_reg(*elem, *dst);
        return dst;
    }

    void Stack::move_avx_reg(StackElem &src, StackElem &dst)
    {
        AvxReg const reg = *src.avx_reg_;
        MONAD_VM_ASSERT(avx_reg_stack_elems_[reg.reg] == &src);
        dst.avx_reg_ = reg;
        src.avx_reg_ = std::nullopt;
        avx_reg_stack_elems_[reg.reg] = &dst;
    }

    StackElemRef Stack::release_general_reg(StackElem &elem)
    {
        auto dst = new_stack_elem();
        move_general_reg(elem, *dst);
        return dst;
    }

    StackElemRef Stack::release_general_reg(StackElemRef elem)
    {
        return release_general_reg(*elem);
    }

    void Stack::move_general_reg(StackElem &src, StackElem &dst)
    {
        GeneralReg const reg = *src.general_reg_;
        MONAD_VM_ASSERT(general_reg_stack_elems_[reg.reg] == &src);
        dst.general_reg_ = reg;
        src.general_reg_ = std::nullopt;
        general_reg_stack_elems_[reg.reg] = &dst;
    }

    void Stack::swap_general_regs(StackElem &e1, StackElem &e2)
    {
        MONAD_VM_ASSERT(e1.general_reg_.has_value());
        MONAD_VM_ASSERT(e2.general_reg_.has_value());

        GeneralReg const reg1 = *e1.general_reg_;
        GeneralReg const reg2 = *e2.general_reg_;
        MONAD_VM_ASSERT(general_reg_stack_elems_[reg1.reg] == &e1);
        MONAD_VM_ASSERT(general_reg_stack_elems_[reg2.reg] == &e2);

        e1.general_reg_ = reg2;
        e2.general_reg_ = reg1;
        general_reg_stack_elems_[reg1.reg] = &e2;
        general_reg_stack_elems_[reg2.reg] = &e1;
    }

    void Stack::remove_general_reg(StackElem &e)
    {
        MONAD_VM_ASSERT(e.general_reg_.has_value());
        e.remove_general_reg();
    }

    void Stack::remove_stack_offset(StackElem &e)
    {
        MONAD_VM_ASSERT(e.stack_offset().has_value());
        e.remove_stack_offset();
    }

    bool Stack::is_general_reg_on_stack(GeneralReg reg)
    {
        auto *e = general_reg_stack_elems_[reg.reg];
        return e != nullptr && e->is_on_stack();
    }
}
