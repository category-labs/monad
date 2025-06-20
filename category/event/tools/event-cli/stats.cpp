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

#include "stats.hpp"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <limits>
#include <print>
#include <span>
#include <vector>

// TDigest implementation notes
//
// Resources for understanding TDigests:
//
//   - The original paper by Dunning and Ertl, cited as [DE] in the comments:
//
//         Computing Extremely Accurate Quantiles Using t-Digests
//         (arXiv:1902.04023 [stat.CO])
//
//     The algorithms in this paper (algorithm 1 and algorithm 2) are referred
//     to in comments using the notation [DEA2:L2], meaning [DE] Algorithm 2,
//     line 2
//
//   - Reference Java implementation by Ted Dunning
//
//         https://github.com/tdunning/t-digest
//
//     The merging digest implementation (in the file "MergingDigest.java") is
//     particularly relevant, and is called "JMD" (Java Merging Digest) in the
//     comments. The README.md has links to other resources too
//
//   - Redis implementation (as a plugin)
//
//        https://github.com/usmanm/redis-tdigest
//
//     and its documentation:
//
//        https://redis.io/docs/latest/develop/data-types/probabilistic/t-digest/
//
//     This is interesting to look at because it is also in C, and is referred
//     to in the comments as the "RP" (Redis Plugin) implementation

constexpr double DefaultCompression = 50.0;

inline bool float_equal(double x, double y)
{
    return std::fabs(x - y) < std::numeric_limits<double>::epsilon();
}

inline double k_1(double q, double compression)
{
    return compression * std::asin(2 * q - 1.0) / (2 * M_PI);
}

// The inverse function of k_1, which yields q; in the Java reference
// implementation this is called `K_1.q`, in the paper it is `k^{-1}`
inline double k_1_inv(double k, double compression)
{
    return (std::sin(k * (2 * M_PI / compression)) + 1.0) / 2.0;
}

inline double compute_max_q_right(double q_left, double compression)
{
    return k_1_inv(k_1(q_left, compression) + 1.0, compression);
}

TDigest::TDigest()
    : compression_{DefaultCompression}
    , min_{std::numeric_limits<double>::max()}
    , max_{std::numeric_limits<double>::min()}
    , total_weight_{0}
{
}

void TDigest::add(double value)
{
    struct CentroidCandidate
    {
        std::vector<Centroid>::iterator i_centroid;
        double q_left;
        double q_right;
    };

    if (!std::isfinite(value)) {
        return;
    }

    // [DEA2] 2.7 The clustering variant
    auto const centroid_end = cend(centroids_);
    std::vector<CentroidCandidate> candidates;
    double min_distance = std::numeric_limits<double>::max();
    double q_left = 0;

    total_weight_ += 1;
    min_ = std::min(min_, value);
    max_ = std::max(max_, value);

    // [DEA2:L2-3] compute z and part of `S` from the next line (but don't
    // compute the k-size, since it's less efficient to compute
    // `|c_i.mean - x| == z` first
    double const tw = static_cast<double>(total_weight_);
    for (auto i_c = begin(centroids_); i_c != centroid_end; ++i_c) {
        Centroid const &c = *i_c;
        double const distance = std::fabs(c.mean() - value);
        double const relative_weight = static_cast<double>(c.weight) / tw;
        double const q_right = q_left + relative_weight;
        if (float_equal(min_distance, distance)) {
            candidates.emplace_back(i_c, q_left, q_right);
        }
        else if (distance < min_distance) {
            candidates.clear();
            candidates.emplace_back(i_c, q_left, q_right);
            min_distance = distance;
        }
        else {
            // Once the distance series begins increasing, it will increase
            // forever
            break;
        }
        q_left += relative_weight;
    }

    // [DEA2:L3] partition the set into those candidates with valid k weight
    // and those without
    auto invalid_candidates =
        std::ranges::partition(candidates, [this](CentroidCandidate const &cc) {
            return k_1(cc.q_right, compression_) -
                       k_1(cc.q_left, compression_) <=
                   1;
        });

    std::ranges::subrange const valid_candidates{
        begin(candidates), begin(invalid_candidates)};
    if (empty(valid_candidates)) {
        // [DEA2:L9-10]: create a new centroid and merge it in; we do it like
        // this instead of calling merge_centroids since we already know there
        // is no centroid whose k-size will allow this point to be added, so
        // the sorted insertion is the only thing we need; we skip the
        // compression step in [DEA2:L11] since we don't appear to need it
        auto const i_insert =
            std::ranges::lower_bound(centroids_, value, {}, &Centroid::mean);
        centroids_.emplace(i_insert, value, 1);
        return;
    }

    // [DEA2:L5]
    std::ranges::sort(
        valid_candidates,
        [](CentroidCandidate const &lhs, CentroidCandidate const &rhs) {
            return rhs.i_centroid->sum < lhs.i_centroid->sum;
        });

    // [DEA2:L6-8]
    Centroid &merge = *begin(valid_candidates)->i_centroid;
    merge.sum += value;
    merge.weight += 1;

    // Once we do the step above, the strict sorted order can break; we could
    // optimize this if there was a need to
    std::ranges::sort(centroids_, {}, &Centroid::mean);
}

double TDigest::compute_quantile(double q) const
{
    if (!std::isfinite(q) || q < 0.0 || q > 1.0 || empty(centroids_)) {
        return NAN;
    }

    if (size(centroids_) == 1) {
        return centroids_[0].mean();
    }
    if (float_equal(q, 0.0)) {
        return min_;
    }
    if (float_equal(q, 1.0)) {
        return max_;
    }

    // In the JMD and RP implementations this is called `index`; we call it `h`
    // to be consistent with `compute_quantile_sorted`, where it matches the
    // common variable name used in literature describing "full sorted sample"
    // quantile calculations
    double const h = q * static_cast<double>(total_weight_);

    if (h < 1) {
        // h \in [0, 1) should correspond to C_0 iff C_0 can capture the min
        // faithfully (i.e., has unit weight such that the min doesn't get
        // accidentally merged). For some choices of the scale function this
        // can happen, so we defensively track min_ and return it manually.
        return min_;
    }

    if (Centroid const &leftmost = centroids_.front();
        leftmost.weight > 1 && h < leftmost.half_weight()) {
        // The case where we interpolate between min and the left-most
        // centroid
        double const t = (h - 1.0) / (leftmost.half_weight() - 1.0);
        return std::lerp(min_, leftmost.mean(), t);
    }

    if (h > static_cast<double>(total_weight_) - 1.0) {
        // Symmetric case as with min, at the max boundary
        return max_;
    }

    if (Centroid const &rightmost = centroids_.back();
        rightmost.weight > 1 &&
        static_cast<double>(total_weight_) <= h - rightmost.half_weight()) {
        // TODO(ken): alternate forwards and backwards, see [DE] for why
        //   we need to do this
        double const t = (static_cast<double>(total_weight_) - h - 1) /
                         (rightmost.half_weight() - 1);
        return std::lerp(rightmost.mean(), max_, t);
    }

    double weight_so_far = centroids_.front().half_weight();
    size_t const n_centroids = size(centroids_);
    for (size_t i = 0; i < n_centroids - 1; ++i) {
        Centroid const &left = centroids_[i];
        Centroid const &right = centroids_[i + 1];

        // The weight range covered by the left and right centroids is
        // [weight_so_far, weight_so_far + dw]. If `h` is greater than this,
        // then its interpolation target lies between a further out pair of
        // centroids
        double const dw = static_cast<double>(left.weight + right.weight) / 2.0;
        if (h > weight_so_far + dw) {
            weight_so_far += dw;
            continue;
        }

        // left and right are the pair of centroids between which we're
        // supposed to interpolate
        double left_unit = 0;
        if (left.is_unit_weight()) {
            if (h - weight_so_far < 0.5) {
                return left.mean();
            }
            left_unit = 0.5;
        }

        double right_unit = 0;
        if (right.is_unit_weight()) {
            if (weight_so_far + dw - h <= 0.5) {
                return right.mean();
            }
            right_unit = 0.5;
        }

        /// XXX: document and explain _unit variables and why we interpolate
        /// this way
        double const w1 = h - weight_so_far - left_unit;
        double const w2 = weight_so_far + dw - h - right_unit;
        return (w1 * left.mean() + w2 * right.mean()) / (w1 + w2);
    }

    Centroid const &rightmost = centroids_.back();
    double const w1 =
        h - static_cast<double>(total_weight_) - rightmost.half_weight();
    double const w2 = rightmost.half_weight() - w1;
    return (w1 * rightmost.mean() + w2 * max_) / (w1 + w2);
}

void TDigest::dump(std::FILE *output)
{
    std::println(output, "{} centroids", size(centroids_));
    for (size_t i = 0; Centroid const &c : centroids_) {
        std::println(
            output,
            "{:4} -> s: {:20} w: {:5}, m: {:20}",
            i++,
            c.sum,
            c.weight,
            c.mean());
    }
}

void TDigest::merge_centroids(
    std::span<Centroid const> incoming, size_t incoming_weight)
{
    // The notation `[DEA1:L#]` refers to line numbers in the pseudo-code of
    // "Algorithm 1" (A1) in 'Computing Extremely Accurate Quantiles Using
    // t-Digests' by Dunning and Ertl (DE)
    MONAD_DEBUG_ASSERT(std::ranges::is_sorted(
        incoming, [](Centroid const &lhs, Centroid const &rhs) {
            return lhs.mean() < rhs.mean();
        }));

    merge_buf_.clear(); // [DEA1:L3]: C' = []
    total_weight_ += incoming_weight; // [DEA1:L2]: S = sum(X)
    double const final_weight = static_cast<double>(total_weight_);

    if (empty(incoming)) {
        return;
    }

    // When `centroids_` is empty, this sets the initial value, then faithfully
    // updates it for any newer values
    min_ = std::min(min_, incoming.front().mean());
    max_ = std::max(max_, incoming.back().mean());

    struct IterationState
    {
        std::span<Centroid const>::iterator i_centroid;
        std::span<Centroid const>::iterator i_end;

        bool is_exhausted() const
        {
            return i_centroid == i_end;
        }
    };

    // Create a span over `centroids_` so that its iterators can be held in
    // an IterationState, as with `incoming`
    std::span<Centroid const> const current = centroids_;
    std::vector iters{IterationState{cbegin(incoming), cend(incoming)}};
    if (!empty(current)) {
        iters.emplace_back(cbegin(current), cend(current));
    }

    // [DEA1:L3] calls q_left `q_0` instead; we call it `q_left` to match
    // `W_left / N` on [DE p4], which is what it represents
    double q_left = 0;

    // The definition of q_limit is not explained clearly in [DE], the
    // rationale here is that the k-size bound [DE p6 eq. 4] for measuring
    // "fully merged" centroids is:
    //
    //     |C|_k = k(q_right) - k(q_left) <= 1
    //
    // The k-size is maximized when `k(q_right) - k(q_left) == 1`, so the
    // implied maximum value of q_right that causes this to happen is
    //
    //     q_right_max = k_inverse(k(q_left) + 1)
    //
    // In this loop we decide to merge (or not) the next centroid, which
    // would extend the q_right. This is allowed up to Q_limit
    double q_limit = compute_max_q_right(q_left, compression_);

    // This loop is a merge join; in [DEA1:L1], the pseudocode materializes
    // the merge into a new version of `X`, written as `X <- sort(C Union X)`.
    // In our case, both C (centroids_) and the original X (incoming) are known
    // to be sorted, so are not formally merged but visited in merge join order.
    while (!empty(iters)) {
        IterationState *is = std::addressof(iters[0]);
        if (size(iters) == 2 &&
            iters[1].i_centroid->mean() < iters[0].i_centroid->mean()) {
            is = std::addressof(iters[1]);
        }

        Centroid const &c_merge = *is->i_centroid++;
        if (is->is_exhausted()) {
            if (size(iters) == 2 && is == std::addressof(iters[0])) {
                std::swap(iters[0], iters[1]);
            }
            iters.pop_back();
        }

        if (empty(merge_buf_)) {
            // [DEA1:L5]: this is shown as occurring before the loop
            // construct starts, but because our loop is structured
            // differently we do it here
            merge_buf_.push_back(c_merge);
            continue;
        }

        // [DEA1:L6-L15]: we rename the variable `q` to `q_right`, matching
        // the description of the k-size bound: it is the candidate q_right for
        // the current cluster if we are allowed to add `to_merge` into the
        // active cluster, sigma
        Centroid &sigma = merge_buf_.back();
        double const q_right =
            q_left +
            static_cast<double>(sigma.weight + c_merge.weight) / final_weight;
        if (q_right <= q_limit) {
            sigma.sum += c_merge.sum;
            sigma.weight += c_merge.weight;
        }
        else {
            q_left += static_cast<double>(sigma.weight) / final_weight;
            q_limit = compute_max_q_right(q_left, compression_);
            merge_buf_.push_back(c_merge);
        }
    }

    std::swap(centroids_, merge_buf_);
}

double compute_quantile_sorted(std::span<double const> data, double q)
{
    if (!std::isfinite(q) || q < 0.0 || q > 1.0 || empty(data)) {
        return NAN;
    }
    if (float_equal(q, 1.0)) {
        return data.back(); // Otherwise data[index+1] is undefined
    }
    // Hyndman and Fan Type 7 quantile computation, see
    //   https://blogs.sas.com/content/iml/2017/05/24/definitions-sample-quantiles.html
    double const h = static_cast<double>(size(data) - 1) * q;
    double const h_floor = std::floor(h);
    auto const index = static_cast<size_t>(h_floor);
    double const x0 = data[index];
    double const x1 = data[index + 1];
    return std::lerp(x0, x1, h - h_floor);
}

void print_quantile_header(
    std::span<double const> quantiles, unsigned width, std::FILE *output)
{
    for (double const q : quantiles) {
        // TODO(ken): see std::runtime_format comments in execstat.cpp,
        //  should be removed later
        if (q == 0.0) {
            std::print(output, " {:>{}}", "MIN", width);
        }
        else if (q == 1.0) {
            std::print(output, " {:>{}}", "MAX", width);
        }
        else {
            double const scaled_percentage = q * 100;
            double ignored;
            unsigned frac_digits = 0;
            for (double p = scaled_percentage;
                 std::modf(p, &ignored) >
                 std::numeric_limits<double>::epsilon();
                 p *= 10) {
                ++frac_digits;
            }
            std::print(
                output,
                " {:>{}.{}f}%",
                scaled_percentage,
                width - 1,
                frac_digits);
        }
    }
}
