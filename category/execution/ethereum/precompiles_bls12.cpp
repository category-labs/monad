#include <category/core/config.hpp>
#include <category/core/assert.h>
#include <category/execution/ethereum/precompiles_bls12.hpp>

#include <array>
#include <memory>

MONAD_NAMESPACE_BEGIN

namespace bls12
{
    template <>
    uint16_t msm_discount<G1>(uint64_t const k)
    {
        MONAD_ASSERT(k > 0);

        static constexpr auto table = std::array<uint16_t, 128>{
            1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692,
            687,  682, 677, 673, 669, 665, 661, 658, 654, 651, 648, 645, 642,
            640,  637, 635, 632, 630, 627, 625, 623, 621, 619, 617, 615, 613,
            611,  609, 608, 606, 604, 603, 601, 599, 598, 596, 595, 593, 592,
            591,  589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576, 575,
            574,  573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561,
            560,  559, 558, 557, 556, 555, 554, 553, 552, 551, 550, 549, 548,
            547,  547, 546, 545, 544, 543, 542, 541, 540, 540, 539, 538, 537,
            536,  536, 535, 534, 533, 532, 532, 531, 530, 529, 528, 528, 527,
            526,  525, 525, 524, 523, 522, 522, 521, 520, 520, 519};

        return table[std::min(k, 128ul) - 1];
    }

    template <>
    uint16_t msm_discount<G2>(uint64_t const k)
    {
        MONAD_ASSERT(k > 0);

        static constexpr auto table = std::array<uint16_t, 128>{
            1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740,
            732,  724,  717, 711, 704, 699, 693, 688, 683, 679, 674, 670, 666,
            663,  659,  655, 652, 649, 646, 643, 640, 637, 634, 632, 629, 627,
            624,  622,  620, 618, 615, 613, 611, 609, 607, 606, 604, 602, 600,
            598,  597,  595, 593, 592, 590, 589, 587, 586, 584, 583, 582, 580,
            579,  578,  576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565,
            563,  562,  561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 552,
            551,  550,  549, 548, 547, 546, 545, 545, 544, 543, 542, 541, 541,
            540,  539,  538, 537, 537, 536, 535, 535, 534, 533, 532, 532, 531,
            530,  530,  529, 528, 528, 527, 526, 526, 525, 524, 524};

        return table[std::min(k, 128ul) - 1];
    }

    blst_scalar read_scalar(uint8_t const *const in)
    {
        blst_scalar result;
        blst_scalar_from_bendian(&result, in);
        return result;
    }

    std::optional<blst_fp> read_fp(uint8_t const *const in)
    {
        static_assert(sizeof(blst_fp) == 48);
        static constexpr std::size_t fp_encoded_offset = 16;

        auto const integer_value = intx::be::unsafe::load<intx::uint512>(in);

        if (MONAD_UNLIKELY(integer_value >= BASE_FIELD_MODULUS)) {
            return std::nullopt;
        }

        blst_fp element;
        blst_fp_from_bendian(&element, in + fp_encoded_offset);

        return element;
    }

    std::optional<blst_fp2> read_fp2(uint8_t const *const in)
    {
        auto const maybe_x = read_fp(in);
        if (MONAD_UNLIKELY(!maybe_x.has_value())) {
            return std::nullopt;
        }

        auto const maybe_y = read_fp(in + G1::element_encoded_size);
        if (MONAD_UNLIKELY(!maybe_y.has_value())) {
            return std::nullopt;
        }

        return blst_fp2{*maybe_x, *maybe_y};
    }

    std::optional<blst_p1_affine> read_g1(uint8_t const *const in)
    {
        auto const maybe_x = read_fp(in);
        if (MONAD_UNLIKELY(!maybe_x.has_value())) {
            return std::nullopt;
        }

        auto const maybe_y = read_fp(in + G1::element_encoded_size);
        if (MONAD_UNLIKELY(!maybe_y.has_value())) {
            return std::nullopt;
        }

        auto const point = blst_p1_affine{*maybe_x, *maybe_y};

        auto const on_curve = blst_p1_affine_on_curve(&point);
        auto const is_infinity = blst_p1_affine_is_inf(&point);

        auto const valid = on_curve || is_infinity;
        if (MONAD_UNLIKELY(!valid)) {
            return std::nullopt;
        }

        return point;
    }

    std::optional<blst_p2_affine> read_g2(uint8_t const *const in)
    {
        auto const maybe_x = read_fp2(in);
        if (MONAD_UNLIKELY(!maybe_x.has_value())) {
            return std::nullopt;
        }

        auto const maybe_y = read_fp2(in + G2::element_encoded_size);
        if (MONAD_UNLIKELY(!maybe_y.has_value())) {
            return std::nullopt;
        }

        auto const point = blst_p2_affine{*maybe_x, *maybe_y};

        auto const on_curve = blst_p2_affine_on_curve(&point);
        auto const is_infinity = blst_p2_affine_is_inf(&point);

        auto const valid = on_curve || is_infinity;
        if (MONAD_UNLIKELY(!valid)) {
            return std::nullopt;
        }

        return point;
    }

    void write_fp(blst_fp const &point, uint8_t *const buf)
    {
        static_assert(sizeof(blst_fp) == 48);
        static constexpr std::size_t fp_encoded_offset = 16;

        std::memset(buf, 0, fp_encoded_offset);
        blst_bendian_from_fp(buf + fp_encoded_offset, &point);
    }

    void write_fp2(blst_fp2 const &point, uint8_t *const buf)
    {
        write_fp(point.fp[0], buf);
        write_fp(point.fp[1], buf + G1::element_encoded_size);
    }

    void write_g1(blst_p1_affine const &point, uint8_t *const buf)
    {
        write_fp(point.x, buf);
        write_fp(point.y, buf + G1::element_encoded_size);
    }

    void write_g2(blst_p2_affine const &point, uint8_t *const buf)
    {
        write_fp2(point.x, buf);
        write_fp2(point.y, buf + G2::element_encoded_size);
    }

    template <typename Group>
    PrecompileResult add(byte_string_view const input)
    {
        if (MONAD_UNLIKELY(input.size() != 2 * Group::encoded_size)) {
            return PrecompileResult::failure();
        }

        auto const a = Group::read(input.data());
        if (MONAD_UNLIKELY(!a.has_value())) {
            return PrecompileResult::failure();
        }

        auto const b = Group::read(input.data() + Group::encoded_size);
        if (MONAD_UNLIKELY(!b.has_value())) {
            return PrecompileResult::failure();
        }

        typename Group::Point a_non_affine;
        Group::from_affine(&a_non_affine, &*a);

        typename Group::Point result_non_affine;
        Group::add(&result_non_affine, &a_non_affine, &*b);

        typename Group::AffinePoint result;
        Group::to_affine(&result, &result_non_affine);

        auto *const output_buf =
            static_cast<uint8_t *>(std::malloc(Group::encoded_size));
        MONAD_ASSERT(output_buf != nullptr);

        Group::write(result, output_buf);

        return {
            .status_code = EVMC_SUCCESS,
            .obuf = output_buf,
            .output_size = Group::encoded_size,
        };
    }

    template PrecompileResult add<G1>(byte_string_view);
    template PrecompileResult add<G2>(byte_string_view);

    template <typename Group>
    PrecompileResult msm(byte_string_view const input)
    {
        static constexpr auto pair_size = Group::encoded_size + 32;

        if (MONAD_UNLIKELY(input.size() % pair_size != 0)) {
            return PrecompileResult::failure();
        }

        auto const k = input.size() / pair_size;

        if (MONAD_UNLIKELY(k == 0)) {
            return PrecompileResult::failure();
        }
        else if (k == 1) {
            return mul<Group>(input);
        }
        else {
            return msm_pippenger<Group>(input, k);
        }
    }

    template PrecompileResult msm<G1>(byte_string_view);
    template PrecompileResult msm<G2>(byte_string_view);

    template <typename Group>
    PrecompileResult mul(byte_string_view const input)
    {
        auto const affine_point = Group::read(input.data());
        if (MONAD_UNLIKELY(!affine_point.has_value())) {
            return PrecompileResult::failure();
        }

        auto const scalar = read_scalar(input.data() + Group::encoded_size);

        typename Group::Point point;
        Group::from_affine(&point, &*affine_point);

        if (MONAD_UNLIKELY(!Group::point_in_group(&point))) {
            return PrecompileResult::failure();
        }

        typename Group::Point result;
        Group::mul(&result, &point, scalar.b, 256);

        typename Group::AffinePoint affine_result;
        Group::to_affine(&affine_result, &result);

        auto *const output_buf =
            static_cast<uint8_t *>(std::malloc(Group::encoded_size));
        MONAD_ASSERT(output_buf != nullptr);

        Group::write(affine_result, output_buf);

        return {
            .status_code = EVMC_SUCCESS,
            .obuf = output_buf,
            .output_size = Group::encoded_size,
        };
    }

    template PrecompileResult mul<G1>(byte_string_view);
    template PrecompileResult mul<G2>(byte_string_view);

    template <typename Group>
    PrecompileResult
    msm_pippenger(byte_string_view const input, uint64_t const k)
    {
        auto affine_points = std::vector<typename Group::AffinePoint>{};
        affine_points.reserve(k);

        auto affine_point_ptrs =
            std::vector<typename Group::AffinePoint const *>{};
        affine_point_ptrs.reserve(k);

        auto scalars = std::vector<blst_scalar>{};
        scalars.reserve(k);

        auto scalar_ptrs = std::vector<uint8_t const *>{};
        scalar_ptrs.reserve(k);

        static constexpr auto pair_size = Group::encoded_size + 32;
        auto const *const end_ptr = input.data() + (k * pair_size);

        for (auto const *ptr = input.data(); ptr != end_ptr; ptr += pair_size) {
            auto const affine_point = Group::read(ptr);
            if (MONAD_UNLIKELY(!affine_point.has_value())) {
                return PrecompileResult::failure();
            }

            if (MONAD_UNLIKELY(!Group::affine_point_in_group(&*affine_point))) {
                return PrecompileResult::failure();
            }

            if (Group::affine_point_is_inf(&*affine_point)) {
                continue;
            }

            auto const &p = affine_points.emplace_back(*affine_point);
            affine_point_ptrs.emplace_back(&p);

            auto const scalar = read_scalar(ptr + Group::encoded_size);

            auto const &s = scalars.emplace_back(scalar);
            scalar_ptrs.emplace_back(s.b);
        }

        auto *const output_buf =
            static_cast<uint8_t *>(std::malloc(Group::encoded_size));
        MONAD_ASSERT(output_buf != nullptr);

        if (affine_point_ptrs.empty()) {
            std::memset(output_buf, 0, Group::encoded_size);
        }
        else {
            auto const n_points = affine_point_ptrs.size();

            auto const scratch_size = Group::msm_scratch_size(n_points);
            auto const scratch =
                std::make_unique_for_overwrite<uint8_t[]>(scratch_size);

            typename Group::Point result;
            Group::msm(
                &result,
                affine_point_ptrs.data(),
                n_points,
                scalar_ptrs.data(),
                256,
                reinterpret_cast<limb_t *>(scratch.get()));

            typename Group::AffinePoint affine_result;
            Group::to_affine(&affine_result, &result);

            Group::write(affine_result, output_buf);
        }

        return {
            .status_code = EVMC_SUCCESS,
            .obuf = output_buf,
            .output_size = Group::encoded_size,
        };
    }

    template PrecompileResult msm_pippenger<G1>(byte_string_view, uint64_t);
    template PrecompileResult msm_pippenger<G2>(byte_string_view, uint64_t);

    PrecompileResult pairing_check(byte_string_view const input)
    {
        static constexpr auto pair_size = G1::encoded_size + G2::encoded_size;

        if (MONAD_UNLIKELY(input.size() % pair_size != 0)) {
            return PrecompileResult::failure();
        }

        auto const k = input.size() / pair_size;

        if (MONAD_UNLIKELY(k == 0)) {
            return PrecompileResult::failure();
        }

        auto result = *blst_fp12_one();
        auto const *const end_ptr = input.data() + input.size();

        for (auto const *ptr = input.data(); ptr != end_ptr; ptr += pair_size) {
            auto const maybe_g1 = G1::read(ptr);
            if (MONAD_UNLIKELY(!maybe_g1.has_value())) {
                return PrecompileResult::failure();
            }

            auto const maybe_g2 = G2::read(ptr + G1::encoded_size);
            if (MONAD_UNLIKELY(!maybe_g2.has_value())) {
                return PrecompileResult::failure();
            }

            if (MONAD_UNLIKELY(!G1::affine_point_in_group(&*maybe_g1))) {
                return PrecompileResult::failure();
            }

            if (MONAD_UNLIKELY(!G2::affine_point_in_group(&*maybe_g2))) {
                return PrecompileResult::failure();
            }

            if (G1::affine_point_is_inf(&*maybe_g1)) {
                continue;
            }

            if (G2::affine_point_is_inf(&*maybe_g2)) {
                continue;
            }

            blst_fp12 paired;
            blst_miller_loop(&paired, &*maybe_g2, &*maybe_g1);
            blst_fp12_mul(&result, &result, &paired);
        }

        blst_final_exp(&result, &result);

        static constexpr auto bool_encoded_size = 32;

        auto *const output_buf =
            static_cast<uint8_t *>(std::malloc(bool_encoded_size));
        MONAD_ASSERT(output_buf != nullptr);
        std::memset(output_buf, 0, bool_encoded_size);

        if (blst_fp12_is_one(&result)) {
            output_buf[bool_encoded_size - 1] = 1;
        }

        return {
            .status_code = EVMC_SUCCESS,
            .obuf = output_buf,
            .output_size = bool_encoded_size,
        };
    }

    template <typename Group>
    PrecompileResult map_fp_to_g(byte_string_view const input)
    {
        if (MONAD_UNLIKELY(input.size() != Group::element_encoded_size)) {
            return PrecompileResult::failure();
        }

        auto const maybe_fp = Group::read_element(input.data());
        if (MONAD_UNLIKELY(!maybe_fp.has_value())) {
            return PrecompileResult::failure();
        }

        typename Group::Point point;
        Group::map_to_group(&point, &*maybe_fp, nullptr);

        typename Group::AffinePoint result;
        Group::to_affine(&result, &point);

        auto *const output_buf =
            static_cast<uint8_t *>(std::malloc(Group::encoded_size));
        MONAD_ASSERT(output_buf != nullptr);

        Group::write(result, output_buf);

        return {
            .status_code = EVMC_SUCCESS,
            .obuf = output_buf,
            .output_size = Group::encoded_size,
        };
    }

    template PrecompileResult map_fp_to_g<G1>(byte_string_view);
    template PrecompileResult map_fp_to_g<G2>(byte_string_view);
} // namespace bls12

MONAD_NAMESPACE_END
