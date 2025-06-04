#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/execution/precompiles.hpp>

#include <blst.h>
#include <intx/intx.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

namespace bls12
{
    using namespace intx::literals;

    inline constexpr auto BASE_FIELD_MODULUS =
        0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab_u384;

    template <typename Group>
    uint16_t msm_discount(uint64_t);

    blst_scalar read_scalar(uint8_t const *);
    std::optional<blst_fp> read_fp(uint8_t const *);
    std::optional<blst_fp2> read_fp2(uint8_t const *);
    std::optional<blst_p1_affine> read_g1(uint8_t const *);
    std::optional<blst_p2_affine> read_g2(uint8_t const *);

    void write_fp(blst_fp const &, uint8_t *);
    void write_fp2(blst_fp2 const &, uint8_t *);
    void write_g1(blst_p1_affine const &, uint8_t *);
    void write_g2(blst_p2_affine const &, uint8_t *);

    template <typename Group>
    PrecompileResult add(byte_string_view);

    template <typename Group>
    PrecompileResult msm(byte_string_view);

    template <typename Group>
    PrecompileResult mul(byte_string_view);

    template <typename Group>
    PrecompileResult msm_pippenger(byte_string_view, uint64_t);

    PrecompileResult pairing_check(byte_string_view);

    template <typename Group>
    PrecompileResult map_fp_to_g(byte_string_view);

    struct G1
    {
        using FieldElement = blst_fp;
        using Point = blst_p1;
        using AffinePoint = blst_p1_affine;

        static constexpr auto element_encoded_size = 64;
        static constexpr auto encoded_size = 2 * element_encoded_size;

        static constexpr auto read = read_g1;
        static constexpr auto read_element = read_fp;
        static constexpr auto write = write_g1;
        static constexpr auto add = blst_p1_add_or_double_affine;
        static constexpr auto map_to_group = blst_map_to_g1;
        static constexpr auto point_in_group = blst_p1_in_g1;
        static constexpr auto affine_point_in_group = blst_p1_affine_in_g1;
        static constexpr auto affine_point_is_inf = blst_p1_affine_is_inf;
        static constexpr auto mul = blst_p1_mult;
        static constexpr auto msm_scratch_size =
            blst_p1s_mult_pippenger_scratch_sizeof;
        static constexpr auto msm = blst_p1s_mult_pippenger;
        static constexpr auto to_affine = blst_p1_to_affine;
        static constexpr auto from_affine = blst_p1_from_affine;
    };

    struct G2
    {
        using FieldElement = blst_fp2;
        using Point = blst_p2;
        using AffinePoint = blst_p2_affine;

        static constexpr auto element_encoded_size =
            2 * G1::element_encoded_size;
        static constexpr auto encoded_size = 2 * element_encoded_size;

        static constexpr auto read = read_g2;
        static constexpr auto read_element = read_fp2;
        static constexpr auto write = write_g2;
        static constexpr auto add = blst_p2_add_or_double_affine;
        static constexpr auto map_to_group = blst_map_to_g2;
        static constexpr auto point_in_group = blst_p2_in_g2;
        static constexpr auto affine_point_in_group = blst_p2_affine_in_g2;
        static constexpr auto affine_point_is_inf = blst_p2_affine_is_inf;
        static constexpr auto mul = blst_p2_mult;
        static constexpr auto msm_scratch_size =
            blst_p2s_mult_pippenger_scratch_sizeof;
        static constexpr auto msm = blst_p2s_mult_pippenger;
        static constexpr auto to_affine = blst_p2_to_affine;
        static constexpr auto from_affine = blst_p2_from_affine;
    };
} // namespace bls12

MONAD_NAMESPACE_END
