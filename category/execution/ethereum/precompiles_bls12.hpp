#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/precompiles.hpp>

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

    // The BLST library is implemented as an internal C static library with
    // language-specific bindings applied on top. The implementation and
    // bindings for C are not actually coupled: both the bindings and
    // implementations define separate types representing points (though they
    // share the same representation). This means that calling (e.g.)
    // `blst_p1_add` through the function pointer `&blst_p1_add` is undefined
    // behaviour, because the function pointer type is a
    // different-but-compatible type to the actual type of the function
    // implementation.
    //
    // This means that directly using the bindings-supplied function pointers in
    // these trait classes is UB, and we need to introduce a layer of
    // indirection via a function for each of them to avoid the UB case. Doing
    // so means that the BLST functions are never called through a function
    // pointer. The UB in question is unlikely to matter in practice, but doing
    // this allows us to run the code in a well-defined manner and without
    // adding UBSan suppressions.
#define DECLARE_GROUP_FN(name, impl)                                           \
    [[gnu::always_inline]]                                                     \
    static inline auto name(auto &&...args)                                    \
    {                                                                          \
        return impl(std::forward<decltype(args)>(args)...);                    \
    }

    struct G1
    {
        using FieldElement = blst_fp;
        using Point = blst_p1;
        using AffinePoint = blst_p1_affine;

        static constexpr auto element_encoded_size = 64;
        static constexpr auto encoded_size = 2 * element_encoded_size;

        DECLARE_GROUP_FN(read, read_g1);
        DECLARE_GROUP_FN(read_element, read_fp);
        DECLARE_GROUP_FN(write, write_g1);
        DECLARE_GROUP_FN(add, blst_p1_add_or_double_affine);
        DECLARE_GROUP_FN(map_to_group, blst_map_to_g1);
        DECLARE_GROUP_FN(point_in_group, blst_p1_in_g1);
        DECLARE_GROUP_FN(affine_point_in_group, blst_p1_affine_in_g1);
        DECLARE_GROUP_FN(affine_point_is_inf, blst_p1_affine_is_inf);
        DECLARE_GROUP_FN(mul, blst_p1_mult);
        DECLARE_GROUP_FN(
            msm_scratch_size, blst_p1s_mult_pippenger_scratch_sizeof);
        DECLARE_GROUP_FN(msm, blst_p1s_mult_pippenger);
        DECLARE_GROUP_FN(to_affine, blst_p1_to_affine);
        DECLARE_GROUP_FN(from_affine, blst_p1_from_affine);
    };

    struct G2
    {
        using FieldElement = blst_fp2;
        using Point = blst_p2;
        using AffinePoint = blst_p2_affine;

        static constexpr auto element_encoded_size =
            2 * G1::element_encoded_size;
        static constexpr auto encoded_size = 2 * element_encoded_size;

        DECLARE_GROUP_FN(read, read_g2);
        DECLARE_GROUP_FN(read_element, read_fp2);
        DECLARE_GROUP_FN(write, write_g2);
        DECLARE_GROUP_FN(add, blst_p2_add_or_double_affine);
        DECLARE_GROUP_FN(map_to_group, blst_map_to_g2);
        DECLARE_GROUP_FN(point_in_group, blst_p2_in_g2);
        DECLARE_GROUP_FN(affine_point_in_group, blst_p2_affine_in_g2);
        DECLARE_GROUP_FN(affine_point_is_inf, blst_p2_affine_is_inf);
        DECLARE_GROUP_FN(mul, blst_p2_mult);
        DECLARE_GROUP_FN(
            msm_scratch_size, blst_p2s_mult_pippenger_scratch_sizeof);
        DECLARE_GROUP_FN(msm, blst_p2s_mult_pippenger);
        DECLARE_GROUP_FN(to_affine, blst_p2_to_affine);
        DECLARE_GROUP_FN(from_affine, blst_p2_from_affine);
    };

#undef DECLARE_GROUP_FN
} // namespace bls12

MONAD_NAMESPACE_END
