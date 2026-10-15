/* Spike-only stand-ins: every accelerator the guest links, each failing the
 * run (abort -> unprovable). Real ones come from airbender-crypto or C libs. */
void abort(void) __attribute__((noreturn));
#ifdef STUB_FAIL
/* Test builds: a missing accelerator reports failure (ZKVM_EFAIL). */
#define STUB(name) __attribute__((weak)) int name(void) { return -1; }
#else
#define STUB(name) __attribute__((weak)) void name(void) { abort(); }
#endif
STUB(zkvm_secp256r1_verify)
STUB(zkvm_modexp) STUB(zkvm_kzg_point_eval)
STUB(zkvm_bn254_pairing) STUB(zkvm_bn254_g1_mul) STUB(zkvm_bn254_g1_add)
STUB(zkvm_bls12_pairing) STUB(zkvm_bls12_map_fp_to_g1) STUB(zkvm_bls12_map_fp2_to_g2)
STUB(zkvm_bls12_g2_msm) STUB(zkvm_bls12_g2_add) STUB(zkvm_bls12_g1_msm)
STUB(zkvm_bls12_g1_add) STUB(zkvm_blake2f)
STUB(strerror) STUB(snprintf)
/* std::__throw_out_of_range_fmt(char const*, ...) */
STUB(_ZSt24__throw_out_of_range_fmtPKcz)
