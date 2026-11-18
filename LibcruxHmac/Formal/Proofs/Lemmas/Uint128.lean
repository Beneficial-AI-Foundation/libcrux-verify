import LibcruxHmac.Formal.Proofs.Lemmas.Wrapping
import LibcruxHmac.Formal.Trusted.Sha2Hacl

/-!
# Step lemmas for the 128-bit helpers of `hacl::hmac::compute_sha2_{384,512}`

`compute_sha2_384` and `compute_sha2_512` keep the total length of the message in a
`u128`, built with `fstar::uint128::uint64_to_uint128` and `fstar::uint128::add`. Their
behaviour is the Trusted A2 axioms `uint64_to_uint128_spec` and `uint128_add_spec`; these
are the same facts in the form `step` uses.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac.Lemmas

theorem uint64_to_uint128_step (x : U64) :
    libcrux_hacl_rs.fstar.uint128.uint64_to_uint128 x ⦃ r => r.val = x.val ⦄ := by
  rw [Trusted.uint64_to_uint128_spec, spec_ok]
  show (UScalar.cast .U128 x).val = x.val
  scalar_tac

theorem uint128_add_step (x y : U128) :
    libcrux_hacl_rs.fstar.uint128.add x y ⦃ r => r.val = (x.val + y.val) % 2 ^ 128 ⦄ := by
  rw [Trusted.uint128_add_spec, spec_ok]
  show (UScalar.wrapping_add x y).val = (x.val + y.val) % 2 ^ 128
  rw [UScalar.wrapping_add_val_eq, UScalar.size_def]
  rfl

end libcrux_hmac.Lemmas
