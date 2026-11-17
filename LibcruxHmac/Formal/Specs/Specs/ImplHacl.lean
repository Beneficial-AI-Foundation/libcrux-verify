import LibcruxHmac.Formal.Proofs.HmacSha2_256
import LibcruxHmac.Formal.Proofs.HmacSha2_384
import LibcruxHmac.Formal.Proofs.HmacSha2_512

/-!
# Specifications for `crates/algorithms/hmac/src/impl_hacl.rs`

Public items of `impl_hacl.rs` (claim C1) and their statements. Each statement
is declared once, in `LibcruxHmac/Formal/Proofs/`. It is restated here with
`recall`, which fails to build if the declared statement differs.

* `libcrux_hmac::hmac_sha2_256` (C1): `hmac_sha2_256_spec`, `hmac_sha2_256_panic`
  (`Proofs/HmacSha2_256.lean`);
* `libcrux_hmac::hmac_sha2_384` (C1): `hmac_sha2_384_spec`, `hmac_sha2_384_panic`
  (`Proofs/HmacSha2_384.lean`);
* `libcrux_hmac::hmac_sha2_512` (C1): `hmac_sha2_512_spec`, `hmac_sha2_512_panic`
  (`Proofs/HmacSha2_512.lean`).

Not stated: `hacl::hmac::compute_sha2_{256,384,512}`. Under the default features
(no `expose-hacl`) they are `pub(crate)`, so they are proof helpers, not public
API.

Each `#print axioms` below is followed by its guard list. The guard is
**pending**: until the proof PR, the output also contains `sorryAx`. After the
proof PR it must show exactly the listed axioms.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac.impl_hacl

/-! ## `libcrux_hmac::hmac_sha2_256` (C1) -/

recall hmac_sha2_256_spec
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst : Array U8 32#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_256 dst key data ⦃ tag => tag.val = Spec.hmacSha256 key.val data.val ⦄

#print axioms hmac_sha2_256_spec
/- Axiom guard (pending):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac_sha2_256` (boundary A2, types only):
     `libcrux_sha2.hacl.{h256, hash_256, sha256_init, sha256_update_nblocks,
     sha256_update_last, sha256_finish}`, `libcrux_hacl_rs.lowstar.ignore.ignore`.
   * Extraction axioms of open gaps: `core.num.U32.wrapping_div`,
     `core.num.U32.wrapping_rem`, `alloc.vec.Vec.into_boxed_slice` (assumed only
     through `hdiv`, `hrem`, `hbox`), and
     `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (never called).
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`):
     `Trusted.h256_spec`, `Trusted.sha256_init_spec`, `Trusted.sha256_update_nblocks_spec`,
     `Trusted.sha256_update_last_spec`, `Trusted.sha256_finish_spec`,
     `Trusted.hash_256_spec`, `Trusted.ignore_spec`.
   * Translation patch (A1, ratified): `sp-04`. -/

recall hmac_sha2_256_panic (dst : Array U8 32#usize) (key data : Slice U8)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac_sha2_256 dst key data = fail .panic

#print axioms hmac_sha2_256_panic
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`, and the
   extraction axioms reached through `hmac_sha2_256` (as for `hmac_sha2_256_spec`).
   No Trusted axiom and no gap hypothesis. -/

/-! ## `libcrux_hmac::hmac_sha2_384` (C1) -/

recall hmac_sha2_384_spec
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst : Array U8 48#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_384 dst key data ⦃ tag => tag.val = Spec.hmacSha384 key.val data.val ⦄

#print axioms hmac_sha2_384_spec
/- Axiom guard (pending):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac_sha2_384` (boundary A2, types only):
     `libcrux_sha2.hacl.{h384, hash_384, sha384_init, sha384_update_nblocks,
     sha384_update_last, sha384_finish}`, `libcrux_hacl_rs.lowstar.ignore.ignore`,
     `libcrux_hacl_rs.fstar.uint128.{add, uint64_to_uint128}`.
   * Extraction axioms of open gaps: `core.num.U32.wrapping_div`,
     `core.num.U32.wrapping_rem`, `alloc.vec.Vec.into_boxed_slice` (assumed only
     through `hdiv`, `hrem`, `hbox`), and
     `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (never called).
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`):
     `Trusted.h384_spec`, `Trusted.sha384_init_spec`, `Trusted.sha384_update_nblocks_spec`,
     `Trusted.sha384_update_last_spec`, `Trusted.sha384_finish_spec`,
     `Trusted.hash_384_spec`, `Trusted.ignore_spec`,
     `Trusted.uint128_add_spec`, `Trusted.uint64_to_uint128_spec`.
   * Translation patch (A1, ratified): `sp-05`. -/

recall hmac_sha2_384_panic (dst : Array U8 48#usize) (key data : Slice U8)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac_sha2_384 dst key data = fail .panic

#print axioms hmac_sha2_384_panic
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`, and the
   extraction axioms reached through `hmac_sha2_384` (as for `hmac_sha2_384_spec`).
   No Trusted axiom and no gap hypothesis. -/

/-! ## `libcrux_hmac::hmac_sha2_512` (C1) -/

recall hmac_sha2_512_spec
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst : Array U8 64#usize) (key data : Slice U8)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac_sha2_512 dst key data ⦃ tag => tag.val = Spec.hmacSha512 key.val data.val ⦄

#print axioms hmac_sha2_512_spec
/- Axiom guard (pending):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac_sha2_512` (boundary A2, types only):
     `libcrux_sha2.hacl.{h512, hash_512, sha512_init, sha512_update_nblocks,
     sha512_update_last, sha512_finish}`, `libcrux_hacl_rs.lowstar.ignore.ignore`,
     `libcrux_hacl_rs.fstar.uint128.{add, uint64_to_uint128}`.
   * Extraction axioms of open gaps: `core.num.U32.wrapping_div`,
     `core.num.U32.wrapping_rem`, `alloc.vec.Vec.into_boxed_slice` (assumed only
     through `hdiv`, `hrem`, `hbox`), and
     `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (never called).
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`):
     `Trusted.h512_spec`, `Trusted.sha512_init_spec`, `Trusted.sha512_update_nblocks_spec`,
     `Trusted.sha512_update_last_spec`, `Trusted.sha512_finish_spec`,
     `Trusted.hash_512_spec`, `Trusted.ignore_spec`,
     `Trusted.uint128_add_spec`, `Trusted.uint64_to_uint128_spec`.
   * Translation patch (A1, ratified): `sp-06`. -/

recall hmac_sha2_512_panic (dst : Array U8 64#usize) (key data : Slice U8)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac_sha2_512 dst key data = fail .panic

#print axioms hmac_sha2_512_panic
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`, and the
   extraction axioms reached through `hmac_sha2_512` (as for `hmac_sha2_512_spec`).
   No Trusted axiom and no gap hypothesis. -/

end libcrux_hmac.impl_hacl
