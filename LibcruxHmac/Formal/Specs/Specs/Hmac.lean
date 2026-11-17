import LibcruxHmac.Formal.Proofs.TagSize
import LibcruxHmac.Formal.Proofs.Hmac

/-!
# Specifications for `crates/algorithms/hmac/src/hmac.rs`

Public items of `hmac.rs` and their statements. Each statement is declared once,
in `LibcruxHmac/Formal/Proofs/`. It is restated here with `recall`, which fails to
build if the declared statement differs.

* `libcrux_hmac::tag_size`: `tag_size_spec` (`Proofs/TagSize.lean`);
* `libcrux_hmac::hmac` (C4): `hmac_spec`, `hmac_panic` (`Proofs/Hmac.lean`).

Definitions, not separate statements: `Algorithm`, `Error`, the trait `HmacState`.

Not stated:
* the derived `Clone`, `Copy`, `Debug` and `PartialEq` impls of `Algorithm` and
  `Error`;
* the private helper `wrap_bufalloc`: translation patch `sp-08` inlines it, and
  `hmac_spec` covers its three instances (hmac.rs lines 83–85).

Each `#print axioms` below is followed by its guard list. The guard is
**pending**: until the proof PR, the output also contains `sorryAx`. After the
proof PR it must show exactly the listed axioms.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac

/-! ## `libcrux_hmac::tag_size` -/

recall tag_size_spec (alg : Algorithm) :
    tag_size alg ⦃ n => n.val = Spec.tagLength alg ⦄

#print axioms tag_size_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`.
   No Trusted axiom, no extraction axiom. -/

/-! ## `libcrux_hmac::hmac` (C4) -/

recall hmac_spec
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice) (htrunc : Spec.Gap.VecTruncate)
    (alg : Algorithm) (key data : Slice U8) (tag_length : Option Usize)
    (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
    hmac alg key data tag_length ⦃ v =>
      v.val = (Spec.hmacOf alg key.val data.val).take
        ((tag_length.map (·.val)).getD (Spec.tagLength alg)) ⦄

#print axioms hmac_spec
/- Axiom guard (pending):
   * Lean: `propext`, `Classical.choice`, `Quot.sound`.
   * Extraction axioms reached through `hmac` (boundary A2, types only):
     `libcrux_sha2.hacl.{h256, h384, h512, hash_256, hash_384, hash_512,
     sha{256,384,512}_{init, update_nblocks, update_last, finish}}` and
     `libcrux_hacl_rs.{fstar.uint128.add, fstar.uint128.uint64_to_uint128,
     lowstar.ignore.ignore}`.
   * Extraction axioms of open gaps, reached through `hmac`:
     `alloc.vec.Vec.into_boxed_slice`, `alloc.vec.Vec.truncate`,
     `core.num.U32.wrapping_div`, `core.num.U32.wrapping_rem` (each assumed only
     through the hypotheses `hbox`, `htrunc`, `hdiv`, `hrem`), and
     `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` (never called).
   * Trusted axioms the proof rests on (A2, `Trusted/Sha2Hacl.lean`), through C1:
     `Trusted.{h256, h384, h512}_spec`, `Trusted.sha{256,384,512}_init_spec`,
     `Trusted.sha{256,384,512}_update_nblocks_spec`,
     `Trusted.sha{256,384,512}_update_last_spec`, `Trusted.sha{256,384,512}_finish_spec`,
     `Trusted.hash_{256,384,512}_spec`, `Trusted.uint128_add_spec`,
     `Trusted.uint64_to_uint128_spec`, `Trusted.ignore_spec`.
   * Translation patches (A1, ratified): `sp-04`, `sp-05`, `sp-06`, `sp-08`. -/

recall hmac_panic (alg : Algorithm) (key data : Slice U8) (tag_length : Option Usize)
    (h : U32.max < key.length ∨ U32.max < data.length) :
    hmac alg key data tag_length = fail .panic

#print axioms hmac_panic
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`, and the
   extraction axioms reached through `hmac` (as for `hmac_spec`). No Trusted
   axiom and no gap hypothesis: the `unwrap` fails before any of them is called. -/

end libcrux_hmac
