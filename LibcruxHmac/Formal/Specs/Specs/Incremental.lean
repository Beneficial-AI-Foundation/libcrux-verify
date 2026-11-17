import LibcruxHmac.Formal.Proofs.HmacStreamNew
import LibcruxHmac.Formal.Proofs.HmacStreamUpdate
import LibcruxHmac.Formal.Proofs.HmacStreamFinalize

/-!
# Specifications for `crates/algorithms/hmac/src/incremental.rs`

Public items of `incremental.rs` (claim C3) and their statements. Each statement
is declared once, in `LibcruxHmac/Formal/Proofs/`. It is restated here with
`recall`, which fails to build if the declared statement differs.

* `<HmacStream as HmacState>::new` (C3): `new_spec`; `new_sha{256,384,512}_spec`
  (`Proofs/HmacStreamNew.lean`);
* `<HmacStream as HmacState>::update` (C3): `update_spec`, `update_err`;
  `update_sha{256,384,512}_{spec,err}` (`Proofs/HmacStreamUpdate.lean`);
* `<HmacStream as HmacState>::finalize` (C3): `finalize_spec`;
  `finalize_sha{256,384,512}_spec` (`Proofs/HmacStreamFinalize.lean`).

The trait methods are generic in the digest. Each is stated once for any digest
that meets a `DigestContract` (`Defs/Stream.lean`). It is then instantiated at the
public aliases `HmacSha256`, `HmacSha384` and `HmacSha512`, with the instance
terms the extraction itself uses (`incremental.hmac_sha2_*_slices`), and with
the A2 contract axioms `Trusted.sha{256,384,512}Contract`
(`Trusted/Sha2Stream.lean`). The alias statements are proved from the generic
ones; this also shows that the generic hypotheses hold for the aliases.

Definitions, not separate statements: the struct `HmacStream` and the three
type aliases.

Not stated (agreed exclusion, boundary A3): `incremental::hmac_slices`, which
Aeneas extracts as an axiom (its `&[&[u8]]` argument is a nested borrow), and
the wrappers `hmac_sha2_{256,384,512}_slices`, which call it.

The `example` at the end checks that the three alias statements compose into
C3: `new`, two `update`s and `finalize` give the C1 tag of the concatenated data.

Each `#print axioms` below is followed by its guard list. The guard is
**pending**: until the proof PR, the output also contains `sorryAx`. After the
proof PR it must show exactly the listed axioms. No statement here uses a
translation patch or a core/alloc gap.
-/

open Aeneas Aeneas.Std Result WP
open libcrux_hmac.libcrux_traits.digest (InitializeDigestState)
open libcrux_hmac.libcrux_traits.digest.arrayref (DigestIncremental)
open libcrux_hmac.Spec (DigestContract StreamRep HmacSha256 HmacSha384 HmacSha512
  sha256Digest sha256Init sha384Digest sha384Init sha512Digest sha512Init
  sha256StreamMax sha512StreamMax)

namespace libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState

/-! ## `<HmacStream as HmacState>::new` (C3) -/

recall new_spec {D S : Type} {OUTLEN : Usize} (BLOCK : Usize)
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (hOB : OUTLEN.val ≤ BLOCK.val) (hB : BLOCK.val ≤ U32.max) (hmax : 2 ^ 33 ≤ maxLen)
    (key : Slice U8) :
    new BLOCK inst init key ⦃ r =>
      (key.length ≤ U32.max → ∃ st, r = .Ok st ∧ StreamRep C st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄

#print axioms new_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt` (an extraction
   axiom, A2; only an instance argument of `expect`, never called). -/

recall new_sha256_spec (key : Slice U8) :
    new 64#usize sha256Digest sha256Init key ⦃ r =>
      (key.length ≤ U32.max →
        ∃ st, r = .Ok st ∧ StreamRep Trusted.sha256Contract st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄

#print axioms new_sha256_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha256Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha256`, its `InitializeDigestState` `new`, the
   `Sha256Hash` digest-trait `update`, `reset` and `finish`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt`. -/

recall new_sha384_spec (key : Slice U8) :
    new 128#usize sha384Digest sha384Init key ⦃ r =>
      (key.length ≤ U32.max →
        ∃ st, r = .Ok st ∧ StreamRep Trusted.sha384Contract st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄

#print axioms new_sha384_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha384Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha384`, its `InitializeDigestState` `new`, the
   `Sha384Hash` digest-trait `update`, `reset` and `finish`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt`. -/

recall new_sha512_spec (key : Slice U8) :
    new 128#usize sha512Digest sha512Init key ⦃ r =>
      (key.length ≤ U32.max →
        ∃ st, r = .Ok st ∧ StreamRep Trusted.sha512Contract st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄

#print axioms new_sha512_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha512Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha512`, its `InitializeDigestState` `new`, the
   `Sha512Hash` digest-trait `update`, `reset` and `finish`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt`. -/

/-! ## `<HmacStream as HmacState>::update` (C3) -/

recall update_spec {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep C st key msg) (hdata : data.length ≤ U32.max)
    (hlen : BLOCK.val + msg.length + data.length ≤ maxLen) :
    update inst init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep C st' key (msg ++ data.val) ⦄

#print axioms update_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`. -/

recall update_err {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep C st key msg) (hdata : U32.max < data.length) :
    update inst init st data = ok (.Err .InvalidInputLength, st)

#print axioms update_err
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`. -/

recall update_sha256_spec (st : HmacSha256) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha256Contract st key msg) (hdata : data.length ≤ U32.max)
    (hlen : 64 + msg.length + data.length ≤ sha256StreamMax) :
    update sha256Digest sha256Init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep Trusted.sha256Contract st' key (msg ++ data.val) ⦄

#print axioms update_sha256_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha256Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha256` and its digest-trait operations. -/

recall update_sha256_err (st : HmacSha256) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha256Contract st key msg) (hdata : U32.max < data.length) :
    update sha256Digest sha256Init st data = ok (.Err .InvalidInputLength, st)

#print axioms update_sha256_err
/- Axiom guard (pending): as for `update_sha256_spec`. -/

recall update_sha384_spec (st : HmacSha384) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha384Contract st key msg) (hdata : data.length ≤ U32.max)
    (hlen : 128 + msg.length + data.length ≤ sha512StreamMax) :
    update sha384Digest sha384Init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep Trusted.sha384Contract st' key (msg ++ data.val) ⦄

#print axioms update_sha384_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha384Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha384` and its digest-trait operations. -/

recall update_sha384_err (st : HmacSha384) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha384Contract st key msg) (hdata : U32.max < data.length) :
    update sha384Digest sha384Init st data = ok (.Err .InvalidInputLength, st)

#print axioms update_sha384_err
/- Axiom guard (pending): as for `update_sha384_spec`. -/

recall update_sha512_spec (st : HmacSha512) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha512Contract st key msg) (hdata : data.length ≤ U32.max)
    (hlen : 128 + msg.length + data.length ≤ sha512StreamMax) :
    update sha512Digest sha512Init st data ⦃ r st' =>
      r = .Ok () ∧ StreamRep Trusted.sha512Contract st' key (msg ++ data.val) ⦄

#print axioms update_sha512_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`;
   Trusted (A2): `Trusted.sha512Contract`; extraction axioms (A2, types only):
   `libcrux_sha2.impl_hacl.Sha512` and its digest-trait operations. -/

recall update_sha512_err (st : HmacSha512) (key msg : List U8) (data : Slice U8)
    (hrep : StreamRep Trusted.sha512Contract st key msg) (hdata : U32.max < data.length) :
    update sha512Digest sha512Init st data = ok (.Err .InvalidInputLength, st)

#print axioms update_sha512_err
/- Axiom guard (pending): as for `update_sha512_spec`. -/

/-! ## `<HmacStream as HmacState>::finalize` (C3) -/

recall finalize_spec {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (hOB : OUTLEN.val ≤ BLOCK.val) (hB : BLOCK.val ≤ U32.max) (hmax : 2 ^ 33 ≤ maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8)
    (dst : Array U8 OUTLEN) (hrep : StreamRep C st key msg) :
    finalize inst init st dst ⦃ tag => tag.val = Spec.hmac H BLOCK.val key msg ⦄

#print axioms finalize_spec
/- Axiom guard (pending): `propext`, `Classical.choice`, `Quot.sound`, and
   `libcrux_traits.digest.UpdateError.Insts.CoreFmtDebug.fmt` (never called). -/

recall finalize_sha256_spec (st : HmacSha256) (key msg : List U8) (dst : Array U8 32#usize)
    (hrep : StreamRep Trusted.sha256Contract st key msg) :
    finalize sha256Digest sha256Init st dst ⦃ tag => tag.val = Spec.hmacSha256 key msg ⦄

#print axioms finalize_sha256_spec
/- Axiom guard (pending): as for `new_sha256_spec`. -/

recall finalize_sha384_spec (st : HmacSha384) (key msg : List U8) (dst : Array U8 48#usize)
    (hrep : StreamRep Trusted.sha384Contract st key msg) :
    finalize sha384Digest sha384Init st dst ⦃ tag => tag.val = Spec.hmacSha384 key msg ⦄

#print axioms finalize_sha384_spec
/- Axiom guard (pending): as for `new_sha384_spec`. -/

recall finalize_sha512_spec (st : HmacSha512) (key msg : List U8) (dst : Array U8 64#usize)
    (hrep : StreamRep Trusted.sha512Contract st key msg) :
    finalize sha512Digest sha512Init st dst ⦃ tag => tag.val = Spec.hmacSha512 key msg ⦄

#print axioms finalize_sha512_spec
/- Axiom guard (pending): as for `new_sha512_spec`. -/

/-! ## The three statements compose into C3 -/

/-- At `HmacSha256`: `new`, then `update` with `d₁` and `d₂`, then `finalize`
writes HMAC-SHA-256 of `d₁ ‖ d₂`, the C1 tag of the concatenation. -/
example (key d₁ d₂ : Slice U8) (dst : Array U8 32#usize)
    (hk : key.length ≤ U32.max) (h₁ : d₁.length ≤ U32.max) (h₂ : d₂.length ≤ U32.max)
    (hlen : 64 + d₁.length + d₂.length ≤ sha256StreamMax) :
    (do
      let r ← new 64#usize sha256Digest sha256Init key
      match r with
      | .Ok st =>
        let (_, st) ← update sha256Digest sha256Init st d₁
        let (_, st) ← update sha256Digest sha256Init st d₂
        finalize sha256Digest sha256Init st dst
      | .Err _ => fail .panic) ⦃ tag =>
        tag.val = Spec.hmacSha256 key.val (d₁.val ++ d₂.val) ⦄ := by
  step as ⟨r, hr, _hr⟩
  obtain ⟨st, rfl, hst⟩ := hr hk
  simp only
  step as ⟨r₁, st₁, _e₁, h₁'⟩
  step as ⟨r₂, st₂, _e₂, h₂'⟩
  step as ⟨tag, htag⟩
  simpa using htag

end libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState
