import LibcruxHmac.Formal.Trusted.Sha2Stream

/-!
# `<libcrux_hmac::incremental::HmacStream as HmacState>::finalize`
(crates/algorithms/hmac/src/incremental.rs lines 72–82)

Extracted as `libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.finalize`
(`LibcruxHmac/Extraction/LibcruxHmac.lean` lines 1933–1967), generic in the digest.
Stated once generically (`finalize_spec`), then at `HmacSha256`, `HmacSha384`
and `HmacSha512` with the A2 contract axioms; the alias corollaries are proved
from the generic statement.

natural language description:
    `finalize(dst)` finishes the inner digest (the hash of `(K₀ ⊕ ipad) ‖ msg`),
    then hashes `(K₀ ⊕ opad) ‖ inner hash` with a fresh digest state and writes
    the result into `dst`. Its two `expect`s would panic only if a digest update
    failed.

natural language specs:
    Hypotheses of the generic statement: the digest meets its contract for some
    hash `H` and total limit `maxLen`; `OUTLEN ≤ BLOCK ≤ u32::MAX`; and
    `2 ^ 33 ≤ maxLen`, so that the `BLOCK + OUTLEN` bytes of the outer hash fit.
    For the aliases they hold by computation.
    * If `st` is keyed with `key` after the data `msg` (`StreamRep C st key msg`),
      `finalize` does not panic and writes `Spec.hmac H BLOCK key msg` into
      `dst`, whatever `dst` held (FIPS 198-1 §4 steps 5–9). `msg` is the accepted
      transcript: the bytes that the `update` calls actually absorbed.
    With `new` and `update` this gives C3: `new(key)`, then `update` with `d₁`, …,
    `dₙ` (each at most `u32::MAX` bytes), then `finalize` writes
    `Spec.hmacSha* key (d₁ ‖ … ‖ dₙ)`, as long as `BLOCK + |d₁ ‖ … ‖ dₙ|` stays
    within the digest's total limit. `Spec.hmacSha*` is the mathematical HMAC; it
    is the tag of the C1 function `hmac_sha2_*` when the key and the concatenation
    are below `2 ^ 32` bytes. Past the limit, `update` drops input silently
    (`update_full`), and the tag is the HMAC of the accepted transcript, not of
    all the data passed.
    Conditional on: A1; for the aliases, A2 through the axioms
    `Trusted.sha256Contract`, `Trusted.sha384Contract`, `Trusted.sha512Contract`.
-/

open Aeneas Aeneas.Std Result WP
open libcrux_hmac.libcrux_traits.digest (InitializeDigestState)
open libcrux_hmac.libcrux_traits.digest.arrayref (DigestIncremental)
open libcrux_hmac.Spec (DigestContract StreamRep HmacSha256 HmacSha384 HmacSha512
  sha256Digest sha256Init sha384Digest sha384Init sha512Digest sha512Init)

namespace libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState

/-- C3, `finalize`, for any digest that meets its contract: `finalize` writes the
HMAC tag of the absorbed data under the key. -/
theorem finalize_spec {D S : Type} {OUTLEN BLOCK : Usize}
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (hOB : OUTLEN.val ≤ BLOCK.val) (hB : BLOCK.val ≤ U32.max) (hmax : 2 ^ 33 ≤ maxLen)
    (st : incremental.HmacStream D S OUTLEN BLOCK) (key msg : List U8)
    (dst : Array U8 OUTLEN) (hrep : StreamRep C st key msg) :
    finalize inst init st dst ⦃ tag => tag.val = Spec.hmac H BLOCK.val key msg ⦄ := by
  sorry

/-- C3, `finalize` at `HmacSha256`. -/
@[step]
theorem finalize_sha256_spec (st : HmacSha256) (key msg : List U8) (dst : Array U8 32#usize)
    (hrep : StreamRep Trusted.sha256Contract st key msg) :
    finalize sha256Digest sha256Init st dst ⦃ tag => tag.val = Spec.hmacSha256 key msg ⦄ := by
  simpa [Spec.hmacSha256] using
    finalize_spec sha256Digest sha256Init Trusted.sha256Contract
      (by simp) (by scalar_tac) (by decide) st key msg dst hrep

/-- C3, `finalize` at `HmacSha384`. -/
@[step]
theorem finalize_sha384_spec (st : HmacSha384) (key msg : List U8) (dst : Array U8 48#usize)
    (hrep : StreamRep Trusted.sha384Contract st key msg) :
    finalize sha384Digest sha384Init st dst ⦃ tag => tag.val = Spec.hmacSha384 key msg ⦄ := by
  simpa [Spec.hmacSha384] using
    finalize_spec sha384Digest sha384Init Trusted.sha384Contract
      (by simp) (by scalar_tac) (by decide) st key msg dst hrep

/-- C3, `finalize` at `HmacSha512`. -/
@[step]
theorem finalize_sha512_spec (st : HmacSha512) (key msg : List U8) (dst : Array U8 64#usize)
    (hrep : StreamRep Trusted.sha512Contract st key msg) :
    finalize sha512Digest sha512Init st dst ⦃ tag => tag.val = Spec.hmacSha512 key msg ⦄ := by
  simpa [Spec.hmacSha512] using
    finalize_spec sha512Digest sha512Init Trusted.sha512Contract
      (by simp) (by scalar_tac) (by decide) st key msg dst hrep

end libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState
