import LibcruxHmac.Formal.Trusted.Sha2Stream

/-!
# `<libcrux_hmac::incremental::HmacStream as HmacState>::new`
(crates/algorithms/hmac/src/incremental.rs lines 26–66)

Extracted as `libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState.new`
(`LibcruxHmac/Extraction/LibcruxHmac.lean` lines 2082–2150), generic in the digest.
The item is stated once, generically (`new_spec`), for any digest that meets a
`DigestContract`. It is then instantiated at the three public aliases
`HmacSha256`, `HmacSha384` and `HmacSha512` with the A2 contract axioms; those
three corollaries are proved from `new_spec`.

natural language description:
    `new(key)` returns `Err(InvalidInputLength)` if `key.len() > u32::MAX`.
    Otherwise it builds `K₀` in a `BLOCK`-byte buffer: the key padded with zeros,
    or, for a key longer than `BLOCK`, the `OUTLEN`-byte digest of the key padded
    with zeros. It stores `K₀ ⊕ opad`, and feeds `K₀ ⊕ ipad` to a fresh digest
    state, which it stores as `inner`.
    The two `debug_assert!`s (`OUTLEN ≤ BLOCK`, `BLOCK ≤ u32::MAX`) are
    unconditional assertions in the extraction (`massert`).

natural language specs:
    Hypotheses of the generic statement: the digest meets its contract for some
    hash `H` and total limit `maxLen`; `OUTLEN ≤ BLOCK ≤ u32::MAX` (the two
    assertions); and `2 ^ 33 ≤ maxLen`, so that a key of up to `u32::MAX` bytes
    and the later pads fit. For the aliases they hold by computation.
    * If `key.len() ≤ u32::MAX`, `new` returns `Ok st`, where `st` satisfies
      `StreamRep C st key []`: `st.opad = K₀ ⊕ opad` and `st.inner` has absorbed
      `K₀ ⊕ ipad` (FIPS 198-1 §4 steps 1–4 and 7).
    * If `key.len() > u32::MAX`, `new` returns `Err(InvalidInputLength)`.
    In both cases it does not panic. Together with `update` and `finalize`, this
    gives C3: the tag is `Spec.hmac H BLOCK key (concatenated data)`.
    Conditional on: A1; for the aliases, A2 through the axioms
    `Trusted.sha256Contract`, `Trusted.sha384Contract`, `Trusted.sha512Contract`.
    No translation patch and no core/alloc gap is involved.
-/

open Aeneas Aeneas.Std Result WP
open libcrux_hmac.libcrux_traits.digest (InitializeDigestState)
open libcrux_hmac.libcrux_traits.digest.arrayref (DigestIncremental)
open libcrux_hmac.Spec (DigestContract StreamRep sha256Digest sha256Init sha384Digest
  sha384Init sha512Digest sha512Init)

namespace libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState

/-- C3, `new`, for any digest that meets its contract: below `2 ^ 32` bytes of
key, `new` returns a state keyed with `key` that has absorbed nothing; above,
it returns `Err(InvalidInputLength)`. -/
theorem new_spec {D S : Type} {OUTLEN : Usize} (BLOCK : Usize)
    (inst : DigestIncremental D S OUTLEN) (init : InitializeDigestState S)
    {H : List U8 → List U8} {maxLen : Nat} (C : DigestContract inst init H maxLen)
    (hOB : OUTLEN.val ≤ BLOCK.val) (hB : BLOCK.val ≤ U32.max) (hmax : 2 ^ 33 ≤ maxLen)
    (key : Slice U8) :
    new BLOCK inst init key ⦃ r =>
      (key.length ≤ U32.max → ∃ st, r = .Ok st ∧ StreamRep C st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄ := by
  sorry

/-- C3, `new` at `HmacSha256`. -/
@[step]
theorem new_sha256_spec (key : Slice U8) :
    new 64#usize sha256Digest sha256Init key ⦃ r =>
      (key.length ≤ U32.max →
        ∃ st, r = .Ok st ∧ StreamRep Trusted.sha256Contract st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄ :=
  new_spec 64#usize sha256Digest sha256Init Trusted.sha256Contract
    (by simp) (by scalar_tac) (by decide) key

/-- C3, `new` at `HmacSha384`. -/
@[step]
theorem new_sha384_spec (key : Slice U8) :
    new 128#usize sha384Digest sha384Init key ⦃ r =>
      (key.length ≤ U32.max →
        ∃ st, r = .Ok st ∧ StreamRep Trusted.sha384Contract st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄ :=
  new_spec 128#usize sha384Digest sha384Init Trusted.sha384Contract
    (by simp) (by scalar_tac) (by decide) key

/-- C3, `new` at `HmacSha512`. -/
@[step]
theorem new_sha512_spec (key : Slice U8) :
    new 128#usize sha512Digest sha512Init key ⦃ r =>
      (key.length ≤ U32.max →
        ∃ st, r = .Ok st ∧ StreamRep Trusted.sha512Contract st key.val []) ∧
      (U32.max < key.length → r = .Err .InvalidInputLength) ⦄ :=
  new_spec 128#usize sha512Digest sha512Init Trusted.sha512Contract
    (by simp) (by scalar_tac) (by decide) key

end libcrux_hmac.incremental.HmacStream.Insts.Libcrux_hmacHmacState
