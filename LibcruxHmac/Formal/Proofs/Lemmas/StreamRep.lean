import LibcruxHmac.Formal.Specs.Defs.Stream

/-!
# Helper lemmas for the streaming state invariant `StreamRep` (claim C3)

For an arbitrary hash function `H`, `keyBlock H B K` need not have `B` bytes. A
state `st` that satisfies `StreamRep` does, because `st.opad` is an array of `BLOCK`
bytes and equals `outerKeyBlock H BLOCK key`. The contract laws of `update` count
the bytes of `innerKeyBlock H BLOCK key ++ msg`, so `update` and `finalize` need this.
-/

open Aeneas Aeneas.Std Result WP
open libcrux_hmac.libcrux_traits.digest

namespace libcrux_hmac.Spec

/-- `K₀ ⊕ ipad` of a state has exactly `BLOCK` bytes. -/
theorem StreamRep.innerKeyBlock_length {D S : Type} {OUTLEN BLOCK : Usize}
    {inst : arrayref.DigestIncremental D S OUTLEN} {init : InitializeDigestState S}
    {H : List Byte → List Byte} {maxLen : Nat}
    {C : DigestContract inst init H maxLen}
    {st : incremental.HmacStream D S OUTLEN BLOCK} {key msg : List Byte}
    (h : StreamRep C st key msg) :
    (innerKeyBlock H BLOCK.val key).length = BLOCK.val := by
  obtain ⟨h1, -⟩ := h
  have h2 := st.opad.property
  simp only [innerKeyBlock, outerKeyBlock, List.length_map] at h1 ⊢
  rw [h1] at h2
  simpa using h2

/-- The number of bytes absorbed by the inner digest of a state: the `BLOCK` bytes of
`K₀ ⊕ ipad` and the accepted data. -/
theorem StreamRep.inner_length {D S : Type} {OUTLEN BLOCK : Usize}
    {inst : arrayref.DigestIncremental D S OUTLEN} {init : InitializeDigestState S}
    {H : List Byte → List Byte} {maxLen : Nat}
    {C : DigestContract inst init H maxLen}
    {st : incremental.HmacStream D S OUTLEN BLOCK} {key msg : List Byte}
    (h : StreamRep C st key msg) :
    (innerKeyBlock H BLOCK.val key ++ msg).length = BLOCK.val + msg.length := by
  rw [List.length_append, h.innerKeyBlock_length]

end libcrux_hmac.Spec
