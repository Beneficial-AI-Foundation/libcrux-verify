import LibcruxHmac.Extraction.LibcruxHmac

/-!
# The unrolled state initialisation of `hacl::hmac::compute_sha2_*`

`compute_sha2_*` copies the eight words of its initial hash value into a zeroed state, one
word at a time: `h256 ()` for SHA-256, `h384 ()` for SHA-384 and `h512 ()` for SHA-512. It
turns the array into a slice, splits the slice at index 0, sets a word of the right half,
and turns the pieces back into an array.
`level_step` is one such round, for any element type, and `set_chain` is the result of the
eight rounds.
-/

open Aeneas Aeneas.Std

namespace libcrux_hmac.Lemmas

/-- The cast of a `u32` to `usize` keeps its value. -/
theorem cast_u32_usize (a : U32) : (UScalar.cast .Usize a).val = a.val := by scalar_tac

/-- Reading the element at index `i`, when `i` is `k`. -/
theorem getElem_idx {α : Type} [Inhabited α] (l : List α) (i k : Nat) (hik : i = k)
    (h : i < l.length) : l[i]'h = l[k]! := by
  subst hik
  simp [h]

/-- One round: `c'` is `to_slice_mut` of `back (sam (z, r.set idx x))`, where `z, r` are the
two halves of `c` split at 0 and `back` is `A.from_slice`. Then `c'` is `c` with the
word `k` set to `x`. -/
theorem level_step {α : Type} {n : Usize} (hn : n.val = 8)
    {A : Array α n} (b : Slice α → Array α n) (hb : b = A.from_slice)
    (c z r u c' : Slice α) (sam : Slice α × Slice α → Slice α) (idx : Usize) (x : α) (k : Nat)
    (hc : c.length = 8)
    (hz : z.length = 0) (hr : r.length = c.length - 0)
    (hzv : z.val = List.take 0 c.val) (hrv : r.val = List.drop 0 c.val)
    (hsam : ∀ s0' s1' : Slice α, s0'.length = 0 → s1'.length = c.length - 0 →
      (sam (s0', s1')).val = s0'.val ++ s1'.val ∧ (sam (s0', s1')).length = c.length)
    (hu : u = r.set idx x) (hidx : idx.val = k)
    (hc' : c'.val = (b (sam (z, u))).val) :
    c'.val = c.val.set k x ∧ c'.length = 8 := by
  have hulen : u.length = c.length - 0 := by rw [hu, Slice.set_length]; exact hr
  obtain ⟨h1, h2⟩ := hsam z u hz hulen
  have h3 : (b (sam (z, u))).val = (sam (z, u)).val := by
    rw [hb]
    apply Array.from_slice_val
    have : (sam (z, u)).length = 8 := by rw [h2]; exact hc
    simp only [Slice.length] at this
    rw [this, hn]
  have hv : c'.val = c.val.set k x := by
    rw [hc', h3, h1, hzv, hu, Slice.set_val_eq, hrv, hidx]
    simp
  refine ⟨hv, ?_⟩
  have : c.val.length = 8 := hc
  show c'.val.length = 8
  rw [hv, List.length_set, this]

/-- The eight rounds from the zero state set every word. -/
theorem set_chain {α : Type} [Inhabited α] (l : List α) (d : α) (hl : l.length = 8) :
    ((((((((List.replicate 8 d).set 0 l[0]!).set 1 l[1]!).set 2 l[2]!).set 3 l[3]!).set 4
      l[4]!).set 5 l[5]!).set 6 l[6]!).set 7 l[7]! = l := by
  match l, hl with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ => rfl

end libcrux_hmac.Lemmas
