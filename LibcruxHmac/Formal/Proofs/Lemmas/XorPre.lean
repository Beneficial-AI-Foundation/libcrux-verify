import LibcruxHmac.Extraction.LibcruxHmac
import LibcruxHmac.Formal.Specs.Defs.Sha2

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac

/-- The entries of `a`, the first `s` of them xored with those of `k`: the state of
the xor loops of `compute_sha2_*` after `s` iterations. -/
def xorPre (a k : List U8) (s : Nat) : List U8 :=
  (List.range a.length).map fun j => if j < s then a[j]! ^^^ k[j]! else a[j]!

@[simp] theorem xorPre_length (a k : List U8) (s : Nat) : (xorPre a k s).length = a.length := by
  simp [xorPre]

theorem xorPre_zero (a k : List U8) : xorPre a k 0 = a := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [xorPre, List.getElem?_eq_getElem h2]

theorem xorPre_end (a k : List U8) (hk : a.length ≤ k.length) :
    xorPre a k a.length = List.zipWith (· ^^^ ·) a k := by
  apply List.ext_getElem
  · simp [xorPre]; omega
  · intro i h1 h2
    simp [xorPre, List.getElem_zipWith] at h1 h2 ⊢
    simp [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem (show i < k.length by omega)]
    intro hh; omega

theorem xorPre_get (a k : List U8) (s : Nat) (hs : s < a.length)
    (h : s < (xorPre a k s).length) : (xorPre a k s)[s] = a[s] := by
  simp [xorPre, List.getElem?_eq_getElem hs]

theorem xorPre_get' (a k l : List U8) (s i : Nat) (hl : l = xorPre a k s) (hs : s < a.length)
    (hsi : i = s) (hi : i < l.length) : l[i] = a[s] := by
  subst hl hsi
  exact xorPre_get a k i hs hi

theorem xorPre_set (a k : List U8) (s : Nat) (hs : s < a.length) (hk : s < k.length) :
    (xorPre a k s).set s (a[s] ^^^ k[s]) = xorPre a k (s + 1) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [xorPre, List.getElem_set] at h1 h2 ⊢
    by_cases hsi : s = i
    · subst hsi
      simp [List.getElem?_eq_getElem hs, List.getElem?_eq_getElem hk]
    · split_ifs <;> first | rfl | omega

end libcrux_hmac
