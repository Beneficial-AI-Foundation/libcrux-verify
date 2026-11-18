import LibcruxHmac.Extraction.LibcruxHmac
import LibcruxHmac.Formal.Specs.Defs.Gaps

/-!
# Helper lemma for `libcrux_hmac::hmac` (C4)

`hmac` runs `hmac_sha2_*` on a zeroed buffer, copies the buffer into a `Vec`, and
truncates the `Vec`. `hmac_tail` is that tail, for any digest: if the call returns a
buffer holding `tl`, then `hmac` returns the first `t` bytes of `tl`. It takes the
behaviour of `Vec::truncate` as the hypothesis `htrunc` (`Spec.Gap.VecTruncate`).
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac

/-- The `Vec` copy and the truncation at the end of `hmac`. -/
theorem hmac_tail {n : Usize} (htrunc : Spec.Gap.VecTruncate) (m : Result (Array U8 n))
    (tl : List U8) (t : Usize) (hm : m ⦃ b => b.val = tl ⦄) :
    (do
      let dst ← (do
        let buf1 ← m
        let s ← lift buf1.to_slice
        alloc.slice.Slice.to_vec core.clone.CloneU8 s)
      alloc.vec.Vec.truncate alloc.alloc.Global dst t) ⦃ v => v.val = tl.take t.val ⦄ := by
  refine spec_bind (Pₘ := fun dst => dst.val = tl) ?_ ?_
  · refine spec_bind hm ?_
    intro buf1 hb
    step as ⟨s, hs⟩
    step as ⟨dst, hd⟩
    exact (congrArg (fun x : Slice U8 => x.val) (hd.symm.trans hs)).trans
      (by simp [Array.to_slice, hb])
  · intro dst hd
    refine spec_mono (htrunc dst _) ?_
    intro v hv
    simp [hv, hd]

end libcrux_hmac
