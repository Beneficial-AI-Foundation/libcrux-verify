import LibcruxHmac.Formal.Proofs.Lemmas.HmacPure
import LibcruxHmac.Formal.Proofs.Lemmas.StateInit
import LibcruxHmac.Formal.Proofs.Lemmas.Wrapping
import LibcruxHmac.Formal.Proofs.Lemmas.Uint128
import LibcruxHmac.Formal.Proofs.Lemmas.XorLoops
import LibcruxHmac.Formal.Trusted.Sha2Hacl
import LibcruxHmac.Formal.Specs.Defs.Gaps

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac

private theorem sha384_init_spec' (st : Slice U64) (hst : st.length = 8) :
    libcrux_sha2.hacl.sha384_init st
      ⦃ st' => Spec.bvs st' = Spec.sha384IV ∧ st'.length = 8 ⦄ := by
  refine spec_mono (Trusted.sha384_init_spec st hst) ?_
  intro st' h
  exact ⟨h, (Spec.len_of_iv st' _ h).trans rfl⟩

private theorem sha384_update_nblocks_spec' (len : U32) (b : Slice U8) (st : Slice U64)
    (hst : st.length = 8) (hb : len.val / 128 * 128 ≤ b.length) :
    libcrux_sha2.hacl.sha384_update_nblocks len b st ⦃ st' =>
      Spec.bvs st' = Spec.sha512Core.compressBlocks (Spec.bvs st) (b.val.take (len.val / 128 * 128))
        ∧ st'.length = 8 ⦄ := by
  refine spec_mono (Trusted.sha384_update_nblocks_spec len b st hst hb) ?_
  intro st' h
  exact ⟨h, (Spec.len_of_compress512 st st' _ h).trans hst⟩

private theorem sha384_update_last_spec' (totlen : U128) (len : U32) (b : Slice U8) (st : Slice U64)
    (hst : st.length = 8) (hlen : len.val ≤ 128) (hb : len.val ≤ b.length) :
    libcrux_sha2.hacl.sha384_update_last totlen len b st ⦃ st' =>
      Spec.bvs st' = Spec.sha512Core.compressBlocks (Spec.bvs st)
        (Spec.sha512Core.padTail totlen.val (b.val.take len.val)) ∧ st'.length = 8 ⦄ := by
  refine spec_mono (Trusted.sha384_update_last_spec totlen len b st hst hlen hb) ?_
  intro st' h
  exact ⟨h, (Spec.len_of_compress512 st st' _ h).trans hst⟩

private theorem sha384_finish_spec' (st : Slice U64) (h : Slice U8)
    (hst : st.length = 8) (hh : 48 ≤ h.length) :
    libcrux_sha2.hacl.sha384_finish st h ⦃ h' =>
      h'.val = (Spec.sha512Core.serialize (Spec.bvs st)).take 48 ++ h.val.drop 48
        ∧ h'.length = h.length ⦄ := by
  refine spec_mono (Trusted.sha384_finish_spec st h hst hh) ?_
  intro h' hv
  refine ⟨hv, ?_⟩
  have hs : (Spec.sha512Core.serialize (Spec.bvs st)).length = 64 := Spec.serialize512_length st hst
  show h'.val.length = h.val.length
  rw [hv, List.length_append, List.length_take, hs, List.length_drop]
  have : 48 ≤ h.val.length := hh
  omega

attribute [local step] Trusted.h384_spec Trusted.hash_384_spec
  sha384_init_spec' sha384_update_nblocks_spec' sha384_update_last_spec' sha384_finish_spec'
  Lemmas.uint64_to_uint128_step Lemmas.uint128_add_step

private theorem const_i_spec :
    hacl.hmac.compute_sha2_384.i ⦃ r => r.val = 0 ⦄ := by
  unfold hacl.hmac.compute_sha2_384.i
  step*

private theorem const_i_1_spec :
    hacl.hmac.compute_sha2_384.i_1 ⦃ r => r.val = 1 ⦄ := by
  unfold hacl.hmac.compute_sha2_384.i_1
  step*

private theorem const_i_2_spec :
    hacl.hmac.compute_sha2_384.i_2 ⦃ r => r.val = 2 ⦄ := by
  unfold hacl.hmac.compute_sha2_384.i_2
  step*

private theorem const_i_3_spec :
    hacl.hmac.compute_sha2_384.i_3 ⦃ r => r.val = 3 ⦄ := by
  unfold hacl.hmac.compute_sha2_384.i_3
  step*

private theorem const_i_4_spec :
    hacl.hmac.compute_sha2_384.i_4 ⦃ r => r.val = 4 ⦄ := by
  unfold hacl.hmac.compute_sha2_384.i_4
  step*

private theorem const_i_5_spec :
    hacl.hmac.compute_sha2_384.i_5 ⦃ r => r.val = 5 ⦄ := by
  unfold hacl.hmac.compute_sha2_384.i_5
  step*

private theorem const_i_6_spec :
    hacl.hmac.compute_sha2_384.i_6 ⦃ r => r.val = 6 ⦄ := by
  unfold hacl.hmac.compute_sha2_384.i_6
  step*

private theorem const_i_7_spec :
    hacl.hmac.compute_sha2_384.i_7 ⦃ r => r.val = 7 ⦄ := by
  unfold hacl.hmac.compute_sha2_384.i_7
  step*

attribute [local step] const_i_spec const_i_1_spec const_i_2_spec const_i_3_spec
  const_i_4_spec const_i_5_spec const_i_6_spec const_i_7_spec
  hacl.hmac.compute_sha2_384_loop0_spec hacl.hmac.compute_sha2_384_loop1_spec

set_option maxHeartbeats 600000 in
set_option maxRecDepth 1024 in
theorem hacl.hmac.compute_sha2_384_spec_of_gaps
    (hdiv : Spec.Gap.U32WrappingDiv) (hrem : Spec.Gap.U32WrappingRem)
    (hbox : Spec.Gap.VecIntoBoxedSlice)
    (dst key data : Slice U8) (key_len data_len : U32)
    (hdst : dst.length = 48) (hkl : key_len.val = key.length) (hdl : data_len.val = data.length) :
    hacl.hmac.compute_sha2_384 dst key key_len data data_len
      ⦃ r => r.val = Spec.hmacSha384 key.val data.val ⦄ := by
  have hbox' : ∀ v : alloc.vec.Vec U8, alloc.vec.Vec.into_boxed_slice alloc.alloc.Global v = ok v.slice := hbox
  unfold hacl.hmac.compute_sha2_384
  simp only [hbox', Trusted.ignore_spec, bind_ok]
  step* 12
  -- the length of the key part of `key_block`
  apply spec_bind (Pₘ := fun ite : U32 => ite.val = if key_len.val ≤ 128 then key_len.val else 48)
  · by_cases h : key_len ≤ 128#u32
    · have h' : key_len.val ≤ 128 := by scalar_tac
      simp [h, h']
    · have h' : ¬ key_len.val ≤ 128 := by scalar_tac
      simp [h, h']
  intro ite hite
  have hs1 : s1.length = 128 := by
    have : v.slice.length = v.length := rfl
    scalar_tac
  have hite' : ite.val ≤ 128 := by
    split_ifs at hite <;> scalar_tac
  step* by scalar_tac
  -- the key part of `key_block`: `key`, or its hash
  apply spec_bind (Pₘ := fun s4 : Slice U8 =>
    s4.val = if key.length ≤ 128 then key.val else Spec.sha384 key.val)
  · by_cases hk64 : key_len ≤ 128#u32
    · simp only [hk64, ↓reduceIte]
      step* by scalar_tac
      have hk : key.length ≤ 128 := by scalar_tac
      have hi3 : i3.val = key.length := by scalar_tac
      have hlen : s2.val.length = key.length := by scalar_tac
      rw [s5_post2, s7_post, Slice.setSlice!_val, s6_post, hi3]
      simp [List.setSlice!, hlen, hk]
    · simp only [hk64, ↓reduceIte]
      step* by scalar_tac
      have hk : ¬ key.length ≤ 128 := by scalar_tac
      have hkn : ¬ key_len.val ≤ 128 := by scalar_tac
      have hite32 : ite.val = 48 := by simp [hite, hkn]
      have hs2 : s2.val.length = 48 := by scalar_tac
      rw [s4_post]
      simp only [hk, ↓reduceIte]
      rw [hkl, List.take_length, List.drop_eq_nil_of_le (by omega)]
      simp
  intro x hx
  have hi64 : i.val = 128 := by scalar_tac
  have hi1 : i1.val = ite.val := by scalar_tac
  have hvs : v.slice.val = List.replicate 128 0#u8 := by
    have : v.slice.val = v.val := rfl
    rw [this, v_post, hi64]
  have hs1v : s1.val = List.replicate 128 0#u8 := by rw [s_post3, List.drop_zero, hvs]
  have hkl' : key.val.length = key_len.val := hkl.symm
  have hK : x.val = if key.val.length ≤ 128 then key.val else Spec.sha384 key.val := hx
  have hxlen : x.val.length = i1.val := by
    rw [hK]
    split_ifs with hk
    · have hk' : key_len.val ≤ 128 := by omega
      rw [hi1, hite]
      simp only [hk', ↓reduceIte]
      omega
    · have hk' : ¬ key_len.val ≤ 128 := by omega
      rw [Spec.sha384_length, hi1, hite]
      simp only [hk', ↓reduceIte]
  have hkb1 := s2_post4 x s3 hxlen s2_post1
  have hkb2 := s_post4 s (split_at_mut_back1 (x, s3)) s_post (hkb1.2.trans s_post1)
  generalize split_at_mut_back (s, split_at_mut_back1 (x, s3)) = kb at hkb2 ⊢
  have hkb_len : kb.length = 128 := by
    rw [hkb2.2]
    omega
  have hkb_val : kb.val = Spec.keyBlock Spec.sha384 128 key.val := by
    rw [hkb2.1, hkb1.1, s_post2, s2_post3, hs1v, List.take_zero, List.nil_append,
      List.drop_replicate]
    unfold Spec.keyBlock
    simp only [← hK, hxlen, Spec.byte_zero]
  clear hvs hs1v
  step* 2
  have hv1len : v1.slice.length = 128 := by
    have : v1.slice.length = v1.length := rfl
    scalar_tac
  step* 2
  step* 2
  have hv2len : v2.slice.length = 128 := by
    have : v2.slice.length = v2.length := rfl
    scalar_tac
  step* 1
  step* 58 by scalar_tac
  -- the state after the unrolled initialisation is `a`, the initial hash value
  have hn8 : (8#usize).val = 8 := by simp
  have hs6val : s6.val = List.replicate 8 0#u64 := by
    rw [s6_post, Array.repeat_val]; simp
  have hs6len : s6.length = 8 := by
    have : s6.val.length = 8 := by rw [hs6val]; simp
    exact this
  have hal : a.val.length = 8 := by simp
  have hid0 : i6.val = 0 := by rw [i6_post, Lemmas.cast_u32_usize, i4_post]
  have hxi0 : i5.val = 0 := by rw [i5_post, Lemmas.cast_u32_usize, i4_post]
  have hx0 : x = a.val[0]! := by
    rw [x_post]; exact Lemmas.getElem_idx _ _ _ hxi0 _
  have hlev0 := Lemmas.level_step hn8 to_slice_mut_back to_slice_mut_back_post s6 s7 s8 s9 s11 split_at_mut_back2 i6 x 0
    hs6len s7_post s7_post1 s7_post2 s7_post3 s7_post4 s9_post hid0 s11_post
  have hid1 : i9.val = 1 := by rw [i9_post, Lemmas.cast_u32_usize, i7_post]
  have hxi1 : i8.val = 1 := by rw [i8_post, Lemmas.cast_u32_usize, i7_post]
  have hx1 : x1 = a.val[1]! := by
    rw [x1_post]; exact Lemmas.getElem_idx _ _ _ hxi1 _
  have hlev1 := Lemmas.level_step hn8 to_slice_mut_back1 to_slice_mut_back1_post s11 s12 s13 s14 s16 split_at_mut_back3 i9 x1 1
    hlev0.2 s12_post s12_post1 s12_post2 s12_post3 s12_post4 s14_post hid1 s16_post
  have hid2 : i12.val = 2 := by rw [i12_post, Lemmas.cast_u32_usize, i10_post]
  have hxi2 : i11.val = 2 := by rw [i11_post, Lemmas.cast_u32_usize, i10_post]
  have hx2 : x2 = a.val[2]! := by
    rw [x2_post]; exact Lemmas.getElem_idx _ _ _ hxi2 _
  have hlev2 := Lemmas.level_step hn8 to_slice_mut_back2 to_slice_mut_back2_post s16 s17 s18 s19 s21 split_at_mut_back4 i12 x2 2
    hlev1.2 s17_post s17_post1 s17_post2 s17_post3 s17_post4 s19_post hid2 s21_post
  have hid3 : i15.val = 3 := by rw [i15_post, Lemmas.cast_u32_usize, i13_post]
  have hxi3 : i14.val = 3 := by rw [i14_post, Lemmas.cast_u32_usize, i13_post]
  have hx3 : x3 = a.val[3]! := by
    rw [x3_post]; exact Lemmas.getElem_idx _ _ _ hxi3 _
  have hlev3 := Lemmas.level_step hn8 to_slice_mut_back3 to_slice_mut_back3_post s21 s22 s23 s24 s26 split_at_mut_back5 i15 x3 3
    hlev2.2 s22_post s22_post1 s22_post2 s22_post3 s22_post4 s24_post hid3 s26_post
  have hid4 : i18.val = 4 := by rw [i18_post, Lemmas.cast_u32_usize, i16_post]
  have hxi4 : i17.val = 4 := by rw [i17_post, Lemmas.cast_u32_usize, i16_post]
  have hx4 : x4 = a.val[4]! := by
    rw [x4_post]; exact Lemmas.getElem_idx _ _ _ hxi4 _
  have hlev4 := Lemmas.level_step hn8 to_slice_mut_back4 to_slice_mut_back4_post s26 s27 s28 s29 s31 split_at_mut_back6 i18 x4 4
    hlev3.2 s27_post s27_post1 s27_post2 s27_post3 s27_post4 s29_post hid4 s31_post
  have hid5 : i21.val = 5 := by rw [i21_post, Lemmas.cast_u32_usize, i19_post]
  have hxi5 : i20.val = 5 := by rw [i20_post, Lemmas.cast_u32_usize, i19_post]
  have hx5 : x5 = a.val[5]! := by
    rw [x5_post]; exact Lemmas.getElem_idx _ _ _ hxi5 _
  have hlev5 := Lemmas.level_step hn8 to_slice_mut_back5 to_slice_mut_back5_post s31 s32 s33 s34 s36 split_at_mut_back7 i21 x5 5
    hlev4.2 s32_post s32_post1 s32_post2 s32_post3 s32_post4 s34_post hid5 s36_post
  have hid6 : i24.val = 6 := by rw [i24_post, Lemmas.cast_u32_usize, i22_post]
  have hxi6 : i23.val = 6 := by rw [i23_post, Lemmas.cast_u32_usize, i22_post]
  have hx6 : x6 = a.val[6]! := by
    rw [x6_post]; exact Lemmas.getElem_idx _ _ _ hxi6 _
  have hlev6 := Lemmas.level_step hn8 to_slice_mut_back6 to_slice_mut_back6_post s36 s37 s38 s39 s41 split_at_mut_back8 i24 x6 6
    hlev5.2 s37_post s37_post1 s37_post2 s37_post3 s37_post4 s39_post hid6 s41_post
  have hid7 : i27.val = 7 := by rw [i27_post, Lemmas.cast_u32_usize, i25_post]
  have hxi7 : i26.val = 7 := by rw [i26_post, Lemmas.cast_u32_usize, i25_post]
  have hx7 : x7 = a.val[7]! := by
    rw [x7_post]; exact Lemmas.getElem_idx _ _ _ hxi7 _
  have hlev7 := Lemmas.level_step hn8 to_slice_mut_back7 to_slice_mut_back7_post s41 s42 s43 s44 s46 split_at_mut_back9 i27 x7 7
    hlev6.2 s42_post s42_post1 s42_post2 s42_post3 s42_post4 s44_post hid7 s46_post
  have hs46 : s46.val = a.val := by
    rw [hlev7.1, hlev6.1, hlev5.1, hlev4.1, hlev3.1, hlev2.1, hlev1.1, hlev0.1, hs6val,
      hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7]
    exact Lemmas.set_chain a.val 0#u64 hal
  have hbvs : Spec.bvs s46 = Spec.sha384IV := by
    have hIV : a.val.map (fun (x : U64) => x.bv) = Spec.sha384IV := by assumption
    unfold Spec.bvs
    rw [hs46]
    exact hIV
  have hs46len : s46.length = 8 := hlev7.2
  -- the two padded key blocks
  have hkb_len' : kb.val.length = 128 := hkb_len
  have hi2 : i2.val = 128 := by rw [i2_post, Lemmas.cast_u32_usize]; rfl
  have hi3 : i3.val = 128 := by rw [i3_post, Lemmas.cast_u32_usize]; rfl
  have hv1s : v1.slice.val = List.replicate kb.val.length 54#u8 := by
    have : v1.slice.val = v1.val := rfl
    rw [this, v1_post, hi2, hkb_len']
  have hv2s : v2.slice.val = List.replicate kb.val.length 92#u8 := by
    have : v2.slice.val = v2.val := rfl
    rw [this, v2_post, hi3, hkb_len']
  have hipad_len : ipad1.val.length = 128 := by
    rw [ipad1_post, hv1s, Spec.zipWith_xor_replicate, List.length_map]; exact hkb_len'
  have hopad_len : opad1.val.length = 128 := by
    rw [opad1_post, hv2s, Spec.zipWith_xor_replicate, List.length_map]; exact hkb_len'
  have hipad : ipad1.val = Spec.innerKeyBlock Spec.sha384 128 key.val := by
    rw [ipad1_post, hv1s, Spec.zipWith_xor_replicate, hkb_val]
    simp only [Spec.innerKeyBlock, Spec.ipadByte, Spec.byte_ipad]
  have hopad : opad1.val = Spec.outerKeyBlock Spec.sha384 128 key.val := by
    rw [opad1_post, hv2s, Spec.zipWith_xor_replicate, hkb_val]
    simp only [Spec.outerKeyBlock, Spec.opadByte, Spec.byte_opad]
  clear * - hdiv hrem hdst hdl hbvs hs46len hipad hopad hipad_len hopad_len
  have hipad_len' : ipad1.length = 128 := hipad_len
  have hopad_len' : opad1.length = 128 := hopad_len
  -- the inner hash, `s47`
  apply spec_bind (Pₘ := fun s47 : Slice U64 =>
    Spec.bvs s47 = Spec.sha512Core.compressBlocks Spec.sha384IV
      (Spec.sha512Core.pad (ipad1.val ++ data.val)) ∧ s47.length = 8)
  · have hdl32 : data_len.val < 4294967296 := by scalar_tac
    by_cases h0 : data_len = 0#u32
    · simp only [h0, ↓reduceIte]
      step* by scalar_tac
      have hdata : data.val = [] := by
        have h1 : data_len.val = 0 := by simp [h0]
        have h2 : data.length = 0 := by omega
        exact List.length_eq_zero_iff.mp h2
      have hi28 : i28.val = 0 := by simp [i28_post]
      have hi29 : i29.val = 128 := by simp [i29_post]
      have hi30 : i30.val = 128 := by rw [i30_post, hi29]
      have hi31 : i31.val = 128 := by simp [i31_post, hi28, hi30]
      have htk : List.take 128 ipad1.val = ipad1.val := List.take_of_length_le (by omega)
      refine ⟨?_, by omega⟩
      rw [s47_post, hbvs, hi31, htk]
      unfold Spec.Sha2Core.pad
      rw [hdata, List.append_nil, hipad_len]
    · simp only [h0, ↓reduceIte]
      have hdl0 : data_len.val ≠ 0 := by scalar_tac
      have hdiv' : ∀ a : U32, core.num.U32.wrapping_div a 128#u32 ⦃ r => r.val = a.val / 128 ⦄ :=
        fun a => hdiv a 128#u32 (by scalar_tac)
      have hrem' : ∀ a : U32, core.num.U32.wrapping_rem a 128#u32 ⦃ r => r.val = a.val % 128 ⦄ :=
        fun a => hrem a 128#u32 (by scalar_tac)
      step with hdiv' as ⟨n_blocks, hnb⟩
      step with hrem' as ⟨rem, hrm⟩
      -- the number of whole blocks and the length of the tail
      apply spec_bind (Pₘ := fun p : U32 × U32 =>
        p.1.val * 128 + p.2.val = data_len.val ∧ p.2.val ≤ 128)
      · by_cases hgt : n_blocks > 0#u32
        · simp only [hgt, ↓reduceIte]
          by_cases hr0 : rem = 0#u32
          · simp only [hr0, ↓reduceIte]
            step*
            have hnb1 : 1 ≤ n_blocks.val := by scalar_tac
            have hrm0 : rem.val = 0 := by scalar_tac
            have hd : data_len.val = 128 * n_blocks.val := by omega
            have e1 : n_blocks_prev.val = n_blocks.val - 1 := by
              rw [n_blocks_prev_post]; exact Lemmas.w32_sub _ _ (by simpa using hnb1)
            have e2 : i28.val = n_blocks_prev.val * 128 := by
              rw [i28_post]; exact Lemmas.w32_mul _ _ (by simp; omega)
            have e3 : i29.val = data_len.val - i28.val := by
              rw [i29_post]; exact Lemmas.w32_sub _ _ (by omega)
            show n_blocks_prev.val * 128 + i29.val = data_len.val ∧ i29.val ≤ 128
            omega
          · simp only [hr0, ↓reduceIte]
            step*
            show n_blocks.val * 128 + rem.val = data_len.val ∧ rem.val ≤ 128
            omega
        · simp only [hgt, ↓reduceIte]
          step*
          show n_blocks.val * 128 + rem.val = data_len.val ∧ rem.val ≤ 128
          omega
      intro p hp
      obtain ⟨n0, rl⟩ := p
      obtain ⟨hnl, hrl⟩ := hp
      simp only at hnl hrl ⊢
      step* 1
      have hfl : full_blocks_len.val = n0.val * 128 := by
        rw [full_blocks_len_post]; exact Lemmas.w32_mul _ _ (by simp; omega)
      step* 3
      step* 2
      have hi29 : i29.val = n0.val * 128 := by
        rw [i29_post]; exact Lemmas.w32_mul _ _ (by simp; omega)
      step* 1
      step* 5
      step* 3
      step* 1 by scalar_tac
      have hdl' : data.val.length = data_len.val := hdl.symm
      have hs48 : s48.val = List.drop 0 data.val := by assumption
      have hi28 : i28.val = n0.val * 128 := by rw [i28_post, Lemmas.cast_u32_usize, hfl]
      have hi30 : i30.val = 128 := by simp [i30_post]
      have hi31 : i31.val = 128 := by rw [i31_post, hi30]
      have hi32 : i32.val = n0.val * 128 := by rw [i32_post, Lemmas.cast_u32_u64, hfl]
      have hi33 : i33.val = n0.val * 128 := by rw [i33_post, hi32]
      have hi34 : i34.val = 128 + n0.val * 128 := by
        rw [i34_post, hi31, hi33]; exact Nat.mod_eq_of_lt (by omega)
      have hi35 : i35.val = rl.val := by rw [i35_post]; exact Lemmas.cast_u32_u64 rl
      have hi36 : i36.val = rl.val := by rw [i36_post, hi35]
      have hi37 : i37.val = 128 + n0.val * 128 + rl.val := by
        rw [i37_post, hi34, hi36]; exact Nat.mod_eq_of_lt (by omega)
      have hD : i37.val = ipad1.val.length + data.val.length := by omega
      have hA : List.take (128 / 128 * 128) ipad1.val = ipad1.val :=
        List.take_of_length_le (by omega)
      have hB : List.take (i29.val / 128 * 128) s49.val = data.val.take (n0.val * 128) := by
        have h1 : i29.val / 128 * 128 = n0.val * 128 := by omega
        rw [s49_post2, hs48, List.drop_zero, hi28, h1, List.take_take, min_self]
      have hC : List.take rl.val s50.val = data.val.drop (n0.val * 128) := by
        rw [s49_post3, hs48, List.drop_zero, hi28]
        apply List.take_of_length_le
        simp only [List.length_drop]
        omega
      have hbl : Spec.sha512Core.blockLen = 128 := rfl
      have key := Spec.Sha2Core.compressBlocks_pad_split Spec.sha512Core (by rw [hbl]; decide)
        Spec.sha384IV ipad1.val data.val (n0.val * 128)
        (by simp [hbl, hipad_len]) (by rw [hbl]; exact Dvd.intro_left _ rfl) (by omega)
      refine ⟨?_, s47_post1⟩
      rw [s47_post, s52_post, s51_post, hbvs, hA, hB, hC, hD]
      exact key
  -- the outer hash
  intro s47 hs47
  obtain ⟨hv47, hl47⟩ := hs47
  have hd32 := hdiv 48#u32 128#u32 (by scalar_tac)
  have hr32 := hrem 48#u32 128#u32 (by scalar_tac)
  step* 4
  step with hd32 as ⟨n_blocks, hnb⟩
  step with hr32 as ⟨rem, hrm⟩
  have hnb0 : n_blocks.val = 0 := by simpa using hnb
  have hrm32 : rem.val = 48 := by simpa using hrm
  have hn0 : ¬ n_blocks > 0#u32 := by scalar_tac
  simp only [hn0, ↓reduceIte, bind_ok]
  step* 1
  have hfl : full_blocks_len.val = 0 := by
    rw [full_blocks_len_post]
    exact (Lemmas.w32_mul _ _ (by simp [hnb0])).trans (by simp [hnb0])
  step* 3
  step* 2
  have hi29 : i29.val = 0 := by
    rw [i29_post]
    exact (Lemmas.w32_mul _ _ (by simp [hnb0])).trans (by simp [hnb0])
  step* 1
  step* 5
  step* 3
  step* 2 by scalar_tac
  have hs50 : s50.val = List.drop 0 s49.val := by assumption
  have hs52 : s52.val = List.drop 0 s50.val := by assumption
  have hdst' : dst.val.length = 48 := hdst
  have hi28 : i28.val = 0 := by rw [i28_post, Lemmas.cast_u32_usize, hfl]
  have hi30 : i30.val = 128 := by simp [i30_post]
  have hi31 : i31.val = 128 := by rw [i31_post, hi30]
  have hi32 : i32.val = 0 := by rw [i32_post, Lemmas.cast_u32_u64, hfl]
  have hi33 : i33.val = 0 := by rw [i33_post, hi32]
  have hi34 : i34.val = 128 := by simp [i34_post, hi31, hi33]
  have hi35 : i35.val = 48 := by rw [i35_post, Lemmas.cast_u32_u64, hrm32]
  have hi36 : i36.val = 48 := by rw [i36_post, hi35]
  have hi37 : i37.val = 176 := by simp [i37_post, hi34, hi36]
  have hX : ((Spec.sha512Core.serialize (Spec.bvs s47)).take 48).length = 48 := by
    simp [Spec.serialize512_length s47 hl47]
  have hbl : Spec.sha512Core.blockLen = 128 := rfl
  -- what `update_last` pads: the inner hash
  have hs54 : s54.val
      = (Spec.sha512Core.serialize (Spec.bvs s47)).take 48 ++ List.drop 48 s48.val := by
    rw [s53_post3, hi28, List.drop_zero, hs52, List.drop_zero, hs50, List.drop_zero, s49_post]
  have hC : List.take rem.val s54.val = (Spec.sha512Core.serialize (Spec.bvs s47)).take 48 := by
    rw [hs54, hrm32]; exact List.take_left' hX
  have hB : List.take (i29.val / 128 * 128) s53.val = [] := by
    rw [s53_post2, hi28, List.take_zero, List.take_nil]
  have hA : List.take (128 / 128 * 128) opad1.val = opad1.val :=
    List.take_of_length_le (by omega)
  have e56 : Spec.bvs s56 = Spec.bvs s55 := by
    rw [s56_post, hB]
    exact Spec.Sha2Core.compressBlocks_nil Spec.sha512Core (Spec.bvs s55)
  have hbv57 : Spec.bvs s57 = Spec.sha512Core.compressBlocks
      (Spec.sha512Core.compressBlocks Spec.sha384IV opad1.val)
      (Spec.sha512Core.padTail 176 ((Spec.sha512Core.serialize (Spec.bvs s47)).take 48)) := by
    rw [s57_post, e56, s55_post, hA, ‹Spec.bvs s51 = Spec.sha384IV›, hi37, hC]
  have hY : Spec.sha384 (ipad1.val ++ data.val)
      = (Spec.sha512Core.serialize (Spec.bvs s47)).take 48 := by
    unfold Spec.sha384 Spec.Sha2Core.hash
    rw [← hv47]
  have hpad : Spec.sha512Core.pad
        (opad1.val ++ (Spec.sha512Core.serialize (Spec.bvs s47)).take 48)
      = opad1.val ++ Spec.sha512Core.padTail 176
          ((Spec.sha512Core.serialize (Spec.bvs s47)).take 48) := by
    unfold Spec.Sha2Core.pad
    rw [List.length_append, hopad_len, hX]
    exact Spec.Sha2Core.padTail_append _ _ _ _ (by simp [hbl, hopad_len])
  have hcat : Spec.sha512Core.compressBlocks Spec.sha384IV
      (opad1.val ++ Spec.sha512Core.padTail 176
        ((Spec.sha512Core.serialize (Spec.bvs s47)).take 48))
      = Spec.bvs s57 := by
    rw [hbv57]
    exact Spec.Sha2Core.compressBlocks_append Spec.sha512Core (by simp [hbl]) Spec.sha384IV
      opad1.val _ (by simp [hbl, hopad_len])
  have hQ : Spec.sha384 (opad1.val ++ (Spec.sha512Core.serialize (Spec.bvs s47)).take 48)
      = (Spec.sha512Core.serialize (Spec.bvs s57)).take 48 := by
    unfold Spec.sha384 Spec.Sha2Core.hash
    rw [hpad, hcat]
  have hr : r.val = (Spec.sha512Core.serialize (Spec.bvs s57)).take 48 := by
    rw [r_post, List.drop_eq_nil_of_le (by omega), List.append_nil]
  have hhm : Spec.hmacSha384 key.val data.val
      = Spec.sha384 (opad1.val ++ Spec.sha384 (ipad1.val ++ data.val)) := by
    unfold Spec.hmacSha384 Spec.hmac
    rw [← hipad, ← hopad]
  rw [hr, hhm, hY, hQ]

end libcrux_hmac
