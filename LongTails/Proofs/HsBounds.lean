import LongTails.Proofs.HsInstance

open scoped RealInnerProductSpace BigOperators
open LongTails.Proofs.HsProfile LongTails.Proofs.HsChain LongTails.Proofs.HsInstance
open LongTails.Proofs.HsStability

namespace LongTails.Proofs.HsBounds

variable {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (p : ℕ)

noncomputable def KK (k : ℕ) : ℝ := (k : ℝ) + 1

noncomputable def ca (k : ℕ) : ℝ := 3 / (8 * KK k)

noncomputable def ch (k : ℕ) : ℝ := 1 / (8 * KK k)

noncomputable def cθ (k : ℕ) : ℝ := 1 / (16 * KK k)

noncomputable def cw : ℝ := 1 / 8

noncomputable def cl (k : ℕ) : ℝ := 1 / (8 * KK k)

noncomputable def cκ : ℝ := 4

noncomputable def cC (k : ℕ) : ℝ := 2 * KK k + 1 / 8

noncomputable def cB (k : ℕ) : ℝ := 2 * Real.sqrt (KK k + 1)

lemma KK_pos (k : ℕ) : 0 < KK k := by unfold KK; positivity

lemma KK_ge (k : ℕ) : 1 ≤ KK k := by unfold KK; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma ch_pos (k : ℕ) : 0 < ch k := by unfold ch; have := KK_pos k; positivity

lemma ca_sub_ch (k : ℕ) : ca k - ch k = 1 / (4 * KK k) := by
  unfold ca ch; have := KK_pos k; field_simp; ring

lemma ca_add_ch (k : ℕ) : KK k * (ca k + ch k) = 1 / 2 := by
  unfold ca ch; have := KK_pos k; field_simp; ring

lemma two_θ_le (k : ℕ) : 2 * cθ k ≤ ca k - ch k := by
  rw [ca_sub_ch]; unfold cθ; have := KK_pos k
  rw [show 2 * (1 / (16 * KK k)) = 1 / (8 * KK k) by ring]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma cθ_le (k : ℕ) : cθ k ≤ 1 / 16 := by
  unfold cθ; have := KK_ge k
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable abbrev FF (u : E d) : E d :=
  Fv p p (ca k) (ch k) cw (cl k) cκ (cC k) (nn π) cc u

noncomputable abbrev DFF (u : E d) : E d →L[ℝ] E d :=
  DFv p p (ca k) (ch k) cw (cl k) cκ (cC k) (nn π) cc u

noncomputable abbrev ff (u : E d) : ℝ :=
  fv p p (ca k) (ch k) cw (cl k) cκ (cC k) (nn π) cc u

lemma sp0_le_abs (hp : 1 ≤ p) {a h : ℝ} (hh : 0 < h) (hah : 0 ≤ a - h) (t : ℝ) :
    sp0 p a h t ≤ |t| := by
  have h1 := sp0_le p a hp hh t
  have h2 : cut (t - a + h) ≤ |t| := by
    unfold cut
    exact max_le (by linarith [le_abs_self t]) (abs_nonneg t)
  linarith

lemma abs_le_half (x : ℝ) : |x| ≤ (1 + x ^ 2) / 2 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

lemma Cv_le_quad (hp : 1 ≤ p) (u : E d) :
    Cv p (ca k) (ch k) (nn π) cc u ≤ 1 + KK k + ‖u‖ ^ 2 := by
  have hh := ch_pos k
  have hah : 0 ≤ ca k - ch k := by rw [ca_sub_ch]; have := KK_pos k; positivity
  have h1 : Cv p (ca k) (ch k) (nn π) cc u ≤ ∑ j, |lin (nn π) cc j u| :=
    Finset.sum_le_sum fun j _ => sp0_le_abs p hp hh hah _
  have h2 : ∀ j, |lin (nn π) cc j u| ≤
      (1 + ⟪pv π j, u⟫ ^ 2) / 2 + (1 + u (π j) ^ 2) / 2 + cc j := by
    intro j
    rw [lin_full]
    have hc : 0 ≤ cc j := by unfold cc; split_ifs <;> norm_num
    calc |⟪pv π j, u⟫ - u (π j) + cc j| ≤ |⟪pv π j, u⟫| + |u (π j)| + |cc j| := by
          have := abs_add_le (⟪pv π j, u⟫ - u (π j)) (cc j)
          have := abs_sub (⟪pv π j, u⟫) (u (π j))
          linarith
      _ ≤ _ := by
          rw [abs_of_nonneg hc]
          linarith [abs_le_half ⟪pv π j, u⟫, abs_le_half (u (π j))]
  have h3 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h2 j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h3
  have hc : ∑ j : Fin (k + 1), cc j = 1 := by rw [Fin.sum_univ_succ]; simp [cc]
  have hs1 : ∑ j : Fin (k + 1), (1 + ⟪pv π j, u⟫ ^ 2) / 2 ≤ (KK k + ‖u‖ ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have := sum_pv_sq π u
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold KK
    push_cast
    linarith
  have hs2 : ∑ j : Fin (k + 1), (1 + u (π j) ^ 2) / 2 ≤ (KK k + ‖u‖ ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have := sum_sq_le_norm_sq π u
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold KK
    push_cast
    linarith
  rw [hc] at h3
  linarith

lemma zv_far (hp : 1 ≤ p) (u : E d) (hu : 4 * KK k + 4 ≤ ‖u‖ ^ 2) (t : ℕ) :
    cw ≤ zv p (ca k) (ch k) cκ (cC k) (nn π) cc u ∧
      cw ≤ zv p (ca k) (ch k) cκ (cC k) (nt π t) (ct t) u := by
  have hq := Cv_le_quad π p hp u
  have hm := Cv_masked_le π p (ca k) hp (ch_pos k)
    (by rw [ca_sub_ch]; have := KK_pos k; positivity) t u
  have hK := KK_ge k
  unfold zv Rv cκ cC cw
  constructor <;> linarith

lemma answers_far (hp : 1 ≤ p) {n : Fin (k + 1) → E d} {c : Fin (k + 1) → ℝ} (u : E d)
    (hz : cw ≤ zv p (ca k) (ch k) cκ (cC k) n c u) :
    Fv p p (ca k) (ch k) cw (cl k) cκ (cC k) n c u = (cl k + cκ) • u ∧
      DFv p p (ca k) (ch k) cw (cl k) cκ (cC k) n c u =
        (cl k + cκ) • ContinuousLinearMap.id ℝ (E d) := by
  have hw : (0 : ℝ) < cw := by unfold cw; norm_num
  have h1 : sp1 p 0 cw (zv p (ca k) (ch k) cκ (cC k) n c u) = 1 :=
    sp1_of_ge p 0 hp hw (by linarith)
  have h2 : sp2 p 0 cw (zv p (ca k) (ch k) cκ (cC k) n c u) = 0 :=
    sp2_eq_zero p 0 hp hw (by rw [sub_zero, abs_of_nonneg (by linarith)]; exact hz)
  constructor
  · simp only [Fv, dv, h1, one_smul]
    rw [add_smul]; abel
  · simp only [DFv, h1, h2, one_smul, zero_smul, add_zero]
    module

lemma Cg_norm_le (hp : 1 ≤ p) (u : E d) : ‖Cg p (ca k) (ch k) (nn π) cc u‖ ≤ 2 * KK k := by
  unfold Cg
  calc ‖∑ j, sp1 p (ca k) (ch k) (lin (nn π) cc j u) • nn π j‖ ≤
      ∑ j, ‖sp1 p (ca k) (ch k) (lin (nn π) cc j u) • nn π j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (k + 1), (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sp1_nonneg p _ hp _)]
        calc sp1 p (ca k) (ch k) (lin (nn π) cc j u) * ‖nn π j‖ ≤ 1 * 2 :=
              mul_le_mul (sp1_le_one p _ hp _) (norm_nn_le π j) (norm_nonneg _) zero_le_one
          _ = 2 := by norm_num
    _ = 2 * KK k := by simp [KK]; ring

lemma band (hp : 1 ≤ p) (u : E d) (hz : |zv p (ca k) (ch k) cκ (cC k) (nn π) cc u| < cw) :
    ‖dv p (ca k) (ch k) cκ (nn π) cc u‖ ≤ 14 * KK k + 9 := by
  have hq := Cv_le_quad π p hp u
  have hK := KK_ge k
  have hz' := (abs_lt.mp hz).2
  have hu2 : ‖u‖ ^ 2 < 3 * KK k + 5 / 4 := by
    unfold zv Rv cκ cC cw at hz'
    linarith
  have hu : ‖u‖ ≤ 3 * KK k + 9 / 4 := by nlinarith [norm_nonneg u, sq_nonneg (‖u‖ - 1)]
  have hg := Cg_norm_le π p hp u
  unfold dv cκ
  calc ‖(4 : ℝ) • u - Cg p (ca k) (ch k) (nn π) cc u‖ ≤
      ‖(4 : ℝ) • u‖ + ‖Cg p (ca k) (ch k) (nn π) cc u‖ := norm_sub_le _ _
    _ ≤ 4 * (3 * KK k + 9 / 4) + 2 * KK k := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        linarith
    _ = 14 * KK k + 9 := by ring

noncomputable def cx (k : ℕ) (j : Fin (k + 1)) : ℝ := 1 - ((j : ℝ) + 1) / (4 * KK k)

noncomputable def xb : E d := ∑ j, cx k j • ev (π j)

lemma inner_ev_ev (i i' : Fin d) : ⟪ev i, ev i'⟫ = if i = i' then 1 else 0 := by
  simp [ev, EuclideanSpace.inner_single_left]

lemma xb_apply (j0 : Fin (k + 1)) : (xb π) (π j0) = cx k j0 := by
  rw [← inner_ev, xb, inner_sum]
  simp only [inner_smul_right, inner_ev_ev]
  have : ∀ j, (if π j0 = π j then (1 : ℝ) else 0) = if j0 = j then 1 else 0 := by
    intro j
    by_cases h : j0 = j
    · simp [h]
    · simp [h, π.injective.ne h]
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma cx_bounds (j : Fin (k + 1)) : 3 / 4 ≤ cx k j ∧ cx k j ≤ 1 := by
  have hK := KK_pos k
  have hj : ((j : ℝ) + 1) ≤ KK k := by
    unfold KK; have := j.isLt; exact_mod_cast (show j.val + 1 ≤ k + 1 by omega)
  unfold cx
  constructor
  · have : ((j : ℝ) + 1) / (4 * KK k) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  · have : 0 ≤ ((j : ℝ) + 1) / (4 * KK k) := by positivity
    linarith

lemma xb_norm_sq : ‖xb π‖ ^ 2 ≤ KK k := by
  rw [← real_inner_self_eq_norm_sq]
  nth_rw 1 [xb]
  rw [sum_inner]
  simp only [real_inner_smul_left, inner_ev, xb_apply]
  calc ∑ j, cx k j * cx k j ≤ ∑ _j : Fin (k + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        obtain ⟨h1, h2⟩ := cx_bounds j
        nlinarith
    _ = KK k := by simp [KK]

lemma lin_xb (j : Fin (k + 1)) : lin (nn π) cc j (xb π) = ca k - ch k := by
  rw [lin_full, inner_pv, ca_sub_ch]
  have hK := KK_pos k
  by_cases hj : 0 < j.val
  · rw [dite_eq_left hj, xb_apply, xb_apply]
    have : cc j = 0 := by unfold cc; rw [ite_eq_right (by omega)]
    rw [this]
    unfold cx
    have e : (((⟨j.val - 1, by omega⟩ : Fin (k + 1)) : ℕ) : ℝ) + 1 = (j : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast; ring
    rw [e]
    field_simp
    ring
  · rw [dite_eq_right hj, xb_apply]
    have hj0 : j.val = 0 := by omega
    have : cc j = 1 := by unfold cc; rw [ite_eq_left hj0]
    rw [this]
    unfold cx
    have e : (j : ℝ) = 0 := by exact_mod_cast hj0
    rw [e]
    field_simp
    ring

lemma Cv_xb (hp : 1 ≤ p) : Cv p (ca k) (ch k) (nn π) cc (xb π) = 0 := by
  unfold Cv
  apply Finset.sum_eq_zero
  intro j _
  rw [lin_xb]
  exact sp0_of_le p _ hp (ch_pos k) le_rfl

lemma ff_xb (hp : 1 ≤ p) : ff π p (xb π) = cl k / 2 * ‖xb π‖ ^ 2 := by
  have hw : (0 : ℝ) < cw := by unfold cw; norm_num
  have hz : zv p (ca k) (ch k) cκ (cC k) (nn π) cc (xb π) ≤ 0 - cw := by
    unfold zv Rv
    rw [Cv_xb π p hp]
    have := xb_norm_sq π
    unfold cκ cC cw
    linarith
  unfold ff fv
  rw [Cv_xb π p hp, sp0_of_le p 0 hp hw hz]
  ring

lemma ff_xb_le (hp : 1 ≤ p) : ff π p (xb π) ≤ 1 / 16 := by
  rw [ff_xb π p hp]
  have h1 := xb_norm_sq π (k := k)
  have hK := KK_pos k
  unfold cl
  calc 1 / (8 * KK k) / 2 * ‖xb π‖ ^ 2 ≤ 1 / (8 * KK k) / 2 * KK k :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / 16 := by field_simp; ring

lemma Cv_ge (hp : 1 ≤ p) (u : E d) :
    1 / 2 - u (π (Fin.last k)) ≤ Cv p (ca k) (ch k) (nn π) cc u := by
  have h1 : ∑ j, (lin (nn π) cc j u - ca k - ch k) ≤ Cv p (ca k) (ch k) (nn π) cc u :=
    Finset.sum_le_sum fun j _ => sp0_ge p _ hp (ch_pos k) _
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, lin_telescope] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have e := ca_add_ch k
  unfold KK at e
  push_cast at e h1
  linarith

lemma cB_sq : cB k ^ 2 = 4 * KK k + 4 := by
  unfold cB
  rw [mul_pow, Real.sq_sqrt (by have := KK_pos k; positivity)]
  ring

lemma grad_lower (hp : 1 ≤ p) (u : E d)
    (hu : ‖u‖ ≤ cB k → |u (π (Fin.last k))| ≤ cθ k) :
    1 / (8 * Real.sqrt (KK k + 1)) ≤ ‖FF π p u‖ := by
  have hK := KK_ge k
  have hs1 : 1 ≤ Real.sqrt (KK k + 1) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hsK : Real.sqrt (KK k) ≤ Real.sqrt (KK k + 1) := Real.sqrt_le_sqrt (by linarith)
  have hB : cB k = 2 * Real.sqrt (KK k + 1) := rfl
  by_cases hfar : cB k < ‖u‖
  · have hu2 : 4 * KK k + 4 ≤ ‖u‖ ^ 2 := by
      rw [← cB_sq]
      have : 0 ≤ cB k := by rw [hB]; positivity
      nlinarith
    obtain ⟨hz, _⟩ := zv_far π p hp u hu2 0
    obtain ⟨hF, _⟩ := answers_far p hp u hz
    unfold FF
    rw [hF, norm_smul, Real.norm_eq_abs, abs_of_pos (by unfold cl cκ; have := KK_pos k; positivity)]
    have h8 : 1 / (8 * Real.sqrt (KK k + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hcl : 0 ≤ cl k := by unfold cl; have := KK_pos k; positivity
    have : 1 ≤ (cl k + cκ) * ‖u‖ := by
      unfold cκ
      have : 2 ≤ ‖u‖ := by rw [hB] at hfar; linarith
      nlinarith
    linarith
  · push Not at hfar
    have hs := hu hfar
    have hθ := cθ_le k
    have hCv := Cv_ge π p hp u
    have hcoord := (abs_le.mp hs).2
    have hff : 7 / 16 ≤ ff π p u := by
      have h1 := Cv_nonneg p (ca k) (nn π) cc hp (ch_pos k) u
      have hw : (0 : ℝ) < cw := by unfold cw; norm_num
      have h2 := sp0_nonneg p 0 hp hw (zv p (ca k) (ch k) cκ (cC k) (nn π) cc u)
      have h3 : 0 ≤ cl k / 2 * ‖u‖ ^ 2 := by unfold cl; have := KK_pos k; positivity
      unfold ff fv
      linarith
    have hw : (0 : ℝ) < cw := by unfold cw; norm_num
    have hlam : 0 < cl k := by unfold cl; have := KK_pos k; positivity
    obtain ⟨xs, hxs⟩ := exists_minimizer p p (ca k) (cl k) cκ (cC k) (nn π) cc hp hp (ch_pos k) hw hlam
    have hxs1 : ff π p xs ≤ 1 / 16 := (hxs (xb π)).trans (ff_xb_le π p hp)
    have hxs2 : ‖xs‖ ≤ Real.sqrt (KK k) := by
      have h1 := fv_ge p p (ca k) (cl k) cκ (cC k) (nn π) cc hp hp (ch_pos k) hw xs
      have h2 := (hxs (xb π)).trans (le_of_eq (ff_xb π p hp))
      have h3 := xb_norm_sq π (k := k)
      have : ‖xs‖ ^ 2 ≤ KK k := by
        have : cl k / 2 * ‖xs‖ ^ 2 ≤ cl k / 2 * KK k := by
          calc cl k / 2 * ‖xs‖ ^ 2 ≤ cl k / 2 * ‖xb π‖ ^ 2 := h1.trans h2
            _ ≤ cl k / 2 * KK k := mul_le_mul_of_nonneg_left h3 (by positivity)
        exact le_of_mul_le_mul_left this (by positivity)
      exact Real.le_sqrt_of_sq_le this
    have htan := fv_tangent p p (ca k) (cl k) cκ (cC k) (nn π) cc hp (ch_pos k) hw
      (by unfold cκ; norm_num) hlam.le u xs
    have hin : 3 / 8 ≤ ⟪FF π p u, u - xs⟫ := by
      have e : ⟪FF π p u, u - xs⟫ = -⟪FF π p u, xs - u⟫ := by
        rw [← inner_neg_right, neg_sub]
      rw [e]
      unfold ff at hff hxs1
      unfold FF
      linarith
    have hcs := real_inner_le_norm (FF π p u) (u - xs)
    have hdist : ‖u - xs‖ ≤ 3 * Real.sqrt (KK k + 1) := by
      calc ‖u - xs‖ ≤ ‖u‖ + ‖xs‖ := norm_sub_le _ _
        _ ≤ 2 * Real.sqrt (KK k + 1) + Real.sqrt (KK k + 1) := by
            rw [hB] at hfar; linarith
        _ = _ := by ring
    have hpos : 0 < Real.sqrt (KK k + 1) := by linarith
    rw [div_le_iff₀ (by positivity)]
    have h1 : 3 / 8 ≤ ‖FF π p u‖ * (3 * Real.sqrt (KK k + 1)) :=
      hin.trans (hcs.trans (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)))
    nlinarith

lemma rank1_norm_le (a : E d) : ‖rank1 a‖ ≤ ‖a‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _) fun v => ?_
  rw [rank1_apply, norm_smul, Real.norm_eq_abs]
  calc |⟪a, v⟫| * ‖a‖ ≤ (‖a‖ * ‖v‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right (abs_real_inner_le_norm a v) (norm_nonneg a)
    _ = ‖a‖ ^ 2 * ‖v‖ := by ring

lemma CH_norm_le (hp : 1 ≤ p) (u : E d) :
    ‖CH p (ca k) (ch k) (nn π) cc u‖ ≤ 32 * KK k ^ 2 * ((p : ℝ) + 1) := by
  have hh := ch_pos k
  unfold CH
  calc ‖∑ j, sp2 p (ca k) (ch k) (lin (nn π) cc j u) • rank1 (nn π j)‖ ≤
      ∑ j, ‖sp2 p (ca k) (ch k) (lin (nn π) cc j u) • rank1 (nn π j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (k + 1), ((p : ℝ) + 1) / ch k * 4 := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sp2_nonneg p _ hh _)]
        have h1 := sp2_le p (ca k) hh (lin (nn π) cc j u)
        have h2 : ‖rank1 (nn π j)‖ ≤ 4 := by
          have := rank1_norm_le (nn π j)
          have h3 := norm_nn_le π j
          nlinarith [norm_nonneg (nn π j)]
        exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 32 * KK k ^ 2 * ((p : ℝ) + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        unfold ch KK
        push_cast
        field_simp
        ring

lemma DFF_norm_le (hp : 1 ≤ p) (u : E d) :
    ‖DFF π p u‖ ≤ 5 + 64 * KK k ^ 2 * ((p : ℝ) + 1) +
      8 * ((p : ℝ) + 1) * (14 * KK k + 9) ^ 2 := by
  have hw : (0 : ℝ) < cw := by unfold cw; norm_num
  have hH := CH_norm_le π p hp u
  set z := zv p (ca k) (ch k) cκ (cC k) (nn π) cc u
  have hP0 := sp1_nonneg p 0 hp z (h := cw)
  have hP1 := sp1_le_one p 0 hp z (h := cw)
  have hE0 := sp2_nonneg p 0 hw z
  have hE1 : sp2 p 0 cw z ≤ 8 * ((p : ℝ) + 1) :=
    calc sp2 p 0 cw z ≤ ((p : ℝ) + 1) / cw := sp2_le p 0 hw z
      _ = 8 * ((p : ℝ) + 1) := by unfold cw; ring
  have hlam : cl k ≤ 1 := by
    unfold cl; have := KK_ge k
    rw [div_le_one (by positivity)]; linarith
  have hlam0 : 0 ≤ cl k := by unfold cl; have := KK_pos k; positivity
  have hid : ‖ContinuousLinearMap.id ℝ (E d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hrank : sp2 p 0 cw z * ‖rank1 (dv p (ca k) (ch k) cκ (nn π) cc u)‖ ≤
      8 * ((p : ℝ) + 1) * (14 * KK k + 9) ^ 2 := by
    by_cases hz : sp2 p 0 cw z = 0
    · rw [hz, zero_mul]; positivity
    · have hzb : |z| < cw := by
        by_contra hc
        push Not at hc
        exact hz (sp2_eq_zero p 0 hp hw (by rw [sub_zero]; exact hc))
      have hd := band π p hp u hzb
      have h1 := rank1_norm_le (dv p (ca k) (ch k) cκ (nn π) cc u)
      have h2 : ‖dv p (ca k) (ch k) cκ (nn π) cc u‖ ^ 2 ≤ (14 * KK k + 9) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd 2
      exact mul_le_mul hE1 (h1.trans h2) (norm_nonneg _) (by positivity)
  unfold DFF DFv
  calc ‖cl k • ContinuousLinearMap.id ℝ (E d) + CH p (ca k) (ch k) (nn π) cc u +
        sp1 p 0 cw z • (cκ • ContinuousLinearMap.id ℝ (E d) - CH p (ca k) (ch k) (nn π) cc u) +
        sp2 p 0 cw z • rank1 (dv p (ca k) (ch k) cκ (nn π) cc u)‖ ≤
      ‖cl k • ContinuousLinearMap.id ℝ (E d)‖ + ‖CH p (ca k) (ch k) (nn π) cc u‖ +
        ‖sp1 p 0 cw z • (cκ • ContinuousLinearMap.id ℝ (E d) - CH p (ca k) (ch k) (nn π) cc u)‖ +
        ‖sp2 p 0 cw z • rank1 (dv p (ca k) (ch k) cκ (nn π) cc u)‖ := by
          exact norm_add₄_le
    _ ≤ 1 + 32 * KK k ^ 2 * ((p : ℝ) + 1) + (4 + 32 * KK k ^ 2 * ((p : ℝ) + 1)) +
        8 * ((p : ℝ) + 1) * (14 * KK k + 9) ^ 2 := by
          gcongr
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0]
            calc cl k * ‖ContinuousLinearMap.id ℝ (E d)‖ ≤ 1 * 1 :=
                  mul_le_mul hlam hid (norm_nonneg _) zero_le_one
              _ = 1 := by ring
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hP0]
            have h1 : ‖cκ • ContinuousLinearMap.id ℝ (E d) - CH p (ca k) (ch k) (nn π) cc u‖ ≤
                4 + 32 * KK k ^ 2 * ((p : ℝ) + 1) := by
              calc _ ≤ ‖cκ • ContinuousLinearMap.id ℝ (E d)‖ +
                    ‖CH p (ca k) (ch k) (nn π) cc u‖ := norm_sub_le _ _
                _ ≤ 4 + 32 * KK k ^ 2 * ((p : ℝ) + 1) := by
                    gcongr
                    rw [norm_smul, Real.norm_eq_abs]
                    unfold cκ
                    rw [abs_of_pos (by norm_num)]
                    linarith
            calc sp1 p 0 cw z * ‖cκ • ContinuousLinearMap.id ℝ (E d) -
                  CH p (ca k) (ch k) (nn π) cc u‖ ≤ 1 * (4 + 32 * KK k ^ 2 * ((p : ℝ) + 1)) :=
                  mul_le_mul hP1 h1 (norm_nonneg _) zero_le_one
              _ = _ := by ring
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hE0]
            exact hrank
    _ = 5 + 64 * KK k ^ 2 * ((p : ℝ) + 1) + 8 * ((p : ℝ) + 1) * (14 * KK k + 9) ^ 2 := by ring

noncomputable def cS (k p : ℕ) : ℝ := Real.sqrt (32 * KK k * ((p : ℝ) + 1))

noncomputable def cM (k p : ℕ) : ℝ :=
  2 * (4 * (p : ℝ) / ch k) + (14 * KK k + 9) * (4 * ((p : ℝ) + 1) / cw) +
    cS k p * (4 * ((p : ℝ) + 1) / cw) + cκ * (4 * ((p : ℝ) + 1) / cw) + 1 + cS k p

lemma cS_sq : cS k p ^ 2 = 32 * KK k * ((p : ℝ) + 1) := by
  unfold cS; rw [Real.sq_sqrt (by have := KK_pos k; positivity)]

lemma cS_pos : 0 < cS k p := by
  unfold cS; apply Real.sqrt_pos.mpr; have := KK_pos k; positivity

lemma cS_le : cS k p ≤ 32 * KK k * ((p : ℝ) + 1) := by
  have h := cS_sq (k := k) p
  have h1 : 1 ≤ 32 * KK k * ((p : ℝ) + 1) := by
    have := KK_ge k; have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; nlinarith
  have h0 := cS_pos (k := k) p
  nlinarith

set_option maxHeartbeats 800000 in
lemma leftover (hp : 1 ≤ p)
    (hq : 2 ^ 22 * ((p : ℝ) + 1) ^ 3 * KK k ^ 3 * (1 / 2) ^ p ≤ 8) :
    2 * (4 * (p : ℝ) * ((p : ℝ) + 1) * (1 / 2) ^ p / ch k ^ 2) * 4 +
        (14 * KK k + 9) * cκ * (((p : ℝ) + 1) * (1 / 2) ^ p / cw) +
        (14 * KK k + 9) * (((p : ℝ) + 1) * (1 / 2) ^ p / cw) * (((p : ℝ) + 1) / ch k * 4) +
        (14 * KK k + 9) ^ 3 * (4 * (p : ℝ) * ((p : ℝ) + 1) * (1 / 2) ^ p / cw ^ 2) +
        cκ ^ 2 * (((p : ℝ) + 1) * (1 / 2) ^ p / cw) +
        cS k p * (((p : ℝ) + 1) * (1 / 2) ^ p / cw) * (((p : ℝ) + 1) / ch k * 4) ≤
      cM k p * cl k := by
  have hK := KK_ge k
  set K := KK k with hKd
  set q : ℝ := (1 / 2) ^ p with hqd
  have hq0 : 0 ≤ q := by positivity
  have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set P := (p : ℝ) + 1 with hPd
  have hP1 : 1 ≤ P := by linarith
  have hpP : (p : ℝ) ≤ P := by linarith
  have hS := cS_le (k := k) p
  have hS0 := cS_pos (k := k) p
  rw [← hKd, ← hPd] at hS
  have hΔ : 14 * K + 9 ≤ 23 * K := by linarith
  have hch : ch k = 1 / (8 * K) := rfl
  have hcl : cl k = 1 / (8 * K) := rfl
  have hcw : cw = 1 / 8 := rfl
  have hcκ : cκ = 4 := rfl
  have hKpos : 0 < K := by linarith
  have e1 : 2 * (4 * (p : ℝ) * P * q / ch k ^ 2) * 4 = 2048 * (p : ℝ) * P * K ^ 2 * q := by
    rw [hch]; field_simp; ring
  have e2 : (14 * K + 9) * cκ * (P * q / cw) = 32 * (14 * K + 9) * P * q := by
    rw [hcκ, hcw]; field_simp; ring
  have e3 : (14 * K + 9) * (P * q / cw) * (P / ch k * 4) = 256 * (14 * K + 9) * K * P ^ 2 * q := by
    rw [hcw, hch]; field_simp; ring
  have e4 : (14 * K + 9) ^ 3 * (4 * (p : ℝ) * P * q / cw ^ 2) =
      256 * (14 * K + 9) ^ 3 * (p : ℝ) * P * q := by
    rw [hcw]; field_simp; ring
  have e5 : cκ ^ 2 * (P * q / cw) = 128 * P * q := by rw [hcκ, hcw]; field_simp; ring
  have e6 : cS k p * (P * q / cw) * (P / ch k * 4) = 256 * cS k p * K * P ^ 2 * q := by
    rw [hcw, hch]; field_simp; ring
  rw [e1, e2, e3, e4, e5, e6]
  have hX : 0 ≤ P ^ 3 * K ^ 3 * q := by positivity
  have hP0 : (0 : ℝ) ≤ P := by linarith
  have hK2 : K ^ 2 ≤ K ^ 3 := by nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
  have hP2 : P ^ 2 ≤ P ^ 3 := by nlinarith [mul_nonneg (sq_nonneg P) (sub_nonneg.mpr hP1)]
  have hP3 : P ≤ P ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hP1) hP0) (by linarith : (0 : ℝ) ≤ P + 1)]
  have hK3 : K ≤ K ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hK) hKpos.le)
      (by linarith : (0 : ℝ) ≤ K + 1)]
  have hK31 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have b1 : 2048 * (p : ℝ) * P * K ^ 2 * q ≤ 2048 * (P ^ 3 * K ^ 3 * q) := by
    have : (p : ℝ) * P * K ^ 2 ≤ P ^ 3 * K ^ 3 := by
      calc (p : ℝ) * P * K ^ 2 ≤ P * P * K ^ 3 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hpP (by linarith)) hK2 (by positivity)
              (by positivity)
        _ = P ^ 2 * K ^ 3 := by ring
        _ ≤ P ^ 3 * K ^ 3 := mul_le_mul_of_nonneg_right hP2 (by positivity)
    linarith [mul_le_mul_of_nonneg_right this hq0]
  have b2 : 32 * (14 * K + 9) * P * q ≤ 736 * (P ^ 3 * K ^ 3 * q) := by
    have h1 : (14 * K + 9) * P ≤ 23 * (P ^ 3 * K ^ 3) := by
      have e1 : (14 * K + 9) * P ≤ 23 * (K * P) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hK) hP0]
      have e2 : K * P ≤ K ^ 3 * P ^ 3 := mul_le_mul hK3 hP3 hP0 (by positivity)
      linarith
    linarith [mul_le_mul_of_nonneg_right h1 hq0]
  have b3 : 256 * (14 * K + 9) * K * P ^ 2 * q ≤ 5888 * (P ^ 3 * K ^ 3 * q) := by
    have h1 : (14 * K + 9) * K * P ^ 2 ≤ 23 * (P ^ 3 * K ^ 3) := by
      have : (14 * K + 9) * K ≤ 23 * K ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hK) hKpos.le]
      calc (14 * K + 9) * K * P ^ 2 ≤ 23 * K ^ 2 * P ^ 2 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ ≤ 23 * K ^ 3 * P ^ 3 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hK2 (by norm_num)) hP2 (by positivity)
              (by positivity)
        _ = 23 * (P ^ 3 * K ^ 3) := by ring
    linarith [mul_le_mul_of_nonneg_right h1 hq0]
  have b4 : 256 * (14 * K + 9) ^ 3 * (p : ℝ) * P * q ≤ 3114752 * (P ^ 3 * K ^ 3 * q) := by
    have h1 : (14 * K + 9) ^ 3 ≤ 12167 * K ^ 3 :=
      calc (14 * K + 9) ^ 3 ≤ (23 * K) ^ 3 := pow_le_pow_left₀ (by positivity) hΔ 3
        _ = 12167 * K ^ 3 := by ring
    have h2 : (p : ℝ) * P ≤ P ^ 3 := by
      have : (p : ℝ) * P ≤ P * P := mul_le_mul_of_nonneg_right hpP hP0
      nlinarith
    have h3 : (14 * K + 9) ^ 3 * ((p : ℝ) * P) ≤ 12167 * K ^ 3 * P ^ 3 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith [mul_le_mul_of_nonneg_right h3 hq0]
  have b5 : 128 * P * q ≤ 128 * (P ^ 3 * K ^ 3 * q) := by
    have : P ≤ P ^ 3 * K ^ 3 := hP3.trans (le_mul_of_one_le_right (by positivity) hK31)
    linarith [mul_le_mul_of_nonneg_right this hq0]
  have b6 : 256 * cS k p * K * P ^ 2 * q ≤ 8192 * (P ^ 3 * K ^ 3 * q) := by
    have h1 : cS k p * K * P ^ 2 ≤ 32 * K * P * K * P ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS (by linarith)) (by positivity)
    have h2 : 32 * K * P * K * P ^ 2 ≤ 32 * (P ^ 3 * K ^ 3) := by
      have := mul_le_mul_of_nonneg_right hK2 (show 0 ≤ P ^ 3 by positivity)
      linarith
    linarith [mul_le_mul_of_nonneg_right (h1.trans h2) hq0]
  have hsum : 2048 * (P ^ 3 * K ^ 3 * q) + 736 * (P ^ 3 * K ^ 3 * q) +
      5888 * (P ^ 3 * K ^ 3 * q) + 3114752 * (P ^ 3 * K ^ 3 * q) + 128 * (P ^ 3 * K ^ 3 * q) +
      8192 * (P ^ 3 * K ^ 3 * q) ≤ 8 := by
    have : 2 ^ 22 * P ^ 3 * K ^ 3 * q ≤ 8 := hq
    linarith
  have hR : 8 * (p : ℝ) ≤ cM k p * cl k := by
    have hrest : 0 ≤ ((14 * K + 9) * (4 * P / cw) + cS k p * (4 * P / cw) + cκ * (4 * P / cw) +
        1 + cS k p) * cl k := by
      rw [hcw, hcκ, hcl]; positivity
    have e : cM k p * cl k = 2 * (4 * (p : ℝ) / ch k) * cl k +
        ((14 * K + 9) * (4 * P / cw) + cS k p * (4 * P / cw) + cκ * (4 * P / cw) + 1 +
          cS k p) * cl k := by
      unfold cM; rw [← hKd, ← hPd]; ring
    have e2 : 2 * (4 * (p : ℝ) / ch k) * cl k = 8 * (p : ℝ) := by
      rw [hch, hcl]; field_simp; ring
    linarith
  linarith

lemma minimizer_norm (hp : 1 ≤ p) (xs : E d) (hxs : ∀ y, ff π p xs ≤ ff π p y) :
    ‖xs‖ ≤ Real.sqrt (KK k) := by
  have hw : (0 : ℝ) < cw := by unfold cw; norm_num
  have hlam : 0 < cl k := by unfold cl; have := KK_pos k; positivity
  have h1 := fv_ge p p (ca k) (cl k) cκ (cC k) (nn π) cc hp hp (ch_pos k) hw xs
  have h2 := (hxs (xb π)).trans (le_of_eq (ff_xb π p hp))
  have h3 := xb_norm_sq π (k := k)
  have : ‖xs‖ ^ 2 ≤ KK k := by
    have : cl k / 2 * ‖xs‖ ^ 2 ≤ cl k / 2 * KK k := by
      calc cl k / 2 * ‖xs‖ ^ 2 ≤ cl k / 2 * ‖xb π‖ ^ 2 := h1.trans h2
        _ ≤ cl k / 2 * KK k := mul_le_mul_of_nonneg_left h3 (by positivity)
    exact le_of_mul_le_mul_left this (by positivity)
  exact Real.le_sqrt_of_sq_le this

lemma DFF_quad_nonneg (hp : 1 ≤ p) (u v : E d) : 0 ≤ ⟪DFF π p u v, v⟫ := by
  have hw : (0 : ℝ) < cw := by unfold cw; norm_num
  have hP0 := sp1_nonneg p 0 hp (zv p (ca k) (ch k) cκ (cC k) (nn π) cc u) (h := cw)
  have hP1 := sp1_le_one p 0 hp (zv p (ca k) (ch k) cκ (cC k) (nn π) cc u) (h := cw)
  have hE := sp2_nonneg p 0 hw (zv p (ca k) (ch k) cκ (cC k) (nn π) cc u)
  have hQ : 0 ≤ ⟪CH p (ca k) (ch k) (nn π) cc u v, v⟫ := by
    rw [CH_inner]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (sp2_nonneg p _ (ch_pos k) _)
      (mul_self_nonneg _)
  have hlam : 0 ≤ cl k := by unfold cl; have := KK_pos k; positivity
  unfold DFF
  rw [DFv_inner, real_inner_self_eq_norm_sq]
  have hQ1 : ⟪CH p (ca k) (ch k) (nn π) cc u v, v⟫ +
      sp1 p 0 cw (zv p (ca k) (ch k) cκ (cC k) (nn π) cc u) *
        (cκ * ‖v‖ ^ 2 - ⟪CH p (ca k) (ch k) (nn π) cc u v, v⟫) ≥ 0 := by
    have : 0 ≤ (1 - sp1 p 0 cw (zv p (ca k) (ch k) cκ (cC k) (nn π) cc u)) *
        ⟪CH p (ca k) (ch k) (nn π) cc u v, v⟫ := mul_nonneg (by linarith) hQ
    have : 0 ≤ sp1 p 0 cw (zv p (ca k) (ch k) cκ (cC k) (nn π) cc u) * (cκ * ‖v‖ ^ 2) := by
      unfold cκ; positivity
    linarith
  have : 0 ≤ sp2 p 0 cw (zv p (ca k) (ch k) cκ (cC k) (nn π) cc u) *
      (⟪dv p (ca k) (ch k) cκ (nn π) cc u, v⟫ * ⟪dv p (ca k) (ch k) cκ (nn π) cc u, v⟫) :=
    mul_nonneg hE (mul_self_nonneg _)
  have : 0 ≤ cl k * ‖v‖ ^ 2 := by positivity
  linarith

theorem FF_stable (hp : 2 ≤ p) (hq : 2 ^ 22 * ((p : ℝ) + 1) ^ 3 * KK k ^ 3 * (1 / 2) ^ p ≤ 8)
    (x y v : E d) :
    ⟪DFF π p y v, v⟫ ≤ Real.exp (cM k p * ‖y - x‖) * ⟪DFF π p x v, v⟫ := by
  have hw : (0 : ℝ) < cw := by unfold cw; norm_num
  have hlam : 0 ≤ cl k := by unfold cl; have := KK_pos k; positivity
  have hK := KK_pos k
  have hSHc : ((p : ℝ) + 1) / ch k * 4 ≤ cS k p ^ 2 := by
    rw [cS_sq]
    unfold ch
    apply le_of_eq
    field_simp
    ring
  exact DFv_stable p p (ca k) (cl k) cκ (cC k) (nn π) cc hp hp (ch_pos k) hw 4 (cS k p)
    (14 * KK k + 9) (norm_nn_le π) (sum_nn_sq π) (by norm_num)
    (band π p (by omega)) (by unfold cκ; norm_num) hlam (cS_pos p) (by positivity) hSHc
    (leftover p (by omega) hq) x y v

end LongTails.Proofs.HsBounds
