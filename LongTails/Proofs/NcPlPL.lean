import LongTails.Proofs.NcPlLipschitz

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlPL

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlCalc
open LongTails.Proofs.NcPlBlock LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChain
open LongTails.Proofs.NcPlChainPL LongTails.Proofs.NcPlFlat LongTails.Proofs.NcPlCut
open LongTails.Proofs.NcPlInstance LongTails.Proofs.NcPlLipschitz
open LongTails.Proofs.AbcChain (Chain)
open LongTails.Proofs.AbcHardFunction (Space sel sel_apply sel_norm adjoint_norm adjoint_apply
  adjoint_apply_emb)

section Flat

variable {m n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

theorem flat_pl (S : Scales n r ρ) (a b b' : ℕ → ℝ) :
    (rF m n r a b' + ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        hb (lamOf n) ρ (wOf n b' i j)) -
      (rF m n r a b + ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        hb (lamOf n) ρ (wOf n b i j)) ≤
      147 / lamOf n * ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (gW n r (uOf n a) (wOf n b) i j + dhb (lamOf n) ρ (wOf n b i j)) ^ 2 := by
  unfold rF rhat
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact block_pl_chain S (prevRead (uOf n a) i) (uOf n a i) (wOf n b i) (wOf n b' i)

theorem flat_farfield (S : Scales n r ρ) (a b : ℕ → ℝ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gB n r a b p * b p ≤ 40 * ((m : ℝ) + 1) := by
  rw [sum_gB_mul]
  have hterm : ∀ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      gW n r (uOf n a) (wOf n b) i j * b (i * (n + 2) + j) ≤ 40 := fun i _ =>
    farfield S (sig n (prevRead (uOf n a) i)) (uOf n a i) (wOf n b i)
  have h := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  push_cast at h
  linarith

lemma theta_le_zero {c : ℝ} (hc1 : c ≤ 1) (a b : ℕ → ℝ) :
    theta m n r a b c ≤ 0 := by
  unfold theta
  have h1 := rF_nonneg (m := m) (n := n) (r := r) a b
  have h2 := rF_le_cF (m := m) (n := n) (r := r) a b
  nlinarith

lemma theta_ge {c : ℝ} (hc0 : 0 ≤ c) (a b : ℕ → ℝ) :
    -(6 * ((m : ℝ) + 1)) ≤ theta m n r a b c := by
  unfold theta
  have h1 := rF_nonneg (m := m) (n := n) (r := r) a b
  have h2 := cF_le (m := m) (n := n) a
  nlinarith

end Flat

variable (G : Geo) {d : ℕ} (π : Fin (G.k + 1) ↪ Fin d)

noncomputable def dualSet : Finset (Fin d) :=
  (Finset.univ.filter (fun p : Fin (G.k + 1) => p.val % (G.n + 2) ≠ G.n + 1)).map π

lemma sum_fin_split (F : Fin d → ℝ) (Fn : ℕ → ℝ) (hF : ∀ p : Fin (G.k + 1), Fn p = F (π p)) :
    ∑ j, F j = ∑ i ∈ Finset.range (G.m + 1), ∑ j ∈ Finset.range (G.n + 1),
      Fn (i * (G.n + 2) + j) + ∑ j ∈ (dualSet G π)ᶜ, F j := by
  rw [← Finset.sum_add_sum_compl (dualSet G π) F]
  congr 1
  unfold dualSet
  rw [Finset.sum_map, Finset.sum_filter, ← sum_wpos G.n Fn G.m, ← G.hk, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.val % (G.n + 2) = G.n + 1
  · rw [ite_eq_right (not_not.mpr hp), ite_eq_left hp]
  · rw [ite_eq_left hp, ite_eq_right hp, hF]

lemma adjoint_off (v : Chain G.k) (j : Fin d) (hv : ∀ p, π p = j → v p = 0) :
    (sel π).adjoint v j = 0 := by
  rw [adjoint_apply]
  apply Finset.sum_eq_zero
  intro p _
  by_cases h : π p = j
  · rw [ite_eq_left h, hv p h]
  · rw [ite_eq_right h]

lemma vB_xtype (x y : Space d) (p : Fin (G.k + 1)) (hp : p.val % (G.n + 2) = G.n + 1) :
    vB G π x y p = 0 := by
  change gB G.n G.r (seq (chA G π x)) (seq (sel π y)) p = 0
  unfold gB
  rw [ite_eq_left hp]

lemma hardGy_inside (x y : Space d) (hy : ‖y‖ ≤ G.By) :
    hardGy G π x y = baseGrad (lamOf G.n) G.ρ y + (sel π).adjoint (vB G π x y) := by
  unfold hardGy
  rw [cutv_of_le G.hBy hy, cutGrad_of_le G.hBy hy, one_smul, smul_zero, add_zero]

lemma hardGy_dual (x y : Space d) (hy : ‖y‖ ≤ G.By) (p : Fin (G.k + 1)) :
    hardGy G π x y (π p) = gB G.n G.r (seq (chA G π x)) (seq (sel π y)) p +
      dhb (lamOf G.n) G.ρ (seq (sel π y) p) := by
  rw [hardGy_inside G π x y hy, seq_fin, sel_apply]
  change dhb (lamOf G.n) G.ρ (y (π p)) + (sel π).adjoint (vB G π x y) (π p) = _
  rw [adjoint_apply_emb]
  change dhb (lamOf G.n) G.ρ (y (π p)) +
    gB G.n G.r (seq (chA G π x)) (seq (sel π y)) p = _
  ring

lemma hardGy_off (x y : Space d) (hy : ‖y‖ ≤ G.By) (j : Fin d) (hj : j ∈ (dualSet G π)ᶜ) :
    hardGy G π x y j = dhb (lamOf G.n) G.ρ (y j) := by
  rw [hardGy_inside G π x y hy]
  change dhb (lamOf G.n) G.ρ (y j) + (sel π).adjoint (vB G π x y) j = _
  rw [adjoint_off G π _ j, add_zero]
  intro p hp
  apply vB_xtype
  by_contra hne
  apply Finset.mem_compl.mp hj
  unfold dualSet
  rw [Finset.mem_map]
  exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hne⟩, hp⟩

lemma hardF_le (x y : Space d) :
    hardF G π x y ≤ ‖x‖ ^ 2 / 32 + base (lamOf G.n) G.ρ y := by
  unfold hardF
  have := theta_le_zero (m := G.m) (n := G.n) (r := G.r)
    (cutv_le_one G.By y) (seq (chA G π x)) (seq (sel π y))
  linarith

lemma hardF_ge (x y : Space d) :
    ‖x‖ ^ 2 / 32 + base (lamOf G.n) G.ρ y - 6 * ((G.m : ℝ) + 1) ≤ hardF G π x y := by
  unfold hardF
  have := theta_ge (m := G.m) (n := G.n) (r := G.r) (cutv_nonneg G.By y)
    (seq (chA G π x)) (seq (sel π y))
  linarith

lemma gap_le (x y y' : Space d) :
    hardF G π x y' - hardF G π x y ≤
      (base (lamOf G.n) G.ρ y' + rF G.m G.n G.r (seq (chA G π x)) (seq (sel π y'))) -
      (base (lamOf G.n) G.ρ y + cutv G.By y * rF G.m G.n G.r (seq (chA G π x)) (seq (sel π y))) := by
  unfold hardF theta
  have h1 := rF_nonneg (m := G.m) (n := G.n) (r := G.r) (seq (chA G π x)) (seq (sel π y'))
  have h2 := cutv_le_one G.By y'
  have h3 := cutv_nonneg G.By y'
  nlinarith

lemma lam_By : 256 * ((G.m : ℝ) + 1) ≤ lamOf G.n * G.By ^ 2 := by
  have h := G.hByM
  unfold lamOf
  have hn : (0 : ℝ) < 2048 * ((G.n : ℝ) + 1) := by positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hn]
  nlinarith

theorem pl_inside (x y y' : Space d) (hy : ‖y‖ ≤ G.By) :
    hardF G π x y' - hardF G π x y ≤ 147 / lamOf G.n * ‖hardGy G π x y‖ ^ 2 := by
  have hlam := lamOf_pos G.n
  refine (gap_le G π x y y').trans ?_
  rw [cutv_of_le G.hBy hy, one_mul]
  have hbase : ∀ z : Space d, base (lamOf G.n) G.ρ z =
      ∑ i ∈ Finset.range (G.m + 1), ∑ j ∈ Finset.range (G.n + 1),
        hb (lamOf G.n) G.ρ (wOf G.n (seq (sel π z)) i j) +
      ∑ j ∈ (dualSet G π)ᶜ, hb (lamOf G.n) G.ρ (z j) := fun z =>
    sum_fin_split G π (fun j => hb (lamOf G.n) G.ρ (z j))
      (fun p => hb (lamOf G.n) G.ρ (seq (sel π z) p))
      (fun p => by rw [seq_fin, sel_apply])
  have hg : ‖hardGy G π x y‖ ^ 2 =
      ∑ i ∈ Finset.range (G.m + 1), ∑ j ∈ Finset.range (G.n + 1),
        (gW G.n G.r (uOf G.n (seq (chA G π x))) (wOf G.n (seq (sel π y))) i j +
          dhb (lamOf G.n) G.ρ (wOf G.n (seq (sel π y)) i j)) ^ 2 +
      ∑ j ∈ (dualSet G π)ᶜ, dhb (lamOf G.n) G.ρ (y j) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      sum_fin_split G π (fun j => hardGy G π x y j ^ 2)
        (fun p => (gB G.n G.r (seq (chA G π x)) (seq (sel π y)) p +
          dhb (lamOf G.n) G.ρ (seq (sel π y) p)) ^ 2)
        (fun p => by rw [hardGy_dual G π x y hy p])]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < G.n + 1 := Finset.mem_range.mp hj
      unfold gB
      rw [pos_mod G.n i (by omega), ite_eq_right (by omega), pos_div G.n i (by omega)]
      rfl
    · apply Finset.sum_congr rfl
      intro j hj
      rw [hardGy_off G π x y hy j hj]
  have hflat := flat_pl (m := G.m) G.scales (seq (chA G π x)) (seq (sel π y)) (seq (sel π y'))
  have hrest : ∑ j ∈ (dualSet G π)ᶜ, hb (lamOf G.n) G.ρ (y' j) -
      ∑ j ∈ (dualSet G π)ᶜ, hb (lamOf G.n) G.ρ (y j) ≤
      147 / lamOf G.n * ∑ j ∈ (dualSet G π)ᶜ, dhb (lamOf G.n) G.ρ (y j) ^ 2 := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h1 := hb_pl hlam (lamOf_le_one G.n) G.scales.hρ (y j) (y' j)
    have hcoef : (5 : ℝ) / (2 * lamOf G.n) ≤ 147 / lamOf G.n := by
      rw [div_le_div_iff₀ (by positivity) hlam]
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  rw [hbase y, hbase y', hg, mul_add]
  linarith

lemma hardGy_inner (x y : Space d) :
    ⟪hardGy G π x y, y⟫ ≤ -(lamOf G.n * ‖y‖ ^ 2) - ∑ j, pos (-y j - G.ρ / 2) ^ 2 +
      40 * ((G.m : ℝ) + 1) := by
  have hm0 : (0 : ℝ) ≤ (G.m : ℝ) + 1 := by positivity
  unfold hardGy
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]
  have h1 := baseGrad_inner (lamOf G.n) G.scales.hρ.le y
  have h2 : ⟪vB G π x y, sel π y⟫ ≤ 40 * ((G.m : ℝ) + 1) := by
    have hf := flat_farfield (m := G.m) G.scales (seq (chA G π x)) (seq (sel π y))
    rw [← G.hk, Finset.sum_range] at hf
    unfold vB
    rw [inner_toLp]
    simp only [seq_fin] at hf
    exact hf
  have h3 : ⟪cutGrad G.By y, y⟫ ≤ 0 := by
    unfold cutGrad
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hd := dcut_nonpos (‖y‖ ^ 2 / G.By ^ 2)
    have hB := G.hBy
    have hq : (0 : ℝ) ≤ 2 / G.By ^ 2 * ‖y‖ ^ 2 := by positivity
    nlinarith
  have hc0 := cutv_nonneg G.By y
  have hc1 := cutv_le_one G.By y
  have hr0 := rVal_nonneg G π x y
  nlinarith

theorem pl_outside (x y y' : Space d) (hy : G.By < ‖y‖) :
    hardF G π x y' - hardF G π x y ≤ 147 / lamOf G.n * ‖hardGy G π x y‖ ^ 2 := by
  have hlam := lamOf_pos G.n
  have hBy := G.hBy
  have hlB := lam_By G
  have hm0 : (0 : ℝ) ≤ (G.m : ℝ) + 1 := by positivity
  have hN2 : G.By ^ 2 < ‖y‖ ^ 2 := pow_lt_pow_left₀ hy hBy.le two_ne_zero
  have hNpos : 0 < ‖y‖ ^ 2 := lt_trans (by positivity) hN2
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ j, pos (-y j - G.ρ / 2) ^ 2 := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbase : base (lamOf G.n) G.ρ y = -(lamOf G.n / 2 * ‖y‖ ^ 2) - P / 2 := by
    rw [base_eq, hP, Finset.sum_div]
  have hgap : hardF G π x y' - hardF G π x y ≤
      6 * ((G.m : ℝ) + 1) + lamOf G.n / 2 * ‖y‖ ^ 2 + P / 2 := by
    have h1 := hardF_le G π x y'
    have h2 := hardF_ge G π x y
    have h3 := base_le_zero hlam.le G.ρ y'
    have h4 := theta_le_zero (m := G.m) (n := G.n) (r := G.r)
      (cutv_le_one G.By y') (seq (chA G π x)) (seq (sel π y'))
    have h5 := theta_ge (m := G.m) (n := G.n) (r := G.r) (cutv_nonneg G.By y)
      (seq (chA G π x)) (seq (sel π y))
    unfold hardF at h1 h2 ⊢
    rw [hbase] at h2 ⊢
    linarith
  have hin : ⟪hardGy G π x y, y⟫ ≤ -(lamOf G.n * ‖y‖ ^ 2) - P + 40 * ((G.m : ℝ) + 1) := by
    rw [hP]
    exact hardGy_inner G π x y
  have hcs : ⟪hardGy G π x y, y⟫ ^ 2 ≤ ‖hardGy G π x y‖ ^ 2 * ‖y‖ ^ 2 := by
    have h := abs_real_inner_le_norm (hardGy G π x y) y
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow] at h2
    exact h2
  have hlN : 256 * ((G.m : ℝ) + 1) ≤ lamOf G.n * ‖y‖ ^ 2 :=
    hlB.trans (mul_le_mul_of_nonneg_left hN2.le hlam.le)
  obtain ⟨A, hA⟩ : ∃ A, A = 3 / 4 * (lamOf G.n * ‖y‖ ^ 2) + P := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    positivity
  have hAle : A ≤ -⟪hardGy G π x y, y⟫ := by
    rw [hA]
    linarith
  have hA2 : A ^ 2 ≤ ‖hardGy G π x y‖ ^ 2 * ‖y‖ ^ 2 := by
    have := pow_le_pow_left₀ hA0 hAle 2
    rw [neg_sq] at this
    exact this.trans hcs
  have hlow : (9 / 16 * lamOf G.n ^ 2 * ‖y‖ ^ 2 + 3 / 2 * lamOf G.n * P) * ‖y‖ ^ 2 ≤
      ‖hardGy G π x y‖ ^ 2 * ‖y‖ ^ 2 := by
    refine le_trans ?_ hA2
    rw [hA]
    nlinarith [sq_nonneg P]
  have hg2 := le_of_mul_le_mul_right hlow hNpos
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
  have hl1 := lamOf_le_one G.n
  nlinarith [mul_nonneg hlam.le hP0, mul_le_mul_of_nonneg_left hlN hlam.le]

theorem hardF_pl (x y y' : Space d) :
    hardF G π x y' - hardF G π x y ≤ 147 / lamOf G.n * ‖hardGy G π x y‖ ^ 2 := by
  rcases le_or_gt ‖y‖ G.By with h | h
  · exact pl_inside G π x y y' h
  · exact pl_outside G π x y y' h

lemma hardF_continuous_y (x : Space d) : Continuous fun y => hardF G π x y :=
  continuous_iff_continuousAt.mpr fun y => (hardF_hasGradientAt_y G π x y).continuousAt

theorem hardF_attain (x : Space d) : ∃ y, ∀ y', hardF G π x y' ≤ hardF G π x y := by
  have hlam := lamOf_pos G.n
  have hlB := lam_By G
  have hm0 : (0 : ℝ) ≤ (G.m : ℝ) + 1 := by positivity
  obtain ⟨y0, _, hmax⟩ := (isCompact_closedBall (0 : Space d) G.By).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self G.hBy.le⟩ (hardF_continuous_y G π x).continuousOn
  refine ⟨y0, fun y' => ?_⟩
  rcases le_or_gt ‖y'‖ G.By with h | h
  · exact hmax (by rw [Metric.mem_closedBall, dist_zero_right]; exact h)
  · have h0 : hardF G π x 0 ≤ hardF G π x y0 :=
      hmax (Metric.mem_closedBall_self G.hBy.le)
    have h1 := hardF_le G π x y'
    have h2 := hardF_ge G π x 0
    rw [base_zero _ G.scales.hρ.le] at h2
    rw [base_eq] at h1
    have hN2 : G.By ^ 2 < ‖y'‖ ^ 2 := pow_lt_pow_left₀ h G.hBy.le two_ne_zero
    have hsum : 0 ≤ ∑ j, pos (-y' j - G.ρ / 2) ^ 2 / 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    nlinarith

end LongTails.Proofs.NcPlPL
