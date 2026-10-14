import LongTails.Proofs.ArrowHurwiczGap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ArrowHurwicz

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

section Rate

variable {X : Set E} {Y : Set F} {K : E →L[ℝ] F} {g : E → ℝ} {h : F → ℝ} {adj : F → E}
  {px : E × ℝ → E} {py : F × ℝ → F} {η R L M : ℝ} {x0 : E} {y0 : F}

lemma Hyp.inner_le (H : Hyp X Y K g h adj px py η R L M x0 y0) {x : E} {y : F} (hx : x ∈ X)
    (hy : y ∈ Y) : |⟪y, K x⟫| ≤ L * R ^ 2 := by
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (H.boundX _ hx)
  calc |⟪y, K x⟫| ≤ ‖y‖ * ‖K x‖ := abs_real_inner_le_norm _ _
    _ ≤ R * (L * R) := by
        apply mul_le_mul (H.boundY _ hy) (le_trans (H.K_le x)
          (mul_le_mul_of_nonneg_left (H.boundX _ hx) H.L_nonneg)) (norm_nonneg _) hR
    _ = L * R ^ 2 := by ring

lemma Hyp.dist_sq_le (H : Hyp X Y K g h adj px py η R L M x0 y0) {a b : E} (ha : a ∈ X) (hb : b ∈ X) :
    ‖a - b‖ ^ 2 ≤ 4 * R ^ 2 := by
  have h1 : ‖a - b‖ ≤ 2 * R := by
    calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (H.boundX _ ha) (H.boundX _ hb)
      _ = 2 * R := by ring
  nlinarith [norm_nonneg (a - b)]

lemma Hyp.dist_sq_le' (H : Hyp X Y K g h adj px py η R L M x0 y0) {a b : F} (ha : a ∈ Y) (hb : b ∈ Y) :
    ‖a - b‖ ^ 2 ≤ 4 * R ^ 2 := by
  have h1 : ‖a - b‖ ≤ 2 * R := by
    calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (H.boundY _ ha) (H.boundY _ hb)
      _ = 2 * R := by ring
  nlinarith [norm_nonneg (a - b)]

lemma Hyp.total_bound (H : Hyp X Y K g h adj px py η R L M x0 y0) {xh : E} {yh : F}
    (hxh : xh ∈ X) (hyh : yh ∈ Y) (N : ℕ) (hηL : η * L ≤ 1) (hηΛ : η * (L * R + M) ≤ R) :
    ∑ t ∈ Finset.range (N + 1),
        η * gapTerm K g h (xs adj K px py η x0 y0 (t + 1)) (ys adj K px py η x0 y0 (t + 1)) xh yh ≤
      10 * R ^ 2 + η ^ 4 * L ^ 2 * (L * R + M) ^ 2 * (N + 1) / 4 := by
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (H.boundX _ H.memx)
  have hL := H.L_nonneg
  have hη := H.hη
  have hM := H.hM
  set Λ := L * R + M with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hos := H.one_step_sum hxh hyh (N + 1)
  have hfr : ∑ t ∈ Finset.range (N + 1), fr adj K px py η x0 y0 t =
      ∑ s ∈ Finset.range N, fr adj K px py η x0 y0 (s + 1) + fr adj K px py η x0 y0 0 :=
    Finset.sum_range_succ' _ _
  have hsf := H.sum_fr_succ N
  have hf0 := H.fr_zero_le
  have m0 := H.mem 0
  have mT := H.mem (N + 1)
  have m1 := H.mem 1
  have lyap_le : lyap adj K px py η x0 y0 xh yh 0 - lyap adj K px py η x0 y0 xh yh (N + 1) ≤
      4 * R ^ 2 + 3 * (η * L) * R ^ 2 := by
    unfold lyap
    have a1 := H.dist_sq_le m0.1 hxh
    have a2 := H.dist_sq_le' m0.2 hyh
    have a3 := sq_nonneg ‖xs adj K px py η x0 y0 (N + 1) - xh‖
    have a4 := sq_nonneg ‖ys adj K px py η x0 y0 (N + 1) - yh‖
    have b1 := abs_le.mp (H.inner_le m0.1 m0.2)
    have b2 := abs_le.mp (H.inner_le mT.1 mT.2)
    have b3 := abs_le.mp (H.inner_le hxh m0.2)
    have b4 := abs_le.mp (H.inner_le hxh mT.2)
    have c1 := mul_le_mul_of_nonneg_left b1.1 hη.le
    have c2 := mul_le_mul_of_nonneg_left b1.2 hη.le
    have c3 := mul_le_mul_of_nonneg_left b2.1 hη.le
    have c4 := mul_le_mul_of_nonneg_left b2.2 hη.le
    have c5 := mul_le_mul_of_nonneg_left b3.1 hη.le
    have c6 := mul_le_mul_of_nonneg_left b3.2 hη.le
    have c7 := mul_le_mul_of_nonneg_left b4.1 hη.le
    have c8 := mul_le_mul_of_nonneg_left b4.2 hη.le
    nlinarith
  have vel0 : vel adj K px py η x0 y0 0 ≤ (η * Λ) ^ 2 := by
    unfold vel
    have d1 := H.dx_le 0
    have d2 := H.dy_le 0
    have e1 : ‖xs adj K px py η x0 y0 (0 + 1) - xs adj K px py η x0 y0 0‖ ^ 2 ≤ (η * Λ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) d1 2
    have e2 : ‖ys adj K px py η x0 y0 (0 + 1) - ys adj K px py η x0 y0 0‖ ^ 2 ≤ (η * Λ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) d2 2
    linarith
  have velN : 0 ≤ vel adj K px py η x0 y0 N := by unfold vel; positivity
  have ksum : ∑ s ∈ Finset.range N,
      ‖K (xs adj K px py η x0 y0 (s + 2) - xs adj K px py η x0 y0 (s + 1))‖ ^ 2 ≤
      N * (L * (η * Λ)) ^ 2 := by
    have : ∀ s ∈ Finset.range N,
        ‖K (xs adj K px py η x0 y0 (s + 2) - xs adj K px py η x0 y0 (s + 1))‖ ^ 2 ≤
          (L * (η * Λ)) ^ 2 := by
      intro s _
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact le_trans (H.K_le _) (mul_le_mul_of_nonneg_left (H.dx_le (s + 1)) hL)
    calc _ ≤ ∑ s ∈ Finset.range N, (L * (η * Λ)) ^ 2 := Finset.sum_le_sum this
      _ = N * (L * (η * Λ)) ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have pot_le : pot adj K px py η x0 y0 g h (N + 1) - pot adj K px py η x0 y0 g h 1 ≤ 4 * (M * R) := by
    unfold pot
    have g1 := abs_le.mp (H.lipg _ mT.1 _ m1.1)
    have h1 := abs_le.mp (H.liph _ mT.2 _ m1.2)
    have n1 : ‖xs adj K px py η x0 y0 (N + 1) - xs adj K px py η x0 y0 1‖ ≤ 2 * R := by
      calc _ ≤ ‖xs adj K px py η x0 y0 (N + 1)‖ + ‖xs adj K px py η x0 y0 1‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (H.boundX _ mT.1) (H.boundX _ m1.1)
        _ = 2 * R := by ring
    have n2 : ‖ys adj K px py η x0 y0 (N + 1) - ys adj K px py η x0 y0 1‖ ≤ 2 * R := by
      calc _ ≤ ‖ys adj K px py η x0 y0 (N + 1)‖ + ‖ys adj K px py η x0 y0 1‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (H.boundY _ mT.2) (H.boundY _ m1.2)
        _ = 2 * R := by ring
    have p1 := mul_le_mul_of_nonneg_left n1 hM
    have p2 := mul_le_mul_of_nonneg_left n2 hM
    linarith
  have hηM : η * M ≤ R := by
    have h0 : 0 ≤ η * (L * R) := by positivity
    have h1 : η * Λ = η * (L * R) + η * M := by rw [hΛ]; ring
    linarith
  have q1 : η * L * R ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg R]
  have q2 : η ^ 2 * L ^ 2 * R ^ 2 ≤ R ^ 2 := by
    have : (η * L) ^ 2 ≤ 1 := by
      have : 0 ≤ η * L := by positivity
      nlinarith
    nlinarith [sq_nonneg R]
  have q3 : (η * Λ) ^ 2 ≤ R ^ 2 := by
    have : 0 ≤ η * Λ := by positivity
    nlinarith
  have q4 : η * (4 * (M * R)) ≤ 4 * R ^ 2 := by nlinarith
  have q5 : η ^ 2 / 2 * (N * (L * (η * Λ)) ^ 2) = η ^ 4 * L ^ 2 * Λ ^ 2 * N / 2 := by ring
  have q6 : η ^ 2 / 2 * ∑ s ∈ Finset.range N,
      ‖K (xs adj K px py η x0 y0 (s + 2) - xs adj K px py η x0 y0 (s + 1))‖ ^ 2 ≤
      η ^ 2 / 2 * (N * (L * (η * Λ)) ^ 2) := mul_le_mul_of_nonneg_left ksum (by positivity)
  have q7 : η * (pot adj K px py η x0 y0 g h (N + 1) - pot adj K px py η x0 y0 g h 1) ≤
      η * (4 * (M * R)) := mul_le_mul_of_nonneg_left pot_le hη.le
  have q8 : 0 ≤ η ^ 4 * L ^ 2 * Λ ^ 2 := by positivity
  have q9 : 0 ≤ R ^ 2 := sq_nonneg R
  linarith

lemma Hyp.avg_mem (H : Hyp X Y K g h adj px py η R L M x0 y0) (T : ℕ) (hT : 0 < T) :
    ((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T, xs adj K px py η x0 y0 (s + 1) ∈ X ∧
      ((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T, ys adj K px py η x0 y0 (s + 1) ∈ Y := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hw0 : ∀ i ∈ Finset.range T, (0 : ℝ) ≤ ((T : ℝ))⁻¹ := fun _ _ => by positivity
  have hw1 : ∑ i ∈ Finset.range T, ((T : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  rw [Finset.smul_sum, Finset.smul_sum]
  exact ⟨H.convX.sum_mem hw0 hw1 (fun i _ => (H.mem (i + 1)).1),
    H.convY.sum_mem hw0 hw1 (fun i _ => (H.mem (i + 1)).2)⟩

lemma Hyp.avg_gap (H : Hyp X Y K g h adj px py η R L M x0 y0) {xh : E} {yh : F} (T : ℕ) (hT : 0 < T) :
    gapTerm K g h (((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T, xs adj K px py η x0 y0 (s + 1))
        (((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T, ys adj K px py η x0 y0 (s + 1)) xh yh ≤
      ((T : ℝ))⁻¹ * ∑ s ∈ Finset.range T,
        gapTerm K g h (xs adj K px py η x0 y0 (s + 1)) (ys adj K px py η x0 y0 (s + 1)) xh yh := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hw0 : ∀ i ∈ Finset.range T, (0 : ℝ) ≤ ((T : ℝ))⁻¹ := fun _ _ => by positivity
  have hw1 : ∑ i ∈ Finset.range T, ((T : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  have jg := H.cvg.map_sum_le hw0 hw1 (fun i _ => (H.mem (i + 1)).1)
  have jh := H.cvh.map_sum_le hw0 hw1 (fun i _ => (H.mem (i + 1)).2)
  simp only [smul_eq_mul] at jg jh
  rw [← Finset.smul_sum, ← Finset.mul_sum] at jg jh
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have l1 : ⟪yh, K (((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T, xs adj K px py η x0 y0 (s + 1))⟫ =
      ((T : ℝ))⁻¹ * ∑ s ∈ Finset.range T, ⟪yh, K (xs adj K px py η x0 y0 (s + 1))⟫ := by
    rw [map_smul, map_sum, real_inner_smul_right, inner_sum]
  have l2 : ⟪((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T, ys adj K px py η x0 y0 (s + 1), K xh⟫ =
      ((T : ℝ))⁻¹ * ∑ s ∈ Finset.range T, ⟪ys adj K px py η x0 y0 (s + 1), K xh⟫ := by
    rw [real_inner_smul_left, sum_inner]
  have l3 : ((T : ℝ))⁻¹ * ∑ s ∈ Finset.range T,
      gapTerm K g h (xs adj K px py η x0 y0 (s + 1)) (ys adj K px py η x0 y0 (s + 1)) xh yh =
      ((T : ℝ))⁻¹ * ∑ s ∈ Finset.range T, g (xs adj K px py η x0 y0 (s + 1)) +
        ((T : ℝ))⁻¹ * ∑ s ∈ Finset.range T, ⟪yh, K (xs adj K px py η x0 y0 (s + 1))⟫ - h yh -
        g xh - ((T : ℝ))⁻¹ * ∑ s ∈ Finset.range T, ⟪ys adj K px py η x0 y0 (s + 1), K xh⟫ +
        ((T : ℝ))⁻¹ * ∑ s ∈ Finset.range T, h (ys adj K px py η x0 y0 (s + 1)) := by
    unfold gapTerm
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp
    try ring
  rw [l3]
  unfold gapTerm
  rw [l1, l2]
  linarith

end Rate

lemma tuning {R L M ε : ℝ} (hR : 0 < R) (hL : 0 < L) (hM : 0 ≤ M) (hε : 0 < ε) (T : ℕ)
    (hT : (11 * R * (L * R + M) / ε) ^ ((4 : ℝ) / 3) ≤ T) :
    1 ≤ T ∧ R / ((L * R + M) * (T : ℝ) ^ ((1 : ℝ) / 4)) * L ≤ 1 ∧
      R / ((L * R + M) * (T : ℝ) ^ ((1 : ℝ) / 4)) * (L * R + M) ≤ R ∧
      10 * R ^ 2 / (R / ((L * R + M) * (T : ℝ) ^ ((1 : ℝ) / 4)) * T) +
        (R / ((L * R + M) * (T : ℝ) ^ ((1 : ℝ) / 4))) ^ 3 * L ^ 2 * (L * R + M) ^ 2 / 4 ≤ ε := by
  set Λ := L * R + M with hΛ
  have hΛpos : 0 < Λ := by positivity
  have hc : 0 < 11 * R * Λ / ε := by positivity
  have hcp : 0 < (11 * R * Λ / ε) ^ ((4 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hcp hT
  have hT1 : 1 ≤ T := by
    have : 0 < T := by exact_mod_cast hTpos
    omega
  set s := (T : ℝ) ^ ((1 : ℝ) / 4) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hTpos _
  have hs1 : 1 ≤ s := Real.one_le_rpow (by exact_mod_cast hT1) (by norm_num)
  have hs4 : (T : ℝ) = s ^ 4 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
    norm_num
  have hs3 : 11 * R * Λ / ε ≤ s ^ 3 := by
    have h1 : ((11 * R * Λ / ε) ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 4) ≤ (T : ℝ) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hcp.le hT (by norm_num)
    rw [← Real.rpow_mul hc.le] at h1
    rw [show (4 : ℝ) / 3 * (3 / 4) = 1 by norm_num, Real.rpow_one] at h1
    have h2 : (T : ℝ) ^ ((3 : ℝ) / 4) = s ^ 3 := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
      norm_num
    linarith
  have hRL : R * L ≤ Λ := by nlinarith
  refine ⟨hT1, ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := mul_nonneg (mul_nonneg hR.le hΛpos.le) (sub_nonneg.mpr hs1)
    nlinarith
  · rw [hs4]
    have hRne : R ≠ 0 := hR.ne'
    have hΛne : Λ ≠ 0 := hΛpos.ne'
    have hsne : s ≠ 0 := hs0.ne'
    have hs3p : 0 < s ^ 3 := by positivity
    have hq : 0 ≤ R * Λ / s ^ 3 := by positivity
    have e1 : 10 * R ^ 2 / (R / (Λ * s) * s ^ 4) = 10 * (R * Λ / s ^ 3) := by
      field_simp
      try ring
    have e2 : (R / (Λ * s)) ^ 3 * L ^ 2 * Λ ^ 2 / 4 = (R * L) ^ 2 * R / (4 * Λ * s ^ 3) := by
      field_simp
      try ring
    have f1 : (R * L) ^ 2 * R / (4 * Λ * s ^ 3) ≤ R * Λ / s ^ 3 / 4 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : (R * L) ^ 2 ≤ Λ ^ 2 := by
        have : 0 ≤ R * L := by positivity
        nlinarith
      have hm := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ R * (s ^ 3 * 4))
      nlinarith
    have f3 : 11 * (R * Λ / s ^ 3) ≤ ε := by
      rw [show 11 * (R * Λ / s ^ 3) = 11 * R * Λ / s ^ 3 by ring, div_le_iff₀ hs3p]
      rw [div_le_iff₀ hε] at hs3
      linarith
    rw [e1, e2]
    linarith

end OracleTemplate.ArrowHurwicz
