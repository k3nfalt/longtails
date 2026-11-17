import LongTails.Proofs.FrontierChain

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FrontierChainGeometry

open FrontierChain FrontierChainProfiles

variable {d m : ℕ}

noncomputable def scatter (π : Fin m ↪ Fin d) (c : Fin m → ℝ) : EuclideanSpace ℝ (Fin d) :=
  ∑ i, c i • EuclideanSpace.single (π i) (1 : ℝ)

lemma scatter_apply (π : Fin m ↪ Fin d) (c : Fin m → ℝ) (i : Fin m) :
    scatter π c (π i) = c i := by
  classical
  unfold scatter
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [π.injective.ne hj]
  · simp

lemma inner_scatter (π : Fin m ↪ Fin d) (c : Fin m → ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    ⟪scatter π c, v⟫ = ∑ i, c i * v (π i) := by
  unfold scatter
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_left, EuclideanSpace.inner_single_left]
  simp

lemma scatter_norm_sq (π : Fin m ↪ Fin d) (c : Fin m → ℝ) :
    ‖scatter π c‖ ^ 2 = ∑ i, c i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_scatter]
  simp [scatter_apply, pow_two]

lemma scatter_norm_le (π : Fin m ↪ Fin d) (c : Fin m → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) : ‖scatter π c‖ ≤ C * Real.sqrt m := by
  have hs : ‖scatter π c‖ ^ 2 ≤ C ^ 2 * m := by
    rw [scatter_norm_sq]
    calc _ ≤ ∑ _i : Fin m, C ^ 2 := Finset.sum_le_sum fun i _ => by
          have h := pow_le_pow_left₀ (abs_nonneg (c i)) (hc i) 2
          simpa using h
      _ = _ := by simp; ring
  have hr := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hp : 0 ≤ C * Real.sqrt m := mul_nonneg hC (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg (scatter π c)]

lemma field_decomposition {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    field π x = -(potentialSlope (x (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)) +
      (scatter (Fin.castSuccEmb.trans π)
        (fun i => edgeLeft (x (π i.castSucc)) (x (π i.succ)))) +
      (scatter ((Fin.succEmb k).trans π)
        (fun i => edgeRight (x (π i.castSucc)) (x (π i.succ)))) := by
  simp [field, scatter, edgeField, Finset.sum_add_distrib, add_assoc]

lemma field_norm_upper {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ‖field π x‖ ≤ 18 * Real.sqrt (k + 1) := by
  have hleft := scatter_norm_le (Fin.castSuccEmb.trans π)
    (fun i => edgeLeft (x (π i.castSucc)) (x (π i.succ)))
    (by norm_num : (0 : ℝ) ≤ 16) (fun i => abs_le.mpr (by
      have h := edgeLeft_bounds (x (π i.castSucc)) (x (π i.succ))
      constructor <;> linarith))
  have hright := scatter_norm_le ((Fin.succEmb k).trans π)
    (fun i => edgeRight (x (π i.castSucc)) (x (π i.succ)))
    (by norm_num : (0 : ℝ) ≤ 1) (fun i => abs_le.mpr (by
      have h := edgeRight_bounds (x (π i.castSucc)) (x (π i.succ))
      constructor <;> linarith))
  have hp : ‖-(potentialSlope (x (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ))‖ ≤ 1 := by
    simpa [norm_smul, abs_of_nonneg (potentialSlope_bounds (x (π 0))).1] using
      (potentialSlope_bounds (x (π 0))).2
  have hs : Real.sqrt k ≤ Real.sqrt (k + 1) := Real.sqrt_le_sqrt (by linarith)
  have h1 : 1 ≤ Real.sqrt (k + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    simp
  rw [field_decomposition]
  have htri := norm_add_le
    (-(potentialSlope (x (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)) +
      scatter (Fin.castSuccEmb.trans π) (fun i => edgeLeft (x (π i.castSucc)) (x (π i.succ))))
    (scatter ((Fin.succEmb k).trans π) (fun i => edgeRight (x (π i.castSucc)) (x (π i.succ))))
  have htri2 := norm_add_le
    (-(potentialSlope (x (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)))
    (scatter (Fin.castSuccEmb.trans π) (fun i => edgeLeft (x (π i.castSucc)) (x (π i.succ))))
  nlinarith

lemma product_difference {a b c d A B X Y : ℝ} (hb : |b| ≤ B) (hc : |c| ≤ A)
    (hx : |a - c| ≤ X) (hy : |b - d| ≤ Y) : |a * b - c * d| ≤ B * X + A * Y := by
  have hA := (abs_nonneg c).trans hc
  have hB := (abs_nonneg b).trans hb
  have hX := (abs_nonneg (a - c)).trans hx
  have hY := (abs_nonneg (b - d)).trans hy
  calc |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * |b| + |c| * |b - d| := by rw [abs_mul, abs_mul]
    _ ≤ X * B + A * Y := add_le_add
      (mul_le_mul hx hb (abs_nonneg _) hX) (mul_le_mul hc hy (abs_nonneg _) hA)
    _ = _ := by ring

lemma edgeLeft_lipschitz (u v u' v' : ℝ) :
    |edgeLeft u v - edgeLeft u' v'| ≤ 256 * (|u - u'| + |v - v'|) := by
  have hprod (a b c d : ℝ) :
      |gateSlope a * potential b - gateSlope c * potential d| ≤
        128 * |a - c| + 4 * |b - d| := by
    have h := product_difference
      (by simpa only [abs_of_nonneg (potential_bounds b).1] using (potential_bounds b).2)
      (by simpa only [abs_of_nonneg (gateSlope_bounds c).1] using (gateSlope_bounds c).2)
      (gateSlope_lipschitz a c) (potential_lipschitz b d)
    nlinarith
  have hp := hprod u v u' v'
  have hn := hprod (-u) (-v) (-u') (-v')
  simp only [neg_sub_neg, abs_sub_comm] at hn
  have ht := abs_add_le
    (gateSlope (-u) * potential (-v) - gateSlope (-u') * potential (-v'))
    (gateSlope u * potential v - gateSlope u' * potential v')
  have he : edgeLeft u v - edgeLeft u' v' =
      -((gateSlope (-u) * potential (-v) - gateSlope (-u') * potential (-v')) +
        (gateSlope u * potential v - gateSlope u' * potential v')) := by
    unfold edgeLeft
    ring
  rw [he, abs_neg]
  nlinarith [abs_nonneg (v - v')]

lemma edgeRight_lipschitz (u v u' v' : ℝ) :
    |edgeRight u v - edgeRight u' v'| ≤ 8 * (|u - u'| + |v - v'|) := by
  have hprod (a b c d : ℝ) :
      |gate a * potentialSlope b - gate c * potentialSlope d| ≤
        4 * |a - c| + 2 * |b - d| := by
    have h := product_difference
      (by simpa only [abs_of_nonneg (potentialSlope_bounds b).1] using (potentialSlope_bounds b).2)
      (by simpa only [abs_of_nonneg (gate_bounds c).1] using (gate_bounds c).2)
      (gate_lipschitz a c) (potentialSlope_lipschitz b d)
    nlinarith
  have hp := hprod u v u' v'
  have hn := hprod (-u) (-v) (-u') (-v')
  simp only [neg_sub_neg, abs_sub_comm] at hn
  have ht := abs_add_le
    (gate (-u) * potentialSlope (-v) - gate (-u') * potentialSlope (-v'))
    (gate u * potentialSlope v - gate u' * potentialSlope v')
  have he : edgeRight u v - edgeRight u' v' =
      -((gate (-u) * potentialSlope (-v) - gate (-u') * potentialSlope (-v')) +
        (gate u * potentialSlope v - gate u' * potentialSlope v')) := by
    unfold edgeRight
    ring
  rw [he, abs_neg]
  nlinarith [abs_nonneg (v - v')]

lemma coordinate_sq_sum_le (π : Fin m ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ i, x (π i) ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  calc _ = ∑ j ∈ Finset.univ.map π, x j ^ 2 := by simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)

lemma scatter_sub (π : Fin m ↪ Fin d) (c c' : Fin m → ℝ) :
    scatter π c - scatter π c' = scatter π (fun i => c i - c' i) := by
  simp [scatter, sub_smul, Finset.sum_sub_distrib]

lemma scatter_increment (π α β : Fin m ↪ Fin d) (c c' : Fin m → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, |c i - c' i| ≤ C * (|w (α i)| + |w (β i)|)) :
    ‖scatter π c - scatter π c'‖ ≤ 2 * C * ‖w‖ := by
  have hs : ‖scatter π c - scatter π c'‖ ^ 2 ≤ 4 * C ^ 2 * ‖w‖ ^ 2 := by
    rw [scatter_sub, scatter_norm_sq]
    calc _ ≤ ∑ i, 2 * C ^ 2 * (w (α i) ^ 2 + w (β i) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          have hp := pow_le_pow_left₀ (abs_nonneg _) (h i) 2
          have hsq := sq_nonneg (|w (α i)| - |w (β i)|)
          simp only [sq_abs, mul_pow] at hp hsq
          have habs : (|w (α i)| + |w (β i)|) ^ 2 ≤
              2 * (w (α i) ^ 2 + w (β i) ^ 2) := by
            nlinarith [sq_abs (w (α i)), sq_abs (w (β i))]
          have hm := mul_le_mul_of_nonneg_left habs (sq_nonneg C)
          nlinarith
      _ = 2 * C ^ 2 * ((∑ i, w (α i) ^ 2) + ∑ i, w (β i) ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * C ^ 2 * (‖w‖ ^ 2 + ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (coordinate_sq_sum_le α w) (coordinate_sq_sum_le β w)) (by positivity)
      _ = _ := by ring
  have hp : 0 ≤ 2 * C * ‖w‖ := by positivity
  nlinarith [norm_nonneg (scatter π c - scatter π c')]

lemma field_lipschitz {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x y : EuclideanSpace ℝ (Fin d)) : ‖field π x - field π y‖ ≤ 530 * ‖x - y‖ := by
  let α := Fin.castSuccEmb.trans π
  let β := (Fin.succEmb k).trans π
  let cl := fun z : EuclideanSpace ℝ (Fin d) => fun i : Fin k =>
    edgeLeft (z (π i.castSucc)) (z (π i.succ))
  let cr := fun z : EuclideanSpace ℝ (Fin d) => fun i : Fin k =>
    edgeRight (z (π i.castSucc)) (z (π i.succ))
  let s := fun z : EuclideanSpace ℝ (Fin d) =>
    -(potentialSlope (z (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ))
  have hl : ‖scatter α (cl x) - scatter α (cl y)‖ ≤ 512 * ‖x - y‖ := by
    have h := scatter_increment α α β (cl x) (cl y) (x - y)
      (by norm_num : (0 : ℝ) ≤ 256) (fun i => by
        simpa [cl, α, β] using edgeLeft_lipschitz
          (x (π i.castSucc)) (x (π i.succ)) (y (π i.castSucc)) (y (π i.succ)))
    norm_num at h
    exact h
  have hr : ‖scatter β (cr x) - scatter β (cr y)‖ ≤ 16 * ‖x - y‖ := by
    have h := scatter_increment β α β (cr x) (cr y) (x - y)
      (by norm_num : (0 : ℝ) ≤ 8) (fun i => by
        simpa [cr, α, β] using edgeRight_lipschitz
          (x (π i.castSucc)) (x (π i.succ)) (y (π i.castSucc)) (y (π i.succ)))
    norm_num at h
    exact h
  have hs : ‖s x - s y‖ ≤ 2 * ‖x - y‖ := by
    have he : s x - s y = -(potentialSlope (x (π 0)) - potentialSlope (y (π 0))) •
        EuclideanSpace.single (π 0) (1 : ℝ) := by dsimp [s]; module
    rw [he]
    simp only [norm_smul, norm_neg]
    have hc : |x (π 0) - y (π 0)| ≤ ‖x - y‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) (π 0)
    have hp := potentialSlope_lipschitz (x (π 0)) (y (π 0))
    simpa using hp.trans (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))
  have he (z : EuclideanSpace ℝ (Fin d)) :
      field π z = s z + scatter α (cl z) + scatter β (cr z) := field_decomposition π z
  rw [he x, he y]
  have hadd (a b c d : EuclideanSpace ℝ (Fin d)) :
      ‖a + b - (c + d)‖ ≤ ‖a - c‖ + ‖b - d‖ := by
    rw [show a + b - (c + d) = (a - c) + (b - d) by abel]
    exact norm_add_le _ _
  have h1 := hadd (s x + scatter α (cl x)) (scatter β (cr x))
    (s y + scatter α (cl y)) (scatter β (cr y))
  have h2 := hadd (s x) (scatter α (cl x)) (s y) (scatter α (cl y))
  linarith

end LongTails.Proofs.FrontierChainGeometry
