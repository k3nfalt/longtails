import LongTails.Proofs.GeneralizedSmoothHardDual
import LongTails.Proofs.CompactConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothHardDualSegments

open GeneralizedSmoothHardDual CompactConjugate

noncomputable def path {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) (t : ℝ) :=
  (1 - t) • x + t • y

lemma path_nonnegative {m : ℕ} (x y : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ∀ i, 0 ≤ path x y t i := by
  intro i
  change 0 ≤ (1 - t) * x i + t * y i
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hx i)) (mul_nonneg ht.1 (hy i))

lemma path_norm {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖path x y t‖ ≤ max ‖x‖ ‖y‖ := by
  have hx : x ∈ Metric.closedBall 0 (max ‖x‖ ‖y‖) := by simp
  have hy : y ∈ Metric.closedBall 0 (max ‖x‖ ‖y‖) := by simp
  have hh := (convex_closedBall (0 : EuclideanSpace ℝ (Fin m)) (max ‖x‖ ‖y‖)) hx hy
    (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
  simpa only [Metric.mem_closedBall, dist_zero_right, path] using hh

lemma nonnegative_sum_positive {m : ℕ} (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) : 0 < ∑ i, x i := by
  have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
  rcases hs.eq_or_lt with he | he
  · exfalso
    apply hne
    ext i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hx j) (Finset.mem_univ i)
    change x i = 0
    linarith [hx i]
  · exact he

lemma path_sum_positive {m : ℕ} (x y : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hne : x ≠ y)
    (t : ℝ) (ht : t ∈ Ioo 0 1) : 0 < ∑ i, path x y t i := by
  have hsum : (∑ i, path x y t i) = (1 - t) * (∑ i, x i) + t * (∑ i, y i) := by
    simp only [path, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  rw [hsum]
  have hx0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
  have hy0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy i)
  by_cases hxzero : x = 0
  · have hyne : y ≠ 0 := by intro h; exact hne (hxzero.trans h.symm)
    have hp := nonnegative_sum_positive y hy hyne
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.2]) hx0) (mul_pos ht.1 hp)
  · have hp := nonnegative_sum_positive x hx hxzero
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith [ht.2]) hp) (mul_nonneg ht.1.le hy0)

lemma path_coordinate_derivative {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (i : Fin m) :
    HasDerivAt (fun s => path x y s i) ((y - x) i) t := by
  convert (((hasDerivAt_id t).const_sub 1).mul_const (x i)).add
    ((hasDerivAt_id t).mul_const (y i)) using 1
  · rfl
  · simp only [PiLp.sub_apply]
    ring

lemma dual_segment_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (x y : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (t : ℝ) (ht : t ∈ Icc 0 1) :
    dual L₀ L₁ (path x y t) ≤ (1 - t) * dual L₀ L₁ x + t * dual L₀ L₁ y -
      (‖y - x‖ ^ 2 / (L₀ + L₁ * max ‖x‖ ‖y‖)) / 2 * t * (1 - t) := by
  by_cases he : x = y
  · subst y
    have hh : path x x t = x := by simp [path, ← add_smul]
    rw [hh]
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, sub_zero]
    nlinarith
  · have hc : Continuous (path x y) := by unfold path; fun_prop
    have hF : ContinuousOn (fun s => dual L₀ L₁ (path x y s)) (Icc 0 1) :=
      (dual_continuousOn_nonnegative hm L₀ L₁ hL₀ hL₁).comp hc.continuousOn
        (fun s hs => path_nonnegative x y hx hy s hs)
    have h1 (s : ℝ) (hs : s ∈ Ioo 0 1) :
        HasDerivAt (fun a => dual L₀ L₁ (path x y a))
          (dualSlope L₀ L₁ (path x y s) (y - x)) s :=
      dual_hasDerivAt hm L₀ L₁ hL₀ hL₁ (path x y) (y - x) s
        (path_coordinate_derivative x y s) (path_nonnegative x y hx hy s ⟨hs.1.le, hs.2.le⟩)
        (path_sum_positive x y hx hy he s hs)
    have h2 (s : ℝ) (hs : s ∈ Ioo 0 1) :
        HasDerivAt (fun a => dualSlope L₀ L₁ (path x y a) (y - x))
          (dualCurvature L₀ L₁ (path x y s) (y - x)) s :=
      dualSlope_hasDerivAt hm L₀ L₁ hL₀ hL₁ (path x y) (y - x) s
        (path_coordinate_derivative x y s) (path_nonnegative x y hx hy s ⟨hs.1.le, hs.2.le⟩)
        (path_sum_positive x y hx hy he s hs)
    have hK (s : ℝ) (hs : s ∈ Ioo 0 1) :
        ‖y - x‖ ^ 2 / (L₀ + L₁ * max ‖x‖ ‖y‖) ≤ dualCurvature L₀ L₁ (path x y s) (y - x) := by
      apply le_trans _ (dualCurvature_lower hm L₀ L₁ hL₀ hL₁ (path x y s) (y - x)
        (path_nonnegative x y hx hy s ⟨hs.1.le, hs.2.le⟩) (path_sum_positive x y hx hy he s hs))
      gcongr
      exact path_norm x y s ⟨hs.1.le, hs.2.le⟩
    have hh := strong_segment_of_second_derivative _ _ _ _ hF h1 h2 hK t ht
    simpa only [path, sub_zero, sub_self, zero_smul, one_smul, zero_add, add_zero] using hh

lemma dual_optimizer_growth {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)
    (a u v : EuclideanSpace ℝ (Fin m)) (hu : u ∈ feasible G) (hv : v ∈ feasible G)
    (hopt : IsMaxOn (fun z => ⟪a, z⟫ - dual L₀ L₁ z) (feasible G) u) :
    ⟪a, v⟫ - dual L₀ L₁ v + ‖u - v‖ ^ 2 / (2 * (L₀ + L₁ * max ‖u‖ ‖v‖)) ≤
      ⟪a, u⟫ - dual L₀ L₁ u := by
  apply maximizer_growth_of_segment
  · intro t ht
    have hh := dual_segment_bound hm L₀ L₁ hL₀ hL₁ u v hu.1 hv.1 t ht
    change dual L₀ L₁ (path u v t) ≤ _
    rw [norm_sub_rev v] at hh
    convert hh using 1
    field_simp
  · intro t ht
    exact hopt ((feasible_convex G) hu hv (sub_nonneg.mpr ht.2) ht.1 (by ring))

lemma dual_optimizer_distance {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)
    (a b u v : EuclideanSpace ℝ (Fin m)) (hu : u ∈ feasible G) (hv : v ∈ feasible G)
    (hoptu : IsMaxOn (fun z => ⟪a, z⟫ - dual L₀ L₁ z) (feasible G) u)
    (hoptv : IsMaxOn (fun z => ⟪b, z⟫ - dual L₀ L₁ z) (feasible G) v) :
    ‖u - v‖ ≤ (L₀ + L₁ * max ‖u‖ ‖v‖) * ‖a - b‖ := by
  have hu' := dual_optimizer_growth hm L₀ L₁ hL₀ hL₁ G a u v hu hv hoptu
  have hv' := dual_optimizer_growth hm L₀ L₁ hL₀ hL₁ G b v u hv hu hoptv
  rw [norm_sub_rev v, max_comm ‖v‖] at hv'
  exact maximizer_distance_bound (dual L₀ L₁) a b u v _ (by positivity) hu' hv'

lemma conjugate_hasGradientAt {m : ℕ} (hm : 0 < m) (L₀ L₁ B : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)
    (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B)
    (a : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (value (feasible G) (dual L₀ L₁))
      (maximizer (feasible G) (dual L₀ L₁) a) a := by
  have hK := feasible_compact G B hG hB hGB
  have hne : (feasible G).Nonempty := ⟨0, feasible_zero G⟩
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G
  apply value_hasGradientAt hK hne hH (L₀ + L₁ * B) (by positivity)
  intro x v hv
  have hu := maximizer_spec hK hne hH x
  have hg := dual_optimizer_growth hm L₀ L₁ hL₀ hL₁ G x _ v hu.1 hv hu.2
  apply le_trans _ hg
  gcongr
  apply max_le
  · exact feasible_norm_bound G B hG hB hGB _ hu.1
  · exact feasible_norm_bound G B hG hB hGB v hv

lemma conjugate_field_pair {m : ℕ} (hm : 0 < m) (L₀ L₁ B : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)
    (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B)
    (a b : EuclideanSpace ℝ (Fin m)) :
    let g := maximizer (feasible G) (dual L₀ L₁)
    ‖g a - g b‖ ≤ (L₀ + L₁ * max ‖g a‖ ‖g b‖) * ‖a - b‖ := by
  have hK := feasible_compact G B hG hB hGB
  have hne : (feasible G).Nonempty := ⟨0, feasible_zero G⟩
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G
  have ha := maximizer_spec hK hne hH a
  have hb := maximizer_spec hK hne hH b
  exact dual_optimizer_distance hm L₀ L₁ hL₀ hL₁ G a b _ _ ha.1 hb.1 ha.2 hb.2

lemma conjugate_field_lipschitz {m : ℕ} (hm : 0 < m) (L₀ L₁ B : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)
    (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B) :
    LipschitzWith ⟨L₀ + L₁ * B, by positivity⟩ (maximizer (feasible G) (dual L₀ L₁)) := by
  have hK := feasible_compact G B hG hB hGB
  have hne : (feasible G).Nonempty := ⟨0, feasible_zero G⟩
  have hH := dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change ‖maximizer (feasible G) (dual L₀ L₁) a - maximizer (feasible G) (dual L₀ L₁) b‖ ≤
    (L₀ + L₁ * B) * ‖a - b‖
  apply (conjugate_field_pair hm L₀ L₁ B hL₀ hL₁ G hG hB hGB a b).trans
  gcongr
  apply max_le
  · exact feasible_norm_bound G B hG hB hGB _ (maximizer_spec hK hne hH a).1
  · exact feasible_norm_bound G B hG hB hGB _ (maximizer_spec hK hne hH b).1

lemma conjugate_nonnegative {m : ℕ} (hm : 0 < m) (L₀ L₁ B : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)
    (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B)
    (a : EuclideanSpace ℝ (Fin m)) : 0 ≤ value (feasible G) (dual L₀ L₁) a := by
  have hh := (maximizer_spec (feasible_compact G B hG hB hGB) ⟨0, feasible_zero G⟩
    (dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G) a).2 (feasible_zero G)
  change ⟪a, (0 : EuclideanSpace ℝ (Fin m))⟫ - dual L₀ L₁ 0 ≤
    value (feasible G) (dual L₀ L₁) a at hh
  simpa only [inner_zero_right, dual_zero, sub_zero] using hh

lemma conjugate_zero_of_nonpositive {m : ℕ} (hm : 0 < m) (L₀ L₁ B : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)
    (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B)
    (a : EuclideanSpace ℝ (Fin m)) (ha : ∀ i, a i ≤ 0) :
    value (feasible G) (dual L₀ L₁) a = 0 := by
  apply le_antisymm _ (conjugate_nonnegative hm L₀ L₁ B hL₀ hL₁ G hG hB hGB a)
  have hu := (maximizer_spec (feasible_compact G B hG hB hGB) ⟨0, feasible_zero G⟩
    (dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G) a).1
  have hn := (dual_bound hm L₀ L₁ hL₀ hL₁ _ hu.1).1
  have hi : ⟪a, maximizer (feasible G) (dual L₀ L₁) a⟫ ≤ 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_nonpos
    intro i _
    simp only [Real.inner_apply]
    exact mul_nonpos_of_nonpos_of_nonneg (ha i) (hu.1 i)
  unfold value
  linarith

end LongTails.Proofs.GeneralizedSmoothHardDualSegments
