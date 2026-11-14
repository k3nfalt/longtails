import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Filter Set
open scoped BigOperators Topology

namespace LongTails.Proofs.GeneralizedSmoothHardDual

noncomputable def radial (L₀ L₁ s : ℝ) : ℝ :=
  L₀ / L₁ ^ 2 * ((1 + L₁ * s / L₀) * Real.log (1 + L₁ * s / L₀) - L₁ * s / L₀)

noncomputable def entropy (L₁ c p : ℝ) : ℝ :=
  4 / L₁ * ((p + c) * Real.log (1 + p / c) - p)

lemma radial_derivative (L₀ L₁ s : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁)
    (hs : 0 ≤ s) : HasDerivAt (radial L₀ L₁)
      (Real.log (1 + L₁ * s / L₀) / L₁) s := by
  have ha := ((hasDerivAt_id s).const_mul L₁).div_const L₀
  have hb := ha.const_add 1
  have hp : 0 < 1 + L₁ * s / L₀ := by positivity
  have hd := ((hb.mul (hb.log hp.ne')).sub ha).const_mul (L₀ / L₁ ^ 2)
  convert hd using 1
  · ext x
    rfl
  · dsimp
    field_simp
    ring

lemma radial_second_derivative (L₀ L₁ s : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁)
    (hs : 0 ≤ s) : HasDerivAt (fun t => Real.log (1 + L₁ * t / L₀) / L₁)
      (1 / (L₀ + L₁ * s)) s := by
  have ha := (((hasDerivAt_id s).const_mul L₁).div_const L₀).const_add 1
  have hp : 0 < 1 + L₁ * s / L₀ := by positivity
  convert (ha.log hp.ne').div_const L₁ using 1
  dsimp
  field_simp
  simp only [id_eq]
  field_simp

lemma entropy_derivative (L₁ c p : ℝ) (hL₁ : 0 < L₁) (hc : 0 < c)
    (hp : 0 ≤ p) : HasDerivAt (entropy L₁ c)
      (4 / L₁ * Real.log (1 + p / c)) p := by
  have ha := ((hasDerivAt_id p).div_const c).const_add 1
  have hh : 0 < 1 + p / c := by positivity
  have hd := ((((hasDerivAt_id p).add_const c).mul (ha.log hh.ne')).sub
    (hasDerivAt_id p)).const_mul (4 / L₁)
  convert hd using 1
  · ext x
    rfl
  · dsimp
    field_simp
    ring

lemma entropy_second_derivative (L₁ c p : ℝ) (hL₁ : 0 < L₁) (hc : 0 < c)
    (hp : 0 ≤ p) : HasDerivAt (fun t => 4 / L₁ * Real.log (1 + t / c))
      (4 / (L₁ * (p + c))) p := by
  have ha := ((hasDerivAt_id p).div_const c).const_add 1
  have hh : 0 < 1 + p / c := by positivity
  convert (ha.log hh.ne').const_mul (4 / L₁) using 1
  dsimp
  field_simp
  simp only [id_eq]
  field_simp
  ring

lemma entropy_nonneg (L₁ c p : ℝ) (hL₁ : 0 < L₁) (hc : 0 < c) (hp : 0 ≤ p) :
    0 ≤ entropy L₁ c p := by
  have ha : 0 < 1 + p / c := by positivity
  have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ha) (le_of_lt ha)
  have he : (1 + p / c) * (1 - (1 + p / c)⁻¹) = p / c := by field_simp; ring
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hh hc.le
  have he' : c * (p / c) = p := by field_simp
  have he'' : c * ((1 + p / c) * Real.log (1 + p / c)) =
      (p + c) * Real.log (1 + p / c) := by field_simp; ring
  rw [he', he''] at hm
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hm)

lemma entropy_upper (L₁ c p : ℝ) (hL₁ : 0 < L₁) (hc : 0 < c) (hp : 0 ≤ p) :
    entropy L₁ c p ≤ p * (4 / L₁ * Real.log (1 + p / c)) := by
  have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + p / c by positivity)
  have hm := mul_le_mul_of_nonneg_left hh hc.le
  have he : c * (1 + p / c - 1) = p := by field_simp; ring
  rw [he] at hm
  have ht := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 / L₁ by positivity)
  unfold entropy
  nlinarith only [ht]

lemma radial_zero (L₀ L₁ : ℝ) : radial L₀ L₁ 0 = 0 := by simp [radial]

lemma entropy_zero (L₁ c : ℝ) : entropy L₁ c 0 = 0 := by simp [entropy]

noncomputable def dual {m : ℕ} (L₀ L₁ : ℝ) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  let Z := ∑ i, z i
  if Z = 0 then 0 else
    2 * radial L₀ L₁ Z + Z * ∑ i, entropy L₁ (1 / Real.sqrt m) (z i / Z)

lemma radial_coefficient_bound (L₀ L₁ Z p : ℝ) (hL₀ : 0 < L₀)
    (hL₁ : 0 ≤ L₁) (hZ : 0 ≤ Z) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    p ^ 2 / (L₀ + L₁ * Z * p) ≤ 1 / (L₀ + L₁ * Z) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h1 : 0 ≤ L₀ * (1 - p ^ 2) := by
    apply mul_nonneg hL₀.le
    nlinarith
  have h2 : 0 ≤ L₁ * Z * p * (1 - p) := by positivity
  nlinarith only [h1, h2]

lemma decomposition_norm_sq {E : Type*} [NormedAddCommGroup E] (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hn := norm_add_le u v
  nlinarith [norm_nonneg (u + v), norm_nonneg u, norm_nonneg v,
    sq_nonneg (‖u‖ - ‖v‖)]

lemma ratio_derivative {Z z : ℝ → ℝ} {x b d : ℝ}
    (hZ : HasDerivAt Z b x) (hz : HasDerivAt z d x) (hpos : 0 < Z x) :
    HasDerivAt (fun t => z t / Z t) ((d - b * (z x / Z x)) / Z x) x := by
  convert hz.div hZ hpos.ne' using 1
  field_simp

lemma perspective_derivative {Z z : ℝ → ℝ} {x b d : ℝ}
    (L₁ c : ℝ) (hL₁ : 0 < L₁) (hc : 0 < c)
    (hZ : HasDerivAt Z b x) (hz : HasDerivAt z d x) (hpos : 0 < Z x) (hzpos : 0 ≤ z x) :
    HasDerivAt (fun t => Z t * entropy L₁ c (z t / Z t))
      (b * entropy L₁ c (z x / Z x) +
        (4 / L₁ * Real.log (1 + (z x / Z x) / c)) * (d - b * (z x / Z x))) x := by
  have hp : 0 ≤ z x / Z x := div_nonneg hzpos hpos.le
  have hr := ratio_derivative hZ hz hpos
  have he := (entropy_derivative L₁ c (z x / Z x) hL₁ hc hp).comp x hr
  convert hZ.mul he using 1
  · rfl
  · dsimp
    field_simp

lemma perspective_slope_derivative {Z z : ℝ → ℝ} {x b d : ℝ}
    (L₁ c : ℝ) (hL₁ : 0 < L₁) (hc : 0 < c)
    (hZ : HasDerivAt Z b x) (hz : HasDerivAt z d x) (hpos : 0 < Z x) (hzpos : 0 ≤ z x) :
    HasDerivAt (fun t => b * entropy L₁ c (z t / Z t) +
      (4 / L₁ * Real.log (1 + (z t / Z t) / c)) * (d - b * (z t / Z t)))
      (4 / (L₁ * (z x / Z x + c)) * (d - b * (z x / Z x)) ^ 2 / Z x) x := by
  have hp : 0 ≤ z x / Z x := div_nonneg hzpos hpos.le
  have hr := ratio_derivative hZ hz hpos
  have he := (entropy_derivative L₁ c (z x / Z x) hL₁ hc hp).comp x hr
  have hs := (entropy_second_derivative L₁ c (z x / Z x) hL₁ hc hp).comp x hr
  have hd := (he.const_mul b).add (hs.mul ((hr.const_mul b).const_sub d))
  convert hd using 1
  · rfl
  · dsimp
    ring

def feasible {m : ℕ} (G : Fin m → ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i / G i ≤ 1}

lemma feasible_zero {m : ℕ} (G : Fin m → ℝ) : (0 : EuclideanSpace ℝ (Fin m)) ∈ feasible G := by
  simp [feasible]

lemma nonnegative_norm_le_sum {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) (hz : ∀ i, 0 ≤ z i) :
    ‖z‖ ≤ ∑ i, z i := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => z i)
    (fun i _ => hz i)
  rw [← EuclideanSpace.real_norm_sq_eq] at hs
  have hn : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => hz i)
  nlinarith [norm_nonneg z]

lemma feasible_norm_bound {m : ℕ} (G : Fin m → ℝ) (B : ℝ)
    (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B)
    (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ feasible G) : ‖z‖ ≤ B := by
  apply (nonnegative_norm_le_sum z hz.1).trans
  have hh (i : Fin m) : z i ≤ B * (z i / G i) := by
    have hm := mul_le_mul_of_nonneg_right (hGB i) (div_nonneg (hz.1 i) (hG i).le)
    simpa only [mul_div_cancel₀ _ (hG i).ne'] using hm
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)
  rw [← Finset.mul_sum] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left hz.2 hB).trans_eq (mul_one B))

lemma feasible_compact {m : ℕ} (G : Fin m → ℝ) (B : ℝ)
    (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B) : IsCompact (feasible G) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · have h1 : IsClosed {z : EuclideanSpace ℝ (Fin m) | ∀ i, 0 ≤ z i} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      exact isClosed_le continuous_const (by fun_prop)
    have h2 : Continuous (fun z : EuclideanSpace ℝ (Fin m) => ∑ i, z i / G i) := by fun_prop
    exact h1.inter (isClosed_le h2 continuous_const)
  · apply (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin m))).mpr
    refine ⟨B, ?_⟩
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using feasible_norm_bound G B hG hB hGB z hz

lemma radial_nonneg (L₀ L₁ s : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hs : 0 ≤ s) :
    0 ≤ radial L₀ L₁ s := by
  have hh := entropy_nonneg 4 1 (L₁ * s / L₀) (by norm_num) (by norm_num) (by positivity)
  simp only [entropy, div_one, div_self (by norm_num : (4 : ℝ) ≠ 0), one_mul] at hh
  unfold radial
  apply mul_nonneg (by positivity)
  simpa only [add_comm (L₁ * s / L₀) 1] using hh

lemma entropy_upper_linear (L₁ c p : ℝ) (hL₁ : 0 < L₁) (hc : 0 < c)
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    entropy L₁ c p ≤ p * (4 / L₁ * Real.log (1 + 1 / c)) := by
  apply (entropy_upper L₁ c p hL₁ hc hp).trans
  gcongr

lemma perspective_bound {m : ℕ} (L₁ c : ℝ) (hL₁ : 0 < L₁) (hc : 0 < c)
    (z : EuclideanSpace ℝ (Fin m)) (hz : ∀ i, 0 ≤ z i) (hZ : 0 < ∑ i, z i) :
    0 ≤ (∑ i, z i) * ∑ i, entropy L₁ c (z i / ∑ j, z j) ∧
    (∑ i, z i) * ∑ i, entropy L₁ c (z i / ∑ j, z j) ≤
      (∑ i, z i) * (4 / L₁ * Real.log (1 + 1 / c)) := by
  have hp (i : Fin m) : 0 ≤ z i / ∑ j, z j := div_nonneg (hz i) hZ.le
  have hp' (i : Fin m) : z i / ∑ j, z j ≤ 1 := by
    apply (div_le_one hZ).mpr
    exact Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
  constructor
  · exact mul_nonneg hZ.le (Finset.sum_nonneg (fun i _ => entropy_nonneg L₁ c _ hL₁ hc (hp i)))
  · apply mul_le_mul_of_nonneg_left _ hZ.le
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      entropy_upper_linear L₁ c _ hL₁ hc (hp i) (hp' i))
    simpa only [← Finset.sum_mul, ← Finset.sum_div, div_self hZ.ne', one_mul] using hh

lemma feasible_convex {m : ℕ} (G : Fin m → ℝ) : Convex ℝ (feasible G) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) / G i ≤ 1
    simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left hx.2 ha
    have h2 := mul_le_mul_of_nonneg_left hy.2 hb
    nlinarith

lemma dual_zero {m : ℕ} (L₀ L₁ : ℝ) : dual L₀ L₁ (0 : EuclideanSpace ℝ (Fin m)) = 0 := by
  simp [dual]

lemma dual_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁)
    (z : EuclideanSpace ℝ (Fin m)) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ dual L₀ L₁ z ∧ dual L₀ L₁ z ≤
      2 * radial L₀ L₁ (∑ i, z i) + (∑ i, z i) *
        (4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m))) := by
  have hZ : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => hz i)
  by_cases he : ∑ i, z i = 0
  · simp [dual, he, radial_zero]
  · have hp := perspective_bound L₁ (1 / Real.sqrt m) hL₁
      (by positivity) z hz (lt_of_le_of_ne hZ (Ne.symm he))
    have hr := radial_nonneg L₀ L₁ _ hL₀ hL₁ hZ
    simp only [dual, he, ↓reduceIte]
    constructor <;> linarith

lemma dual_continuousWithinAt_zero {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) :
    ContinuousWithinAt (dual L₀ L₁) {z : EuclideanSpace ℝ (Fin m) | ∀ i, 0 ≤ z i} 0 := by
  let C := 4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m))
  have hsum : Continuous (fun z : EuclideanSpace ℝ (Fin m) => ∑ i, z i) := by fun_prop
  have hr : ContinuousAt (fun z : EuclideanSpace ℝ (Fin m) => radial L₀ L₁ (∑ i, z i)) 0 := by
    have hf : ContinuousAt (radial L₀ L₁) (∑ i, (0 : EuclideanSpace ℝ (Fin m)) i) := by
      simpa using (radial_derivative L₀ L₁ 0 hL₀ hL₁ le_rfl).continuousAt
    exact hf.comp (f := fun w : EuclideanSpace ℝ (Fin m) => ∑ i, w i) (x := 0)
      hsum.continuousAt
  have hu : Tendsto (fun z : EuclideanSpace ℝ (Fin m) =>
      2 * radial L₀ L₁ (∑ i, z i) + (∑ i, z i) * C)
      (𝓝[{z | ∀ i, 0 ≤ z i}] 0) (𝓝 0) := by
    have hh := (hr.const_mul 2).add (hsum.continuousAt.mul_const C)
    change ContinuousAt (fun z : EuclideanSpace ℝ (Fin m) =>
      2 * radial L₀ L₁ (∑ i, z i) + (∑ i, z i) * C) 0 at hh
    simpa [radial_zero, Pi.add_apply] using hh.tendsto.mono_left nhdsWithin_le_nhds
  change Tendsto _ _ (𝓝 (dual L₀ L₁ (0 : EuclideanSpace ℝ (Fin m))))
  rw [dual_zero]
  apply squeeze_zero' _ _ hu
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (dual_bound hm L₀ L₁ hL₀ hL₁ z hz).1
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (dual_bound hm L₀ L₁ hL₀ hL₁ z hz).2

lemma dual_continuousAt_positive {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (z : EuclideanSpace ℝ (Fin m))
    (hz : ∀ i, 0 ≤ z i) (hZ : 0 < ∑ i, z i) : ContinuousAt (dual L₀ L₁) z := by
  have hsum : Continuous (fun w : EuclideanSpace ℝ (Fin m) => ∑ i, w i) := by fun_prop
  have hr := (radial_derivative L₀ L₁ (∑ i, z i) hL₀ hL₁ hZ.le).continuousAt.comp
    (f := fun w : EuclideanSpace ℝ (Fin m) => ∑ i, w i) (x := z) hsum.continuousAt
  change ContinuousAt (fun w : EuclideanSpace ℝ (Fin m) => radial L₀ L₁ (∑ i, w i)) z at hr
  have hE (i : Fin m) : ContinuousAt (fun w : EuclideanSpace ℝ (Fin m) =>
      entropy L₁ (1 / Real.sqrt m) (w i / ∑ j, w j)) z := by
    have hp : 0 ≤ z i / ∑ j, z j := div_nonneg (hz i) hZ.le
    have hc : 0 < 1 / Real.sqrt m := by positivity
    have hd : ContinuousAt (fun w : EuclideanSpace ℝ (Fin m) => w i / ∑ j, w j) z :=
      (show ContinuousAt (fun w : EuclideanSpace ℝ (Fin m) => w i) z by fun_prop).div
        hsum.continuousAt hZ.ne'
    exact (entropy_derivative L₁ _ _ hL₁ hc hp).continuousAt.comp
      (f := fun w : EuclideanSpace ℝ (Fin m) => w i / ∑ j, w j) (x := z) hd
  have he : ContinuousAt (fun w : EuclideanSpace ℝ (Fin m) =>
      2 * radial L₀ L₁ (∑ i, w i) + (∑ i, w i) *
        ∑ i, entropy L₁ (1 / Real.sqrt m) (w i / ∑ j, w j)) z := by fun_prop
  apply he.congr_of_eventuallyEq
  filter_upwards [hsum.continuousAt.eventually (lt_mem_nhds hZ)] with w hw
  simp only [dual, ne_of_gt hw, ↓reduceIte]

lemma simplex_norm_lower {m : ℕ} (hm : 0 < m) (p : EuclideanSpace ℝ (Fin m))
    (hs : ∑ i, p i = 1) : 1 / Real.sqrt m ≤ ‖p‖ := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin m => p i) (fun _ => (1 : ℝ))
  simp only [mul_one, hs, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← EuclideanSpace.real_norm_sq_eq] at hh
  have hr : 0 < Real.sqrt m := by positivity
  have he : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  apply (div_le_iff₀ hr).mpr
  have hn := mul_nonneg (norm_nonneg p) hr.le
  nlinarith

lemma simplex_coordinate_bound {m : ℕ} (hm : 0 < m) (p : EuclideanSpace ℝ (Fin m))
    (hs : ∑ i, p i = 1) (i : Fin m) : p i + 1 / Real.sqrt m ≤ 2 * ‖p‖ := by
  have hp := (le_abs_self (p i)).trans (PiLp.norm_apply_le p i)
  linarith [simplex_norm_lower hm p hs]

lemma dual_continuousOn_nonnegative {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) :
    ContinuousOn (dual L₀ L₁) {z : EuclideanSpace ℝ (Fin m) | ∀ i, 0 ≤ z i} := by
  intro z hz
  have hZ : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => hz i)
  rcases hZ.eq_or_lt with he | he
  · have hz0 : z = 0 := by
      ext i
      have hi : z i ≤ ∑ j, z j := Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
      have hh : z i = 0 := by linarith [hz i]
      simpa using hh
    subst z
    exact dual_continuousWithinAt_zero hm L₀ L₁ hL₀ hL₁
  · exact (dual_continuousAt_positive hm L₀ L₁ hL₀ hL₁ z hz he).continuousWithinAt

lemma dual_continuousOn_feasible {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ) :
    ContinuousOn (dual L₀ L₁) (feasible G) :=
  (dual_continuousOn_nonnegative hm L₀ L₁ hL₀ hL₁).mono (fun _ hz => hz.1)

noncomputable def dualSlope {m : ℕ} (L₀ L₁ : ℝ) (z w : EuclideanSpace ℝ (Fin m)) : ℝ :=
  let Z := ∑ i, z i
  let b := ∑ i, w i
  2 * b * (Real.log (1 + L₁ * Z / L₀) / L₁) +
    ∑ i, (b * entropy L₁ (1 / Real.sqrt m) (z i / Z) +
      (4 / L₁ * Real.log (1 + (z i / Z) / (1 / Real.sqrt m))) * (w i - b * (z i / Z)))

noncomputable def dualCurvature {m : ℕ} (L₀ L₁ : ℝ) (z w : EuclideanSpace ℝ (Fin m)) : ℝ :=
  let Z := ∑ i, z i
  let b := ∑ i, w i
  2 * b ^ 2 / (L₀ + L₁ * Z) +
    ∑ i, 4 / (L₁ * (z i / Z + 1 / Real.sqrt m)) * (w i - b * (z i / Z)) ^ 2 / Z

lemma dual_hasDerivAt {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (z : ℝ → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (x : ℝ) (hz : ∀ i, HasDerivAt (fun t => z t i) (w i) x)
    (hpos : ∀ i, 0 ≤ z x i) (hZ : 0 < ∑ i, z x i) :
    HasDerivAt (fun t => dual L₀ L₁ (z t)) (dualSlope L₀ L₁ (z x) w) x := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hz i)
  have hr := ((radial_derivative L₀ L₁ _ hL₀ hL₁ hZ.le).comp x hsum).const_mul 2
  have hp (i : Fin m) := perspective_derivative L₁ (1 / Real.sqrt m) hL₁
    (by positivity) hsum (hz i) hZ (hpos i)
  have hh := hr.add (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hp i))
  have he : 2 * ((Real.log (1 + L₁ * (∑ i, z x i) / L₀) / L₁) * (∑ i, w i)) +
      (∑ i, ((∑ j, w j) * entropy L₁ (1 / Real.sqrt m) (z x i / ∑ j, z x j) +
        (4 / L₁ * Real.log (1 + (z x i / ∑ j, z x j) / (1 / Real.sqrt m))) *
          (w i - (∑ j, w j) * (z x i / ∑ j, z x j)))) = dualSlope L₀ L₁ (z x) w := by
    unfold dualSlope
    ring
  rw [he] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hsum.continuousAt.eventually (lt_mem_nhds hZ)] with t ht
  simp only [dual, ne_of_gt ht, ↓reduceIte, Finset.mul_sum, Pi.add_apply, Function.comp_apply]

lemma dualSlope_hasDerivAt {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (z : ℝ → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (x : ℝ) (hz : ∀ i, HasDerivAt (fun t => z t i) (w i) x)
    (hpos : ∀ i, 0 ≤ z x i) (hZ : 0 < ∑ i, z x i) :
    HasDerivAt (fun t => dualSlope L₀ L₁ (z t) w) (dualCurvature L₀ L₁ (z x) w) x := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hz i)
  have hr := ((radial_second_derivative L₀ L₁ _ hL₀ hL₁ hZ.le).comp x hsum).const_mul (2 * ∑ i, w i)
  have hp (i : Fin m) := perspective_slope_derivative L₁ (1 / Real.sqrt m) hL₁
    (by positivity) hsum (hz i) hZ (hpos i)
  have hh := hr.add (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hp i))
  convert hh using 1
  · rfl
  · unfold dualCurvature
    ring

lemma coordinate_curvature_lower (L₀ L₁ Z r p c : ℝ)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 < L₁) (hZ : 0 < Z) (hr : 0 < r)
    (hpc : 0 < p + c) (hbound : p + c ≤ 2 * r) :
    2 / (L₀ + L₁ * Z * r) ≤ (4 / (L₁ * (p + c))) / Z := by
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 2 * L₁ * Z by positivity)
  nlinarith only [hh, hL₀]

lemma dualCurvature_lower {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (z w : EuclideanSpace ℝ (Fin m))
    (hz : ∀ i, 0 ≤ z i) (hZ : 0 < ∑ i, z i) :
    ‖w‖ ^ 2 / (L₀ + L₁ * ‖z‖) ≤ dualCurvature L₀ L₁ z w := by
  let Z := ∑ i, z i
  let b := ∑ i, w i
  let p : EuclideanSpace ℝ (Fin m) := Z⁻¹ • z
  have hZ' : 0 < Z := hZ
  have hpi (i : Fin m) : p i = z i / Z := by simp [p, div_eq_mul_inv, mul_comm]
  have hp : ∀ i, 0 ≤ p i := fun i => by rw [hpi]; exact div_nonneg (hz i) hZ.le
  have hpsum : ∑ i, p i = 1 := by
    simp only [hpi, ← Finset.sum_div]
    exact div_self hZ.ne'
  have hpn : 0 < ‖p‖ := lt_of_lt_of_le (by positivity : 0 < 1 / Real.sqrt m)
    (simplex_norm_lower hm p hpsum)
  have hpone : ‖p‖ ≤ 1 := (nonnegative_norm_le_sum p hp).trans_eq hpsum
  have hn : ‖z‖ = Z * ‖p‖ := by
    simp only [p, norm_smul, norm_inv, Real.norm_of_nonneg hZ'.le]
    field_simp
  let D := L₀ + L₁ * ‖z‖
  have hD : 0 < D := by dsimp [D]; positivity
  have hcoeff (i : Fin m) : 2 / D ≤ (4 / (L₁ * (p i + 1 / Real.sqrt m))) / Z := by
    dsimp [D]
    rw [hn]
    simpa only [mul_assoc] using coordinate_curvature_lower L₀ L₁ Z ‖p‖ (p i) (1 / Real.sqrt m)
      hL₀.le hL₁ hZ hpn (add_pos_of_nonneg_of_pos (hp i) (by positivity)) (simplex_coordinate_bound hm p hpsum i)
  have hr := mul_le_mul_of_nonneg_left
    (radial_coefficient_bound L₀ L₁ Z ‖p‖ hL₀ hL₁.le hZ.le hpn.le hpone)
    (show 0 ≤ 2 * b ^ 2 by positivity)
  have hrad : 2 * ‖b • p‖ ^ 2 / D ≤ 2 * b ^ 2 / (L₀ + L₁ * Z) := by
    dsimp [D]
    rw [hn]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    convert hr using 1 <;> ring
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hcoeff i) (sq_nonneg (w i - b * p i)))
  have hsum : 2 * ‖w - b • p‖ ^ 2 / D ≤
      ∑ i, 4 / (L₁ * (z i / Z + 1 / Real.sqrt m)) * (w i - b * (z i / Z)) ^ 2 / Z := by
    have he : (∑ i, (2 / D) * (w i - b * p i) ^ 2) = 2 * ‖w - b • p‖ ^ 2 / D := by
      rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [he] at hs
    simpa only [hpi, div_mul_eq_mul_div] using hs
  have hnw := decomposition_norm_sq (b • p) (w - b • p)
  rw [add_sub_cancel] at hnw
  have hd := div_le_div_of_nonneg_right hnw hD.le
  change ‖w‖ ^ 2 / D ≤ _
  unfold dualCurvature
  change ‖w‖ ^ 2 / D ≤ 2 * b ^ 2 / (L₀ + L₁ * Z) + _
  rw [add_div] at hd
  linarith

end LongTails.Proofs.GeneralizedSmoothHardDual
