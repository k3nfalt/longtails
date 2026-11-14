import Mathlib.Tactic
import LongTails.Setups.RipmGeneral
import LongTails.Proofs.CompositeProx
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Instances.RealVectorSpace

open MeasureTheory
open LongTails.Setups.RipmGeneral

namespace LongTails.Proofs.RipmProxGeometry

noncomputable section

lemma prox_exists {d : ℕ} (q : Core.Vec d → ℝ) (a Lq : ℝ)
    (ha : 0 < a) (hLq : 0 ≤ Lq) (hq : ConvexOn ℝ Set.univ q)
    (hlip : ∀ x y, |q x - q y| ≤ Lq * ‖x - y‖) (y : Core.Vec d) :
    ∃ u, IsMinOn (Core.proxObjective q a y) Set.univ u := by
  classical
  have hqc : Continuous q :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hq)
  have hcont : Continuous (Core.proxObjective q a y) := by
    change Continuous (fun u => a * q u + ‖u - y‖ ^ 2 / 2)
    fun_prop
  let R := 2 * a * Lq + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨u, hu, hmin⟩ := (isCompact_closedBall y R).exists_isMinOn
    (show (Metric.closedBall y R).Nonempty from
      ⟨y, Metric.mem_closedBall.mpr (by simpa using hR.le)⟩) hcont.continuousOn
  refine ⟨u, fun x _ => ?_⟩
  by_cases hx : x ∈ Metric.closedBall y R
  · exact hmin hx
  · have hy : y ∈ Metric.closedBall y R :=
      Metric.mem_closedBall.mpr (by simpa using hR.le)
    have hmy := hmin hy
    have hdist : R < ‖x - y‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hx
    have hqxy := (abs_le.mp (hlip x y)).1
    have hmul := mul_le_mul_of_nonneg_left hqxy ha.le
    have hs : 0 ≤ ‖x - y‖ * (‖x - y‖ - 2 * a * Lq) := by
      apply mul_nonneg (norm_nonneg _)
      dsimp [R] at hdist
      linarith
    change a * q u + ‖u - y‖ ^ 2 / 2 ≤ a * q x + ‖x - y‖ ^ 2 / 2
    change a * q u + ‖u - y‖ ^ 2 / 2 ≤ a * q y + ‖y - y‖ ^ 2 / 2 at hmy
    norm_num only [sub_self, norm_zero, zero_pow, zero_div, add_zero] at hmy
    nlinarith


lemma prox_minimizes {d : ℕ} (q : Core.Vec d → ℝ) (a Lq : ℝ)
    (ha : 0 < a) (hLq : 0 ≤ Lq) (hq : ConvexOn ℝ Set.univ q)
    (hlip : ∀ x y, |q x - q y| ≤ Lq * ‖x - y‖) (y : Core.Vec d) :
    IsMinOn (Core.proxObjective q a y) Set.univ (Core.prox q a y) := by
  classical
  have hex := prox_exists q a Lq ha hLq hq hlip y
  change IsMinOn (Core.proxObjective q a y) Set.univ
    (if h : ∃ u, IsMinOn (Core.proxObjective q a y) Set.univ u then
      Classical.choose h else 0)
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex


lemma prox_iff {d : ℕ} (q : Core.Vec d → ℝ) (a Lq : ℝ)
    (ha : 0 < a) (hLq : 0 ≤ Lq) (hq : ConvexOn ℝ Set.univ q)
    (hlip : ∀ x y, |q x - q y| ≤ Lq * ‖x - y‖) (y u : Core.Vec d) :
    u = Core.prox q a y ↔ ∀ x, a * (q u - q x) ≤ inner ℝ (u - y) (x - u) := by
  classical
  have hvi (v : Core.Vec d)
      (hv : IsMinOn (Core.proxObjective q a y) Set.univ v) :
      ∀ x, a * (q v - q x) ≤ inner ℝ (v - y) (x - v) := by
    have heq (x : Core.Vec d) :
        OracleTemplate.Composite.proxObjective q a y 0 x =
          Core.proxObjective q a y x / a := by
      change ‖x - y‖ ^ 2 / (2 * a) + inner ℝ (0 : Core.Vec d) (x - y) + q x =
        (a * q x + ‖x - y‖ ^ 2 / 2) / a
      simp only [inner_zero_left, add_zero]
      field_simp [ha.ne']
      ring
    have hv' : IsMinOn (OracleTemplate.Composite.proxObjective q a y 0) Set.univ v := by
      intro x hx
      change OracleTemplate.Composite.proxObjective q a y 0 v ≤
        OracleTemplate.Composite.proxObjective q a y 0 x
      rw [heq v, heq x]
      exact div_le_div_of_nonneg_right (hv hx) ha.le
    intro x
    have hp := OracleTemplate.Composite.prox_three_point ha
      (strongConvexOn_zero.mpr hq) hv' x
    simp only [inner_zero_left, zero_add, mul_zero, add_zero, one_div] at hp
    have he : y - x = -((v - y) + (x - v)) := by module
    rw [he, norm_neg, norm_add_sq_real, norm_sub_rev v x] at hp
    nlinarith
  have hv := hvi (Core.prox q a y) (prox_minimizes q a Lq ha hLq hq hlip y)
  constructor
  · intro hu
    subst u
    exact hv
  · intro hu
    let v := Core.prox q a y
    have h1 := hu v
    have h2 := hv u
    change a * (q v - q u) ≤ inner ℝ (v - y) (u - v) at h2
    rw [show v - u = -(u - v) by module, inner_neg_right] at h1
    have hn : ‖u - v‖ ^ 2 =
        inner ℝ (u - y) (u - v) - inner ℝ (v - y) (u - v) := by
      rw [← inner_sub_left, show u - y - (v - y) = u - v by module,
        real_inner_self_eq_norm_sq]
    have hz : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)


lemma prox_unique {d : ℕ} (q : Core.Vec d → ℝ) (a Lq : ℝ)
    (ha : 0 < a) (hLq : 0 ≤ Lq) (hq : ConvexOn ℝ Set.univ q)
    (hlip : ∀ x y, |q x - q y| ≤ Lq * ‖x - y‖) (y u : Core.Vec d)
    (hu : IsMinOn (Core.proxObjective q a y) Set.univ u) :
    u = Core.prox q a y := by
  classical
  let v := Core.prox q a y
  have heq (x : Core.Vec d) :
      OracleTemplate.Composite.proxObjective q a y 0 x =
        Core.proxObjective q a y x / a := by
    change ‖x - y‖ ^ 2 / (2 * a) + inner ℝ (0 : Core.Vec d) (x - y) + q x =
      (a * q x + ‖x - y‖ ^ 2 / 2) / a
    simp only [inner_zero_left, add_zero]
    field_simp [ha.ne']
    ring
  have hu' : IsMinOn (OracleTemplate.Composite.proxObjective q a y 0) Set.univ u := by
    intro x hx
    change OracleTemplate.Composite.proxObjective q a y 0 u ≤
      OracleTemplate.Composite.proxObjective q a y 0 x
    rw [heq u, heq x]
    exact div_le_div_of_nonneg_right (hu hx) ha.le
  have hv := prox_minimizes q a Lq ha hLq hq hlip y
  have hv' : OracleTemplate.Composite.proxObjective q a y 0 v ≤
      OracleTemplate.Composite.proxObjective q a y 0 u := by
    rw [heq v, heq u]
    exact div_le_div_of_nonneg_right (hv (Set.mem_univ u)) ha.le
  have hb := OracleTemplate.Composite.strong_minimum_bound
    (OracleTemplate.Composite.prox_strong (strongConvexOn_zero.mpr hq) y 0) hu' v
  have hc : 0 < (1 / a + 0) / 2 := by positivity
  have hz : ‖v - u‖ ^ 2 ≤ 0 := by nlinarith
  have hn : ‖v - u‖ = 0 := by nlinarith [norm_nonneg (v - u)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm


lemma prox_nonexpansive {d : ℕ} (q : Core.Vec d → ℝ) (a Lq : ℝ)
    (ha : 0 < a) (hLq : 0 ≤ Lq) (hq : ConvexOn ℝ Set.univ q)
    (hlip : ∀ x y, |q x - q y| ≤ Lq * ‖x - y‖) (x y : Core.Vec d) :
    ‖Core.prox q a x - Core.prox q a y‖ ≤ ‖x - y‖ := by
  let u := Core.prox q a x
  let v := Core.prox q a y
  have h1 := (prox_iff q a Lq ha hLq hq hlip x u).mp rfl v
  have h2 := (prox_iff q a Lq ha hLq hq hlip y v).mp rfl u
  rw [show v - u = -(u - v) by module, inner_neg_right] at h1
  have hid : ‖u - v‖ ^ 2 =
      inner ℝ (u - x) (u - v) - inner ℝ (v - y) (u - v) +
        inner ℝ (x - y) (u - v) := by
    rw [← inner_sub_left, ← inner_add_left,
      show u - x - (v - y) + (x - y) = u - v by module,
      real_inner_self_eq_norm_sq]
  have hc := real_inner_le_norm (x - y) (u - v)
  change ‖u - v‖ ≤ ‖x - y‖
  nlinarith [norm_nonneg (u - v), norm_nonneg (x - y)]


lemma prox_displacement {d : ℕ} (q : Core.Vec d → ℝ) (a Lq : ℝ)
    (ha : 0 < a) (hLq : 0 ≤ Lq) (hq : ConvexOn ℝ Set.univ q)
    (hlip : ∀ x y, |q x - q y| ≤ Lq * ‖x - y‖) (y : Core.Vec d) :
    ‖Core.prox q a y - y‖ ≤ a * Lq := by
  let u := Core.prox q a y
  have hv := (prox_iff q a Lq ha hLq hq hlip y u).mp rfl y
  rw [show y - u = -(u - y) by module, inner_neg_right,
    real_inner_self_eq_norm_sq] at hv
  have hl := (abs_le.mp (hlip u y)).1
  have hm := mul_le_mul_of_nonneg_left hl ha.le
  change ‖u - y‖ ≤ a * Lq
  by_contra h
  have hlt : a * Lq < ‖u - y‖ := lt_of_not_ge h
  have hnpos : 0 < ‖u - y‖ := lt_of_le_of_lt (mul_nonneg ha.le hLq) hlt
  have hmul := mul_lt_mul_of_pos_right hlt hnpos
  nlinarith only [hv, hm, hmul]


end

end LongTails.Proofs.RipmProxGeometry
