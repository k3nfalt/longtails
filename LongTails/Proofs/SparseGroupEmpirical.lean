import LongTails.Proofs.SparseGroupGeometry
import LongTails.Proofs.SparseConfidenceProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Proofs.SparseGroupEmpirical

open LongTails.Setups.OptimumGapGroupDro LongTails.Algorithms.SparseGroupSampling

noncomputable def empirical (q : Public) (ω : Reservoir q) (i : Fin q.K) (n : ℕ)
    (x : Space q.d) : ℝ := (∑ k ∈ Finset.range n, q.loss x (ω k i)) / n

noncomputable def upperRisk (q : Public) (ω : Reservoir q) (counts : Fin q.K → ℕ)
    (i : Fin q.K) (x : Space q.d) : ℝ :=
  empirical q ω i (counts i) x + radius q (counts i)

lemma empirical_zero (q : Public) (ω : Reservoir q) (i : Fin q.K) (x : Space q.d) :
    empirical q ω i 0 x = 0 := by simp [empirical]

lemma empirical_bounds (q : Public) (ω : Reservoir q) (i : Fin q.K) (n : ℕ)
    {x : Space q.d} (hx : x ∈ q.domain)
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1) :
    0 ≤ empirical q ω i n x ∧ empirical q ω i n x ≤ 1 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun k _ => (hb (ω k i) x hx).1)) (Nat.cast_nonneg n)
  · by_cases hn : n = 0
    · simp [hn, empirical]
    · have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      unfold empirical
      apply (div_le_iff₀ hpos).mpr
      calc
        _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => (hb (ω k i) x hx).2)
        _ = _ := by simp

lemma empirical_lipschitz (q : Public) (ω : Reservoir q) (i : Fin q.K) (n : ℕ)
    (hG : 0 ≤ q.G)
    (hl : ∀ z, ∀ x ∈ q.domain, ∀ y ∈ q.domain,
      |q.loss x z - q.loss y z| ≤ q.G * ‖x - y‖)
    {x y : Space q.d} (hx : x ∈ q.domain) (hy : y ∈ q.domain) :
    |empirical q ω i n x - empirical q ω i n y| ≤ q.G * dist x y := by
  by_cases hn : n = 0
  · simp only [hn, empirical_zero, sub_self, abs_zero]
    exact mul_nonneg hG dist_nonneg
  have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  unfold empirical
  rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n, |q.loss x (ω k i) - q.loss y (ω k i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, q.G * ‖x - y‖ :=
      Finset.sum_le_sum (fun k _ => hl (ω k i) x hx y hy)
    _ = _ := by simp [dist_eq_norm, mul_comm]

lemma empirical_convex (q : Public) (ω : Reservoir q) (i : Fin q.K) (n : ℕ)
    (hQ : Convex ℝ q.domain)
    (hc : ∀ z, ConvexOn ℝ q.domain (fun x => q.loss x z)) :
    ConvexOn ℝ q.domain (empirical q ω i n) := by
  refine ⟨hQ, ?_⟩
  intro x hx y hy a b ha hb hab
  change (∑ k ∈ Finset.range n, q.loss (a • x + b • y) (ω k i)) / n ≤
    a * ((∑ k ∈ Finset.range n, q.loss x (ω k i)) / n) +
    b * ((∑ k ∈ Finset.range n, q.loss y (ω k i)) / n)
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun k _ => (hc (ω k i)).2 hx hy ha hb hab)
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simp only [smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hd
  convert hd using 1
  ring

lemma upperRisk_convex (q : Public) (ω : Reservoir q) (counts : Fin q.K → ℕ)
    (i : Fin q.K) (hQ : Convex ℝ q.domain)
    (hc : ∀ z, ConvexOn ℝ q.domain (fun x => q.loss x z)) :
    ConvexOn ℝ q.domain (upperRisk q ω counts i) :=
  (empirical_convex q ω i (counts i) hQ hc).add_const _

lemma upperRisk_lipschitz (q : Public) (ω : Reservoir q) (counts : Fin q.K → ℕ)
    (i : Fin q.K) (hG : 0 ≤ q.G)
    (hl : ∀ z, ∀ x ∈ q.domain, ∀ y ∈ q.domain,
      |q.loss x z - q.loss y z| ≤ q.G * ‖x - y‖)
    {x y : Space q.d} (hx : x ∈ q.domain) (hy : y ∈ q.domain) :
    |upperRisk q ω counts i x - upperRisk q ω counts i y| ≤ q.G * dist x y := by
  simpa only [upperRisk, add_sub_add_right_eq_sub] using empirical_lipschitz q ω i (counts i) hG hl hx hy

lemma radius_nonneg (q : Public) (n : ℕ) : 0 ≤ radius q n := by
  unfold radius
  split_ifs
  · norm_num
  · exact le_min (by norm_num) (Real.sqrt_nonneg _)

lemma radius_le_one (q : Public) (n : ℕ) : radius q n ≤ 1 := by
  unfold radius
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma upperRisk_bounds (q : Public) (ω : Reservoir q) (counts : Fin q.K → ℕ)
    (i : Fin q.K) {x : Space q.d} (hx : x ∈ q.domain)
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1) :
    0 ≤ upperRisk q ω counts i x ∧ upperRisk q ω counts i x ≤ 2 := by
  have he := empirical_bounds q ω i (counts i) hx hb
  have hr := radius_nonneg q (counts i)
  have hr' := radius_le_one q (counts i)
  unfold upperRisk
  constructor <;> linarith

lemma loss_integrable (q : Public) (p : ProbabilityMeasure (Rows q)) (i : Fin q.K)
    {x : Space q.d} (hx : x ∈ q.domain)
    (hm : Measurable (Function.uncurry q.loss))
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1) :
    Integrable (fun z : Rows q => q.loss x (z i)) (p : Measure _) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (hm.comp (measurable_const.prodMk (measurable_pi_apply i))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (hb (z i) x hx).1]
    exact (hb (z i) x hx).2

lemma risk_bounds (q : Public) (p : ProbabilityMeasure (Rows q)) (i : Fin q.K)
    {x : Space q.d} (hx : x ∈ q.domain)
    (hm : Measurable (Function.uncurry q.loss))
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1) :
    0 ≤ risk q p i x ∧ risk q p i x ≤ 1 := by
  constructor
  · exact integral_nonneg (fun z => (hb (z i) x hx).1)
  · have h := integral_mono (loss_integrable q p i hx hm hb) (integrable_const (1 : ℝ))
      (fun z => (hb (z i) x hx).2)
    simpa [risk] using h

lemma risk_lipschitz (q : Public) (p : ProbabilityMeasure (Rows q)) (i : Fin q.K)
    (hm : Measurable (Function.uncurry q.loss))
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1)
    (hl : ∀ z, ∀ x ∈ q.domain, ∀ y ∈ q.domain,
      |q.loss x z - q.loss y z| ≤ q.G * ‖x - y‖)
    {x y : Space q.d} (hx : x ∈ q.domain) (hy : y ∈ q.domain) :
    |risk q p i x - risk q p i y| ≤ q.G * dist x y := by
  have hix := loss_integrable q p i hx hm hb
  have hiy := loss_integrable q p i hy hm hb
  unfold risk
  rw [← integral_sub hix hiy]
  calc
    _ ≤ ∫ z : Rows q, |q.loss x (z i) - q.loss y (z i)| ∂(p : Measure _) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _z : Rows q, q.G * ‖x - y‖ ∂(p : Measure _) :=
      integral_mono (hix.sub hiy).abs (integrable_const _) (fun z => hl (z i) x hx y hy)
    _ = _ := by simp [dist_eq_norm]

lemma confidence_extension (q : Public) (p : ProbabilityMeasure (Rows q))
    (ω : Reservoir q) (counts : Fin q.K → ℕ) (hε : 0 < q.ε) (hG : 0 ≤ q.G)
    (hx0 : q.x0 ∈ q.domain) (hbound : ∀ x ∈ q.domain, ‖x - q.x0‖ ≤ q.R)
    (hm : Measurable (Function.uncurry q.loss))
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1)
    (hl : ∀ z, ∀ x ∈ q.domain, ∀ y ∈ q.domain,
      |q.loss x z - q.loss y z| ≤ q.G * ‖x - y‖)
    (hconf : ∀ i, ∀ h : PrimalIndex q,
      |empirical q ω i (counts i) h.val - risk q p i h.val| ≤ radius q (counts i))
    (i : Fin q.K) {x : Space q.d} (hx : x ∈ q.domain) :
    upperRisk q ω counts i x ≤ risk q p i x + 2 * radius q (counts i) +
      2 * q.G * ((q.d + 1 : ℝ) * coordinateScale q) := by
  have hmesh := SparseGroupGeometry.primalMesh_valid q hε hG hx0 hbound
  obtain ⟨y, hy, hdist⟩ := hmesh.2.2.2 x hx
  have hyQ := hmesh.2.2.1 y hy
  have he := empirical_lipschitz q ω i (counts i) hG hl hx hyQ
  have hr := risk_lipschitz q p i hm hb hl hx hyQ
  have hc := hconf i ⟨y, hy⟩
  have hmul := mul_le_mul_of_nonneg_left hdist hG
  have he' := le_abs_self (empirical q ω i (counts i) x - empirical q ω i (counts i) y)
  have hr' := neg_le_abs (risk q p i x - risk q p i y)
  have hc' := le_abs_self (empirical q ω i (counts i) y - risk q p i y)
  change |empirical q ω i (counts i) y - risk q p i y| ≤ _ at hc
  unfold upperRisk
  linarith

end LongTails.Proofs.SparseGroupEmpirical
