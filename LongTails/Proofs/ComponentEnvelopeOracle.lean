import LongTails.Proofs.ComponentEnvelopeStopping
import Mathlib.Analysis.Complex.ExponentialBounds
open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators
namespace OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry
open LongTails.Setups.InterpolatedGeneralizedFiniteSum

lemma smoothing_pos (p : Params) (h0 : 0 < p.L0) (he : 0 < p.ε) : 0 < smoothing p := by
  dsimp [smoothing]
  positivity

lemma smoothing_ge (p : Params) (he : 0 ≤ p.ε) : p.L0 ≤ smoothing p := by
  dsimp [smoothing]
  have hh : 0 ≤ 8 * (p.n : ℝ) * p.L1 ^ 2 * p.ε := by positivity
  linarith

lemma tolerance_pos (p : Params) (h0 : 0 < p.L0) (he : 0 < p.ε) (hR : 0 < p.R) :
    0 < tolerance p := by
  have hm := smoothing_pos p h0 he
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  dsimp [tolerance]
  positivity

lemma inner_log_ge_one {L R μ ζ : ℝ} (hL : 0 ≤ L) (hR : 0 < R)
    (hμ : 0 < μ) (hζ : 0 < ζ) :
    1 ≤ Real.log (4 + L * R + μ * R * (1 + L * R) / ζ) := by
  have hA : 4 ≤ 4 + L * R + μ * R * (1 + L * R) / ζ := by
    have hh : 0 ≤ μ * R * (1 + L * R) / ζ := by positivity
    linarith [mul_nonneg hL hR.le]
  have hpos : 0 < 4 + L * R + μ * R * (1 + L * R) / ζ := by linarith
  apply (Real.le_log_iff_exp_le hpos).mpr
  linarith [Real.exp_one_lt_three]

lemma componentPlan_error_cost (p : Params) (I : Instance p) (i : Fin p.n)
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (he : 0 < p.ε) (hR : 0 < p.R)
    (hc : ConvexOn ℝ univ (I.loss i)) (hg : ∀ x, HasGradientAt (I.loss i) (I.grad i x) x)
    (hcont : Continuous (I.grad i))
    (hs : CompositeGeneralized.SymmetricSmooth (I.grad i) p.L0 p.L1)
    (u c : p.E) (hmin : ∀ y, I.loss i u ≤ I.loss i y) (hu : ‖p.x0 - u‖ ≤ p.R)
    (hcball : c ∈ Metric.closedBall p.x0 p.R) :
    ‖Program.eval (fun q => I.grad q.1 q.2) (componentPlan p i c) -
      envelopeField (I.grad i) (smoothing p) c‖ ≤ tolerance p ∧
    (Program.cost (fun q => I.grad q.1 q.2) (componentPlan p i c) : ℝ) ≤
      4096 * Real.log (4 + p.L1 * p.R + smoothing p * p.R * (1 + p.L1 * p.R) / tolerance p) *
        (1 + (p.L1 * ‖c - prox (I.grad i) (smoothing p) c‖) ^ 2) := by
  have hμ := smoothing_pos p h0 he
  have hζ := tolerance_pos p h0 he hR
  have hprox := component_prox_distance hc hg hμ hmin c
  have hcu : ‖c - u‖ ≤ 2 * p.R := by
    have hc' : ‖c - p.x0‖ ≤ p.R := by simpa [dist_eq_norm] using hcball
    have ht := norm_add_le (c - p.x0) (p.x0 - u)
    rw [show c - p.x0 + (p.x0 - u) = c - u by module] at ht
    linarith
  have hd := hprox.trans hcu
  have hell := inner_log_ge_one h1 hR hμ hζ
  apply component_innerPlan_error_cost I.loss I.grad i h0 h1 hμ (smoothing_ge p he.le)
    hR hζ hc hg hcont hs hmin c hd (innerFuel p) hell
  have hq := mul_le_mul_of_nonneg_left hd h1
  have hq2 := pow_le_pow_left₀ (by positivity : 0 ≤ p.L1 * ‖c - prox (I.grad i) (smoothing p) c‖) hq 2
  have hlog : 0 ≤ Real.log (4 + p.L1 * p.R + smoothing p * p.R * (1 + p.L1 * p.R) / tolerance p) := by linarith
  apply le_trans _ (Nat.le_ceil _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith
lemma tolerance_identity (p : Params) :
    1048576 * (p.n : ℝ) * ((epochCount p : ℝ) + 4) ^ 3 * tolerance p = smoothing p * p.R := by
  have hn : (p.n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.n)
  have hS : (epochCount p : ℝ) + 4 ≠ 0 := by positivity
  dsimp [tolerance]
  field_simp

lemma tolerance_warmup (p : Params) (h0 : 0 < p.L0) (he : 0 < p.ε) (hR : 0 < p.R) :
    8 * (p.n : ℝ) * tolerance p ≤ smoothing p * p.R := by
  have hζ := tolerance_pos p h0 he hR
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hS : 1 ≤ ((epochCount p : ℝ) + 4) ^ 3 := by
    have h : 0 ≤ (epochCount p : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (epochCount p : ℝ)]
  have hden : 8 * (p.n : ℝ) ≤ 1048576 * (p.n : ℝ) * ((epochCount p : ℝ) + 4) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hS hn.le
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hden hζ.le
  rw [tolerance_identity] at hh
  exact hh

lemma tolerance_total_error (p : Params) :
    (p.n : ℝ) * (4 * p.R * tolerance p) * ((epochCount p : ℝ) + 4) ^ 3 / 4 =
      smoothing p * p.R ^ 2 / 1048576 := by
  have h := congrArg (fun x : ℝ => x * p.R / 1048576) (tolerance_identity p)
  nlinarith only [h]

lemma epoch_count_positive (p : Params) (h0 : 0 < p.L0) (he : 0 < p.ε) (hR : 0 < p.R) :
    0 < epochCount p := by
  have hμ := smoothing_pos p h0 he
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  apply Nat.ceil_pos.mpr
  apply Real.sqrt_pos.mpr
  positivity

lemma epoch_count_accuracy (p : Params) (h0 : 0 < p.L0) (he : 0 < p.ε) (hR : 0 < p.R) :
    120 * smoothing p * p.R ^ 2 / ((p.n : ℝ) * ((epochCount p : ℝ) + 3) ^ 2) ≤ p.ε / 60 := by
  have hμ := smoothing_pos p h0 he
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have ha : 0 ≤ 7200 * smoothing p * p.R ^ 2 / ((p.n : ℝ) * p.ε) := by positivity
  have hc : Real.sqrt (7200 * smoothing p * p.R ^ 2 / ((p.n : ℝ) * p.ε)) ≤ (epochCount p : ℝ) := Nat.le_ceil _
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc 2
  rw [Real.sq_sqrt ha] at hs
  have hden : 0 < (p.n : ℝ) * ((epochCount p : ℝ) + 3) ^ 2 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hsq := (div_le_iff₀ (mul_pos hn he)).mp hs
  have hS : 0 ≤ (epochCount p : ℝ) := Nat.cast_nonneg _
  have hprod : 0 ≤ (p.n : ℝ) * p.ε * (6 * (epochCount p : ℝ) + 9) := by positivity
  nlinarith


lemma componentPlan_gap_cost (p : Params) (I : Instance p) (i : Fin p.n)
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (he : 0 < p.ε) (hR : 0 < p.R)
    (hc : ConvexOn ℝ univ (I.loss i)) (hg : ∀ x, HasGradientAt (I.loss i) (I.grad i x) x)
    (hcont : Continuous (I.grad i))
    (hs : CompositeGeneralized.SymmetricSmooth (I.grad i) p.L0 p.L1)
    (u c : p.E) (hmin : ∀ y, I.loss i u ≤ I.loss i y) (hu : ‖p.x0 - u‖ ≤ p.R)
    (hcball : c ∈ Metric.closedBall p.x0 p.R) :
    (Program.cost (fun q => I.grad q.1 q.2) (componentPlan p i c) : ℝ) ≤
      4096 * Real.log (4 + p.L1 * p.R + smoothing p * p.R * (1 + p.L1 * p.R) / tolerance p) *
        (1 + (2 * p.L1 ^ 2 / smoothing p) *
          (envelope (I.loss i) (I.grad i) (smoothing p) c - I.loss i u)) := by
  have hμ := smoothing_pos p h0 he
  have hζ := tolerance_pos p h0 he hR
  have hell := inner_log_ge_one h1 hR hμ hζ
  have hcost := (componentPlan_error_cost p I i h0 h1 he hR hc hg hcont hs u c hmin hu hcball).2
  have hgap := component_displacement_gap (g := I.grad i) (μ := smoothing p) hmin c
  have hmul := mul_le_mul_of_nonneg_left hgap (sq_nonneg p.L1)
  have hq : (p.L1 * ‖c - prox (I.grad i) (smoothing p) c‖) ^ 2 ≤
      (2 * p.L1 ^ 2 / smoothing p) * (envelope (I.loss i) (I.grad i) (smoothing p) c - I.loss i u) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hμ).mpr
    nlinarith
  exact hcost.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hq) (by linarith))

lemma componentPlan_uniform_cost (p : Params) (I : Instance p) (i : Fin p.n)
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (he : 0 < p.ε) (hR : 0 < p.R)
    (hc : ConvexOn ℝ univ (I.loss i)) (hg : ∀ x, HasGradientAt (I.loss i) (I.grad i x) x)
    (hcont : Continuous (I.grad i))
    (hs : CompositeGeneralized.SymmetricSmooth (I.grad i) p.L0 p.L1)
    (u c : p.E) (hmin : ∀ y, I.loss i u ≤ I.loss i y) (hu : ‖p.x0 - u‖ ≤ p.R)
    (hcball : c ∈ Metric.closedBall p.x0 p.R) :
    (Program.cost (fun q => I.grad q.1 q.2) (componentPlan p i c) : ℝ) ≤
      4096 * Real.log (4 + p.L1 * p.R + smoothing p * p.R * (1 + p.L1 * p.R) / tolerance p) *
        (1 + 4 * p.L1 ^ 2 * p.R ^ 2) := by
  have hμ := smoothing_pos p h0 he
  have hζ := tolerance_pos p h0 he hR
  have hell := inner_log_ge_one h1 hR hμ hζ
  have hcost := (componentPlan_error_cost p I i h0 h1 he hR hc hg hcont hs u c hmin hu hcball).2
  have hprox := component_prox_distance hc hg hμ hmin c
  have hcu : ‖c - u‖ ≤ 2 * p.R := by
    have hc' : ‖c - p.x0‖ ≤ p.R := by simpa [dist_eq_norm] using hcball
    have ht := norm_add_le (c - p.x0) (p.x0 - u)
    rw [show c - p.x0 + (p.x0 - u) = c - u by module] at ht
    linarith
  have hq := mul_le_mul_of_nonneg_left (hprox.trans hcu) h1
  have hq2 := pow_le_pow_left₀ (by positivity : 0 ≤ p.L1 * ‖c - prox (I.grad i) (smoothing p) c‖) hq 2
  apply hcost.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  nlinarith

lemma tolerance_cost_error (p : Params) (hμ : 0 < smoothing p) :
    (2 * p.L1 ^ 2 / smoothing p) * (4 * p.R * tolerance p) * epochCount p ≤ (p.L1 * p.R) ^ 2 := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast (NeZero.pos p.n)
  have hS : 0 ≤ (epochCount p : ℝ) := Nat.cast_nonneg _
  have hden : 0 < 1048576 * (p.n : ℝ) * ((epochCount p : ℝ) + 4) ^ 3 := by positivity
  have hpoly : 8 * (epochCount p : ℝ) ≤ 1048576 * (p.n : ℝ) * ((epochCount p : ℝ) + 4) ^ 3 := by
    have hcube : 8 * (epochCount p : ℝ) ≤ 1048576 * ((epochCount p : ℝ) + 4) ^ 3 := by
      have hc : 0 ≤ (epochCount p : ℝ) ^ 3 := by positivity
      nlinarith [sq_nonneg (epochCount p : ℝ)]
    have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ 1048576 * ((epochCount p : ℝ) + 4) ^ 3 by positivity)
    nlinarith
  have hident : (2 * p.L1 ^ 2 / smoothing p) * (4 * p.R * tolerance p) * epochCount p =
      (p.L1 * p.R) ^ 2 * (8 * (epochCount p : ℝ)) /
        (1048576 * (p.n : ℝ) * ((epochCount p : ℝ) + 4) ^ 3) := by
    dsimp [tolerance]
    field_simp
    ring
  rw [hident]
  apply (div_le_iff₀ hden).mpr
  exact mul_le_mul_of_nonneg_left hpoly (sq_nonneg (p.L1 * p.R))

end OracleTemplate.ComponentEnvelope
