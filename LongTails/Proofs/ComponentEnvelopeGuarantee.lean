import LongTails.Proofs.ComponentEnvelopeRate
open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators
namespace OracleTemplate.ComponentEnvelope
open LongTails.Setups.InterpolatedGeneralizedFiniteSum
open LongTails.Proofs.RecursiveEnvelopeGeometry
lemma finiteSum_gap_transfer (p : Params) (I : Instance p)
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (he : 0 < p.ε)
    (hc : ∀ i, ConvexOn ℝ univ (I.loss i)) (hg : ∀ i x, HasGradientAt (I.loss i) (I.grad i x) x)
    (hcont : ∀ i, Continuous (I.grad i))
    (hs : ∀ i, CompositeGeneralized.SymmetricSmooth (I.grad i) p.L0 p.L1)
    (u c : p.E) (hmin : ∀ i y, I.loss i u ≤ I.loss i y)
    (hgap : LongTails.Setups.FiniteSumSmoothAndConvex.objective
      (fun i => envelope (I.loss i) (I.grad i) (smoothing p)) c -
        LongTails.Setups.FiniteSumSmoothAndConvex.objective
          (fun i => envelope (I.loss i) (I.grad i) (smoothing p)) u ≤ p.ε / 5) :
    objective I c - objective I u ≤ p.ε := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective
    (fun i => envelope (I.loss i) (I.grad i) (smoothing p))
  let a := fun i => envelope (I.loss i) (I.grad i) (smoothing p) c - I.loss i u
  have hμ := smoothing_pos p h0 he
  have hnu : (p.n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.n)
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have henv i := (component_envelope_at_minimum (hc i) (hg i) hμ (hmin i)).1
  have ha i : 0 ≤ a i := by
    have hh := component_displacement_gap (g := I.grad i) (μ := smoothing p) (hmin i) c
    exact le_trans (by positivity) hh
  have hsum : (∑ i, a i) = (p.n : ℝ) * (H c - H u) := by
    dsimp [a, H, LongTails.Setups.FiniteSumSmoothAndConvex.objective]
    simp_rw [henv]
    rw [Finset.sum_sub_distrib]
    field_simp
  have hi (i : Fin p.n) : a i ≤ (p.n : ℝ) * p.ε := by
    have hsingle := Finset.single_le_sum (s := Finset.univ) (f := a) (fun j _ => ha j) (Finset.mem_univ i)
    rw [hsum] at hsingle
    have hmul := mul_le_mul_of_nonneg_left hgap hn.le
    change _ ≤ (p.n : ℝ) * (p.ε / 5) at hmul
    linarith [mul_pos hn he]
  have hμlower : 8 * (p.n : ℝ) * p.L1 ^ 2 * p.ε ≤ smoothing p := by dsimp [smoothing]; linarith
  have hr (i : Fin p.n) : p.L1 * ‖c - prox (I.grad i) (smoothing p) c‖ ≤ 1 / 2 := by
    have hd := component_displacement_gap (g := I.grad i) (μ := smoothing p) (hmin i) c
    have hb := hd.trans (hi i)
    have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg p.L1)
    have hsquare : (p.L1 * ‖c - prox (I.grad i) (smoothing p) c‖) ^ 2 ≤ 1 / 4 := by
      nlinarith
    nlinarith [sq_nonneg (p.L1 * ‖c - prox (I.grad i) (smoothing p) c‖ - 1 / 2)]
  have ht i := component_gap_transfer h0.le h1 hμ (smoothing_ge p he.le)
    (hg i) (hcont i) (hs i) (hmin i) c (hr i)
  have hav := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ht i)
  change (∑ i, (I.loss i c - I.loss i u)) ≤ ∑ i, 5 * a i at hav
  rw [← Finset.mul_sum, hsum, Finset.sum_sub_distrib] at hav
  have hmul := mul_le_mul_of_nonneg_left hav (inv_nonneg.mpr hn.le)
  change H c - H u ≤ p.ε / 5 at hgap
  dsimp [objective]
  have hid : (p.n : ℝ)⁻¹ * (5 * ((p.n : ℝ) * (H c - H u))) = 5 * (H c - H u) := by field_simp
  rw [hid] at hmul
  nlinarith
lemma instance_plan_accuracy (p : Params) (I : Instance p)
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (he : 0 < p.ε) (hR : 0 < p.R)
    (hc : ∀ i, ConvexOn ℝ univ (I.loss i)) (hg : ∀ i x, HasGradientAt (I.loss i) (I.grad i x) x)
    (hcont : ∀ i, Continuous (I.grad i))
    (hs : ∀ i, CompositeGeneralized.SymmetricSmooth (I.grad i) p.L0 p.L1)
    (u : p.E) (hmin : ∀ i y, I.loss i u ≤ I.loss i y) (hu : ‖p.x0 - u‖ ≤ p.R) :
    let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective
      (fun i => envelope (I.loss i) (I.grad i) (smoothing p))
    (𝔼 seed : Seeds p, H (Program.eval (fun q => I.grad q.1 q.2) (plan p seed))) - H u ≤ p.ε / 60 := by
  have hμ := smoothing_pos p h0 he
  apply model_plan_accuracy p (fun q => I.grad q.1 q.2)
    (fun i => envelope (I.loss i) (I.grad i) (smoothing p))
    (fun q => envelopeField (I.grad q.1) (smoothing p) q.2)
    (fun i => component_envelope_model (hc i) (hg i) hμ (hmin i)) u
    (fun i => (component_envelope_at_minimum (hc i) (hg i) hμ (hmin i)).2) hu
    (fun i x hx => (componentPlan_error_cost p I i h0 h1 he hR (hc i) (hg i) (hcont i) (hs i) u x (hmin i) hu hx).1)
    h0 he hR

lemma instance_plan_cost (p : Params) (I : Instance p)
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (he : 0 < p.ε) (hR : 0 < p.R)
    (hc : ∀ i, ConvexOn ℝ univ (I.loss i)) (hg : ∀ i x, HasGradientAt (I.loss i) (I.grad i x) x)
    (hcont : ∀ i, Continuous (I.grad i))
    (hs : ∀ i, CompositeGeneralized.SymmetricSmooth (I.grad i) p.L0 p.L1)
    (u : p.E) (hmin : ∀ i y, I.loss i u ≤ I.loss i y) (hu : ‖p.x0 - u‖ ≤ p.R) :
    (𝔼 seed : Seeds p, (Program.cost (fun q => I.grad q.1 q.2) (plan p seed) : ℝ)) ≤
      (4096 * Real.log (4 + p.L1 * p.R + smoothing p * p.R * (1 + p.L1 * p.R) / tolerance p)) *
        ((p.n : ℝ) * (4 + 2 * epochCount p) + 752 * p.n * (p.L1 * p.R) ^ 2) := by
  let C := 4096 * Real.log (4 + p.L1 * p.R + smoothing p * p.R * (1 + p.L1 * p.R) / tolerance p)
  let f := fun i => envelope (I.loss i) (I.grad i) (smoothing p)
  let G := fun q : Fin p.n × p.E => envelopeField (I.grad q.1) (smoothing p) q.2
  have hμ := smoothing_pos p h0 he
  have hζ := tolerance_pos p h0 he hR
  have hell := inner_log_ge_one h1 hR hμ hζ
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have henv i := (component_envelope_at_minimum (hc i) (hg i) hμ (hmin i)).1
  apply model_plan_cost p (fun q => I.grad q.1 q.2) f G
    (fun i => component_envelope_model (hc i) (hg i) hμ (hmin i)) u
    (fun i => (component_envelope_at_minimum (hc i) (hg i) hμ (hmin i)).2) hu
    (fun i x hx => (componentPlan_error_cost p I i h0 h1 he hR (hc i) (hg i) (hcont i) (hs i) u x (hmin i) hu hx).1)
    h0 he hR C hC
  · intro x hx
    have hav := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      componentPlan_gap_cost p I i h0 h1 he hR (hc i) (hg i) (hcont i) (hs i) u x (hmin i) hu hx)
    change (𝔼 i : Fin p.n, (Program.cost (fun q => I.grad q.1 q.2) (componentPlan p i x) : ℝ)) ≤
      (𝔼 i : Fin p.n, C * (1 + (2 * p.L1 ^ 2 / smoothing p) * (f i x - I.loss i u))) at hav
    simp_rw [← henv] at hav
    simp only [← Finset.mul_expect, Finset.expect_add_distrib, Finset.expect_sub_distrib, Fintype.expect_const] at hav
    simpa only [← OracleTemplate.FiniteSum.objective_eq_expect, f] using hav
  · intro i x hx
    exact componentPlan_uniform_cost p I i h0 h1 he hR (hc i) (hg i) (hcont i) (hs i) u x (hmin i) hu hx

open MeasureTheory
lemma finite_small_mean_event {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    (hmean : (𝔼 ω, X ω) ≤ 1 / 4) :
    (3 / 4 : ENNReal) ≤ (PMF.uniformOfFintype Ω).toMeasure {ω | X ω < 1} := by
  let P := (PMF.uniformOfFintype Ω).toMeasure
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := P) (Filter.Eventually.of_forall hX)
    (Integrable.of_finite : Integrable X P) 1
  rw [one_mul, OracleTemplate.FiniteSum.uniform_integral] at hm
  have hbad : P {ω | 1 ≤ X ω} ≤ (1 / 4 : ENNReal) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    have h := ENNReal.ofReal_le_ofReal (hm.trans hmean)
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h
  have hmeas : MeasurableSet {ω | 1 ≤ X ω} := (Set.toFinite _).measurableSet
  have heq : {ω | X ω < 1} = {ω | 1 ≤ X ω}ᶜ := by ext ω; simp
  rw [heq, measure_compl hmeas (measure_ne_top _ _), measure_univ]
  calc
    (3 / 4 : ENNReal) = 1 - 1 / 4 := by
      have hh := ENNReal.ofReal_sub (1 : ℝ) (by norm_num : 0 ≤ (1 / 4 : ℝ))
      norm_num only [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hh
      exact hh
    _ ≤ 1 - P {ω | 1 ≤ X ω} := tsub_le_tsub_left hbad 1

lemma finite_accuracy_cost_event {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (F : Ω → ℝ) (N : Ω → ℕ) (ε : ℝ) (K : ℕ)
    (hε : 0 < ε) (hK : 0 < K) (hF : ∀ ω, 0 ≤ F ω)
    (haccuracy : (𝔼 ω, F ω) ≤ ε / 60) (hcost : (𝔼 ω, (N ω : ℝ)) ≤ (K : ℝ) / 6) :
    (3 / 4 : ENNReal) ≤ (PMF.uniformOfFintype Ω).toMeasure {ω | F ω ≤ ε / 5 ∧ N ω ≤ K} := by
  let X := fun ω => 5 * F ω / ε + (N ω : ℝ) / K
  have hKr : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hX ω : 0 ≤ X ω := by
    have hf := hF ω
    dsimp [X]
    positivity
  have hmean : (𝔼 ω, X ω) ≤ 1 / 4 := by
    dsimp [X]
    simp only [Finset.expect_add_distrib, ← Finset.expect_div, ← Finset.mul_expect]
    have ha := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left haccuracy (by norm_num : (0 : ℝ) ≤ 5)) hε.le
    have hb := div_le_div_of_nonneg_right hcost hKr.le
    have hea : (5 * (ε / 60)) / ε = (1 : ℝ) / 12 := by field_simp; ring
    have heb : ((K : ℝ) / 6) / K = (1 : ℝ) / 6 := by field_simp
    rw [hea] at ha
    rw [heb] at hb
    linarith
  have hh := finite_small_mean_event X hX hmean
  apply hh.trans
  apply measure_mono
  intro ω hω
  have hx : X ω < 1 := hω
  have ha : 5 * F ω / ε < 1 := lt_of_le_of_lt
    (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hKr.le)) hx
  have hb : (N ω : ℝ) / K < 1 := lt_of_le_of_lt
    (le_add_of_nonneg_left (div_nonneg (mul_nonneg (by norm_num) (hF ω)) hε.le)) hx
  have har := (div_lt_iff₀ hε).mp ha
  have hbr := (div_lt_iff₀ hKr).mp hb
  constructor
  · linarith
  · have hc : (N ω : ℝ) ≤ K := by linarith
    exact_mod_cast hc

lemma execute_accuracy_probability (p : Params) (I : Instance p)
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (he : 0 < p.ε) (hR : 0 < p.R)
    (hc : ∀ i, ConvexOn ℝ univ (I.loss i)) (hg : ∀ i x, HasGradientAt (I.loss i) (I.grad i x) x)
    (hcont : ∀ i, Continuous (I.grad i))
    (hs : ∀ i, CompositeGeneralized.SymmetricSmooth (I.grad i) p.L0 p.L1)
    (u : p.E) (hmin : ∀ i y, I.loss i u ≤ I.loss i y) (hu : ‖p.x0 - u‖ ≤ p.R)
    (oracle : Oracle (Fin p.n × p.E) p.E)
    (horacle : ∀ history query seed, oracle.answer history (0, query) seed = I.grad query.1 query.2)
    (K : ℕ) (hK : 0 < K)
    (hcost : (𝔼 seed : Seeds p, (Program.cost (fun q => I.grad q.1 q.2) (plan p seed) : ℝ)) ≤ (K : ℝ) / 6) :
    (2 / 3 : ENNReal) ≤ ((PMF.uniformOfFintype (Seeds p)).toMeasure).prod oracle.law.toMeasure
      {ω | objective I (output p oracle K ω.1 ω.2) - objective I u ≤ p.ε} := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective
    (fun i => envelope (I.loss i) (I.grad i) (smoothing p))
  let g := fun q : Fin p.n × p.E => I.grad q.1 q.2
  let F := fun seed : Seeds p => H (Program.eval g (plan p seed)) - H u
  let N := fun seed : Seeds p => Program.cost g (plan p seed)
  let good := {seed : Seeds p | F seed ≤ p.ε / 5 ∧ N seed ≤ K}
  have hμ := smoothing_pos p h0 he
  have hF seed : 0 ≤ F seed := by
    have hh := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      component_envelope_gap_nonneg (hc i) (hg i) hμ (hmin i) (Program.eval g (plan p seed)))
    simp only [Fintype.expect_const, Finset.expect_sub_distrib,
      ← OracleTemplate.FiniteSum.objective_eq_expect] at hh
    exact hh
  have hacc := instance_plan_accuracy p I h0 h1 he hR hc hg hcont hs u hmin hu
  have hmean : (𝔼 seed : Seeds p, F seed) ≤ p.ε / 60 := by
    simpa only [F, Finset.expect_sub_distrib, Fintype.expect_const] using hacc
  have hgood := finite_accuracy_cost_event F N p.ε K he hK hF hmean hcost
  change (3 / 4 : ENNReal) ≤ (PMF.uniformOfFintype (Seeds p)).toMeasure good at hgood
  change (2 / 3 : ENNReal) ≤ ((PMF.uniformOfFintype (Seeds p)).toMeasure.prod oracle.law.toMeasure) _
  calc
    (2 / 3 : ENNReal) ≤ 3 / 4 := by
      have hh := ENNReal.ofReal_le_ofReal (by norm_num : (2 / 3 : ℝ) ≤ 3 / 4)
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_ofNat] using hh
    _ ≤ (PMF.uniformOfFintype (Seeds p)).toMeasure good := hgood
    _ = ((PMF.uniformOfFintype (Seeds p)).toMeasure.prod oracle.law.toMeasure) (good ×ˢ Set.univ) := by
      rw [MeasureTheory.Measure.prod_prod, MeasureTheory.measure_univ, mul_one]
    _ ≤ _ := by
      apply MeasureTheory.measure_mono
      intro ω hω
      have hgoodω := hω.1
      change F ω.1 ≤ p.ε / 5 ∧ N ω.1 ≤ K at hgoodω
      change objective I (output p oracle K ω.1 ω.2) - objective I u ≤ p.ε
      rw [execute_of_cost_le p I.grad oracle horacle K ω.1 ω.2 hgoodω.2]
      exact finiteSum_gap_transfer p I h0 h1 he hc hg hcont hs u (Program.eval g (plan p ω.1)) hmin hgoodω.1

end OracleTemplate.ComponentEnvelope
