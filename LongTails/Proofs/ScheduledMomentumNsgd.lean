import LongTails.Proofs.ScheduledMomentumWitness

namespace LongTails.Proofs.ScheduledMomentumNsgd

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar
open LongTails.Setups.ScheduledMomentumComparison
open LongTails.Proofs.DiagonalSpectral LongTails.Proofs.SeparationInstance
open LongTails.Proofs.SeparationModel LongTails.Proofs.GaussianBlocks
open LongTails.Proofs.GaussianFacts LongTails.Proofs.ScheduledMomentumExecution
open LongTails.Proofs.ScheduledMomentumWitness
open scoped NNReal

lemma dir_kick {R c a b : ℝ} (hR : 0 ≤ R) (hτ : 0 < Real.sqrt R * c) (hb : |b| ≤ c)
    (ha : Real.sqrt R * c ≤ |a|) :
    1 / 2 ≤ (Real.sqrt (a ^ 2 + R * b ^ 2))⁻¹ * |a| := by
  have h1 : (Real.sqrt R * c) ^ 2 ≤ |a| ^ 2 := pow_le_pow_left₀ hτ.le ha 2
  rw [mul_pow, Real.sq_sqrt hR, sq_abs] at h1
  have hb2 : b ^ 2 ≤ c ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg b) hb 2
    rwa [sq_abs] at this
  have hRb : R * b ^ 2 ≤ R * c ^ 2 := mul_le_mul_of_nonneg_left hb2 hR
  have hapos : 0 < |a| := hτ.trans_le ha
  have hle : Real.sqrt (a ^ 2 + R * b ^ 2) ≤ 2 * |a| := by
    calc Real.sqrt (a ^ 2 + R * b ^ 2) ≤ Real.sqrt ((2 * |a|) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_abs a])
      _ = 2 * |a| := Real.sqrt_sq (by positivity)
  have hge : |a| ≤ Real.sqrt (a ^ 2 + R * b ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hR (sq_nonneg b)])
  have hn : 0 < Real.sqrt (a ^ 2 + R * b ^ 2) := hapos.trans_le hge
  rw [inv_mul_eq_div, le_div_iff₀ hn]
  linarith

lemma dir_flat {R c a b : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c) (hτ : 0 < Real.sqrt R * c)
    (hb : |b| ≤ c) :
    (Real.sqrt (a ^ 2 + R * b ^ 2))⁻¹ * |b| ≤ c / max |a| (Real.sqrt R * c) := by
  have hmax : 0 < max |a| (Real.sqrt R * c) := lt_max_of_lt_right hτ
  rcases (Real.sqrt_nonneg (a ^ 2 + R * b ^ 2)).eq_or_lt with hn | hn
  · rw [← hn, inv_zero, zero_mul]
    exact div_nonneg hc hmax.le
  · have hge : |a| ≤ Real.sqrt (a ^ 2 + R * b ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hR (sq_nonneg b)])
    have hgeb : Real.sqrt R * |b| ≤ Real.sqrt (a ^ 2 + R * b ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hR]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])
    rw [inv_mul_eq_div, div_le_div_iff₀ hn hmax]
    rcases le_total |a| (Real.sqrt R * c) with h | h
    · rw [max_eq_right h]
      have : |b| * (Real.sqrt R * c) = c * (Real.sqrt R * |b|) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hgeb hc
    · rw [max_eq_left h]
      calc |b| * |a| ≤ c * |a| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        _ ≤ c * Real.sqrt (a ^ 2 + R * b ^ 2) := mul_le_mul_of_nonneg_left hge hc

lemma dir_le_one {R a b : ℝ} (hR : 1 ≤ R) :
    (Real.sqrt (a ^ 2 + R * b ^ 2))⁻¹ * |a| ≤ 1 ∧ (Real.sqrt (a ^ 2 + R * b ^ 2))⁻¹ * |b| ≤ 1 := by
  rcases (Real.sqrt_nonneg (a ^ 2 + R * b ^ 2)).eq_or_lt with hn | hn
  · rw [← hn, inv_zero]
    simp only [zero_mul]
    exact ⟨zero_le_one, zero_le_one⟩
  · have hge : |a| ≤ Real.sqrt (a ^ 2 + R * b ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
    have hgeb : |b| ≤ Real.sqrt (a ^ 2 + R * b ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a, sq_nonneg b])
    rw [inv_mul_le_iff₀ hn, inv_mul_le_iff₀ hn, mul_one]
    exact ⟨hge, hgeb⟩

variable (r : ℕ) (ℓ c s β : ℝ) (η : ℕ → ℝ) (φ : FlatShape) (B : ℕ)

noncomputable def anchor (ξ : ℕ → ℝ) (u : ℕ) : ℝ :=
  β * (scalarState r true ℓ c s β η φ B ξ u).2.1 +
    (1 - β) * (ℓ * (scalarState r true ℓ c s β η φ B ξ u).1.1)

lemma abs_steps (ξ : ℕ → ℝ) (u : ℕ) :
    |(scalarState r true ℓ c s β η φ B ξ (u + 1)).1.1 -
        (scalarState r true ℓ c s β η φ B ξ u).1.1| =
      |η u| * ((Real.sqrt ((anchor r ℓ c s β η φ B ξ u + (1 - β) * s * blockMean B u ξ) ^ 2 +
        (r - 1 : ℕ) * (scalarState r true ℓ c s β η φ B ξ (u + 1)).2.2 ^ 2))⁻¹ *
        |anchor r ℓ c s β η φ B ξ u + (1 - β) * s * blockMean B u ξ|) ∧
    |(scalarState r true ℓ c s β η φ B ξ (u + 1)).1.2 -
        (scalarState r true ℓ c s β η φ B ξ u).1.2| =
      |η u| * ((Real.sqrt ((anchor r ℓ c s β η φ B ξ u + (1 - β) * s * blockMean B u ξ) ^ 2 +
        (r - 1 : ℕ) * (scalarState r true ℓ c s β η φ B ξ (u + 1)).2.2 ^ 2))⁻¹ *
        |(scalarState r true ℓ c s β η φ B ξ (u + 1)).2.2|) := by
  have ha : β * (scalarState r true ℓ c s β η φ B ξ u).2.1 +
      (1 - β) * (ℓ * (scalarState r true ℓ c s β η φ B ξ u).1.1 + s * blockMean B u ξ) =
      anchor r ℓ c s β η φ B ξ u + (1 - β) * s * blockMean B u ξ := by
    unfold anchor
    ring
  simp only [scalarState, scalarDirection, ↓reduceIte]
  rw [ha]
  constructor
  · rw [show ∀ x y : ℝ, x - η u * y - x = -(η u * y) by intros; ring, abs_neg, abs_mul, abs_mul,
      abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  · rw [show ∀ x y : ℝ, x - η u * y - x = -(η u * y) by intros; ring, abs_neg, abs_mul, abs_mul,
      abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma measurable_anchor (u : ℕ) : Measurable (fun ξ => anchor r ℓ c s β η φ B ξ u) := by
  have h := measurable_scalarState r true ℓ c s β η φ B u
  unfold anchor
  exact (measurable_const.mul h.snd.fst).add (measurable_const.mul (measurable_const.mul h.fst.fst))

lemma local_anchor (u : ℕ) :
    LongTails.Proofs.NsgdProcess.Local (B * u) (fun ξ => anchor r ℓ c s β η φ B ξ u) := by
  intro ξ ξ' h
  unfold anchor
  beta_reduce
  rw [scalarState_local r true ℓ c s β η φ B ξ ξ' u h]

lemma step_le (hR : 1 ≤ ((r - 1 : ℕ) : ℝ)) (ξ : ℕ → ℝ) (u : ℕ) :
    |(scalarState r true ℓ c s β η φ B ξ (u + 1)).1.1 -
        (scalarState r true ℓ c s β η φ B ξ u).1.1| ≤ |η u| ∧
    |(scalarState r true ℓ c s β η φ B ξ (u + 1)).1.2 -
        (scalarState r true ℓ c s β η φ B ξ u).1.2| ≤ |η u| := by
  obtain ⟨h1, h2⟩ := abs_steps r ℓ c s β η φ B ξ u
  have hd := dir_le_one (a := anchor r ℓ c s β η φ B ξ u + (1 - β) * s * blockMean B u ξ)
    (b := (scalarState r true ℓ c s β η φ B ξ (u + 1)).2.2) hR
  rw [h1, h2]
  exact ⟨mul_le_of_le_one_right (abs_nonneg _) hd.1, mul_le_of_le_one_right (abs_nonneg _) hd.2⟩

lemma stiff_le (hR : 1 ≤ ((r - 1 : ℕ) : ℝ)) (ξ : ℕ → ℝ) (t : ℕ) :
    |(scalarState r true ℓ c s β η φ B ξ t).1.1| ≤ ∑ u ∈ Finset.range t, |η u| := by
  induction t with
  | zero => simp [scalarState]
  | succ t ih =>
      rw [Finset.sum_range_succ]
      have h := (step_le r ℓ c s β η φ B hR ξ t).1
      calc |(scalarState r true ℓ c s β η φ B ξ (t + 1)).1.1|
          ≤ |(scalarState r true ℓ c s β η φ B ξ t).1.1| +
            |(scalarState r true ℓ c s β η φ B ξ (t + 1)).1.1 -
              (scalarState r true ℓ c s β η φ B ξ t).1.1| := by
            have := abs_add_le (scalarState r true ℓ c s β η φ B ξ t).1.1
              ((scalarState r true ℓ c s β η φ B ξ (t + 1)).1.1 -
                (scalarState r true ℓ c s β η φ B ξ t).1.1)
            rwa [add_sub_cancel] at this
        _ ≤ _ := add_le_add ih h

lemma bounded_integrable {F : (ℕ → ℝ) → ℝ} (hF : Measurable F) (C : ℝ) (h : ∀ ξ, |F ξ| ≤ C) :
    Integrable F stdStream :=
  Integrable.of_bound hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact h ξ)

lemma kick_expect {B : ℕ} (hB : 0 < B) {τ : ℝ} (hτ : 0 < τ) (hσ : 0 < (1 - β) * s) (u : ℕ) :
    |η u| * (1 / 2) * (1 - 4 / 5 * τ / Real.sqrt ((((1 - β) * s) ^ 2 / B).toNNReal : ℝ)) ≤
      ∫ ξ, |η u| * (1 / 2) * (if τ ≤ |anchor r ℓ c s β η φ B ξ u +
        (1 - β) * s * blockMean B u ξ| then 1 else 0) ∂stdStream := by
  set V : ℝ≥0 := (((1 - β) * s) ^ 2 / B).toNNReal
  have hV : V ≠ 0 := by
    intro h
    rw [Real.toNNReal_eq_zero] at h
    have : 0 < ((1 - β) * s) ^ 2 / B := by
      have : (0 : ℝ) < B := by exact_mod_cast hB
      positivity
    linarith
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hΦm : Measurable (Function.uncurry fun (q z : ℝ) =>
      if τ ≤ |q + (1 - β) * s * z| then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
      measurable_const
  have hΦb : ∀ q z : ℝ, |(if τ ≤ |q + (1 - β) * s * z| then (1 : ℝ) else 0)| ≤ 1 := by
    intro q z
    split_ifs <;> norm_num
  rw [condition_scalar hB u (local_anchor r ℓ c s β η φ B u) (measurable_anchor r ℓ c s β η φ B u)
    hΦm hΦb]
  have hin : ∀ q : ℝ, 1 - 4 / 5 * τ / Real.sqrt V ≤
      ∫ z, (if τ ≤ |q + (1 - β) * s * z| then (1 : ℝ) else 0)
        ∂gaussianReal 0 (1 / (B : ℝ≥0)) := by
    intro q
    have hm : Measurable (fun y : ℝ => if τ ≤ |q + y| then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
        measurable_const
    have hns := LongTails.Proofs.NsgdProcess.noise_scale hB hσ
      (fun y : ℝ => if τ ≤ |q + y| then (1 : ℝ) else 0) hm
    rw [show (fun z : ℝ => if τ ≤ |q + (1 - β) * s * z| then (1 : ℝ) else 0) =
      fun z => (fun y : ℝ => if τ ≤ |q + y| then (1 : ℝ) else 0) ((1 - β) * s * z) from rfl, hns]
    have hind : (fun y : ℝ => if τ ≤ |q + y| then (1 : ℝ) else 0) =
        Set.indicator {y : ℝ | τ ≤ |q + y|} 1 := by
      funext y
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [hind, integral_indicator_one (measurableSet_le measurable_const (by fun_prop))]
    exact large_prob V hV q τ hτ.le
  have hinner : Integrable (fun ξ => ∫ z, (if τ ≤ |anchor r ℓ c s β η φ B ξ u +
      (1 - β) * s * z| then (1 : ℝ) else 0) ∂gaussianReal 0 (1 / (B : ℝ≥0))) stdStream := by
    apply bounded_integrable
      ((hΦm.stronglyMeasurable.integral_prod_right'.measurable).comp
        (measurable_anchor r ℓ c s β η φ B u)) 1
    intro ξ
    have h := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 (1 / (B : ℝ≥0))) (C := 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hΦb (anchor r ℓ c s β η φ B ξ u) z)
    simpa [Real.norm_eq_abs] using h
  calc 1 - 4 / 5 * τ / Real.sqrt V = ∫ _ξ, (1 - 4 / 5 * τ / Real.sqrt V) ∂stdStream := by
        rw [integral_const, probReal_univ, one_smul]
    _ ≤ _ := integral_mono (integrable_const _) hinner fun ξ => hin _

lemma flat_expect {B : ℕ} (hB : 0 < B) {τ : ℝ} (hτ : 0 < τ) (hσ : 0 < (1 - β) * s)
    (hτV : τ ≤ Real.sqrt ((((1 - β) * s) ^ 2 / B).toNNReal : ℝ)) (hc : 0 ≤ c) (u : ℕ) :
    (∫ ξ, |η u| * c * (1 / max |anchor r ℓ c s β η φ B ξ u + (1 - β) * s * blockMean B u ξ| τ)
      ∂stdStream) ≤
      |η u| * c * ((2 + Real.log (Real.sqrt ((((1 - β) * s) ^ 2 / B).toNNReal : ℝ) / τ)) /
        Real.sqrt ((((1 - β) * s) ^ 2 / B).toNNReal : ℝ)) := by
  set V : ℝ≥0 := (((1 - β) * s) ^ 2 / B).toNNReal
  have hV : V ≠ 0 := by
    intro h
    rw [Real.toNNReal_eq_zero] at h
    have : 0 < ((1 - β) * s) ^ 2 / B := by
      have : (0 : ℝ) < B := by exact_mod_cast hB
      positivity
    linarith
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) hc)
  have hΦm : Measurable (Function.uncurry fun (q z : ℝ) => 1 / max |q + (1 - β) * s * z| τ) :=
    measurable_const.div ((by fun_prop : Measurable fun x : ℝ × ℝ =>
      |x.1 + (1 - β) * s * x.2|).max measurable_const)
  have hΦb : ∀ q z : ℝ, |1 / max |q + (1 - β) * s * z| τ| ≤ 1 / τ := by
    intro q z
    have hpos : 0 < max |q + (1 - β) * s * z| τ := lt_max_of_lt_right hτ
    rw [abs_of_pos (one_div_pos.mpr hpos)]
    exact one_div_le_one_div_of_le hτ (le_max_right _ _)
  rw [condition_scalar hB u (local_anchor r ℓ c s β η φ B u) (measurable_anchor r ℓ c s β η φ B u)
    hΦm hΦb]
  have hin : ∀ q : ℝ, (∫ z, 1 / max |q + (1 - β) * s * z| τ ∂gaussianReal 0 (1 / (B : ℝ≥0))) ≤
      (2 + Real.log (Real.sqrt V / τ)) / Real.sqrt V := by
    intro q
    have hm : Measurable (fun y : ℝ => 1 / max |q + y| τ) :=
      measurable_const.div ((by fun_prop : Measurable fun y : ℝ => |q + y|).max measurable_const)
    rw [show (fun z : ℝ => 1 / max |q + (1 - β) * s * z| τ) =
      fun z => (fun y : ℝ => 1 / max |q + y| τ) ((1 - β) * s * z) from rfl,
      LongTails.Proofs.NsgdProcess.noise_scale hB hσ (fun y : ℝ => 1 / max |q + y| τ) hm]
    exact (inv_max_integral V hV q τ hτ hτV).2
  have hinner : Integrable (fun ξ => ∫ z, 1 / max |anchor r ℓ c s β η φ B ξ u +
      (1 - β) * s * z| τ ∂gaussianReal 0 (1 / (B : ℝ≥0))) stdStream := by
    apply bounded_integrable
      ((hΦm.stronglyMeasurable.integral_prod_right'.measurable).comp
        (measurable_anchor r ℓ c s β η φ B u)) (1 / τ)
    intro ξ
    have h := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 (1 / (B : ℝ≥0)))
      (C := 1 / τ) (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hΦb (anchor r ℓ c s β η φ B ξ u) z)
    simpa [Real.norm_eq_abs] using h
  calc (∫ ξ, ∫ z, 1 / max |anchor r ℓ c s β η φ B ξ u + (1 - β) * s * z| τ
        ∂gaussianReal 0 (1 / (B : ℝ≥0)) ∂stdStream) ≤
        ∫ _ξ, (2 + Real.log (Real.sqrt V / τ)) / Real.sqrt V ∂stdStream :=
        integral_mono hinner (integrable_const _) fun ξ => hin _
    _ = _ := by rw [integral_const, probReal_univ, one_smul]

set_option maxHeartbeats 2000000 in
theorem nsgd_momentum_lower (p : LongTails.Setups.BatchedSpectralSmooth.Public)
    (hp : LongTails.Setups.ScheduledMomentumComparison.spec.valid p) : NsgdMomentumLower p := by
  obtain ⟨hr, hL, hΔ, hs, hε, hLΔ⟩ := hp
  intro β hβ0 hβ1 η B T hB A hA
  have hr0 : 0 < min p.m p.n := by omega
  set R : ℝ := ((min p.m p.n - 1 : ℕ) : ℝ) with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    exact_mod_cast (show 1 ≤ min p.m p.n - 1 by omega)
  have hR0 : 0 < R := by linarith
  set c := 3 * p.ε / R with hcdef
  have hc : 0 < c := by positivity
  have hRc : R * c = 3 * p.ε := by rw [hcdef]; field_simp
  set w := 6 * p.ε / p.L with hwdef
  have hw : 0 < w := by positivity
  set D := p.Δ / (3 * p.ε) with hDdef
  set ℓ := p.L / 2 with hℓdef
  have hℓ : 0 < ℓ := by positivity
  set φ := valleyShape hw D with hφ
  have hDw4 : p.Δ / (4 * p.ε) ≤ D - w := by
    rw [hDdef, hwdef]
    have h1 : p.Δ / (3 * p.ε) - p.Δ / (4 * p.ε) = p.Δ / (12 * p.ε) := by field_simp; ring
    have h2 : 6 * p.ε / p.L ≤ p.Δ / (12 * p.ε) := by
      rw [div_le_div_iff₀ hL (by positivity)]
      nlinarith
    linarith
  have hΔpos : 0 < p.Δ := by
    by_contra h
    push Not at h
    nlinarith [sq_pos_of_pos hε, mul_nonneg hL.le (show 0 ≤ -p.Δ by linarith)]
  have hDw : 0 < D - w := lt_of_lt_of_le (by positivity) hDw4
  refine ⟨objective ℓ c φ p.x0,
    LongTails.Proofs.SeparationSuccess.gaussianOracle (sample ℓ c p.s φ p.x0),
    witness_admissible p hr hL hΔ hs hε hRdef rfl hw rfl rfl, ?_⟩
  intro hsucc
  set Λ := 2 + Real.log (1 + p.s * Real.sqrt (min p.m p.n) / p.ε) with hΛdef
  have hΛ2 : 2 ≤ Λ := by
    have h1 : (1 : ℝ) ≤ 1 + p.s * Real.sqrt (min p.m p.n) / p.ε := by
      have : 0 ≤ p.s * Real.sqrt (min p.m p.n) / p.ε := by positivity
      linarith
    have := Real.log_nonneg h1
    linarith
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hβ1' : 0 < 1 - β := by linarith
  rcases hs.eq_or_lt with hs0 | hspos
  · left
    have h0 : (1 - β) * R * p.L * p.Δ * p.s = 0 := by rw [← hs0]; ring
    rw [h0]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  set σ := (1 - β) * p.s with hσdef
  have hσ : 0 < σ := by positivity
  set τ := Real.sqrt R * c with hτdef
  have hsqR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
  have hτ : 0 < τ := by positivity
  have hsqB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
  set sV := Real.sqrt (((σ ^ 2 / B).toNNReal : ℝ)) with hsVdef
  have hsV : sV = σ / Real.sqrt B := by
    rw [hsVdef, Real.coe_toNNReal _ (by positivity), Real.sqrt_div (sq_nonneg _),
      Real.sqrt_sq hσ.le]
  have hτR : τ ^ 2 * R = 9 * p.ε ^ 2 := by
    calc τ ^ 2 * R = (R * c) ^ 2 := by rw [hτdef, mul_pow, Real.sq_sqrt hR0.le]; ring
      _ = 9 * p.ε ^ 2 := by rw [hRc]; ring
  by_cases hcase : 8 / 5 * τ ≤ sV
  swap
  · right
    push Not at hcase
    rw [hsV, div_lt_iff₀ hsqB] at hcase
    have h2 : σ ^ 2 < (8 / 5 * τ * Real.sqrt B) ^ 2 := by nlinarith
    have h3 : (8 / 5 * τ * Real.sqrt B) ^ 2 = 64 / 25 * τ ^ 2 * B := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hBpos.le]; ring
    have h5 : σ ^ 2 * R ≤ 64 / 25 * τ ^ 2 * B * R := by
      have := mul_le_mul_of_nonneg_right (h2.le.trans h3.le) hR0.le
      linarith
    have h6 : 64 / 25 * τ ^ 2 * B * R = 576 / 25 * p.ε ^ 2 * B := by
      rw [show 64 / 25 * τ ^ 2 * B * R = 64 / 25 * B * (τ ^ 2 * R) by ring, hτR]; ring
    have h7 : (B : ℝ) ≤ B * (T + 1) := by nlinarith
    calc (1 - β) ^ 2 * R * p.s ^ 2 = σ ^ 2 * R := by rw [hσdef]; ring
      _ ≤ 576 / 25 * p.ε ^ 2 * B := h5.trans h6.le
      _ ≤ 24 * p.ε ^ 2 * (B * (T + 1)) := by nlinarith [sq_nonneg p.ε]
  left
  have hτV : τ ≤ sV := by linarith
  have hsVpos : 0 < sV := hτ.trans_le hτV
  set Λ' := 2 + Real.log (sV / τ) with hΛ'def
  have hΛ'0 : 0 ≤ Λ' := by
    have : 0 ≤ Real.log (sV / τ) := Real.log_nonneg ((one_le_div hτ).mpr hτV)
    linarith
  have hΛ'Λ : Λ' ≤ Λ := by
    have hsVσ : sV ≤ p.s := by
      rw [hsV, div_le_iff₀ hsqB]
      have h1 : 1 ≤ Real.sqrt B := by rw [Real.one_le_sqrt]; exact hBr
      have h2 : σ ≤ p.s := by rw [hσdef]; nlinarith
      nlinarith
    have hτsq : τ * Real.sqrt R = 3 * p.ε := by
      rw [hτdef, show Real.sqrt R * c * Real.sqrt R = (Real.sqrt R * Real.sqrt R) * c by ring,
        Real.mul_self_sqrt hR0.le, hRc]
    have hRmin : R ≤ (min p.m p.n : ℝ) := by
      rw [hRdef]
      exact_mod_cast Nat.sub_le (min p.m p.n) 1
    have hsqm : Real.sqrt R ≤ Real.sqrt (min p.m p.n) := Real.sqrt_le_sqrt hRmin
    have hratio : sV / τ ≤ p.s * Real.sqrt (min p.m p.n) / p.ε := by
      rw [div_le_div_iff₀ hτ hε]
      have h1 : sV * p.ε ≤ p.s * p.ε := mul_le_mul_of_nonneg_right hsVσ hε.le
      have h2 : p.s * p.ε * 3 = p.s * Real.sqrt R * τ := by rw [show p.s * Real.sqrt R * τ = p.s * (τ * Real.sqrt R) by ring, hτsq]; ring
      have h3 : p.s * Real.sqrt R * τ ≤ p.s * Real.sqrt (min p.m p.n) * τ := by
        have := mul_le_mul_of_nonneg_left hsqm hs
        exact mul_le_mul_of_nonneg_right this hτ.le
      nlinarith [mul_nonneg hs hε.le]
    have hlog := Real.log_le_log (div_pos hsVpos hτ)
      (show sV / τ ≤ 1 + p.s * Real.sqrt (min p.m p.n) / p.ε by linarith)
    rw [hΛ'def, hΛdef]
    linarith
  have hσV : (((1 - β) * p.s) ^ 2 / B).toNNReal = (σ ^ 2 / B).toNNReal := rfl
  have hkick : ∀ u, |η u| / 4 ≤ ∫ ξ, |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.1 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.1| ∂stdStream := by
    intro u
    have h1 := kick_expect (min p.m p.n) ℓ c p.s β η φ hB hτ hσ u
    have h2 : (1 / 2 : ℝ) ≤ 1 - 4 / 5 * τ / sV := by
      have : 4 / 5 * τ / sV ≤ 1 / 2 := by
        rw [div_le_iff₀ hsVpos]
        linarith
      linarith
    have hanc := measurable_anchor (min p.m p.n) ℓ c p.s β η φ B u
    have hbm := measurable_blockMean B u
    have hS := measurable_scalarState (min p.m p.n) true ℓ c p.s β η φ B
    have hlhs : Integrable (fun ξ => |η u| * (1 / 2) *
        (if τ ≤ |anchor (min p.m p.n) ℓ c p.s β η φ B ξ u + (1 - β) * p.s * blockMean B u ξ|
          then (1 : ℝ) else 0)) stdStream := by
      apply bounded_integrable _ (|η u| * (1 / 2))
      · intro ξ
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |η u| * (1 / 2))]
        apply mul_le_of_le_one_right (by positivity)
        split_ifs <;> norm_num
      · exact measurable_const.mul (Measurable.ite
          (measurableSet_le measurable_const (by fun_prop)) measurable_const measurable_const)
    have hrhs : Integrable (fun ξ => |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.1 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.1|) stdStream := by
      apply bounded_integrable _ |η u|
      · intro ξ
        rw [abs_abs]
        exact (step_le (min p.m p.n) ℓ c p.s β η φ B hR1 ξ u).1
      · exact ((hS (u + 1)).fst.fst.sub (hS u).fst.fst).abs
    have h3 := integral_mono hlhs hrhs fun ξ => by
      show |η u| * (1 / 2) * _ ≤ _
      rw [(abs_steps (min p.m p.n) ℓ c p.s β η φ B ξ u).1]
      split_ifs with h
      · rw [mul_one]
        exact mul_le_mul_of_nonneg_left (dir_kick hR0.le hτ
          (flat_momentum_le _ true η φ B ξ hc.le hβ0 hβ1.le (u + 1)) h) (abs_nonneg _)
      · rw [mul_zero]
        positivity
    have h4 : |η u| / 4 ≤ |η u| * (1 / 2) * (1 - 4 / 5 * τ / sV) := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ |η u| * (1 / 2))
      linarith
    exact h4.trans (h1.trans h3)
  have hflat : ∀ u, ∫ ξ, |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.2 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.2| ∂stdStream ≤
      |η u| * c * (Λ' / sV) := by
    intro u
    have h1 := flat_expect (min p.m p.n) ℓ c p.s β η φ hB hτ hσ hτV hc.le u
    have hanc := measurable_anchor (min p.m p.n) ℓ c p.s β η φ B u
    have hbm := measurable_blockMean B u
    have hS := measurable_scalarState (min p.m p.n) true ℓ c p.s β η φ B
    have hrhs : Integrable (fun ξ => |η u| * c * (1 / max |anchor (min p.m p.n) ℓ c p.s β η φ B
        ξ u + (1 - β) * p.s * blockMean B u ξ| τ)) stdStream := by
      apply bounded_integrable _ (|η u| * c * (1 / τ))
      · intro ξ
        have hpos : 0 < max |anchor (min p.m p.n) ℓ c p.s β η φ B ξ u +
            (1 - β) * p.s * blockMean B u ξ| τ := lt_max_of_lt_right hτ
        rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hτ (le_max_right _ _))
          (by positivity)
      · exact measurable_const.mul (measurable_const.div
          ((by fun_prop : Measurable fun ξ => |anchor (min p.m p.n) ℓ c p.s β η φ B ξ u +
            (1 - β) * p.s * blockMean B u ξ|).max measurable_const))
    have hlhs : Integrable (fun ξ => |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.2 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.2|) stdStream := by
      apply bounded_integrable _ |η u|
      · intro ξ
        rw [abs_abs]
        exact (step_le (min p.m p.n) ℓ c p.s β η φ B hR1 ξ u).2
      · exact ((hS (u + 1)).fst.snd.sub (hS u).fst.snd).abs
    have h3 := integral_mono hlhs hrhs fun ξ => by
      show _ ≤ |η u| * c * _
      rw [(abs_steps (min p.m p.n) ℓ c p.s β η φ B ξ u).2, mul_one_div]
      have hd := mul_le_mul_of_nonneg_left (dir_flat
        (a := anchor (min p.m p.n) ℓ c p.s β η φ B ξ u + (1 - β) * p.s * blockMean B u ξ)
        hR0.le hc.le hτ (flat_momentum_le (min p.m p.n) true (ℓ := ℓ) (s := p.s) η φ B ξ hc.le
          hβ0 hβ1.le (u + 1))) (abs_nonneg (η u))
      rw [mul_div_assoc'] at hd
      exact hd
    refine h3.trans (h1.trans (le_of_eq ?_))
    rw [hΛ'def]
  have hS := measurable_scalarState (min p.m p.n) true ℓ c p.s β η φ B
  have hstiff_int : ∀ t, Integrable (fun ξ => |ℓ * (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.1|) stdStream := by
    intro t
    apply bounded_integrable ((measurable_const.mul (hS t).fst.fst).abs)
      (ℓ * ∑ u ∈ Finset.range t, |η u|)
    intro ξ
    rw [abs_abs]
    show |ℓ * (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.1| ≤ _
    rw [abs_mul, abs_of_pos hℓ]
    exact mul_le_mul_of_nonneg_left (stiff_le (min p.m p.n) ℓ c p.s β η φ B hR1 ξ t) hℓ.le
  have hflat_int : ∀ t, Integrable (fun ξ => R * |c * valleySlope w D (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.2|) stdStream := by
    intro t
    apply bounded_integrable (measurable_const.mul ((measurable_const.mul
      (φ.continuous_slope.measurable.comp (hS t).fst.snd)).abs)) (R * c)
    intro ξ
    show abs (R * |c * φ.slope (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.2|) ≤ R * c
    rw [abs_mul, abs_abs, abs_of_pos hR0, abs_mul, abs_of_pos hc]
    have hb := φ.bounded (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.2
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hc.le hb) hR0.le
  have hi : ∀ t, Integrable (fun ξ => nuclearNorm (gradient (objective ℓ c φ p.x0)
      (sampledMomentum (matrixDirection true) β η B p.x0 (sample ℓ c p.s φ p.x0) ξ t).1))
      stdStream := by
    intro t
    have he := funext fun ξ => nuclear_momentum hr0 true ℓ c p.s β η φ p.x0 hB ξ t
    rw [he]
    exact (hstiff_int t).add (hflat_int t)
  have hA' : FollowsScheduledMomentum (matrixDirection true) β η B T p.x0 A := hA
  have hdir : Measurable (matrixDirection true : Space p.m p.n → Space p.m p.n) :=
    LongTails.Proofs.SeparationSuccess.measurable_frobeniusNormalize p.m p.n
  have hsum := success_sum_momentum (measurable_sample ℓ c p.s φ p.x0) hdir hA' hi hsucc
  simp_rw [nuclear_momentum hr0 true ℓ c p.s β η φ p.x0 hB] at hsum
  have hyint : ∀ u, Integrable (fun ξ => |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.2 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.2|) stdStream := by
    intro u
    apply bounded_integrable (((hS (u + 1)).fst.snd.sub (hS u).fst.snd).abs) |η u|
    intro ξ
    rw [abs_abs]
    exact (step_le (min p.m p.n) ℓ c p.s β η φ B hR1 ξ u).2
  have hVint : Integrable (fun ξ => ∑ u ∈ Finset.range T,
      |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.2 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.2|) stdStream :=
    integrable_finsetSum _ fun u _ => hyint u
  have hmain := travel_bound hRc hc.le hR0.le hw hDw hε.le (fun ξ t => (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.1)
    (fun ξ t => (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.2) (fun ξ => rfl) hstiff_int hflat_int hVint hsum
  rw [integral_finsetSum _ fun u _ => hyint u] at hmain
  set H := ∑ u ∈ Finset.range T, |η u| with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hEV : (∑ u ∈ Finset.range T, ∫ ξ, |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.2 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.2| ∂stdStream) ≤
      c * H * (Λ' / sV) := by
    rw [hH, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro u _
    have := hflat u
    linarith [show |η u| * c * (Λ' / sV) = c * |η u| * (Λ' / sV) by ring]
  have hxint : ∀ t, Integrable (fun ξ => |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.1|) stdStream := by
    intro t
    apply bounded_integrable (hS t).fst.fst.abs (∑ u ∈ Finset.range t, |η u|)
    intro ξ
    rw [abs_abs]
    exact stiff_le (min p.m p.n) ℓ c p.s β η φ B hR1 ξ t
  have hpair : ∀ u, (∫ ξ, |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.1 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.1| ∂stdStream) ≤
      (∫ ξ, |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.1| ∂stdStream) + ∫ ξ, |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.1| ∂stdStream := by
    intro u
    rw [← integral_add (hxint (u + 1)) (hxint u)]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ((hxint (u + 1)).add (hxint u))
    exact Filter.Eventually.of_forall fun ξ => abs_sub _ _
  set e := fun t => ∫ ξ, |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.1| ∂stdStream with hedef
  have he0 : ∀ t, 0 ≤ e t := fun t => integral_nonneg fun _ => abs_nonneg _
  have hsum2 : (∑ u ∈ Finset.range T, (e (u + 1) + e u)) ≤
      2 * ∑ t ∈ Finset.range (T + 1), e t := by
    rw [Finset.sum_add_distrib]
    have h1 := Finset.sum_range_succ' e T
    have h2 := Finset.sum_range_succ e T
    linarith [he0 0, he0 T]
  have hstiff : ℓ / 8 * H ≤ ∑ t ∈ Finset.range (T + 1), ∫ ξ, |ℓ * (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.1| ∂stdStream := by
    have hl : (∑ t ∈ Finset.range (T + 1), ∫ ξ, |ℓ * (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ t).1.1| ∂stdStream) =
        ℓ * ∑ t ∈ Finset.range (T + 1), e t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [hedef]
      simp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        simp only
        rw [abs_mul, abs_of_pos hℓ]
    have hk : H / 4 ≤ ∑ u ∈ Finset.range T, (e (u + 1) + e u) := by
      rw [hH, Finset.sum_div]
      apply Finset.sum_le_sum
      intro u _
      exact (hkick u).trans (hpair u)
    rw [hl]
    nlinarith
  set Q := 3 * p.ε / 2 * (T + 1) * c * Λ' / (sV * (D - w)) with hQ
  have hQH : 3 * p.ε / 2 * (T + 1) * (∑ u ∈ Finset.range T,
      ∫ ξ, |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.2 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.2| ∂stdStream) / (D - w) ≤ Q * H := by
    have hc1 : 0 ≤ 3 * p.ε / 2 * (T + 1) := by positivity
    calc 3 * p.ε / 2 * (T + 1) * (∑ u ∈ Finset.range T,
        ∫ ξ, |(scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ (u + 1)).1.2 - (scalarState (min p.m p.n) true ℓ c p.s β η φ B ξ u).1.2| ∂stdStream) / (D - w) ≤
          3 * p.ε / 2 * (T + 1) * (c * H * (Λ' / sV)) / (D - w) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hEV hc1) hDw.le
      _ = Q * H := by
          rw [hQ]
          field_simp
  have hpos : 0 < ((T : ℝ) + 1) * p.ε / 2 := by positivity
  have hKQ : ℓ / 8 ≤ Q := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_right h.le hH0]
  have h1 : ℓ / 8 * (sV * (D - w)) ≤ 3 * p.ε / 2 * (T + 1) * c * Λ' := by
    rw [hQ, le_div_iff₀ (mul_pos hsVpos hDw)] at hKQ
    exact hKQ
  have h2 : ℓ * σ * (D - w) ≤ 12 * p.ε * (T + 1) * c * Λ' * Real.sqrt B := by
    rw [hsV] at h1
    have e : ℓ / 8 * (σ / Real.sqrt B * (D - w)) * (8 * Real.sqrt B) = ℓ * σ * (D - w) := by
      field_simp
    rw [← e]
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 8 * Real.sqrt B)
    linarith
  have h3 : ℓ * σ * (p.Δ / (4 * p.ε)) ≤ 12 * p.ε * (T + 1) * c * Λ' * Real.sqrt B :=
    (mul_le_mul_of_nonneg_left hDw4 (by positivity)).trans h2
  have hsB : Real.sqrt B ≤ B := by
    calc Real.sqrt B ≤ Real.sqrt ((B : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = B := Real.sqrt_sq (by linarith)
  have e1 : (1 - β) * R * p.L * p.Δ * p.s = 8 * p.ε * R * (ℓ * σ * (p.Δ / (4 * p.ε))) := by
    rw [hℓdef, hσdef]
    field_simp
    ring
  have e2 : 8 * p.ε * R * (12 * p.ε * (T + 1) * c * Λ' * Real.sqrt B) =
      288 * p.ε ^ 3 * Λ' * ((T + 1) * Real.sqrt B) := by
    rw [show 8 * p.ε * R * (12 * p.ε * (T + 1) * c * Λ' * Real.sqrt B) =
      96 * p.ε ^ 2 * (R * c) * Λ' * ((T + 1) * Real.sqrt B) by ring, hRc]
    ring
  rw [e1]
  calc 8 * p.ε * R * (ℓ * σ * (p.Δ / (4 * p.ε))) ≤
      8 * p.ε * R * (12 * p.ε * (T + 1) * c * Λ' * Real.sqrt B) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 288 * p.ε ^ 3 * Λ' * ((T + 1) * Real.sqrt B) := e2
    _ ≤ 288 * p.ε ^ 3 * Λ * (B * (T + 1)) := by
        have h4 : (T + 1) * Real.sqrt B ≤ B * (T + 1) := by nlinarith
        have h5 : 288 * p.ε ^ 3 * Λ' ≤ 288 * p.ε ^ 3 * Λ :=
          mul_le_mul_of_nonneg_left hΛ'Λ (by positivity)
        have h6 : 0 ≤ 288 * p.ε ^ 3 * Λ' := by positivity
        calc 288 * p.ε ^ 3 * Λ' * ((T + 1) * Real.sqrt B) ≤
            288 * p.ε ^ 3 * Λ' * (B * (T + 1)) := mul_le_mul_of_nonneg_left h4 h6
          _ ≤ _ := mul_le_mul_of_nonneg_right h5 (by positivity)

end LongTails.Proofs.ScheduledMomentumNsgd
