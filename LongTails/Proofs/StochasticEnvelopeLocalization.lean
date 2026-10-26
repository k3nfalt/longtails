import LongTails.Proofs.StochasticEnvelopePilot
import LongTails.Proofs.StochasticEnvelopeGeometry
import LongTails.Algorithms.StochasticEnvelopeLocalization
import LongTails.Proofs.AcceleratedMarkovConvergence
import LongTails.Proofs.AcceleratedMarkovTuning
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.GdPL

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.StochasticEnvelopeLocalization

lemma stage_movement {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (L μ p s a U : ℝ) {D : ℝ} (hD : 0 ≤ D) (center anchor : E)
    (K n : ℕ) (ξ : Fin (n + 1) → ℕ → Ω) :
    ‖LongTails.Algorithms.StochasticEnvelopeLocalization.stage g L μ p s a U D center anchor K n ξ
      - anchor‖ ≤ D := by
  unfold LongTails.Algorithms.StochasticEnvelopeLocalization.stage
    OracleTemplate.MultiplicativeRobustEstimator.medoid
  exact (OracleTemplate.HeavyTailedMarkovGradient.clippedRun_ball _ _ _ hD 1 anchor _ K).1

lemma stage_zero_radius {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (L μ p s a U : ℝ) (center anchor : E)
    (K n : ℕ) (ξ : Fin (n + 1) → ℕ → Ω) :
    LongTails.Algorithms.StochasticEnvelopeLocalization.stage g L μ p s a U 0 center anchor K n ξ
      = anchor := by
  have hh := stage_movement g L μ p s a U (le_refl 0) center anchor K n ξ
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

open LongTails.Algorithms.StochasticEnvelopeLocalization in
lemma refineRun_advance {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (L μ p s a U n : ℝ) (center start : E)
    (K replicas : ℕ) (ξ : ℕ → Fin (replicas + 1) → ℕ → Ω) (J : ℕ) :
    OracleTemplate.StochasticGradient.advance
      (fun j state => refineStep g L μ p s a U n center K replicas state (ξ j))
      J 0 (0, start) = (J, refineRun g L μ p s a U n center start K replicas ξ J) := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [OracleTemplate.HeavyTailedMarkovGradient.advance_add, ih]
    simp only [OracleTemplate.StochasticGradient.advance, Nat.zero_add,
      refineStep, refineRun]

lemma fixed_stage_stop {a n q U B : ℝ} (ha : 0 < a) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hU : 0 ≤ U) (hB : a * U ≤ B) :
    U * (1 / 2 : ℝ) ^ ⌈2 * Real.log (1 + n / a)⌉₊ ≤ B * n ^ (-1 / q) := by
  have hn0 : 0 < n := by linarith
  have hq0 : 0 < q := by linarith
  have hh := OracleTemplate.PLGradient.geometric_budget 2 1 1 (a / n)
    (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have he : (1 : ℝ) / (a / n) = n / a := by field_simp
  simp only [he] at hh
  norm_num only at hh
  simp only [mul_one] at hh
  have hpow : n⁻¹ ≤ n ^ (-1 / q) := by
    rw [← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le hn
    apply (le_div_iff₀ hq0).mpr
    linarith
  calc
    _ ≤ U * (a / n) := mul_le_mul_of_nonneg_left hh hU
    _ = (a * U) * n⁻¹ := by ring
    _ ≤ (a * U) * n ^ (-1 / q) := mul_le_mul_of_nonneg_left hpow (mul_nonneg ha.le hU)
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hn0.le _)

lemma shrinking_movement {E : Type*} [NormedAddCommGroup E] {U : ℝ}
    (x : ℕ → E) (hstep : ∀ j, ‖x (j + 1) - x j‖ ≤ U * (1 / 2 : ℝ) ^ j) (N : ℕ) :
    ‖x N - x 0‖ ≤ 2 * U * (1 - (1 / 2 : ℝ) ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ht := norm_sub_le_norm_sub_add_norm_sub (x (N + 1)) (x N) (x 0)
    have hs := hstep N
    rw [pow_succ]
    nlinarith only [ht, hs, ih]

lemma refineRun_step_movement {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (L μ p s a n : ℝ) {U : ℝ} (hU : 0 ≤ U) (center start : E)
    (K replicas : ℕ) (ξ : ℕ → Fin (replicas + 1) → ℕ → Ω) (j : ℕ) :
    let run := LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun
      g L μ p s a U n center start K replicas ξ
    ‖run (j + 1) - run j‖ ≤ U * (1 / 2 : ℝ) ^ j := by
  dsimp only
  rw [LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun]
  split_ifs
  · simp only [sub_self, norm_zero]
    positivity
  · have hh := stage_movement g L μ p s a U
      (by positivity : 0 ≤ U / (2 : ℝ) ^ j) center
      (LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun
        g L μ p s a U n center start K replicas ξ j) K replicas (ξ j)
    simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using hh

lemma refineRun_movement {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (L μ p s a n : ℝ) {U : ℝ} (hU : 0 ≤ U) (center start : E)
    (K replicas : ℕ) (ξ : ℕ → Fin (replicas + 1) → ℕ → Ω) (J : ℕ) :
    ‖LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun
      g L μ p s a U n center start K replicas ξ J - start‖ ≤ 2 * U := by
  have hh := shrinking_movement
    (LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun
      g L μ p s a U n center start K replicas ξ)
    (refineRun_step_movement g L μ p s a n hU center start K replicas ξ) J
  apply hh.trans
  have hp : 0 ≤ (1 / 2 : ℝ) ^ J := by positivity
  nlinarith

lemma shrinking_accuracy {E : Type*} [NormedAddCommGroup E] (x : ℕ → E) (target : E)
    {U τ : ℝ} (hinit : ‖x 0 - target‖ ≤ U)
    (hfreeze : ∀ j, U * (1 / 2 : ℝ) ^ j ≤ τ → x (j + 1) = x j) (J : ℕ)
    (hcontract : ∀ j < J, τ < U * (1 / 2 : ℝ) ^ j →
      ‖x j - target‖ ≤ U * (1 / 2 : ℝ) ^ j →
      ‖x (j + 1) - target‖ ≤ U * (1 / 2 : ℝ) ^ (j + 1)) :
    ‖x J - target‖ ≤ max (U * (1 / 2 : ℝ) ^ J) τ := by
  induction J with
  | zero => simpa only [pow_zero, mul_one] using hinit.trans (le_max_left U τ)
  | succ J ih =>
    have ih := ih (fun j hj => hcontract j (by omega))
    by_cases hstop : U * (1 / 2 : ℝ) ^ J ≤ τ
    · rw [hfreeze J hstop]
      exact (ih.trans (by rw [max_eq_right hstop])).trans (le_max_right _ _)
    · have hactive := lt_of_not_ge hstop
      have hx : ‖x J - target‖ ≤ U * (1 / 2 : ℝ) ^ J := by
        simpa only [max_eq_left hactive.le] using ih
      exact (hcontract J (by omega) hactive hx).trans (le_max_left _ _)

lemma refineRun_accuracy {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (L μ p s a U n : ℝ) (center start target : E)
    (K replicas : ℕ) (ξ : ℕ → Fin (replicas + 1) → ℕ → Ω)
    (hinit : ‖start - target‖ ≤ U) (J : ℕ)
    (hstage : ∀ j < J,
      let D := U / (2 : ℝ) ^ j
      let anchor := LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun
        g L μ p s a U n center start K replicas ξ j
      (s / μ + a * U) * n ^ (-(p - 1) / p) < D → ‖anchor - target‖ ≤ D →
      ‖LongTails.Algorithms.StochasticEnvelopeLocalization.stage
        g L μ p s a U D center anchor K replicas (ξ j) - target‖ ≤ D / 2) :
    ‖LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun
      g L μ p s a U n center start K replicas ξ J - target‖ ≤
      max (U / (2 : ℝ) ^ J) ((s / μ + a * U) * n ^ (-(p - 1) / p)) := by
  have he (j : ℕ) : U * (1 / 2 : ℝ) ^ j = U / (2 : ℝ) ^ j := by
    rw [div_pow, one_pow, mul_one_div]
  apply (shrinking_accuracy
    (LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun
      g L μ p s a U n center start K replicas ξ) target hinit ?_ J ?_).trans_eq
      (congrArg (fun z => max z _) (he J))
  · intro j hj
    rw [he] at hj
    rw [LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun, ite_eq_left hj]
  · intro j hjJ hj hx
    rw [he] at hj hx
    rw [LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun, ite_eq_right (not_le.mpr hj), he]
    have hh := hstage j hjJ hj hx
    convert hh using 1
    rw [pow_succ, div_mul_eq_div_mul_one_div]
    ring

lemma padded_noise_budget {q n x : ℝ} (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hx : 0 ≤ x) (hxn : x ≤ n ^ (1 / q) + 2) :
    (33554432 * x) ^ q ≤ (268435456 : ℝ) ^ q * n := by
  have hq0 : 0 < q := by linarith
  have hn0 : 0 < n := by linarith
  have hnroot : 1 ≤ n ^ (1 / q) := Real.one_le_rpow hn (by positivity)
  have hscale : 33554432 * x ≤ 268435456 * n ^ (1 / q) := by nlinarith
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 33554432 * x) hscale hq0.le
  have he : (n ^ (1 / q)) ^ q = n := by
    rw [← Real.rpow_mul hn0.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 268435456) (by positivity), he] at hh
  exact hh

lemma padded_count_bounds {q n κ : ℝ} (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hκ : Real.sqrt κ ≤ n) :
    let K := ⌈(268435456 : ℝ) ^ q * (Real.sqrt κ + n + 1)⌉₊
    0 < K ∧ 2048 * Real.sqrt κ ≤ K ∧
      (268435456 : ℝ) ^ q * n ≤ K ∧
      (K : ℝ) ≤ 4 * (268435456 : ℝ) ^ q * n := by
  let C := (268435456 : ℝ) ^ q
  have hC : 268435456 ≤ C := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 268435456) hq
  have hC0 : 0 < C := by linarith
  have hn0 : 0 < n := by linarith
  have hs := Real.sqrt_nonneg κ
  have hbase : 0 < C * (Real.sqrt κ + n + 1) := by positivity
  have hlo := Nat.le_ceil (C * (Real.sqrt κ + n + 1))
  have hhi := Nat.ceil_lt_add_one hbase.le
  have hdet : 2048 * Real.sqrt κ ≤ C * (Real.sqrt κ + n + 1) := by
    have hh := mul_le_mul_of_nonneg_right (show (2048 : ℝ) ≤ C by linarith) hs
    have ht : 0 ≤ C * (n + 1) := by positivity
    nlinarith only [hh, ht]
  have hstat : C * n ≤ C * (Real.sqrt κ + n + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC0.le
    linarith
  have hupper : C * (Real.sqrt κ + n + 1) + 1 ≤ 4 * C * n := by
    have hh := mul_le_mul_of_nonneg_left hκ hC0.le
    have hcn := mul_le_mul_of_nonneg_left hn hC0.le
    nlinarith only [hh, hcn, hC]
  refine ⟨?_, hdet.trans hlo, hstat.trans hlo, hhi.le.trans hupper⟩
  exact_mod_cast hbase.trans_le hlo

lemma padded_stage_budget {L μ p s a U D n : ℝ}
    (hL : 0 ≤ L) (hμ : 0 < μ) (hp : 1 < p) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hU : 0 ≤ U) (hD : 0 < D) (hn : 1 ≤ n)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hactive : (s / μ + a * U) * n ^ (-1 / (p / (p - 1))) < D) :
    let σ := s + a * μ * U + 2 * a * L * D
    let q := p / (p - 1)
    let K := ⌈(268435456 : ℝ) ^ q * (Real.sqrt ((L + μ) / μ) + n + 1)⌉₊
    (33554432 * σ / (μ * D)) ^ q ≤ (268435456 : ℝ) ^ q * n ∧
    0 < K ∧ 2048 * Real.sqrt ((L + μ) / μ) ≤ K ∧
      (33554432 * σ / (μ * D)) ^ q ≤ K := by
  let κ := (L + μ) / μ
  let q := p / (p - 1)
  let σ := s + a * μ * U + 2 * a * L * D
  have hκ0 : 0 < κ := by dsimp [κ]; positivity
  have hq : 1 ≤ q := by
    dsimp [q]
    apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
    linarith
  have hq0 : 0 < q := by linarith
  have hn0 : 0 < n := by linarith
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hpow : κ ^ (-2 : ℝ) * κ ^ 2 = 1 := by
    rw [Real.rpow_neg hκ0.le, Real.rpow_two]
    field_simp
  have ha2 : a * κ ^ 2 ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right haκ (sq_nonneg κ)).trans_eq hpow
  have hak : a * κ ≤ 1 := by
    have hk : κ ≤ κ ^ 2 := by change 2 ≤ κ at hκ; nlinarith
    exact (mul_le_mul_of_nonneg_left hk ha).trans ha2
  have haL : a * L ≤ μ := by
    have hh : a * (L + μ) / μ ≤ 1 := by
      simpa only [κ, mul_div_assoc] using hak
    have hm := (div_le_iff₀ hμ).mp hh
    nlinarith [mul_nonneg ha hμ.le]
  have hnp : n ^ (-1 / q) * n ^ (1 / q) = 1 := by
    rw [← Real.rpow_add hn0]
    rw [show -1 / q + 1 / q = 0 by ring, Real.rpow_zero]
  have hB : s / μ + a * U < D * n ^ (1 / q) := by
    have hh := mul_lt_mul_of_pos_right hactive (Real.rpow_pos_of_pos hn0 (1 / q))
    have he : ((s / μ + a * U) * n ^ (-1 / q)) * n ^ (1 / q) = s / μ + a * U := by
      rw [mul_assoc, hnp, mul_one]
    rw [he] at hh
    exact hh
  have hx : σ / (μ * D) ≤ n ^ (1 / q) + 2 := by
    have he : σ / (μ * D) = (s / μ + a * U) / D + 2 * (a * L / μ) := by
      dsimp [σ]
      field_simp
    rw [he]
    have h₁ : (s / μ + a * U) / D < n ^ (1 / q) :=
      (div_lt_iff₀ hD).mpr (by simpa only [mul_comm] using hB)
    have h₂ : a * L / μ ≤ 1 := (div_le_iff₀ hμ).mpr (by simpa only [one_mul] using haL)
    linarith
  have hnoise : (33554432 * σ / (μ * D)) ^ q ≤ (268435456 : ℝ) ^ q * n := by
    simpa only [mul_div_assoc] using padded_noise_budget hq hn
      (div_nonneg hσ (mul_pos hμ hD).le) hx
  let C := (268435456 : ℝ) ^ q
  have hC : 268435456 ≤ C := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 268435456) hq
  have hC0 : 0 < C := by linarith
  have hbase : 0 < C * (Real.sqrt κ + n + 1) := by positivity
  have hlo := Nat.le_ceil (C * (Real.sqrt κ + n + 1))
  have hdet : 2048 * Real.sqrt κ ≤ C * (Real.sqrt κ + n + 1) := by
    have hh := mul_le_mul_of_nonneg_right (show (2048 : ℝ) ≤ C by linarith) (Real.sqrt_nonneg κ)
    have ht : 0 ≤ C * (n + 1) := by positivity
    nlinarith only [hh, ht]
  have hstat : C * n ≤ C * (Real.sqrt κ + n + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC0.le
    linarith [Real.sqrt_nonneg κ]
  refine ⟨hnoise, ?_, hdet.trans hlo, hnoise.trans (hstat.trans hlo)⟩
  exact_mod_cast hbase.trans_le hlo

variable {Ω : Type} [MeasurableSpace Ω]

lemma iid_path_law (p : ProbabilityMeasure Ω) :
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (Kernel.const Ω (p : Measure Ω)) p : Measure (ℕ → Ω)) =
      Measure.infinitePi (fun _ : ℕ => (p : Measure Ω)) := by
  have he : (p : Measure Ω).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Ω)).symm =
      Measure.pi (fun _ : Finset.Iic 0 => (p : Measure Ω)) := by
    exact ((measurePreserving_piUnique (fun _ : Finset.Iic 0 => (p : Measure Ω))).symm
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Ω))).map_eq
  change (Kernel.traj (X := fun _ : ℕ => Ω) (fun n => Kernel.const (Finset.Iic n → Ω) (p : Measure Ω)) 0) ∘ₘ
    ((p : Measure Ω).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Ω)).symm) = _
  rw [he]
  exact (Measure.isProjectiveLimit_infinitePiNat (fun _ : ℕ => (p : Measure Ω))).unique
    (Measure.isProjectiveLimit_infinitePi (fun _ : ℕ => (p : Measure Ω)))

open OracleTemplate.HeavyTailedMarkovGradient
open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

lemma iid_mixing_distance (p : ProbabilityMeasure Ω) (z : Ω) :
    mixingDistance (Kernel.const Ω (p : Measure Ω)) p 1 z = 0 := by
  simp only [mixingDistance, pow_one, Kernel.const_apply, sub_self, abs_zero, ciSup_const]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
lemma measurable_clippedRun_parameters {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    {D R C : A → ℝ} {anchor : A → E} {ξ : A → ℕ → Ω}
    (hD : Measurable D) (hR : Measurable R) (hC : Measurable C)
    (ha : Measurable anchor) (hξ : Measurable ξ) (K : ℕ) :
    Measurable (fun ω => (clippedRun g (D ω) (R ω) (C ω) 1 (anchor ω) (ξ ω) K).2) := by
  induction K with
  | zero => exact ha.prodMk ha
  | succ K ih =>
    let state := fun ω => clippedRun g (D ω) (R ω) (C ω) 1 (anchor ω) (ξ ω) K
    have hq : Measurable (fun ω => OracleTemplate.Gradient.acceleratedQuery (state ω)) := by
      simp only [state, clippedRun_index, OracleTemplate.Gradient.acceleratedQuery]
      exact (ih.fst.const_smul _).add (ih.snd.const_smul _)
    have hgq := hg.comp (hq.prodMk ((measurable_pi_apply (K * 1)).comp hξ))
    have hr := StochasticEnvelopePilot.measurable_variable_clip hC hgq
    have hz := ha.add (StochasticEnvelopePilot.measurable_variable_clip hR
      ((ih.snd.sub (((measurable_const : Measurable (fun _ : A => ((K : ℝ) + 1) / 2)).div hD).smul hr)).sub ha))
    simp only [clippedRun, projectedClippedUpdate, clippedRun_index,
      OracleTemplate.Gradient.acceleratedQuery]
    simpa only [state, OracleTemplate.Gradient.acceleratedQuery, clippedRun_index,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply', Pi.div_apply, Function.comp_apply, Function.uncurry_apply_pair] using
      (((ih.fst.const_smul (((K : ℝ) * ((K : ℝ) + 1) / 4) /
        ((K : ℝ) * ((K : ℝ) + 1) / 4 + ((K : ℝ) + 1) / 2))).add
        (hz.const_smul ((((K : ℝ) + 1) / 2) /
        ((K : ℝ) * ((K : ℝ) + 1) / 4 + ((K : ℝ) + 1) / 2)))).prodMk hz)

omit [CompleteSpace E] in
lemma measurable_stage {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ p s a : ℝ) (center : E) {U D : A → ℝ} {anchor : A → E}
    (hU : Measurable U) (hD : Measurable D) (ha : Measurable anchor)
    (K replicas : ℕ) {ξ : A → Fin (replicas + 1) → ℕ → Ω} (hξ : Measurable ξ) :
    Measurable (fun ω => LongTails.Algorithms.StochasticEnvelopeLocalization.stage
      g L μ p s a (U ω) (D ω) center (anchor ω) K replicas (ξ ω)) := by
  let σ := fun ω => s + a * μ * U ω + 2 * a * L * D ω
  let e := fun ω => μ * D ω ^ 2 / 131072
  let Λ := fun ω => 2 * (L + μ) + e ω * (K : ℝ) ^ 2 / (16 * D ω ^ 2)
  let C := fun ω => 4 * (L + μ) * D ω + e ω / D ω *
    (256 * σ ω * D ω / e ω) ^ (p / (p - 1))
  have hσ : Measurable σ := by dsimp [σ]; fun_prop
  have he : Measurable e := by dsimp [e]; fun_prop
  have hΛ : Measurable Λ := by dsimp [Λ]; fun_prop
  have hC : Measurable C := by dsimp [C]; fun_prop
  have hg' : Measurable (fun w : E × Ω => g w.1 w.2 + μ • (w.1 - center)) :=
    hg.add (by fun_prop)
  apply OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
  apply Measurable.of_eval
  intro i
  exact (measurable_clippedRun_parameters hg' hΛ hD hC ha
    ((measurable_pi_apply i).comp hξ) K).fst

omit [CompleteSpace E] in
lemma measurable_refineStep {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ p s a U n : ℝ) (center : E) (K replicas : ℕ) :
    Measurable (Function.uncurry (LongTails.Algorithms.StochasticEnvelopeLocalization.refineStep
      g L μ p s a U n center K replicas)) := by
  classical
  have hD : Measurable (fun w : (ℕ × E) × (Fin (replicas + 1) → ℕ → Ω) =>
      U / (2 : ℝ) ^ w.1.1) :=
    (measurable_of_countable (fun j : ℕ => U / (2 : ℝ) ^ j)).comp measurable_fst.fst
  have hτ : Measurable (fun _ : (ℕ × E) × (Fin (replicas + 1) → ℕ → Ω) =>
      (s / μ + a * U) * n ^ (-(p - 1) / p)) := measurable_const
  have hpoint : Measurable (fun w : (ℕ × E) × (Fin (replicas + 1) → ℕ → Ω) =>
      (LongTails.Algorithms.StochasticEnvelopeLocalization.refineStep
        g L μ p s a U n center K replicas w.1 w.2).2) :=
    Measurable.ite (measurableSet_le hD hτ) measurable_fst.snd
    (measurable_stage hg L μ p s a center (U := fun _ => U) measurable_const hD measurable_fst.snd K replicas
      measurable_snd)
  exact (by fun_prop : Measurable (fun w : (ℕ × E) × (Fin (replicas + 1) → ℕ → Ω) =>
    w.1.1 + 1)).prodMk hpoint

omit [CompleteSpace E] in
lemma measurable_refineRun {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ p s a n : ℝ) (center : E) {U : A → ℝ} {start : A → E}
    (hU : Measurable U) (hstart : Measurable start) (K replicas : ℕ)
    {ξ : A → ℕ → Fin (replicas + 1) → ℕ → Ω} (hξ : Measurable ξ) (J : ℕ) :
    Measurable (fun ω => LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun
      g L μ p s a (U ω) n center (start ω) K replicas (ξ ω) J) := by
  induction J with
  | zero => exact hstart
  | succ J ih =>
    have hD : Measurable (fun ω => U ω / (2 : ℝ) ^ J) := hU.div_const _
    have hτ : Measurable (fun ω => (s / μ + a * U ω) * n ^ (-(p - 1) / p)) := by fun_prop
    exact Measurable.ite (measurableSet_le hD hτ) ih
      (measurable_stage hg L μ p s a center hU hD ih K replicas
        ((measurable_pi_apply J).comp hξ))

open RecursiveEnvelopeGeometry in
lemma regularized_oracle_contract (P : Measure Ω) [IsProbabilityMeasure P]
    {f : E → ℝ} {field : E → E} {g : E → Ω → E} {L μ p s a D U : ℝ}
    (h : Model L f field) (hμ : 0 < μ) (hp : 1 ≤ p) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center anchor : E) (hanchor : ‖anchor - prox field μ center‖ ≤ D)
    (hU : ‖center - prox field μ center‖ ≤ U) :
    Measurable (fun w : E × Ω => g w.1 w.2 + μ • (w.1 - center)) ∧
    (∀ x, Integrable (fun ω => g x ω + μ • (x - center)) P ∧
      (∫ ω, g x ω + μ • (x - center) ∂P) = field x + μ • (x - center) ∧
      Integrable (fun ω => ‖(g x ω + μ • (x - center)) -
        (field x + μ • (x - center))‖ ^ p) P) ∧
    (∀ x, ‖x - anchor‖ ≤ D →
      (∫ ω, ‖(g x ω + μ • (x - center)) -
        (field x + μ • (x - center))‖ ^ p ∂P) ≤ (s + a * μ * U + 2 * a * L * D) ^ p) := by
  refine ⟨hg.add (by fun_prop), ?_, ?_⟩
  · intro x
    refine ⟨(hi x).add (integrable_const _), ?_, ?_⟩
    · rw [integral_add (hi x) (integrable_const _), hmean]
      simp
    · simpa only [add_sub_add_right_eq_sub] using hpi x
  · intro x hx
    simp only [add_sub_add_right_eq_sub]
    have hscale : s + a * ‖field x‖ ≤ s + a * μ * U + 2 * a * L * D := by
      have hlocal := StochasticEnvelopeGeometry.localized_affine_scale (s := s) h hμ ha
        center anchor x hanchor hx
      have hmul := mul_le_mul_of_nonneg_left hU (mul_nonneg ha hμ.le)
      nlinarith only [hlocal, hmul]
    calc
      _ ≤ s ^ p + a ^ p * ‖field x‖ ^ p := hm x
      _ = s ^ p + (a * ‖field x‖) ^ p := by rw [Real.mul_rpow ha (norm_nonneg _)]
      _ ≤ (s + a * ‖field x‖) ^ p :=
        Real.add_rpow_le_rpow_add hs (mul_nonneg ha (norm_nonneg _)) hp
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hscale (by linarith)

lemma iid_clipped_rate (π : ProbabilityMeasure Ω)
    {f : E → ℝ} {g : E → Ω → E} (hG : Measurable (Function.uncurry g))
    (hGi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ y, g x y ∂(π : Measure Ω) = gradient f x)
    {L D R C p σ : ℝ} (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hσ : 0 ≤ σ) (hC : 0 < C) (hLC : 4 * L * R ≤ C) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmi : ∀ x, Integrable (fun y => ‖g x y - gradient f x‖ ^ p) (π : Measure Ω))
    (hmoment : ∀ x, (∫ y, ‖g x y - gradient f x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p)
    (x0 u : E) (hm : IsMinOn f Set.univ u) (hu : ‖u - x0‖ ≤ R) (K : ℕ) (hK : 0 < K) :
    Integrable (fun ξ => f (clippedRun g D R C 1 x0 ξ K).2.1 - f u)
      (Measure.infinitePi fun _ : ℕ => (π : Measure Ω)) ∧
    (∫ ξ, f (clippedRun g D R C 1 x0 ξ K).2.1 - f u
      ∂Measure.infinitePi (fun _ : ℕ => (π : Measure Ω))) ≤
      2 * D * R ^ 2 / (K : ℝ) ^ 2 +
      4 * σ ^ p * R ^ (2 - p) * (K : ℝ) ^ (p - 1) / D ^ (p - 1) +
      2 * R * (σ ^ p / (C / 2) ^ (p - 1)) := by
  have hπ : (Kernel.const Ω (π : Measure Ω)) ∘ₘ (π : Measure Ω) = (π : Measure Ω) := by
    simp only [Measure.const_comp, measure_univ, one_smul]
  have hz : mixingDistance (Kernel.const Ω (π : Measure Ω)) π 1 = fun _ => 0 :=
    funext (iid_mixing_distance π)
  have hh := clippedRun_rate (Kernel.const Ω (π : Measure Ω)) π hπ hG hGi hmean
    hL hD hLD hR hσ hC hLC hp hp2 hc hg hlip hmi hmoment 1
    (by rw [hz]; exact integrable_const 0) (by rw [hz]; simp : (∫ z,
      mixingDistance (Kernel.const Ω (π : Measure Ω)) π 1 z ∂(π : Measure Ω)) ≤ 0)
    x0 u hm hu K hK
  simpa only [iid_path_law, mul_zero, add_zero] using hh

lemma iid_clipped_tuned (π : ProbabilityMeasure Ω)
    {f : E → ℝ} {g : E → Ω → E} (hG : Measurable (Function.uncurry g))
    (hGi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ y, g x y ∂(π : Measure Ω) = gradient f x)
    {L R p σ ε : ℝ} (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ) (hε : 0 < ε)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmi : ∀ x, Integrable (fun y => ‖g x y - gradient f x‖ ^ p) (π : Measure Ω))
    (hmoment : ∀ x, (∫ y, ‖g x y - gradient f x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p)
    (x0 u : E) (hm : IsMinOn f Set.univ u) (hu : ‖u - x0‖ ≤ R) (K : ℕ) (hK : 0 < K)
    (hdet : Real.sqrt (32 * L * R ^ 2 / ε) ≤ K)
    (hnoise : (256 * σ * R / ε) ^ (p / (p - 1)) ≤ K) :
    let D := 2 * L + ε * (K : ℝ) ^ 2 / (16 * R ^ 2)
    let C := 4 * L * R + ε / R * (256 * σ * R / ε) ^ (p / (p - 1))
    Integrable (fun ξ => f (clippedRun g D R C 1 x0 ξ K).2.1 - f u)
      (Measure.infinitePi fun _ : ℕ => (π : Measure Ω)) ∧
    (∫ ξ, f (clippedRun g D R C 1 x0 ξ K).2.1 - f u
      ∂Measure.infinitePi (fun _ : ℕ => (π : Measure Ω))) ≤ ε := by
  let D := 2 * L + ε * (K : ℝ) ^ 2 / (16 * R ^ 2)
  let C := 4 * L * R + ε / R * (256 * σ * R / ε) ^ (p / (p - 1))
  have hD : 0 < D := by dsimp [D]; positivity
  have hLD : 2 * L ≤ D := by dsimp [D]; exact le_add_of_nonneg_right (by positivity)
  have hC : 0 < C := by dsimp [C]; positivity
  have hLC : 4 * L * R ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
  obtain ⟨hi, hb⟩ := iid_clipped_rate π hG hGi hmean hL hD hLD hR.le hσ hC hLC hp.le hp2
    hc hg hlip hmi hmoment x0 u hm hu K hK
  have hN : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have h₁ := accelerated_initial_tuning hL hR hε hN hdet
  have h₂ := accelerated_heavy_noise_tuning hL hσ hR hε hN hp hp2 hnoise
  have h₃ := accelerated_clipping_tuning hL hσ hR hε hp hp2
  refine ⟨hi, hb.trans ?_⟩
  dsimp [D, C]
  linarith only [h₁, h₂, h₃, hε]

noncomputable def oracleExtension (g : E → Ω → E) (field : E → E) (center : E)
    (R : ℝ) (x : E) (ω : Ω) : E :=
  if ‖x - center‖ ≤ R then g x ω else field x

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma oracleExtension_measurable (g : E → Ω → E) (field : E → E) (center : E) (R : ℝ)
    (hg : Measurable (Function.uncurry g)) (hf : Measurable field) :
    Measurable (Function.uncurry (oracleExtension g field center R)) := by
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) hg
    (hf.comp measurable_fst)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma oracleExtension_integrable (π : ProbabilityMeasure Ω) (g : E → Ω → E)
    (field : E → E) (center : E) (R : ℝ)
    (hi : ∀ x, Integrable (g x) (π : Measure Ω)) (x : E) :
    Integrable (oracleExtension g field center R x) (π : Measure Ω) := by
  unfold oracleExtension
  split_ifs
  · exact hi x
  · exact integrable_const _

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma oracleExtension_mean (π : ProbabilityMeasure Ω) (g : E → Ω → E)
    (field : E → E) (center : E) (R : ℝ)
    (hm : ∀ x, (∫ ω, g x ω ∂(π : Measure Ω)) = field x) (x : E) :
    (∫ ω, oracleExtension g field center R x ω ∂(π : Measure Ω)) = field x := by
  unfold oracleExtension
  split_ifs
  · exact hm x
  · simp

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma oracleExtension_moment (π : ProbabilityMeasure Ω) (g : E → Ω → E)
    (field : E → E) (center : E) (R σ p : ℝ) (hσ : 0 ≤ σ) (hp : 0 < p)
    (hi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) (π : Measure Ω))
    (hb : ∀ x, ‖x - center‖ ≤ R →
      (∫ ω, ‖g x ω - field x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p) (x : E) :
    Integrable (fun ω => ‖oracleExtension g field center R x ω - field x‖ ^ p)
      (π : Measure Ω) ∧
    (∫ ω, ‖oracleExtension g field center R x ω - field x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p := by
  unfold oracleExtension
  split_ifs with hx
  · exact ⟨hi x, hb x hx⟩
  · simp only [sub_self, norm_zero, Real.zero_rpow hp.ne', integral_zero]
    exact ⟨integrable_const 0, Real.rpow_nonneg hσ _⟩

omit [MeasurableSpace Ω] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma oracleExtension_run (g : E → Ω → E) (field : E → E) (center : E)
    (D C R : ℝ) (hR : 0 ≤ R) (ξ : ℕ → Ω) (N : ℕ) :
    clippedRun (oracleExtension g field center R) D R C 1 center ξ N =
      clippedRun g D R C 1 center ξ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [clippedRun, ih]
    rw [oracleExtension, ite_eq_left (clippedRun_query_ball g D C hR 1 center ξ N)]

open RecursiveEnvelopeGeometry in
lemma stage_replica_expected_gap {Ω : Type} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) {f : E → ℝ} {field : E → E} {g : E → Ω → E}
    {L μ p s a U D : ℝ} (h : Model L f field) (hμ : 0 < μ) (hD : 0 < D)
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ ω, g x ω ∂(π : Measure Ω) = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) (π : Measure Ω))
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂(π : Measure Ω)) ≤
      s ^ p + a ^ p * ‖field x‖ ^ p)
    (center anchor : E) (hanchor : ‖anchor - prox field μ center‖ ≤ D)
    (hU : ‖center - prox field μ center‖ ≤ U) (K : ℕ) (hK : 0 < K)
    (hdet : 2048 * Real.sqrt ((L + μ) / μ) ≤ K)
    (hnoise : (33554432 * (s + a * μ * U + 2 * a * L * D) / (μ * D)) ^
      (p / (p - 1)) ≤ K) :
    let σ := s + a * μ * U + 2 * a * L * D
    let e := μ * D ^ 2 / 131072
    let Λ := 2 * (L + μ) + e * (K : ℝ) ^ 2 / (16 * D ^ 2)
    let C := 4 * (L + μ) * D + e / D * (256 * σ * D / e) ^ (p / (p - 1))
    let F := regularized f μ center
    let point := fun ξ => (clippedRun (fun x ω => g x ω + μ • (x - center))
      Λ D C 1 anchor ξ K).2.1
    Integrable (fun ξ => F (point ξ) - F (prox field μ center))
      (Measure.infinitePi fun _ : ℕ => (π : Measure Ω)) ∧
    (∫ ξ, F (point ξ) - F (prox field μ center)
      ∂Measure.infinitePi (fun _ : ℕ => (π : Measure Ω))) ≤ e := by
  let F := regularized f μ center
  let H := fun x => field x + μ • (x - center)
  let G := fun x ω => g x ω + μ • (x - center)
  let σ := s + a * μ * U + 2 * a * L * D
  let e := μ * D ^ 2 / 131072
  have hU0 : 0 ≤ U := (norm_nonneg _).trans hU
  have hL : 0 < L := h.pos
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hmodel : Model (L + μ) F H := by
    refine ⟨by linarith [h.pos], ?_, ?_⟩
    · intro x y
      have hb := h.regularized_lower (μ := μ) center x y
      have hn : 0 ≤ μ / 2 * ‖y - x‖ ^ 2 := by positivity
      exact (le_add_of_nonneg_right hn).trans hb
    · exact h.regularized_upper center
  have hgrad (x : E) : gradient F x = H x :=
    (StochasticEnvelopeGeometry.model_hasGradientAt hmodel x).gradient
  have hH : Measurable H := by
    have hl : LipschitzWith ⟨L + μ, hmodel.pos.le⟩ H :=
      LipschitzWith.of_dist_le_mul (fun x y => by
        simp only [dist_eq_norm]
        change ‖H x - H y‖ ≤ (L + μ) * ‖x - y‖
        exact hmodel.lipschitz x y)
    exact hl.continuous.measurable
  obtain ⟨hG, hGi, hGm⟩ := regularized_oracle_contract (π : Measure Ω) h hμ hp.le hs ha
    hg hi hmean hpi hm center anchor hanchor hU
  let ext := oracleExtension G H anchor D
  have hExt : Measurable (Function.uncurry ext) :=
    oracleExtension_measurable G H anchor D hG hH
  have hEi (x : E) : Integrable (ext x) (π : Measure Ω) :=
    oracleExtension_integrable π G H anchor D (fun x => (hGi x).1) x
  have hEm (x : E) : (∫ ω, ext x ω ∂(π : Measure Ω)) = gradient F x := by
    rw [hgrad]
    exact oracleExtension_mean π G H anchor D (fun x => (hGi x).2.1) x
  have hEp (x : E) : Integrable (fun ω => ‖ext x ω - gradient F x‖ ^ p)
      (π : Measure Ω) ∧
      (∫ ω, ‖ext x ω - gradient F x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p := by
    rw [hgrad]
    exact oracleExtension_moment π G H anchor D σ p hσ (by linarith)
      (fun x => (hGi x).2.2) hGm x
  have hdet' : Real.sqrt (32 * (L + μ) * D ^ 2 / e) ≤ K := by
    have heq : 32 * (L + μ) * D ^ 2 / e = 4194304 * ((L + μ) / μ) := by
      dsimp [e]
      field_simp
      ring
    rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4194304)]
    norm_num
    exact hdet
  have hnoise' : (256 * σ * D / e) ^ (p / (p - 1)) ≤ K := by
    have heq : 256 * σ * D / e = 33554432 * σ / (μ * D) := by
      dsimp [e]
      field_simp
      ring
    rw [heq]
    exact hnoise
  have hmin : IsMinOn F Set.univ (prox field μ center) :=
    fun x _ => h.prox_minimum hμ center x
  obtain ⟨hI, hB⟩ := iid_clipped_tuned π hExt hEi hEm hmodel.pos hD hσ he hp hp2
    (StochasticEnvelopeGeometry.model_convex hmodel)
    (fun x => by rw [hgrad]; exact StochasticEnvelopeGeometry.model_hasGradientAt hmodel x)
    (fun x y => by rw [hgrad, hgrad]; exact hmodel.lipschitz x y)
    (fun x => (hEp x).1) (fun x => (hEp x).2)
    anchor (prox field μ center) hmin (by simpa only [norm_sub_rev] using hanchor)
    K hK hdet' hnoise'
  have hrun (Λ C : ℝ) (ξ : ℕ → Ω) :
      clippedRun ext Λ D C 1 anchor ξ K = clippedRun G Λ D C 1 anchor ξ K :=
    oracleExtension_run G H anchor Λ C D hD.le ξ K
  simp only [hrun] at hI hB
  exact ⟨hI, hB⟩

open RecursiveEnvelopeGeometry in
lemma stage_failure_probability {Ω : Type} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) {f : E → ℝ} {field : E → E} {g : E → Ω → E}
    {L μ p s a U D : ℝ} (h : Model L f field) (hμ : 0 < μ) (hD : 0 < D)
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ ω, g x ω ∂(π : Measure Ω) = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) (π : Measure Ω))
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂(π : Measure Ω)) ≤
      s ^ p + a ^ p * ‖field x‖ ^ p)
    (center anchor : E) (hanchor : ‖anchor - prox field μ center‖ ≤ D)
    (hU : ‖center - prox field μ center‖ ≤ U) (K : ℕ) (hK : 0 < K)
    (hdet : 2048 * Real.sqrt ((L + μ) / μ) ≤ K)
    (hnoise : (33554432 * (s + a * μ * U + 2 * a * L * D) / (μ * D)) ^
      (p / (p - 1)) ≤ K) (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => Measure.infinitePi fun _ : ℕ => (π : Measure Ω))
      {ξ | D / 2 < ‖LongTails.Algorithms.StochasticEnvelopeLocalization.stage
        g L μ p s a U D center anchor K n ξ - prox field μ center‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  let σ := s + a * μ * U + 2 * a * L * D
  let e := μ * D ^ 2 / 131072
  let Λ := 2 * (L + μ) + e * (K : ℝ) ^ 2 / (16 * D ^ 2)
  let C := 4 * (L + μ) * D + e / D * (256 * σ * D / e) ^ (p / (p - 1))
  let F := regularized f μ center
  let G := fun x ω => g x ω + μ • (x - center)
  let point := fun ξ => (clippedRun G Λ D C 1 anchor ξ K).2.1
  have hG : Measurable (Function.uncurry G) := hg.add (by fun_prop)
  have hpoint : Measurable point :=
    (measurable_clippedRun_parameters hG measurable_const measurable_const measurable_const
      measurable_const measurable_id K).fst
  obtain ⟨hiPoint, hmPoint⟩ := stage_replica_expected_gap π h hμ hD hp hp2 hs ha
    hg hi hmean hpi hm center anchor hanchor hU K hK hdet hnoise
  have hgrowth (ξ : ℕ → Ω) : μ / 2 * ‖point ξ - prox field μ center‖ ^ 2 ≤
      F (point ξ) - F (prox field μ center) := by
    have hb := h.prox_growth hμ center (point ξ)
    change F (prox field μ center) + _ ≤ F (point ξ) at hb
    linarith only [hb]
  exact StochasticEnvelopeSampling.gap_medoid_failure hpoint F (prox field μ center)
    hμ hD hgrowth hiPoint (by simpa only [show (2 : ℝ) ^ (17 : ℕ) = 131072 by norm_num] using hmPoint) n

open LongTails.Algorithms.StochasticEnvelopeLocalization in
omit [CompleteSpace E] in
lemma refineRun_failure_probability {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ p s a U n : ℝ) (center start target : E) (K replicas J : ℕ)
    (Q : Measure (Fin (replicas + 1) → ℕ → Ω)) [IsProbabilityMeasure Q]
    {η : ℝ} (hη : 0 ≤ η) (hinit : ‖start - target‖ ≤ U)
    (hstage : ∀ j anchor,
      (s / μ + a * U) * n ^ (-(p - 1) / p) < U / (2 : ℝ) ^ j →
      ‖anchor - target‖ ≤ U / (2 : ℝ) ^ j →
      Q {ξ | U / (2 : ℝ) ^ j / 2 <
        ‖stage g L μ p s a U (U / (2 : ℝ) ^ j) center anchor K replicas ξ - target‖} ≤
          ENNReal.ofReal η) :
    (Measure.infinitePi fun _ : ℕ => Q) {ξ |
      max (U / (2 : ℝ) ^ J) ((s / μ + a * U) * n ^ (-(p - 1) / p)) <
      ‖refineRun g L μ p s a U n center start K replicas ξ J - target‖} ≤
        ENNReal.ofReal (J * η) := by
  let τ := (s / μ + a * U) * n ^ (-(p - 1) / p)
  let bad : Set ((ℕ × E) × (Fin (replicas + 1) → ℕ → Ω)) := {w |
    τ < U / (2 : ℝ) ^ w.1.1 ∧ ‖w.1.2 - target‖ ≤ U / (2 : ℝ) ^ w.1.1 ∧
    U / (2 : ℝ) ^ w.1.1 / 2 <
      ‖stage g L μ p s a U (U / (2 : ℝ) ^ w.1.1) center w.1.2 K replicas w.2 - target‖}
  have hD : Measurable (fun w : (ℕ × E) × (Fin (replicas + 1) → ℕ → Ω) =>
      U / (2 : ℝ) ^ w.1.1) :=
    (measurable_of_countable (fun j : ℕ => U / (2 : ℝ) ^ j)).comp measurable_fst.fst
  have hs := measurable_stage hg L μ p s a center (U := fun _ => U)
    measurable_const hD measurable_fst.snd K replicas measurable_snd
  have hbad : MeasurableSet bad :=
    (measurableSet_lt measurable_const hD).inter
      ((measurableSet_le ((measurable_fst.snd.sub_const target).norm) hD).inter
        (measurableSet_lt (hD.div_const 2) ((hs.sub_const target).norm)))
  have hprob (state : ℕ × E) : Q.real {ξ | (state, ξ) ∈ bad} ≤ η := by
    have hb : Q {ξ | (state, ξ) ∈ bad} ≤ ENNReal.ofReal η := by
      by_cases hactive : τ < U / (2 : ℝ) ^ state.1
      · by_cases hanchor : ‖state.2 - target‖ ≤ U / (2 : ℝ) ^ state.1
        · exact (measure_mono (fun ξ hξ => hξ.2.2)).trans
            (hstage state.1 state.2 hactive hanchor)
        · simp [bad, hanchor]
      · simp [bad, hactive]
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [measureReal_def, ENNReal.toReal_ofReal hη] using hh
  have hu := (StochasticEnvelopeFreshness.fixed_step_failure_probability Q
    (refineStep g L μ p s a U n center K replicas)
    (measurable_refineStep hg L μ p s a U n center K replicas)
    bad hbad hprob J (0, start)).2
  apply (measure_mono ?_).trans hu
  intro ξ hfail
  by_contra hnone
  have hh := refineRun_accuracy g L μ p s a U n center start target K replicas ξ hinit J ?_
  · exact (not_lt_of_ge hh) hfail
  · intro j hj
    dsimp only
    intro hactive hanchor
    apply le_of_not_gt
    intro hfar
    apply hnone
    refine ⟨j, hj, ?_⟩
    rw [refineRun_advance]
    exact ⟨hactive, hanchor, hfar⟩

open RecursiveEnvelopeGeometry LongTails.Algorithms.StochasticEnvelopeLocalization in
lemma refineRun_padded_failure {Ω : Type} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) {f : E → ℝ} {field : E → E} {g : E → Ω → E}
    {L μ p s a U n : ℝ} (h : Model L f field) (hμ : 0 < μ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a) (hn : 1 ≤ n)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ ω, g x ω ∂(π : Measure Ω) = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) (π : Measure Ω))
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂(π : Measure Ω)) ≤
      s ^ p + a ^ p * ‖field x‖ ^ p)
    (center start : E) (hU : ‖center - prox field μ center‖ ≤ U)
    (hstart : ‖start - prox field μ center‖ ≤ U) (replicas J : ℕ) :
    let K := ⌈(268435456 : ℝ) ^ (p / (p - 1)) *
      (Real.sqrt ((L + μ) / μ) + n + 1)⌉₊
    let Q := Measure.pi fun _ : Fin (replicas + 1) =>
      Measure.infinitePi fun _ : ℕ => (π : Measure Ω)
    (Measure.infinitePi fun _ : ℕ => Q) {ξ |
      max (U / (2 : ℝ) ^ J) ((s / μ + a * U) * n ^ (-(p - 1) / p)) <
      ‖refineRun g L μ p s a U n center start K replicas ξ J - prox field μ center‖} ≤
        ENNReal.ofReal (J * (1 / 2 : ℝ) ^ (replicas + 1)) := by
  let K := ⌈(268435456 : ℝ) ^ (p / (p - 1)) *
    (Real.sqrt ((L + μ) / μ) + n + 1)⌉₊
  let Q := Measure.pi fun _ : Fin (replicas + 1) =>
    Measure.infinitePi fun _ : ℕ => (π : Measure Ω)
  have hU0 : 0 ≤ U := (norm_nonneg _).trans hstart
  have hτ : 0 ≤ (s / μ + a * U) * n ^ (-(p - 1) / p) := by positivity
  apply refineRun_failure_probability hg L μ p s a U n center start (prox field μ center)
    K replicas J Q (by positivity) hstart
  intro j anchor hactive hanchor
  have hD : 0 < U / (2 : ℝ) ^ j := hτ.trans_lt hactive
  have hexp : -1 / (p / (p - 1)) = -(p - 1) / p := by field_simp
  have hbudget := padded_stage_budget h.pos.le hμ hp hs ha hU0 hD hn hκ haκ
    (by simpa only [hexp] using hactive)
  exact stage_failure_probability π h hμ hD hp hp2 hs ha hg hi hmean hpi hm
    center anchor hanchor hU K hbudget.2.1 hbudget.2.2.1 hbudget.2.2.2 replicas

open RecursiveEnvelopeGeometry LongTails.Algorithms.StochasticEnvelopeLocalization in
lemma refineRun_stopped_failure {Ω : Type} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) {f : E → ℝ} {field : E → E} {g : E → Ω → E}
    {L μ p s a U n : ℝ} (h : Model L f field) (hμ : 0 < μ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (hn : 1 ≤ n)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ ω, g x ω ∂(π : Measure Ω) = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) (π : Measure Ω))
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂(π : Measure Ω)) ≤
      s ^ p + a ^ p * ‖field x‖ ^ p)
    (center start : E) (hU : ‖center - prox field μ center‖ ≤ U)
    (hstart : ‖start - prox field μ center‖ ≤ U) {η : ℝ} (hη : 0 < η) :
    let K := ⌈(268435456 : ℝ) ^ (p / (p - 1)) *
      (Real.sqrt ((L + μ) / μ) + n + 1)⌉₊
    let J := ⌈2 * Real.log (1 + n / a)⌉₊
    let replicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η)⌉₊
    let Q := Measure.pi fun _ : Fin (replicas + 1) =>
      Measure.infinitePi fun _ : ℕ => (π : Measure Ω)
    (Measure.infinitePi fun _ : ℕ => Q) {ξ |
      (s / μ + a * U) * n ^ (-(p - 1) / p) <
      ‖refineRun g L μ p s a U n center start K replicas ξ J - prox field μ center‖} ≤
        ENNReal.ofReal η := by
  let K := ⌈(268435456 : ℝ) ^ (p / (p - 1)) *
    (Real.sqrt ((L + μ) / μ) + n + 1)⌉₊
  let J := ⌈2 * Real.log (1 + n / a)⌉₊
  let replicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η)⌉₊
  have hU0 : 0 ≤ U := (norm_nonneg _).trans hstart
  have hq : 1 ≤ p / (p - 1) := by
    apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
    linarith
  have hstop := fixed_stage_stop (B := s / μ + a * U) ha hn hq hU0
    (le_add_of_nonneg_left (div_nonneg hs hμ.le))
  have hexp : -1 / (p / (p - 1)) = -(p - 1) / p := by field_simp
  have hpow : U * (1 / 2 : ℝ) ^ J = U / (2 : ℝ) ^ J := by
    rw [div_pow, one_pow, mul_one_div]
  change U * (1 / 2 : ℝ) ^ J ≤ _ at hstop
  rw [hpow, hexp] at hstop
  have hh := refineRun_padded_failure π h hμ hp hp2 hs ha.le hn hκ haκ hg hi hmean hpi hm
    center start hU hstart replicas J
  rw [max_eq_right hstop] at hh
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hb := (StochasticEnvelopeSampling.confidence_allocation J hη).2
  have hterm : 0 ≤ (1 / 2 : ℝ) ^ (replicas + 1) := by positivity
  change (J + 1 : ℝ) * (1 / 2 : ℝ) ^ (replicas + 1) ≤ η at hb
  nlinarith only [hb, hterm]

end LongTails.Proofs.StochasticEnvelopeLocalization
