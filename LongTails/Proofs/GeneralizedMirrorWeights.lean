import LongTails.Proofs.GeneralizedMirrorProcess

open MeasureTheory
open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror
open LongTails.Proofs.GeneralizedMirrorProcess
open OracleTemplate.StochasticGeneralized

namespace LongTails.Proofs.GeneralizedMirrorWeights

noncomputable def activeWeight (q : Public) (ell : ℝ) {m : ℕ} (s : State q m) : ℝ :=
  if 0 < s.A ∧ s.A < q.R ^ 2 / q.ε then stepWeight q ell s.A else 0

lemma measurable_activeWeight (q : Public) (ell : ℝ) (m : ℕ) :
    Measurable (activeWeight q ell (m := m)) := by
  have hA := GeneralizedMirrorExecution.measurable_state_A q m
  exact ((GeneralizedMirrorExecution.measurable_stepWeight q ell).comp hA).ite
    ((measurableSet_lt measurable_const hA).inter (measurableSet_lt hA measurable_const))
    measurable_const

lemma activeWeight_nonneg (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    {m : ℕ} (s : State q m) : 0 ≤ activeWeight q ell s := by
  unfold activeWeight
  split_ifs with h
  · exact (GeneralizedMirrorTuning.stepWeight_pos q hq hell h.1).le
  · exact le_rfl

lemma phaseNext_weight (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (b : Fin (m + 2) → q.Ω) :
    (phaseNext q ell m I g s b).A = s.A + activeWeight q ell s := by
  unfold phaseNext activeWeight
  split_ifs <;> simp

lemma phaseNext_cap (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (s : State q m)
    (b : Fin (m + 2) → q.Ω) (hs : s.A ≤ 2 * q.R ^ 2 / q.ε) :
    (phaseNext q ell m I g s b).A ≤ 2 * q.R ^ 2 / q.ε := by
  rw [phaseNext_weight]
  unfold activeWeight
  split_ifs with h
  · have ha := GeneralizedMirrorTuning.stepWeight_relative q hq hell h.1
    have hT : 0 < q.R ^ 2 / q.ε := by
      have hR := hq.2.2.1
      have hε := hq.2.2.2.2.2.2.2.2.1
      positivity
    rw [mul_div_assoc]
    linarith [h.2]
  · simpa using hs

lemma trace_cap (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (s : State q m)
    (hs : s.A ≤ 2 * q.R ^ 2 / q.ε) (ξ : ℕ → q.Ω) (k : ℕ) :
    (trace q ell m I g s ξ k).1.A ≤ 2 * q.R ^ 2 / q.ε := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [trace_succ]
    exact phaseNext_cap q hq hell m I g _ _ ih

lemma trace_weight_sum (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (ξ : ℕ → q.Ω) (k : ℕ) :
    (trace q ell m I g s ξ k).1.A = s.A +
      ∑ i ∈ Finset.range k, activeWeight q ell (trace q ell m I g s ξ i).1 := by
  induction k with
  | zero => simp [trace, blockTrace]
  | succ k ih =>
    rw [trace_succ, Finset.sum_range_succ]
    dsimp only
    rw [phaseNext_weight, ih]
    ring

lemma accumulated_weights_bound (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (s : State q m)
    (hA : 0 ≤ s.A) (hs : s.A ≤ 2 * q.R ^ 2 / q.ε) (ξ : ℕ → q.Ω) (k : ℕ) :
    accumulated (fun _ => m + 2) (liftedNext q ell m I g)
      (fun _ s _ => activeWeight q ell s) k s ξ ≤ 2 * q.R ^ 2 / q.ε := by
  rw [accumulated_eq_sum]
  have hc := trace_cap q hq hell m I g s hs ξ k
  have he := trace_weight_sum q ell m I g s ξ k
  change (∑ i ∈ Finset.range k, activeWeight q ell (trace q ell m I g s ξ i).1) ≤ _
  linarith

lemma activeWeight_motion (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    {m : ℕ} (s : State q m) :
    activeWeight q ell s * (3 * clipRadius q / 2) ≤ q.R / (32768 * ell) := by
  unfold activeWeight
  split_ifs with h
  · have ha := GeneralizedMirrorTuning.stepWeight_pos q hq hell h.1
    have hm := GeneralizedMirrorTuning.stepWeight_motion q hq (A := s.A) hell
    have hB := GeneralizedMirrorTuning.clipRadius_pos q hq.2.2.1
      hq.2.2.2.2.2.1 hq.2.2.2.2.2.2.2.2.1
    apply (le_div_iff₀ (by positivity : 0 < 32768 * ell)).mpr
    have hh := mul_nonneg (mul_nonneg hB.le hell.le) ha.le
    nlinarith
  · have hR := hq.2.2.1
    simp only [zero_mul]
    positivity

lemma activeWeight_variance (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    {m : ℕ} (s : State q m) :
    activeWeight q ell s ^ 2 * noiseMoment q ≤
      q.ε / (65536 * ell) * activeWeight q ell s := by
  unfold activeWeight
  split_ifs with h
  · have ha := GeneralizedMirrorTuning.stepWeight_pos q hq hell h.1
    have hv := GeneralizedMirrorTuning.stepWeight_variance q hq (A := s.A) hell
    have hn : 0 ≤ noiseMoment q := by
      rcases hq with ⟨_, _, hR, _, _, hσ, _, _, hε, _⟩
      have hB := GeneralizedMirrorTuning.clipRadius_pos q hR hσ hε
      unfold noiseMoment
      positivity
    have hx : 0 ≤ q.ε ^ 2 / q.R ^ 2 := by positivity
    have hm := mul_nonneg (mul_nonneg hx hell.le) ha.le
    have hv' : 65536 * ell * (noiseMoment q * stepWeight q ell s.A) ≤ q.ε := by
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hv' ha.le
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 65536 * ell)).mpr
    nlinarith only [hh]
  · simp

lemma accumulated_variance_bound (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (s : State q m)
    (hA : 0 ≤ s.A) (hs : s.A ≤ 2 * q.R ^ 2 / q.ε) (ξ : ℕ → q.Ω) (k : ℕ) :
    accumulated (fun _ => m + 2) (liftedNext q ell m I g)
      (fun _ s _ => activeWeight q ell s ^ 2 * noiseMoment q) k s ξ ≤
        q.R ^ 2 / (32768 * ell) := by
  have hw := accumulated_weights_bound q hq hell m I g s hA hs ξ k
  rw [accumulated_eq_sum] at hw ⊢
  have hε := hq.2.2.2.2.2.2.2.2.1
  calc
    _ ≤ ∑ i ∈ Finset.range k, q.ε / (65536 * ell) *
        activeWeight q ell (trace q ell m I g s ξ i).1 :=
      Finset.sum_le_sum (fun i _ => activeWeight_variance q hq hell _)
    _ = q.ε / (65536 * ell) *
        ∑ i ∈ Finset.range k, activeWeight q ell (trace q ell m I g s ξ i).1 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q.ε / (65536 * ell) * (2 * q.R ^ 2 / q.ε) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = q.R ^ 2 / (32768 * ell) := by field_simp; ring

lemma log_increment_lower {A a : ℝ} (hA : 0 < A) (ha : 0 ≤ a) (haA : a ≤ A) :
    a / (2 * A) ≤ Real.log (A + a) - Real.log A := by
  have hnew : 0 < A + a := by positivity
  have hr : 0 < (A + a) / A := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hr
  rw [Real.log_div hnew.ne' hA.ne'] at hl
  have he : 1 - ((A + a) / A)⁻¹ = a / (A + a) := by field_simp; ring
  rw [he] at hl
  exact (div_le_div_of_nonneg_left ha hnew (by linarith : A + a ≤ 2 * A)).trans hl

lemma sqrt_increment_lower {A a : ℝ} (hA : 0 < A) (ha : 0 ≤ a) (haA : a ≤ A) :
    a / (4 * Real.sqrt A) ≤ Real.sqrt (A + a) - Real.sqrt A := by
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hnew : 0 ≤ A + a := by positivity
  have hdiff : 0 ≤ Real.sqrt (A + a) - Real.sqrt A :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hsq := Real.sq_sqrt hA.le
  have hsqnew := Real.sq_sqrt hnew
  have hcap : Real.sqrt (A + a) ≤ 2 * Real.sqrt A := by
    nlinarith [Real.sqrt_nonneg (A + a)]
  have hh := mul_le_mul_of_nonneg_left (show Real.sqrt (A + a) + Real.sqrt A ≤
      4 * Real.sqrt A by linarith) hdiff
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt A)).mpr
  nlinarith only [hh, hsq, hsqnew]

noncomputable def growthGauge (c d e A : ℝ) : ℝ :=
  c * Real.log A + 2 * d * Real.sqrt A + e * A

lemma growthGauge_step {A a c d e : ℝ} (hA : 0 < A) (ha : 0 ≤ a) (haA : a ≤ A)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hstep : 1 ≤ a * (c / A + d / Real.sqrt A + e)) :
    1 / 2 ≤ growthGauge c d e (A + a) - growthGauge c d e A := by
  have hl := mul_le_mul_of_nonneg_left (log_increment_lower hA ha haA) hc
  have hs := mul_le_mul_of_nonneg_left (sqrt_increment_lower hA ha haA)
    (show 0 ≤ 2 * d by positivity)
  have hpos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hid : c * (a / (2 * A)) + 2 * d * (a / (4 * Real.sqrt A)) + e * a / 2 =
      a * (c / A + d / Real.sqrt A + e) / 2 := by ring
  have ht : 1 / 2 ≤ c * (a / (2 * A)) + 2 * d * (a / (4 * Real.sqrt A)) + e * a / 2 := by
    rw [hid]
    linarith
  unfold growthGauge
  nlinarith only [hl, hs, ht, mul_nonneg he ha]

lemma min_four_gain {A c d e f : ℝ} (hA : 0 < A) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf : 0 < f) :
    let a := min (A / c) (min (Real.sqrt A / d) (min (1 / e) (1 / f)))
    1 ≤ a * (c / A + d / Real.sqrt A + e + f) := by
  intro a
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have ha : 0 < a := by dsimp [a]; positivity
  have hca : 0 ≤ a * c / A := by positivity
  have hda : 0 ≤ a * d / Real.sqrt A := by positivity
  have hea : 0 ≤ a * e := by positivity
  have hfa : 0 ≤ a * f := by positivity
  have hcases : a = A / c ∨ a = Real.sqrt A / d ∨ a = 1 / e ∨ a = 1 / f := by
    rcases min_choice (A / c) (min (Real.sqrt A / d) (min (1 / e) (1 / f))) with h | h
    · exact Or.inl h
    · rcases min_choice (Real.sqrt A / d) (min (1 / e) (1 / f)) with h' | h'
      · exact Or.inr (Or.inl (h.trans h'))
      · rcases min_choice (1 / e) (1 / f) with h'' | h''
        · exact Or.inr (Or.inr (Or.inl (h.trans (h'.trans h''))))
        · exact Or.inr (Or.inr (Or.inr (h.trans (h'.trans h''))))
  have hid : a * (c / A + d / Real.sqrt A + e + f) =
      a * c / A + a * d / Real.sqrt A + a * e + a * f := by ring
  rw [hid]
  rcases hcases with h | h | h | h
  · have hh : a * c / A = 1 := by rw [h]; field_simp
    linarith
  · have hh : a * d / Real.sqrt A = 1 := by rw [h]; field_simp
    linarith
  · have hh : a * e = 1 := by rw [h]; field_simp
    linarith
  · have hh : a * f = 1 := by rw [h]; field_simp
    linarith

noncomputable def weightGauge (q : Public) (ell A : ℝ) : ℝ :=
  growthGauge (1024 * (1 + q.L1 * q.R)) (128 * Real.sqrt (q.L0 + q.L1 * q.G))
    (65536 * clipRadius q * ell / q.R + 65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell / q.ε) A

lemma weightGauge_step (q : Public) (hq : spec.valid q) {ell A : ℝ}
    (hell : 0 < ell) (hA : 0 < A) :
    1 / 2 ≤ weightGauge q ell (A + stepWeight q ell A) - weightGauge q ell A := by
  have ha := GeneralizedMirrorTuning.stepWeight_pos q hq hell hA
  have hrel := GeneralizedMirrorTuning.stepWeight_relative q hq hell hA
  rcases hq with ⟨h0, h1, hR, _, hG, hσ, _, _, hε, _⟩
  have hB := GeneralizedMirrorTuning.clipRadius_pos q hR hσ hε
  have hV : 0 ≤ noiseMoment q := by unfold noiseMoment; positivity
  let c := 1024 * (1 + q.L1 * q.R)
  let d := 128 * Real.sqrt (q.L0 + q.L1 * q.G)
  let e := 65536 * clipRadius q * ell / q.R
  let f := 65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell / q.ε
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hf : 0 < f := by dsimp [f]; positivity
  have heq : 1 / e = q.R / (65536 * clipRadius q * ell) := by dsimp [e]; field_simp
  have hfq : 1 / f = q.ε / (65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell) := by
    dsimp [f]
    field_simp
  have hg := min_four_gain hA hc hd he hf
  dsimp only at hg
  rw [heq, hfq] at hg
  change 1 ≤ stepWeight q ell A * (c / A + d / Real.sqrt A + e + f) at hg
  change 1 / 2 ≤ growthGauge c d (e + f) (A + stepWeight q ell A) - growthGauge c d (e + f) A
  apply growthGauge_step hA ha.le (by linarith) hc.le hd.le (by positivity)
  simpa only [add_assoc] using hg

lemma trace_A_positive (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (s : State q m)
    (hA : 0 < s.A) (ξ : ℕ → q.Ω) (k : ℕ) : 0 < (trace q ell m I g s ξ k).1.A := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    rw [trace_succ]
    exact phaseNext_positive q hq hell m I g _ _ ih

lemma trace_A_monotone (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (s : State q m)
    (ξ : ℕ → q.Ω) : Monotone (fun k => (trace q ell m I g s ξ k).1.A) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [trace_succ]
  dsimp only
  rw [phaseNext_weight]
  linarith [activeWeight_nonneg q hq hell (trace q ell m I g s ξ k).1]

lemma trace_weightGauge_growth (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (s : State q m)
    (hA : 0 < s.A) (ξ : ℕ → q.Ω) (k : ℕ)
    (hfinal : (trace q ell m I g s ξ k).1.A < q.R ^ 2 / q.ε) :
    k / 2 ≤ weightGauge q ell (trace q ell m I g s ξ k).1.A - weightGauge q ell s.A := by
  induction k with
  | zero => simp [trace, blockTrace]
  | succ k ih =>
    have hk : (trace q ell m I g s ξ k).1.A < q.R ^ 2 / q.ε :=
      ((trace_A_monotone q hq hell m I g s ξ) (Nat.le_succ k)).trans_lt hfinal
    have hp := trace_A_positive q hq hell m I g s hA ξ k
    have ih := ih hk
    have hg := weightGauge_step q hq hell hp
    have he : (trace q ell m I g s ξ (k + 1)).1.A = (trace q ell m I g s ξ k).1.A +
        stepWeight q ell (trace q ell m I g s ξ k).1.A := by
      rw [trace_succ]
      dsimp only
      rw [phaseNext_weight]
      simp only [activeWeight, hp, hk, and_self, ↓reduceIte]
    rw [he, Nat.cast_add, Nat.cast_one]
    linarith

lemma growthGauge_upper {A A0 T c d e : ℝ} (hA : 0 < A) (hA0 : 0 < A0)
    (hT : A ≤ T) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    growthGauge c d e A - growthGauge c d e A0 ≤
      c * Real.log (T / A0) + 2 * d * Real.sqrt T + e * T := by
  have hTp : 0 < T := hA.trans_le hT
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_log hA hT) hc
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hT) (show 0 ≤ 2 * d by positivity)
  have ht := mul_le_mul_of_nonneg_left hT he
  rw [Real.log_div hTp.ne' hA0.ne']
  unfold growthGauge
  nlinarith only [hl, hs, ht, mul_nonneg hd (Real.sqrt_nonneg A0), mul_nonneg he hA0.le]

noncomputable def horizonScale (q : Public) : ℝ :=
  4096 * (1 + q.L1 * q.R) * Real.log (8 + 8 * q.Δ / q.ε) +
    1024 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) +
      262144 * (1 + clipRadius q * q.R / q.ε + noiseMoment q * q.R ^ 2 / q.ε ^ 2)

lemma horizonScale_lower (q : Public) (hq : spec.valid q) : 262144 ≤ horizonScale q := by
  rcases hq with ⟨h0, h1, hR, hΔ, hG, hσ, _, _, hε, _⟩
  have hB := GeneralizedMirrorTuning.clipRadius_pos q hR hσ hε
  have hV : 0 ≤ noiseMoment q := by unfold noiseMoment; positivity
  have hl : 0 ≤ Real.log (8 + 8 * q.Δ / q.ε) :=
    Real.log_nonneg (by
      have hh : 0 ≤ 8 * q.Δ / q.ε := by positivity
      linarith)
  have ht : 0 ≤ 4096 * (1 + q.L1 * q.R) * Real.log (8 + 8 * q.Δ / q.ε) := by positivity
  have hn : 0 ≤ clipRadius q * q.R / q.ε := by positivity
  have hv : 0 ≤ noiseMoment q * q.R ^ 2 / q.ε ^ 2 := by positivity
  unfold horizonScale
  nlinarith [Real.sqrt_nonneg ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε)]

lemma weightGauge_upper (q : Public) (hq : spec.valid q) {ell A : ℝ} (hell : 1 ≤ ell)
    (hA : 0 < A) (hT : A ≤ q.R ^ 2 / q.ε) :
    weightGauge q ell A - weightGauge q ell (initialWeight q) ≤ horizonScale q * ell / 4 := by
  have hell0 : 0 < ell := by linarith
  rcases hq with ⟨h0, h1, hR, hΔ, hG, hσ, _, _, hε, _⟩
  have hB := GeneralizedMirrorTuning.clipRadius_pos q hR hσ hε
  have hV : 0 ≤ noiseMoment q := by unfold noiseMoment; positivity
  have hA0 := GeneralizedMirrorTuning.initialWeight_pos q hR hΔ hε
  have hc : 0 ≤ 1024 * (1 + q.L1 * q.R) := by positivity
  have hd : 0 ≤ 128 * Real.sqrt (q.L0 + q.L1 * q.G) := by positivity
  have he : 0 ≤ 65536 * clipRadius q * ell / q.R +
      65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell / q.ε := by positivity
  have hh := growthGauge_upper hA hA0 hT hc hd he
  have hratio : (q.R ^ 2 / q.ε) / initialWeight q = 8 + 8 * q.Δ / q.ε := by
    unfold initialWeight
    field_simp
    ring
  have hsqrt : Real.sqrt (q.L0 + q.L1 * q.G) * Real.sqrt (q.R ^ 2 / q.ε) =
      Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ q.L0 + q.L1 * q.G)]
    congr 1
    ring
  have hnoise : (65536 * clipRadius q * ell / q.R +
      65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell / q.ε) * (q.R ^ 2 / q.ε) =
        65536 * ell * (1 + clipRadius q * q.R / q.ε + noiseMoment q * q.R ^ 2 / q.ε ^ 2) := by
    field_simp
    ring
  rw [hratio, hnoise] at hh
  have hroot : 2 * (128 * Real.sqrt (q.L0 + q.L1 * q.G)) * Real.sqrt (q.R ^ 2 / q.ε) =
      256 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) := by
    nlinarith only [hsqrt]
  rw [hroot] at hh
  have hl : 0 ≤ Real.log (8 + 8 * q.Δ / q.ε) :=
    Real.log_nonneg (by
      have hh : 0 ≤ 8 * q.Δ / q.ε := by positivity
      linarith)
  have hterm : 0 ≤ 1024 * (1 + q.L1 * q.R) * Real.log (8 + 8 * q.Δ / q.ε) +
      256 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) := by positivity
  have hm := mul_le_mul_of_nonneg_right hell hterm
  unfold weightGauge horizonScale
  nlinarith only [hh, hm]

lemma trace_reaches_target (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 1 ≤ ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (ξ : ℕ → q.Ω) (K : ℕ)
    (hK : horizonScale q * ell ≤ K) :
    q.R ^ 2 / q.ε ≤ (trace q ell m I g (initialState q m) ξ K).1.A := by
  have hell0 : 0 < ell := by linarith
  have hA0 := GeneralizedMirrorTuning.initialWeight_pos q hq.2.2.1 hq.2.2.2.1
    hq.2.2.2.2.2.2.2.2.1
  by_contra hn
  have hfinal := lt_of_not_ge hn
  have hg := trace_weightGauge_growth q hq hell0 m I g (initialState q m) hA0 ξ K hfinal
  have hp := trace_A_positive q hq hell0 m I g (initialState q m) hA0 ξ K
  have hu := weightGauge_upper q hq hell hp hfinal.le
  have hH := horizonScale_lower q hq
  have hpos : 0 < horizonScale q * ell := mul_pos (by linarith) hell0
  change K / 2 ≤ weightGauge q ell (trace q ell m I g (initialState q m) ξ K).1.A -
    weightGauge q ell (initialWeight q) at hg
  linarith

end LongTails.Proofs.GeneralizedMirrorWeights
