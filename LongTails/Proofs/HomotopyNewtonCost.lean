import LongTails.Proofs.HomotopyNewtonExecution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HomotopyNewtonCost

open LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
open LongTails.Algorithms.HomotopyNewtonAEP
open LongTails.Proofs.HomotopyNewtonSchedule
open LongTails.Proofs.HomotopyNewtonInner
open LongTails.Proofs.HomotopyNewtonOuter
open LongTails.Proofs.HomotopyNewtonExecution

noncomputable section

variable {p : Params}

def logTerm (k : ℕ) : ℝ :=
  Real.log (1 + step p k * stiff p) + Real.log (1 + 100 * Real.sqrt (step p k * p.L) * p.D)

lemma logTerm_nonneg (hp : Valid p) (k : ℕ) : 0 ≤ logTerm (p := p) k := by
  unfold logTerm
  have h1 := one_le_denom hp k
  have h2 : 1 ≤ 1 + 100 * Real.sqrt (step p k * p.L) * p.D := by
    have := hp.D; have := Real.sqrt_nonneg (step p k * p.L); nlinarith
  have := Real.log_nonneg h1
  have := Real.log_nonneg h2
  linarith

lemma stages_le (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j : ℕ) :
    (stages p k g j : ℝ) ≤
      2 * Real.log ((1 + step p k * stiff p) / ratio p k g j) / ratio p k g j + 1 := by
  have hη := ratio_pos hp k hg j
  have hη1 := ratio_le_one (p := p) k g j
  have hs := start_pos hp k hg j
  have ha := step_pos hp k
  have hd := one_le_denom hp k
  have hlog : 0 < Real.log (1 + ratio p k g j) := Real.log_pos (by linarith)
  have hge : ratio p k g j / 2 ≤ Real.log (1 + ratio p k g j) := log_one_add_ge hη.le hη1
  have hab : step p k / start p k g j ≤ (1 + step p k * stiff p) / ratio p k g j := by
    unfold start
    rcases le_total (step p k) (step p k * ratio p k g j * 2 ^ j / (1 + step p k * stiff p))
      with hm | hm
    · rw [min_eq_left hm, div_self ha.ne', le_div_iff₀ hη]; nlinarith
    · rw [min_eq_right hm]
      have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hη]
      have : step p k * (1 + step p k * stiff p) * ratio p k g j ≤
          (1 + step p k * stiff p) * (step p k * ratio p k g j * 2 ^ j) := by
        nlinarith [mul_pos ha hη, mul_pos (mul_pos ha hη) (by linarith : (0 : ℝ) < 1 + step p k * stiff p)]
      linarith
  have hab1 : 1 ≤ step p k / start p k g j := by rw [le_div_iff₀ hs]; simpa using start_le k g j
  have hL0 : 0 ≤ Real.log (step p k / start p k g j) := Real.log_nonneg hab1
  have hL1 : Real.log (step p k / start p k g j) ≤
      Real.log ((1 + step p k * stiff p) / ratio p k g j) :=
    Real.log_le_log (by linarith) hab
  have hceil : (stages p k g j : ℝ) <
      Real.log (step p k / start p k g j) / Real.log (1 + ratio p k g j) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hL0 hlog.le)
  have hdiv : Real.log (step p k / start p k g j) / Real.log (1 + ratio p k g j) ≤
      2 * Real.log ((1 + step p k * stiff p) / ratio p k g j) / ratio p k g j := by
    rw [div_le_div_iff₀ hlog hη]
    have := mul_le_mul hL1 hge (by positivity) (hL0.trans hL1)
    nlinarith
  linarith

lemma log_ratio_le (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j : ℕ) {ρmax : ℝ}
    (hρ : guess p k g j ≤ ρmax) (hρD : ρmax ≤ 2 * p.D) :
    Real.log ((1 + step p k * stiff p) / ratio p k g j) ≤ logTerm (p := p) k := by
  have hη := ratio_pos hp k hg j
  have hd := one_le_denom hp k
  have hinv := ratio_inv_le hp k hg j
  have hsq := Real.sqrt_nonneg (step p k * p.L)
  have hb : 1 / ratio p k g j ≤ 1 + 100 * Real.sqrt (step p k * p.L) * p.D := by
    refine hinv.trans ?_
    nlinarith [guess_pos hp k hg j]
  unfold logTerm
  rw [div_eq_mul_one_div, Real.log_mul (by positivity) (by positivity)]
  have := Real.log_le_log (by positivity) hb
  linarith

lemma attemptTicks_le (hp : Valid p) (F : p.E → p.E) (k : ℕ) (z Fz : p.E)
    (hg : 0 < gval F k z Fz) (j : ℕ) {ρmax : ℝ}
    (hρ : guess p k (gval F k z Fz) j ≤ ρmax) (hρD : ρmax ≤ 2 * p.D) :
    (attemptTicks F k z Fz j : ℝ) ≤
      12 * logTerm (p := p) k * (1 + 50 * Real.sqrt (step p k * p.L) *
        guess p k (gval F k z Fz) j) + 13 + 2 * extra p k := by
  set g := gval F k z Fz
  have hη := ratio_pos hp k hg j
  have hst := stages_le hp k hg j
  have hlr := log_ratio_le hp k hg j hρ hρD
  have hinv := ratio_inv_le hp k hg j
  have hlt := logTerm_nonneg hp k
  have hd := one_le_denom hp k
  have hlogpos : 0 ≤ Real.log ((1 + step p k * stiff p) / ratio p k g j) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hη]; nlinarith [ratio_le_one (p := p) k g j]
  have hkey : 2 * Real.log ((1 + step p k * stiff p) / ratio p k g j) / ratio p k g j ≤
      2 * logTerm (p := p) k * (1 + 50 * Real.sqrt (step p k * p.L) * guess p k g j) := by
    have e : 2 * Real.log ((1 + step p k * stiff p) / ratio p k g j) / ratio p k g j =
        2 * (Real.log ((1 + step p k * stiff p) / ratio p k g j) * (1 / ratio p k g j)) := by
      ring
    rw [e, mul_assoc 2 (logTerm (p := p) k)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul hlr hinv (one_div_pos.mpr hη).le hlt
  unfold attemptTicks programLength
  push_cast
  linarith

lemma guess_geom (hp : Valid p) (k : ℕ) (g : ℝ) (hg : 0 ≤ g) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), guess p k g j ≤ 2 * guess p k g J := by
  induction J with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    have h0 : 0 ≤ guess p k g 0 := by
      unfold guess
      have := one_le_denom hp k
      exact div_nonneg (mul_nonneg hg (by positivity)) (by linarith)
    linarith
  | succ J ih =>
    rw [Finset.sum_range_succ, guess_succ]
    linarith

lemma failTicks_add (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (J : ℕ) :
    failTicks F k z Fz J + attemptTicks F k z Fz J =
      ∑ j ∈ Finset.range (J + 1), attemptTicks F k z Fz j := by
  induction J with
  | zero => simp [failTicks]
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, failTicks]; ring

def constTerm (k : ℕ) : ℝ :=
  1 + ((attemptCap (p := p) k : ℝ) + 1) * (12 * logTerm (p := p) k + 13 + 2 * extra p k)

lemma outerTicks_le (hp : Valid p) (F : p.E → p.E) (k : ℕ) (z Fz : p.E)
    (hf : StepFacts F k z Fz) :
    (outerTicks F k z Fz : ℝ) ≤ constTerm (p := p) k +
      3600 * logTerm (p := p) k * Real.sqrt (step p k * p.L) *
        ‖nextPoint F k z Fz - center p k z Fz‖ := by
  classical
  have hlt := logTerm_nonneg hp k
  have hsq := Real.sqrt_nonneg (step p k * p.L)
  have hgap := norm_nonneg (nextPoint F k z Fz - center p k z Fz)
  have hc0 : 1 ≤ constTerm (p := p) k := by
    unfold constTerm
    have h1 : (0 : ℝ) ≤ (attemptCap (p := p) k : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) ≤ 12 * logTerm (p := p) k + 13 + 2 * (extra p k : ℝ) := by
      have : (0 : ℝ) ≤ extra p k := Nat.cast_nonneg _
      linarith
    nlinarith [mul_nonneg h1 h2]
  by_cases hg0 : gval F k z Fz = 0
  · simp only [outerTicks, hg0, ↓reduceIte, Nat.cast_one]
    nlinarith [mul_nonneg (mul_nonneg hlt hsq) hgap]
  · have hg : 0 < gval F k z Fz := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0)
    rcases hf.cost with h0 | ⟨hcap, hguess⟩
    · exact absurd h0 hg0
    set J := firstAttempt F k z Fz
    set R := ‖resolvent F k z - center p k z Fz‖
    have hRD : R ≤ p.D := hf.radD
    have hR32 : R ≤ 3 / 2 * ‖nextPoint F k z Fz - center p k z Fz‖ := hf.rad
    simp only [outerTicks, hg0, ↓reduceIte]
    rw [failTicks_add]
    push_cast
    have hρmax : 2 * R ≤ 2 * p.D := by linarith
    have hterm : ∀ j ∈ Finset.range (J + 1), (attemptTicks F k z Fz j : ℝ) ≤
        12 * logTerm (p := p) k * (1 + 50 * Real.sqrt (step p k * p.L) *
          guess p k (gval F k z Fz) j) + 13 + 2 * extra p k := by
      intro j hj
      have hjJ : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hmono : guess p k (gval F k z Fz) j ≤ guess p k (gval F k z Fz) J := by
        unfold guess
        have hd := one_le_denom hp k
        gcongr
        · norm_num
      exact attemptTicks_le hp F k z Fz hg j (hmono.trans hguess) hρmax
    have hterm' : ∀ j ∈ Finset.range (J + 1), (attemptTicks F k z Fz j : ℝ) ≤
        (12 * logTerm (p := p) k + 13 + 2 * (extra p k : ℝ)) + (600 * logTerm (p := p) k * Real.sqrt (step p k * p.L)) * guess p k (gval F k z Fz) j := by
      intro j hj
      have := hterm j hj
      linarith
    have hsum := Finset.sum_le_sum hterm'
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum] at hsum
    have hgeom := guess_geom hp k (gval F k z Fz) (norm_nonneg _) J
    push_cast at hsum
    have hJcap : ((J : ℝ) + 1) ≤ (attemptCap (p := p) k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hcap
    have hK0 : (0 : ℝ) ≤ extra p k := Nat.cast_nonneg _
    have hA : 0 ≤ (12 * logTerm (p := p) k + 13 + 2 * (extra p k : ℝ)) := by linarith
    have hB : 0 ≤ (600 * logTerm (p := p) k * Real.sqrt (step p k * p.L)) := mul_nonneg (mul_nonneg (by norm_num) hlt) hsq
    have h600 : (600 * logTerm (p := p) k * Real.sqrt (step p k * p.L)) * ∑ j ∈ Finset.range (J + 1), guess p k (gval F k z Fz) j ≤
        3600 * logTerm (p := p) k * Real.sqrt (step p k * p.L) *
          ‖nextPoint F k z Fz - center p k z Fz‖ := by
      calc _ ≤ (600 * logTerm (p := p) k * Real.sqrt (step p k * p.L)) * (2 * (2 * R)) := by
            apply mul_le_mul_of_nonneg_left _ hB; linarith
        _ ≤ _ := by nlinarith [mul_nonneg hB hgap]
    unfold constTerm
    have := mul_le_mul_of_nonneg_right hJcap hA
    linarith

end

end LongTails.Proofs.HomotopyNewtonCost
