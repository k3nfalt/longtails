import LongTails.Proofs.PolynomialMixingLinearTesting
import LongTails.Proofs.PolynomialMixingLowerParameters

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.PolynomialMixingHardInstance

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Proofs.PolynomialMixingLowerBound
open LongTails.Proofs.PolynomialMixingBurst LongTails.Proofs.PolynomialMixingLowerParameters
open LongTails.Proofs.PolynomialMixingLinearTesting
open OracleTemplate

abbrev Fails (q : Params) (alg : Algorithm (↥(Domain q)) (Space q) (↥(Domain q))) (N : ℕ) :=
  ∃ (f : Space q → ℝ) (O : Oracle (↥(Domain q)) (Space q)), spec.admissible q f O ∧
    ¬spec.successful q f (fun w : alg.Seed × ((k : ℕ) → O.Seed k) =>
      execute O alg (fun _ => N) w.1 w.2)
      ⟨(alg.law : Measure _).prod (O.law : Measure _), inferInstance⟩

lemma gated_fails (q : Params) (hp : spec.valid q) (P : ProbabilityMeasure Path)
    (hr : AbsolutelyRegular P q.τ q.β) (A : Set ℝ) (hA : MeasurableSet A) (b : ℝ) (hb : b ∉ A)
    (s : ℝ) (hs : 0 ≤ s)
    (hm : ((P : Measure Path).map (fun z => z 0)).real A * s ^ q.p ≤ q.G ^ q.p)
    (hsep : q.ε < q.R * (((P : Measure Path).map (fun z => z 0)).real A * s))
    (alg : Algorithm (↥(Domain q)) (Space q) (↥(Domain q))) (N : ℕ)
    (hprob : 2 * q.δ < (P : Measure Path).real (commonPrefix b N)) : Fails q alg N := by
  let v : Space q := PiLp.single 2 (⟨0, hp.1⟩ : Fin q.d) (1 : ℝ)
  have hv : ‖v‖ = 1 := by simp [v]
  let π := (P : Measure Path).map (fun z => z 0)
  have hadm (w : Space q) (hw : ‖w‖ = s) :=
    linear_admissible hr A hA w (by linarith [hp.2.2.2.1]) (by rwa [hw])
  by_contra hn
  apply linear_obstruction P A b hb v hv s hsep alg N hprob
  constructor
  · by_contra hf
    exact hn ⟨linear (π.real A • s • v), _, hadm (s • v) (by simp [norm_smul, hv, Real.norm_eq_abs, abs_of_nonneg hs]), hf⟩
  · by_contra hf
    exact hn ⟨linear (π.real A • -(s • v)), _, hadm (-(s • v)) (by simp [norm_smul, hv, Real.norm_eq_abs, abs_of_nonneg hs]), hf⟩

lemma accuracy_hard (q : Params) (hp : spec.valid q)
    (alg : Algorithm (↥(Domain q)) (Space q) (↥(Domain q))) (N : ℕ)
    (hn : (N : ℝ) ≤ q.τ * (q.G * q.R / (8 * q.ε)) ^ (q.p / (q.p - 1) * (1 + 1 / q.β)) *
      Real.log (1 / (4 * q.δ)) / (4 * (1 + 2 * q.β))) : Fails q alg N := by
  obtain ⟨_, hR, hG, hp1, hp2, hβ, hτ, hε, hscale, hδ, hδ'⟩ := And.intro hp.1 hp.2
  let x := q.G * q.R / (8 * q.ε)
  let k := q.p / (q.p - 1)
  let a := (2 * x) ^ (-k)
  have hx : 1 ≤ x := (one_le_div (by positivity)).mpr hscale
  obtain ⟨ha, ha', hmean, hmom, _⟩ := rare_calibration hp1 hp2 hx
  change 0 < a at ha
  change a ≤ 1 / 4 at ha'
  let m := width a q.β q.τ
  let l := arrival a q.β q.τ ha.le (show a ≤ 1 by linarith)
  let P := burstLaw m l
  let π := (P : Measure Path).map (fun z => z 0)
  have hτ' : 0 < q.τ := by linarith
  have hr : AbsolutelyRegular P q.τ q.β := calibrated_regular ha ha' hβ hτ'
  obtain ⟨hlow, hup, _⟩ := stationary_mass_bounds a q.β q.τ ha ha'
  change a / 2 ≤ π.real ({0}ᶜ) at hlow
  change π.real ({0}ᶜ) ≤ a at hup
  let s := q.G * a ^ (-(1 / q.p))
  have hs : 0 < s := mul_pos hG (Real.rpow_pos_of_pos ha _)
  have hm : π.real ({0}ᶜ) * s ^ q.p ≤ q.G ^ q.p := by
    apply (mul_le_mul_of_nonneg_right hup (Real.rpow_nonneg hs.le _)).trans
    change a * (q.G * a ^ (-(1 / q.p))) ^ q.p ≤ _
    rw [Real.mul_rpow hG.le (Real.rpow_nonneg ha.le _)]
    change a * (a ^ (-(1 / q.p))) ^ q.p = 1 at hmom
    nlinarith only [congrArg (fun z => q.G ^ q.p * z) hmom]
  have sep : q.ε < q.R * (π.real ({0}ᶜ) * s) := by
    have he : q.R * (a / 2 * s) = 2 * q.ε := by
      change a * a ^ (-(1 / q.p)) = 1 / (2 * x) at hmean
      dsimp only [s]
      calc
        _ = q.R * q.G / 2 * (a * a ^ (-(1 / q.p))) := by ring
        _ = _ := by rw [hmean]; dsimp [x]; field_simp; ring
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlow hs.le) hR.le
    linarith
  have hlog : 0 ≤ Real.log (1 / (4 * q.δ)) :=
    Real.log_nonneg ((one_le_div (by positivity)).mpr (by linarith))
  have hraw := rare_budget_le hx hp1 hp2 hβ hτ'
  have hN : (N : ℝ) ≤ m * Real.log (1 / (4 * q.δ)) / (2 * a) := by
    apply hn.trans
    convert mul_le_mul_of_nonneg_right hraw hlog using 1 <;> dsimp [x, k, a, m] <;> ring
  have hno := rare_silence a q.β q.τ q.δ ha ha' hδ N hN
  exact gated_fails q hp P hr _ (measurableSet_singleton (0 : ℝ)).compl 0 (by simp)
    s hs.le hm sep alg N hno

lemma confidence_hard (q : Params) (hp : spec.valid q)
    (alg : Algorithm (↥(Domain q)) (Space q) (↥(Domain q))) (N : ℕ)
    (hn : (N : ℝ) ≤ q.τ * (16 * q.δ) ^ (-(1 / q.β)) / (4 * (1 + 2 * q.β))) :
    Fails q alg N := by
  obtain ⟨_, hR, hG, _, _, hβ, hτ, hε, hscale, hδ, hδ'⟩ := And.intro hp.1 hp.2
  let a := 8 * q.δ
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a ≤ 1 / 4 := by dsimp [a]; linarith
  let m := width a q.β q.τ
  let l := arrival a q.β q.τ ha.le (show a ≤ 1 by linarith)
  let P := burstLaw m l
  let π := (P : Measure Path).map (fun z => z 0)
  let : IsProbabilityMeasure π := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply 0).aemeasurable).mpr inferInstance
  have hr : AbsolutelyRegular P q.τ q.β := calibrated_regular ha ha' hβ (by linarith)
  obtain ⟨_, _, hzero⟩ := stationary_mass_bounds a q.β q.τ ha ha'
  change 1 - a ≤ π.real {0} at hzero
  have hm : π.real {0} * q.G ^ q.p ≤ q.G ^ q.p :=
    mul_le_of_le_one_left (Real.rpow_nonneg hG.le q.p) measureReal_le_one
  have hsep : q.ε < q.R * (π.real {0} * q.G) := by
    have hh : 3 / 4 ≤ π.real {0} := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg hG.le hR.le)]
  have hw := width_lower ha ha' hβ (show 0 ≤ q.τ by linarith)
  rw [show 2 * a = 16 * q.δ by dsimp [a]; ring] at hw
  have hN : 2 * N ≤ m := by
    have he : q.τ * (16 * q.δ) ^ (-(1 / q.β)) / (2 * (1 + 2 * q.β)) =
        2 * (q.τ * (16 * q.δ) ^ (-(1 / q.β)) / (4 * (1 + 2 * q.β))) := by field_simp; ring
    rw [he] at hw
    exact_mod_cast (show 2 * (N : ℝ) ≤ m by linarith)
  exact gated_fails q hp P hr _ (measurableSet_singleton 0) 1 (by norm_num)
    q.G hG.le hm hsep alg N (rare_trap q.δ q.β q.τ hδ hδ' N hN)

end LongTails.Proofs.PolynomialMixingHardInstance
