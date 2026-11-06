import LongTails.Proofs.CovarianceAcceleratedConvergence
import LongTails.Proofs.CovarianceAcceleratedTuning
import LongTails.Algorithms.CovarianceAcceleratedTuned

namespace LongTails.Proofs.CovarianceAcceleratedRate

lemma normalized_energy_bound {L R s σ η b a T A S ell : ℝ}
    (hL : 0 ≤ L) (hη : 0 < η) (hb : 0 < b)
    (hT : 1 ≤ T) (hell : 0 ≤ ell) (ha2 : a ^ 2 = b / η)
    (hA : η * T ^ 2 / 2 ≤ A)
    (hS : S ≤ 320 * η ^ 2 * R ^ 2 * s ^ 2 * T ^ 3 +
      80 * η ^ 2 * a ^ 2 * σ ^ 2 * T ^ 3 + ell) :
    L * (R / T ^ 2) ^ 2 / 2 +
      (R ^ 2 / (2 * a ^ 2) + (2 * η * L) * R ^ 2 / 2 + η * L * R ^ 2 + 2 * S + 2 * ell) / A ≤
      5 * L * R ^ 2 / T ^ 2 + R ^ 2 / (b * T ^ 2) +
        1280 * η * R ^ 2 * s ^ 2 * T + 320 * b * σ ^ 2 * T + 8 * ell / (η * T ^ 2) := by
  have hTpos : 0 < T := by linarith
  have hApos : 0 < A := (show 0 < η * T ^ 2 / 2 by positivity).trans_le hA
  let Q := 4 * L * R ^ 2 / T ^ 2 + R ^ 2 / (b * T ^ 2) +
    1280 * η * R ^ 2 * s ^ 2 * T + 320 * b * σ ^ 2 * T + 8 * ell / (η * T ^ 2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have he : Q * (η * T ^ 2 / 2) = R ^ 2 / (2 * a ^ 2) +
      (2 * η * L) * R ^ 2 / 2 + η * L * R ^ 2 +
      2 * (320 * η ^ 2 * R ^ 2 * s ^ 2 * T ^ 3 + 80 * η ^ 2 * a ^ 2 * σ ^ 2 * T ^ 3 + ell) + 2 * ell := by
    dsimp [Q]
    rw [ha2]
    field_simp
    ring
  have hnum :
      (R ^ 2 / (2 * a ^ 2) + (2 * η * L) * R ^ 2 / 2 + η * L * R ^ 2 + 2 * S + 2 * ell) / A ≤ Q := by
    apply (div_le_iff₀ hApos).mpr
    calc
      _ ≤ Q * (η * T ^ 2 / 2) := by rw [he]; linarith
      _ ≤ Q * A := mul_le_mul_of_nonneg_left hA hQ
  have hmesh : L * (R / T ^ 2) ^ 2 / 2 ≤ L * R ^ 2 / T ^ 2 := by
    have hT2 : 1 ≤ T ^ 2 := by nlinarith
    apply (div_le_div_iff₀ (show (0 : ℝ) < 2 by norm_num) (sq_pos_of_pos hTpos)).mpr
    field_simp
    have hn : 0 ≤ L * R ^ 2 := by positivity
    nlinarith [mul_nonneg hn (show 0 ≤ 2 * T ^ 2 - 1 by linarith)]
  have hsum := add_le_add hmesh hnum
  dsimp [Q] at hsum
  convert hsum using 1
  ring

open MeasureTheory ProbabilityTheory Convexity
open scoped NNReal
open LongTails.Algorithms.CovarianceAccelerated
open LongTails.Proofs.CovarianceAcceleratedParameters
open LongTails.Proofs.CovarianceAcceleratedProcesses

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma tuned_failure_probability {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P)
    {f : E → ℝ} {g : E → Ω → E} {σ s L R j ell : ℝ}
    (ho : LongTails.Setups.CovarianceSmoothConvex.IsCovarianceGradient μ f g σ s)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hL : 0 < L) (hσ : 0 ≤ σ) (hs : 0 ≤ s) (hR : 0 < R)
    (x0 xstar : E) (hmin : IsMinOn f Set.univ xstar) (hdist : ‖x0 - xstar‖ ≤ R)
    (k T : ℕ) (hk : 1 ≤ k) (hT : 1 ≤ T) (hj : 1 ≤ j) (hell : 0 < ell)
    (hej : ell ≤ j) (hjk : j ≤ k) (hkT : (k : ℝ) ^ 2 ≤ T)
    (hleak : 18 * (T : ℝ) * Real.exp (-j) ≤ ell) :
    let cfg := LongTails.Algorithms.CovarianceAcceleratedTuned.config x0 L R σ s j ell k T
    P {ω | 65536 * (L * R ^ 2 * (k : ℝ) ^ 2 / (T : ℝ) ^ 2 +
      R * (σ + s * Real.sqrt ell) / Real.sqrt T) <
        f (output cfg g (fun i => ξ i ω) (k + T)) - f xstar} ≤
      ENNReal.ofReal ((T : ℝ) * Real.exp (-7 * k / 32)) +
        2 * ENNReal.ofReal (Real.exp (-ell)) := by
  intro cfg
  let M := 100 * (σ * T + L * R * k)
  let ν := σ ^ 2 * T + j * M ^ 2 * ell / (T : ℝ) ^ 2
  let b := R / (32 * T * Real.sqrt ν)
  let η := 1 / (16 * R * s * T * Real.sqrt T / Real.sqrt ell + 64 * R * M + 64 * b * j * M ^ 2)
  let a := Real.sqrt (b / η)
  let proxy : ℝ≥0 := ⟨1 / (32 * j), by positivity⟩
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hjpos : 0 < j := by linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hν : 0 < ν := tuning_variance_pos hM hjpos hell hTpos
  have hb : 0 < b := by dsimp [b]; positivity
  have hsteps := reciprocal_step_bounds hR hs hTpos hell hM hb hjpos
  have hη : 0 < η := hsteps.1
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos hb hη)
  have ha2 : a ^ 2 = b / η := Real.sq_sqrt (by positivity)
  have hwindow : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hwindowR : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast hwindow
  have hp0 : 0 < (proxy : ℝ) := by change 0 < 1 / (32 * j); positivity
  have hp1 : (proxy : ℝ) ≤ 1 / 4 := by
    change 1 / (32 * j) ≤ 1 / 4
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)).mpr
    linarith
  have heproxy : 1 / (32 * (proxy : ℝ)) = j := by
    change 1 / (32 * (1 / (32 * j))) = j
    field_simp
  let B := fun t : ℕ => 48 * σ + 96 * L * R * k / ((t : ℝ) + 1)
  have hcaps (t : ℕ) (ht : t < T) :
      2 * R * weight η t * B t ≤ 1 / 4 ∧ (weight η t * a) ^ 2 * B t ^ 2 ≤ (proxy : ℝ) := by
    have hbound : weight η t * B t ≤ η * M := weighted_residual_le hη.le hσ hL.le hR.le k T t ht
    have hz : 0 ≤ weight η t * B t := by dsimp [weight, B]; positivity
    exact CovarianceAcceleratedTuning.clipping_scalar_caps hη hR.le hjpos ha2 hz hbound hsteps.2.1 hsteps.2.2
  have hsmall (t : ℕ) (ht : t < T) :
      2 * R * weight η t * (48 * σ + 96 * L * R * ((k - 1 : ℕ) + 1) / ((t : ℝ) + 1)) ≤ 1 / 4 := by
    simpa only [B, hwindowR] using (hcaps t ht).1
  have hproxy (t : ℕ) (ht : t < T) :
      (weight η t * a) ^ 2 * (48 * σ + 96 * L * R * ((k - 1 : ℕ) + 1) / ((t : ℝ) + 1)) ^ 2 ≤ (proxy : ℝ) := by
    simpa only [B, hwindowR] using (hcaps t ht).2
  have hprob := CovarianceAcceleratedConvergence.grid_failure_probability hsamples ho hc hg hlip hL.le hσ hR.le
    (show 0 < R / (T : ℝ) ^ 2 by positivity) ha hη (le_refl (2 * η * L))
    (show 0 < η * L * R ^ 2 by positivity) x0 xstar hmin hdist (k - 1) T (by omega) ell hp0 hp1 hsmall hproxy
  have hcost : (∑ t ∈ Finset.range T, momentCost cfg R σ s proxy t) ≤
      320 * η ^ 2 * R ^ 2 * s ^ 2 * (T : ℝ) ^ 3 +
        80 * η ^ 2 * a ^ 2 * σ ^ 2 * (T : ℝ) ^ 3 + ell := by
    have hh := moment_cost_sum_le η R s a σ (Real.exp (-1 / (32 * (proxy : ℝ)))) T
    have he : -1 / (32 * (proxy : ℝ)) = -j := by rw [neg_div, heproxy]
    rw [he] at hh
    change (∑ t ∈ Finset.range T, (320 * weight η t ^ 2 * R ^ 2 * s ^ 2 +
      80 * weight η t ^ 2 * a ^ 2 * σ ^ 2 + 18 * Real.exp (-1 / (32 * (proxy : ℝ))))) ≤ _
    rw [he]
    linarith
  have hnorm := normalized_energy_bound hL.le hη hb hTr hell.le ha2
    (cumulative_lower hη.le T) hcost
  have hrate := CovarianceAcceleratedTuning.tuned_rate_bound hL hR hσ hs hkr hTpos hjpos hell hej hjk hkT
  change 5 * L * R ^ 2 / (T : ℝ) ^ 2 + R ^ 2 / (b * (T : ℝ) ^ 2) +
    1280 * η * R ^ 2 * s ^ 2 * T + 320 * b * σ ^ 2 * T + 8 * ell / (η * (T : ℝ) ^ 2) ≤ _ at hrate
  have hthreshold := hnorm.trans hrate
  have hcfg : LongTails.Algorithms.CovarianceAcceleratedGrid.config x0 R (R / (T : ℝ) ^ 2)
      a η (2 * η * L) (η * L * R ^ 2) (k - 1) = cfg := rfl
  rw [hcfg] at hprob
  rw [hwindow, hwindowR] at hprob
  apply (measure_mono ?_).trans hprob
  intro ω hbad
  exact lt_of_le_of_lt hthreshold hbad

end LongTails.Proofs.CovarianceAcceleratedRate
