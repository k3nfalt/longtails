import LongTails.Proofs.RobustPLBlocks
import LongTails.Proofs.RobustPLRun
import LongTails.Proofs.RobustPLTuning

open MeasureTheory Set
open scoped ENNReal

namespace OracleTemplate.HeavyTailedPLHessian

open RobustPLPotential PLHessian

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

lemma tuned_accuracy {f : E → ℝ} {g : E → Ω → E} {u x0 : E} {L μ ρ σ p Δ ε : ℝ}
    (H : PLHessian.Hyp (Measure.pi fun _ : Fin 65 => P) f
      (fun x (_ : Fin 65 → Ω) => gradient f x) u L μ ρ 0 1)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = gradient f x)
    (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ p) P)
    (hpm : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ p ∂P) ≤ σ ^ p)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hgap : f x0 - f u ≤ Δ) :
    let h := stepFraction L μ ρ σ p ε
    let η := h / μ
    let τ := clipRadius L μ ρ σ p ε
    let n := ⌈64 / h * Real.log (1 + 48 * Real.sqrt (L / μ) * Δ / ε)⌉₊
    let m := ⌈8 / h⌉₊
    let G := fun x (block : Fin 65 → Ω) => flatEstimate τ (fun i => g x (block i))
    ∫⁻ ω, ENNReal.ofReal (f (sgdSeq G η x0 ω.2 (n + ω.1.val)) - f u)
      ∂((PMF.uniformOfFintype (Fin (m + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin 65 => P)) ≤ ENNReal.ofReal ε := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let h := stepFraction L μ ρ σ p ε
  let η := h / μ
  let τ := clipRadius L μ ρ σ p ε
  let t := threshold L μ ρ ε
  let ν := noiseLevel L μ ρ ε
  let lam := 32 * Real.sqrt (L / μ) / μ
  let V := 2 ^ 64 * σ ^ p * τ ^ (2 - p)
  let G := fun x (block : Fin 65 → Ω) => flatEstimate τ (fun i => g x (block i))
  let n := ⌈64 / h * Real.log (1 + 48 * Real.sqrt (L / μ) * Δ / ε)⌉₊
  let m := ⌈8 / h⌉₊
  obtain ⟨ht, hν, hh, hh1, hη, hτ, hστ, hlocal, hstep, hsmall, hVsmall, hQsmall,
    hBsmall, hnoise, hνε⟩ := tuning_conditions H.μ_pos H.μ_le hσ hp hε (ρ := ρ)
  have hμ := H.μ_pos
  change 0 < η at hη
  change 0 < h at hh
  change h ≤ 1 at hh1
  change η * V ≤ ν at hnoise
  have hlam0 : 0 ≤ lam := by dsimp [lam]; positivity
  have hlam : lam * μ = 32 * Real.sqrt (L / μ) := by dsimp [lam]; field_simp
  have hG : Measurable (Function.uncurry G) := measurable_sampledReply hg τ
  have hs : ∀ y, Integrable (fun ω => pot f u lam t (y - η • G y ω))
      (Measure.pi fun _ : Fin 65 => P) ∧
      (∫ ω, pot f u lam t (y - η • G y ω) ∂Measure.pi (fun _ : Fin 65 => P)) ≤
        (1 - μ * η / 64) * pot f u lam t y - η / 2 * (f y - f u) + 290 * η ^ 2 * V :=
    sampled_contraction H hg hgi hmean hp.le hp2 hσ hτ hστ hpi hpm hη ht hlam hlocal
      hstep hsmall hVsmall hQsmall hBsmall
  have he : μ * η = h := by dsimp [η]; field_simp
  have hq : 0 < μ * η / 64 := by rw [he]; positivity
  have hq1 : μ * η / 64 ≤ 1 := by rw [he]; linarith
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hC : 0 ≤ 290 * η ^ 2 * V :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg η)) hV0
  have hW : pot f u lam t x0 ≤ 48 * Real.sqrt (L / μ) * Δ / μ := by
    exact (H.pot_le_gap ht x0).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (by positivity)) H.μ_pos.le)
  have hw := warmup_potential H.μ_pos hη (by rwa [he]) (Real.sqrt_nonneg _) hΔ hε hW hnoise
  rw [he] at hw
  have hm : 8 / (μ * η) ≤ (m : ℝ) + 1 := by
    rw [he]
    exact (Nat.le_ceil (8 / h)).trans (by linarith)
  have ha := window_noise_accuracy H.μ_pos hη hε hν.le hνε hm
  change 2 * ((ε + 18560 * ν) / μ) / η / (m + 1) + 580 * ν ≤ ε at ha
  have hacc : 2 * ((ε + 18560 * ν) / μ) / η / (m + 1) +
      2 * (290 * η ^ 2 * V) / η ≤ ε := by
    have hn : 2 * (290 * η ^ 2 * V) / η = 580 * (η * V) := by field_simp; ring
    rw [hn]
    linarith
  exact RobustPLProcess.window_accuracy H hG hη ht hlam0 hq hq1 hC hs x0 n m
    (by simpa only [he, n] using hw) hacc

end OracleTemplate.HeavyTailedPLHessian
