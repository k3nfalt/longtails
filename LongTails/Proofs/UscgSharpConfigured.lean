import LongTails.Proofs.UscgSharpProbability
import LongTails.Proofs.UscgSharpTuning

namespace LongTails.Proofs.UscgSharpConfigured

open MeasureTheory
open LongTails.Setups.UscgConstant
open LongTails.Setups.UscgHighProbability (Public)
open LongTails.Algorithms.UscgSharpConfidence
open OracleTemplate.NormBallLMO
open UscgSharpTuning

lemma hard_path_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {f : Space q.d → ℝ} {g : Space q.d → Ω → Space q.d}
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (H : Problem q.N q.L q.L₂ q.σ q.Δ q.x₁ f g p)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (hR : ∀ v, q.N v ≤ 1 → ‖v‖ ≤ q.R) (hdef : ∀ x, q.N x = 0 → x = 0)
    (hL : 0 < q.L) (hζ : 0 < q.ζ) (he : 0 < q.ε)
    (hδ : 0 < q.δ) (hδ1 : q.δ ≤ 1)
    (hζnorm : ∀ u, dualNorm q.N u ≤ q.ζ * ‖u‖)
    {lmo : Space q.d → Space q.d} (hlmo : IsBallLMO q.N 1 lmo)
    (hhard : ¬2 * q.L * q.Δ ≤ q.ε ^ 2) :
    let T := horizon q
    let α := 1 / inverseMemory q
    let η := 4 * q.Δ / (q.ε * T)
    P.real {ξ | q.ε * T < ∑ t ∈ Finset.range T,
      dualNorm q.N (gradient f (path (fun x m => x + η • lmo m)
        (correctedWeight α) q.x₁ g ξ t).1)} ≤ q.δ := by
  let T := horizon q
  let a := inverseMemory q
  let α := 1 / a
  let η := 4 * q.Δ / (q.ε * T)
  let D := q.L * q.Δ / q.ε ^ 2
  let ℓ := Real.log (1 / q.δ)
  let G := 2 * q.ε * Real.sqrt D
  let s := q.ε / (256 * q.ζ)
  have hΔ : 0 < q.Δ := by nlinarith [lt_of_not_ge hhard, sq_pos_of_pos he]
  have hD : 0 < D := by dsimp [D]; positivity
  have hTn : 0 < T := horizon_pos q hL.le hΔ.le hδ hδ1
  have hT : 0 < (T : ℝ) := by exact_mod_cast hTn
  have ha : 2 ≤ a := inverseMemory_ge_two q
  have ha0 : 0 < a := by linarith
  have hα : 0 < α ∧ α < 1 := memory_pos_lt_one q
  have hη : 0 < η := by dsimp [η]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hℓ : 0 ≤ ℓ := confidence_log_nonneg hδ hδ1
  have hcount : 4096 * a * (1 + D + Real.sqrt D * (1 + ℓ)) ≤ (T : ℝ) :=
    horizon_lower q hhard
  have hDscale : q.ε ^ 2 * D = q.L * q.Δ := by dsimp [D]; field_simp
  have hscale : q.L * η * T = 4 * q.ε * D := by
    dsimp [η, D]
    field_simp
  have hηscale : η * q.ε * T = 4 * q.Δ := by dsimp [η]; field_simp
  have hGsq : 4 * q.L * q.Δ ≤ G ^ 2 := by
    dsimp [G]
    nlinarith [Real.sq_sqrt hD.le]
  have hparts := count_parts ha hD.le (Real.sqrt_nonneg D) hℓ hT he
    (mul_pos hL hη).le hcount hscale
  have hn : 10 * q.ζ * s ≤ q.ε / 16 := by
    have heq : 10 * q.ζ * s = 5 * q.ε / 128 := by dsimp [s]; field_simp; ring
    rw [heq]
    linarith
  have ht : 2 * G + 8 * G / α * ℓ + 2 * G / α ≤ q.ε * T / 16 := by
    convert hparts.2.2 using 1
    dsimp [G, α]
    field_simp
  have hb : 2 * q.L * η / α ≤ q.ε / 16 := by
    convert hparts.1 using 1
    dsimp [α]
    field_simp
  have hm := margin_from_parts hα.1 hη.le hζ hT.le hηscale hn ht hb hparts.2.1
  have hp := UscgSharpProbability.path_tail H hIID hR hdef hL hζ hζnorm hlmo
    hα.1 hα.2 hη hs hG (memory_noise q he hζ) hGsq T hm
    (show 2 * q.Δ ≤ η * (q.ε * T) by nlinarith [hηscale])
  have hex : Real.exp (-ℓ) = q.δ := by
    dsimp [ℓ]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    simp
  exact hp.trans_eq hex

end LongTails.Proofs.UscgSharpConfigured
