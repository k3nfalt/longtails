import LongTails.Proofs.UscgSharpPath
import LongTails.Proofs.UscgSharpNoise
import LongTails.Proofs.UscgSharpSchedule

namespace LongTails.Proofs.UscgSharpProbability

open MeasureTheory
open LongTails.Setups.UscgConstant
open LongTails.Algorithms.UscgSharpConfidence
open OracleTemplate.NormBallLMO
open UscgSharpTracking UscgSharpGeometry UscgSharpSchedule
open scoped RealInnerProductSpace

lemma path_tail {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {N : Seminorm ℝ (Space d)} {L L₂ σ Δ R ζ α η s G ε ℓ : ℝ}
    {x₁ : Space d} {f : Space d → ℝ} {g : Space d → Ω → Space d}
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (H : Problem N L L₂ σ Δ x₁ f g p)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    (hL : 0 < L) (hζ : 0 < ζ) (hζnorm : ∀ u, dualNorm N u ≤ ζ * ‖u‖)
    {lmo : Space d → Space d} (hlmo : IsBallLMO N 1 lmo)
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) (hs : 0 < s) (hG : 0 < G)
    (hscale : α * σ ^ 2 ≤ s ^ 2) (hGsq : 4 * L * Δ ≤ G ^ 2) (T : ℕ)
    (hmargin : η * (2 * ζ * (5 * s * T + (4 * (G / ζ) / α) * ℓ + G / ζ) +
      2 * (G + T * (L * η)) / α) + T * (L * η ^ 2 / 2) ≤ Δ)
    (haccuracy : 2 * Δ ≤ η * (ε * T)) :
    P.real {ξ | ε * T < ∑ t ∈ Finset.range T,
      dualNorm N (gradient f (path (fun x m => x + η • lmo m)
        (correctedWeight α) x₁ g ξ t).1)} ≤ Real.exp (-ℓ) := by
  let step := fun x m => x + η • lmo m
  have hstep : Measurable (fun z : Space d × Space d => step z.1 z.2) :=
    measurable_fst.add ((hlmo.measurable.comp measurable_snd).const_smul η)
  let Y := UscgSharpNoise.noise step (correctedWeight α) x₁ f g
  let Z := CappedMomentumProcess.ema α Y
  let C := G / ζ
  let Q := 5 * s * T + (4 * C / α) * ℓ
  have hC : 0 < C := div_pos hG hζ
  have htail := UscgSharpNoise.noise_tail H hIID hstep (correctedWeight α)
    hα hα1.le hs hC hscale T ℓ
  apply le_trans (b := P.real {ξ | Q ≤ ∑ t ∈ Finset.range T, min C ‖Z t ξ‖}) ?_ htail
  apply measureReal_mono (μ := P) ?_ (by finiteness)
  intro ξ hbad
  by_contra hnot
  have hgood : ∑ t ∈ Finset.range T, min C ‖Z t ξ‖ ≤ Q := le_of_lt (lt_of_not_ge hnot)
  let x := fun t => (path step (correctedWeight α) x₁ g ξ t).1
  let v := fun t => lmo (path step (correctedWeight α) x₁ g ξ (t + 1)).2
  let samples := fun t => g (x t) (ξ t)
  have hx : ∀ t, x (t + 1) = x t + η • v t := by
    intro t
    rfl
  have hv : ∀ t, N (v t) ≤ 1 := fun t => hlmo.feasible _
  have hm : ∀ t w, N w ≤ 1 →
      ⟪mean α samples (t + 1), v t⟫ ≤ ⟪mean α samples (t + 1), w⟫ := by
    intro t w hw
    have hraw := raw_momentum step hα hα1 x₁ g ξ (t + 1)
    change mass α (t + 1) • (path step (correctedWeight α) x₁ g ξ (t + 1)).2 =
      mean α samples (t + 1) at hraw
    rw [← hraw]
    exact scaled_direction (mass_pos hα hα1 (by omega)).le
      (hlmo.minimal (path step (correctedWeight α) x₁ g ξ (t + 1)).2) w hw
  have hz : ∀ t, mean α (fun k => samples k - gradient f (x k)) t = Z t ξ := by
    intro t
    exact mean_eval α Y ξ t
  have hcap : ∑ t ∈ Finset.range T, min (G / ζ)
      ‖mean α (fun k => samples k - gradient f (x k)) (t + 1)‖ ≤ Q + C := by
    simp_rw [hz]
    have hh := UscgSharpDescent.shifted_sum_le
      (a := fun t => min C ‖Z t ξ‖) (le_min hC.le (norm_nonneg _))
      (fun t => min_le_left C ‖Z t ξ‖) T
    exact hh.trans (by linarith)
  obtain ⟨fmin, hfmin, hgap⟩ := H.lower
  have hp := UscgSharpPath.pathwise_bound hR hdef hL.le hα hα1.le hη.le hζ hG.le hζnorm
    H.differentiable H.lipschitz hfmin
    (gradient_self_bound hR hdef hL H.differentiable H.lipschitz hfmin hlmo)
    x v samples T hgap hGsq hv hx hm hcap hmargin
  have hh := hp.2
  have hbad' : ε * T < ∑ t ∈ Finset.range T, dualNorm N (gradient f (x t)) := hbad
  have hstrict := mul_lt_mul_of_pos_left hbad' hη
  linarith

end LongTails.Proofs.UscgSharpProbability
