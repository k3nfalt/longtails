import LongTails.Proofs.CappedMomentumProcess
import LongTails.Proofs.MuonProcess
import LongTails.Proofs.LmoTrajectory
import LongTails.Proofs.NormBallGeometry

namespace LongTails.Proofs.UscgSharpNoise

open MeasureTheory
open LongTails.Setups.UscgConstant
open OracleTemplate.NormBallLMO
open LongTails.Proofs.MuonProcess LongTails.Algorithms.ValidatedMuon

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

lemma adapted_path {step : Space d → Space d → Space d}
    (hstep : Measurable (fun z : Space d × Space d => step z.1 z.2))
    (α : ℕ → ℝ) (x₁ : Space d) {g : Space d → Ω → Space d}
    (hg : Measurable (Function.uncurry g)) :
    ∀ t, Measurable[past t] (fun ξ : ℕ → Ω => path step α x₁ g ξ t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have ih' := ih.mono (past_mono (Nat.le_succ t)) le_rfl
    have hm := ((hg.comp (ih'.fst.prodMk (measurable_eval_past (Nat.lt_succ_self t)))).const_smul
      (α (t + 1))).add (ih'.snd.const_smul (1 - α (t + 1)))
    simpa only [path_succ, Function.comp_def, Function.uncurry, Pi.add_apply, Pi.smul_apply] using
      (hstep.comp (ih'.fst.prodMk hm)).prodMk hm

noncomputable def noise (step : Space d → Space d → Space d) (α : ℕ → ℝ) (x₁ : Space d)
    (f : Space d → ℝ) (g : Space d → Ω → Space d) (t : ℕ) (ξ : ℕ → Ω) : Space d :=
  g (path step α x₁ g ξ t).1 (ξ t) - gradient f (path step α x₁ g ξ t).1

lemma noise_moments {N : Seminorm ℝ (Space d)} {L L₂ σ Δ : ℝ}
    {x₁ : Space d} {f : Space d → ℝ} {g : Space d → Ω → Space d}
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (H : Problem N L L₂ σ Δ x₁ f g p)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p P)
    {step : Space d → Space d → Space d}
    (hstep : Measurable (fun z : Space d × Space d => step z.1 z.2))
    (α : ℕ → ℝ) (t : ℕ) :
    MemLp (noise step α x₁ f g t) 2 P ∧
    P[noise step α x₁ f g t | past t] =ᵐ[P] 0 ∧
    ∀ᵐ ξ ∂P, P[(fun v => ‖noise step α x₁ f g t v‖ ^ 2) | past t] ξ ≤ σ ^ 2 := by
  let W : Space d → Ω → Space d := fun x ω => g x ω - gradient f x
  have hW : Measurable (Function.uncurry W) :=
    H.measurable.sub ((measurable_gradient_space f).comp measurable_fst)
  have hrows : ∀ x, MemLp (W x) 2 p := by
    intro x
    apply (OracleTemplate.TwoSidedPL.memLp_two_iff_sq
      ((hW.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr
    exact H.variance_integrable x
  have hmean : ∀ x, (∫ ω, W x ω ∂p) = 0 := by
    intro x
    dsimp [W]
    rw [integral_sub (H.integrable x) (integrable_const _), H.unbiased x]
    simp
  exact adaptive_kernel_moments hIID t (adapted_path hstep α x₁ H.measurable t).fst
    hW hrows hmean H.variance

lemma noise_adapted {step : Space d → Space d → Space d}
    (hstep : Measurable (fun z : Space d × Space d => step z.1 z.2))
    (α : ℕ → ℝ) (x₁ : Space d) (f : Space d → ℝ)
    {g : Space d → Ω → Space d} (hg : Measurable (Function.uncurry g)) (t : ℕ) :
    StronglyMeasurable[past (t + 1)] (noise step α x₁ f g t) := by
  have hx := ((adapted_path hstep α x₁ hg t).fst).mono (past_mono (Nat.le_succ t)) le_rfl
  exact ((hg.comp (hx.prodMk (measurable_eval_past (Nat.lt_succ_self t)))).sub
    ((measurable_gradient_space f).comp hx)).stronglyMeasurable

lemma noise_tail {N : Seminorm ℝ (Space d)} {L L₂ σ Δ : ℝ}
    {x₁ : Space d} {f : Space d → ℝ} {g : Space d → Ω → Space d}
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (H : Problem N L L₂ σ Δ x₁ f g p)
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p P)
    {step : Space d → Space d → Space d}
    (hstep : Measurable (fun z : Space d × Space d => step z.1 z.2))
    (weights : ℕ → ℝ) {α s G : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : 0 < s) (hG : 0 < G)
    (hscale : α * σ ^ 2 ≤ s ^ 2) (n : ℕ) (u : ℝ) :
    P.real {ξ | 5 * s * n + (4 * G / α) * u ≤
      ∑ i ∈ Finset.range n, min G
        ‖CappedMomentumProcess.ema α (noise step weights x₁ f g) i ξ‖} ≤ Real.exp (-u) := by
  apply CappedMomentumProcess.ema_capped_tail (fun _ _ h => past_mono h) past_le
    hα hα1 hs hG hscale
    (fun t => (noise_moments H hIID hstep weights t).1)
    (noise_adapted hstep weights x₁ f H.measurable)
    (fun t => (noise_moments H hIID hstep weights t).2.1)
    (fun t => (noise_moments H hIID hstep weights t).2.2)

end LongTails.Proofs.UscgSharpNoise
