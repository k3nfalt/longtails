import LongTails.Proofs.FairSampling
import LongTails.Proofs.FairTuningError
import LongTails.Proofs.FairBudget
import LongTails.Setups.RelativeEnergySymmetricNonconvex

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory ProbabilityTheory
open LongTails.Setups.RelativeEnergySymmetricNonconvex

lemma tuned_trajectory_accuracy (q : Params) (hv : spec.valid q)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (g : q.E → q.Ω → q.E) (f : q.E → ℝ)
    (hF : ∀ x, HasGradientAt f (gradient f x) x)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (hgap : ∀ x, f q.x0 - f x ≤ q.Δ) (hg : Measurable (Function.uncurry g))
    (hs : ∀ x, p.map (fun ω => g x ω - gradient f x) = p.map (fun ω => -(g x ω - gradient f x)))
    (hp : ∀ x, p.real {ω | q.r < ‖g x ω - gradient f x‖} ≤ 1 / 64)
    (hrel : ∀ x y, (∫ ω, (‖(g x ω - gradient f x) - (g y ω - gradient f y)‖ /
      (q.r + ‖g x ω - gradient f x‖ + ‖g y ω - gradient f y‖)) ^ 2 ∂p) ≤ q.κ ^ 2 * ‖x - y‖ ^ 2) :
    let cfg := tunedConfig q.L q.κ q.r q.Δ q.ε
    let Q := (algorithm cfg q.x0).law.val.prod (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin cfg.m => p)
    Integrable (fun z : Fin (max 1 cfg.T) × (ℕ → Fin cfg.m → q.Ω) =>
      ‖gradient f (trajectory cfg g q.x0 z.2 z.1.val).1‖) Q ∧
    (∫ z : Fin (max 1 cfg.T) × (ℕ → Fin cfg.m → q.Ω),
      ‖gradient f (trajectory cfg g q.x0 z.2 z.1.val).1‖ ∂Q) ≤ q.ε := by
  rcases hv with ⟨hL, hκ, hr, hΔ, hε⟩
  let cfg := tunedConfig q.L q.κ q.r q.Δ q.ε
  let k := tuneBlockQuarter q.L q.r q.Δ q.ε
  let δ := (1 / 4 : ℝ) ^ k
  let V0 := 9 * cfg.R ^ 2 + (2 * cfg.G + 3 * cfg.R) ^ 2 * δ
  let V1 := (2 : ℝ) ^ 23 * cfg.R ^ 2 * (q.κ ^ 2 * cfg.η ^ 2 + δ) + 8 * cfg.B ^ 2 * δ
  let β0 := (2 * cfg.G + 3 * cfg.R) * δ
  let β1 := 2 / cfg.B * ((2 : ℝ) ^ 23 * cfg.R ^ 2 * (q.κ ^ 2 * cfg.η ^ 2 + δ)) + 4 * cfg.B * δ
  let μ := Measure.pi fun _ : Fin cfg.m => p
  let P := Measure.infinitePi fun _ : ℕ => μ
  have hk : 0 < k := tuneBlockQuarter_pos q.L q.r q.Δ q.ε
  have hm : 0 < cfg.m := by change 0 < 4 * k; omega
  have hq : 0 < cfg.q := tunePeriod_pos hL hκ hε
  have hR : 0 < cfg.R := tuneRadius_pos hr hε
  have hG : 0 ≤ cfg.G := tuneGradientBound_nonneg hL hε
  have hB : 0 < cfg.B := tuneClip_pos hr hε
  have hη : 0 < cfg.η := tuneStep_pos hL hε
  have hT : 0 < cfg.T := tuneIterations_pos q.L q.Δ q.ε
  have hb : ∀ t, 0 < cfg.batch t := tuned_batch_pos hr hε
  have hFm : Measurable (gradient f) :=
    (show LipschitzWith ⟨q.L, hL.le⟩ (gradient f) from
      (lipschitzWith_iff_norm_sub_le).mpr hLip).continuous.measurable
  have hl : ∀ t < cfg.T, ∀ ξ,
      ‖localBias cfg μ g (gradient f) t (trajectory cfg g q.x0 ξ t).1 (trajectory cfg g q.x0 ξ t).2.1‖ ≤
        (if cfg.isRefresh t then β0 else β1) ∧
      observationVariance cfg μ g t (trajectory cfg g q.x0 ξ t).1 (trajectory cfg g q.x0 ξ t).2.1 ≤
        (if cfg.isRefresh t then V0 else V1) := by
    intro t ht ξ
    exact trajectory_oracle_bounds cfg hk rfl hR hB hη.le hL hΔ hr hg
      (show q.r ≤ cfg.R by change q.r ≤ q.r + q.ε; linarith) hF hLip q.x0 hgap le_rfl
      (tune_step_clip hL hr hε) hs hp hrel ξ ht
  have herr : ∀ t < cfg.T,
      Integrable (fun ξ => ‖direction cfg g q.x0 ξ t - gradient f (trajectory cfg g q.x0 ξ t).1‖) P ∧
      (∫ ξ, ‖direction cfg g q.x0 ξ t - gradient f (trajectory cfg g q.x0 ξ t).1‖ ∂P) ≤ q.ε / 16 := by
    intro t ht
    have hh := expected_error_uniform_bound cfg hq hm hR hG hB.le μ hg hFm q.x0 hb
      (show 0 ≤ V1 by dsimp [V1, δ]; positivity)
      (show 0 ≤ β1 by dsimp [β1, δ]; positivity)
      (fun j hj ξ => (hl j hj ξ).2) (fun j hj ξ => (hl j hj ξ).1) ht
    exact ⟨hh.1, hh.2.trans (tuned_error_bound hL hκ hr hΔ hε)⟩
  have hdes := trajectory_expected_descent cfg hm hR hη.le hL hΔ hF hFm hLip hg q.x0 hgap le_rfl P herr
  have hsum : (∑ t ∈ Finset.range cfg.T, ∫ ξ, ‖gradient f (trajectory cfg g q.x0 ξ t).1‖ ∂P) ≤ cfg.T * q.ε :=
    tuned_descent_accuracy hL hΔ hε hdes.2
  let : Nonempty (Fin (max 1 cfg.T)) := ⟨⟨0, by omega⟩⟩
  have hu := uniform_trajectory_bound cfg hm hR hT hg hFm q.x0 P
    (fun ξ t ht => trajectory_gradient_bound cfg hη.le hL hΔ hF hLip g q.x0 hgap le_rfl ξ ht.le) hsum
  exact hu.2

lemma tuned_execute_accuracy (q : Params) (hv : spec.valid q) (f : q.E → ℝ)
    (O : Oracle q.E q.E) (hadm : spec.admissible q f O) (K : ℕ)
    (hK : (tunedConfig q.L q.κ q.r q.Δ q.ε).calls ≤ K) :
    let A := algorithm (tunedConfig q.L q.κ q.r q.Δ q.ε) q.x0
    spec.successful q f (fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => K) z.1 z.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨g, p, P, hIID, rfl, hF, hLip, hgap, hg, hs, hp, hrel⟩ := hadm
  obtain ⟨hL, hκ, hr, hΔ, hε⟩ := hv
  let cfg := tunedConfig q.L q.κ q.r q.Δ q.ε
  let paired := P.map (fun ξ k => ξ (k / 2))
  let O : Oracle q.E q.E := { Seed := fun _ => q.Ω, law := paired, answer := fun _ (_, x) ω => g x ω }
  let : Nonempty (Fin (max 1 cfg.T)) := ⟨⟨0, by omega⟩⟩
  let μ := (PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod (paired : Measure (ℕ → q.Ω))
  let Fout := fun z : Fin (max 1 cfg.T) × (ℕ → q.Ω) => execute O (algorithm cfg q.x0) (fun _ => K) z.1 z.2
  let φ := fun x : q.E => ‖gradient f x‖
  change Measurable Fout ∧ Integrable (fun z => φ (Fout z)) μ ∧ (∫ z, φ (Fout z) ∂μ) ≤ q.ε
  have hm : 0 < cfg.m := by have := tuneBlockQuarter_pos q.L q.r q.Δ q.ε; change 0 < 4 * _; omega
  have hR : 0 < cfg.R := tuneRadius_pos hr hε
  have hT : 0 < cfg.T := tuneIterations_pos q.L q.Δ q.ε
  have hmeas : Measurable Fout := measurable_execute cfg hm hR hg q.x0 paired K
  have hgrad : LipschitzWith ⟨q.L, hL.le⟩ (gradient f) := (lipschitzWith_iff_norm_sub_le).mpr hLip
  have hφ : Measurable φ := hgrad.continuous.measurable.norm
  have hid := execute_identDistrib cfg hm hR hT (tuned_batch_pos hr hε) hg q.x0
    (p : Measure q.Ω) P hIID.independent hIID.marginal K hK
  have hh := hid.comp hφ
  have ht := tuned_trajectory_accuracy q ⟨hL, hκ, hr, hΔ, hε⟩ (p : Measure q.Ω) g f hF hLip hgap hg hs hp hrel
  refine ⟨hmeas, hh.integrable_iff.mpr ht.1, ?_⟩
  exact hh.integral_eq.le.trans ht.2

end OracleTemplate.FairVarianceReduction
