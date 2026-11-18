import LongTails.Proofs.LocalizedClippedPath

open MeasureTheory OracleTemplate
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)
open LongTails.Setups.TerminalClippingConvex
open LongTails.Algorithms.LocalizedClippedSubgradient
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.LocalizedClippedSubgradient

lemma iteration_scale (p : Public) (hδ : 0 < p.δ) (hδ' : p.δ < 1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hn : p.ε < p.G * p.R) :
    0 < iterations p ∧
    Real.log (1 / p.δ) + 1 / 8 ≤
      (1 / (8 * p.R ^ 2)) * step p * p.ε * iterations p := by
  have hG : 0 < p.G := (mul_pos_iff_of_pos_right hR).mp (hε.trans hn)
  have hv : 0 < p.G^2 + p.B^2*p.R^2 := by positivity
  have hδ8 : 1 < 8 / p.δ := (lt_div_iff₀ hδ).2 (by linarith)
  have hl := Real.log_pos hδ8
  unfold iterations
  rw [ite_eq_right hn.not_ge]
  refine ⟨Nat.ceil_pos.mpr (by positivity), ?_⟩
  have h2 := Real.log_le_sub_one_of_pos (show 0 < (1/8:ℝ) by norm_num)
  rw [one_div, Real.log_inv] at h2
  let m := 1024*p.R^2*(p.G^2+p.B^2*p.R^2)*Real.log (8/p.δ)/p.ε^2
  calc
    Real.log (1 / p.δ) + 1 / 8 ≤ 2 * Real.log (8 / p.δ) := by
      rw [one_div, Real.log_inv, Real.log_div (by norm_num) hδ.ne']
      linarith [Real.log_neg hδ hδ']
    _ = 1 / (8 * p.R^2) * step p * p.ε * m := by
      dsimp only [step, m]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil m)
      (mul_nonneg (mul_nonneg (by positivity) (div_nonneg hε.le (mul_nonneg (by norm_num) hv.le))) hε.le)


lemma confidence {Ω : Type} [MeasurableSpace Ω] (p : Public)
    (hδ : 0 < p.δ) (hδ' : p.δ < 1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hn : p.ε < p.G * p.R)
    (g : Vector p.d → Ω → Vector p.d) (proj : Vector p.d → Vector p.d)
    (ν : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun i (ω : ℕ → Ω) => ω i)
      (ν : Measure Ω) (P : Measure (ℕ → Ω)))
    {X : Set (Vector p.d)} {f : Vector p.d → ℝ} (hX : MeasurableSet X)
    (hf : ConvexOn ℝ X f) (hfm : Measurable f) (hx0 : p.x0 ∈ X)
    (hp : Measurable proj) (hpX : ∀ y, proj y ∈ X)
    (hpv : ∀ y, ∀ u ∈ X, ⟪y-proj y,u-proj y⟫ ≤ 0)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x ∈ X, Integrable (g x) (ν : Measure Ω))
    (hmi : ∀ x ∈ X, Integrable (fun ω => ‖g x ω‖^2) (ν : Measure Ω))
    (hm : ∀ x ∈ X, (∫ ω, ‖g x ω‖^2 ∂(ν : Measure Ω)) ≤ p.B^2 * ‖x-p.x0‖^2+p.G^2)
    {u : Vector p.d} (hu : u ∈ X) (hd : ‖p.x0-u‖ ≤ p.R)
    (hsub : ∀ x ∈ X, f x - f u ≤ ⟪∫ ω, g x ω ∂(ν : Measure Ω),x-u⟫) :
    let y := fun ξ : ℕ → Ω => execute (TerminalClipping.sampleOracle p g proj P)
      (algorithm p) (fun _ => 2 * iterations p) () ξ
    Measurable y ∧ (∀ ξ, y ξ ∈ X) ∧
      (P : Measure (ℕ → Ω)) {ξ | p.ε < f (y ξ) - f u} ≤ ENNReal.ofReal p.δ := by
  let N := iterations p
  let τ := 1 / (8 * p.R^2)
  let η := step p
  let F := fun x => f x - f u
  let V := fun s : Vector p.d × ℝ => τ * ‖s.1-u‖^2 + 2*τ*η*s.2
  let good := fun s : Vector p.d × ℝ => s.1 ∈ X ∧ ‖s.1-p.x0‖ ≤ p.R
  let trans := fun (s : Vector p.d × ℝ) (ω : Ω) => (next p g proj s.1 ω, s.2 + F s.1)
  let read := fun (ξ : ℕ → Ω) (i : Fin N) => ξ (2*i.val)
  have hn' := iteration_scale p hδ hδ' hR hε hn
  have hN : 0 < N := hn'.1
  have hG : 0 < p.G := (mul_pos_iff_of_pos_right hR).mp (hε.trans hn)
  have hv : 0 < p.G^2+p.B^2*p.R^2 := by positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hv)
  have hc : 0 ≤ τ * η * p.ε := by positivity
  have hgset : MeasurableSet {s | good s} := (hX.preimage measurable_fst).inter
    (measurableSet_le (measurable_fst.sub_const p.x0).norm measurable_const)
  have ht : Measurable (Function.uncurry trans) :=
    ((next_measurable p hg hp).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      (measurable_fst.snd.add ((hfm.sub_const _).comp measurable_fst.fst))
  have hV : Measurable V := by dsimp [V]; fun_prop
  have hs (s : Vector p.d × ℝ) (hs : good s) :
      Integrable (fun ω => Real.exp (V (trans s ω))) (ν : Measure Ω) ∧
      (∫ ω, Real.exp (V (trans s ω)) ∂(ν : Measure Ω)) ≤ Real.exp (V s + τ*η*p.ε) := by
    have hmoment := (hm s.1 hs.1).trans (show _ ≤ p.G^2+p.B^2*p.R^2 by
      linarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs.2 2) (sq_nonneg p.B)])
    have hd1 := clipped_drift p hR hε hv (hg.comp (measurable_const.prodMk measurable_id))
      (hgi _ hs.1) (hmi _ hs.1) hmoment hp hd hs.2
      (fun y => TerminalClipping.projection_distance (hpv y u hu)) (hsub _ hs.1)
    change Integrable (fun ω => Real.exp (τ*‖next p g proj s.1 ω-u‖^2+2*τ*η*(s.2+F s.1))) _ ∧ _
    simp only [V, trans, Real.exp_add]
    refine ⟨hd1.1.mul_const _, ?_⟩
    rw [integral_mul_const]
    have hh := mul_le_mul_of_nonneg_right hd1.2 (Real.exp_nonneg (2*τ*η*(s.2+F s.1)))
    apply hh.trans_eq
    simp only [← Real.exp_add]
    congr 1
    dsimp [τ, η, F]
    ring
  have htail := TerminalClipping.stopped_exponential_tail hgset ht hV ν hc hs N (p.x0,0)
    (2*τ*η*N*p.ε)
  have hread : MeasurePreserving read (P : Measure (ℕ → Ω)) (Measure.pi fun _ : Fin N => (ν : Measure Ω)) := by
    simpa [read] using FixedBatchConfidence.iid_finite_block_law (TerminalClipping.even_samples_iid hIID) 0 N
  let Z := fun ξ : ℕ → Ω => execute (TerminalClipping.sampleOracle p g proj P)
    (algorithm p) (fun _ => 2*N) () ξ
  have heq (ξ : ℕ → Ω) : Z ξ = ((N : ℝ)⁻¹) •
      ∑ t ∈ Finset.range N, path p g proj (fun k => ξ (2*k)) t := by
    have hh := congrArg Prod.snd (iterate_path p g proj (fun k => ξ (2*k)) N)
    calc
      Z ξ = (N : ℝ)⁻¹ • (iterateSamples (transition p g proj) N (p.x0,0) (read ξ)).2 := by
        simpa only [Z, N, read, output, ite_eq_right hn'.1.ne'] using execute_output p g proj P ξ
      _ = _ := congrArg (fun v : Vector p.d => (N : ℝ)⁻¹ • v) hh
  have ha (ξ : ℕ → Ω) := average_gap hf hN (path p g proj (fun k => ξ (2*k)))
    (fun i => (path_good p g proj _ hR.le hx0 hpX hpv i).1) u
  have hiter : Measurable (fun ξ => (iterateSamples (transition p g proj) N (p.x0,0) (read ξ)).2) := ((GapStrongGrowth.iterateSamples_measurable (transition_measurable p hg hp) N).comp
    (measurable_const.prodMk hread.measurable)).snd
  have hZ : Measurable Z := by
    have he : Z = fun ξ => ((N : ℝ)⁻¹) •
        (iterateSamples (transition p g proj) N (p.x0, 0) (read ξ)).2 := by
      funext ξ
      simpa [Z, N, output, hn'.1.ne', read] using execute_output p g proj P ξ
    rw [he]
    exact hiter.const_smul ((N : ℝ)⁻¹)
  change Measurable Z ∧ (∀ ξ, Z ξ ∈ X) ∧ _
  refine ⟨hZ, fun ξ => by rw [heq ξ]; exact (ha ξ).1, ?_⟩
  have hinc : {ξ | p.ε < f (Z ξ)-f u} ⊆ read ⁻¹'
      {z | 2*τ*η*N*p.ε < V (iterateSamples (TerminalClipping.stopUnless good trans) N (p.x0,0) z)} := by
    intro ξ hbad
    have hpath := stopped_path p g proj (fun k => ξ (2*k)) F
      (fun x => x ∈ X ∧ ‖x-p.x0‖ ≤ p.R) (path_good p g proj _ hR.le hx0 hpX hpv) N
    change 2*τ*η*N*p.ε < V (iterateSamples _ N _ (read ξ))
    rw [show iterateSamples (TerminalClipping.stopUnless good trans) N (p.x0,0) (read ξ) = _ from hpath]
    have h := (ha ξ).2
    rw [← heq ξ] at h
    have h1 := (mul_lt_mul_of_pos_left hbad (Nat.cast_pos.mpr hN)).trans_le h
    have h2 := mul_lt_mul_of_pos_left h1 (show 0 < 2*τ*η by positivity)
    dsimp only [V, F, Prod.fst, Prod.snd]
    linarith only [h2, mul_nonneg hτ.le (sq_nonneg ‖path p g proj (fun k => ξ (2*k)) N - u‖)]
  apply (measure_mono hinc).trans ((hread.measure_preimage_le _).trans (htail.trans ?_))
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_log hδ]
  apply Real.exp_le_exp.mpr
  have hstart : τ * ‖p.x0-u‖^2 ≤ 1/8 := by
    dsimp [τ]
    field_simp
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hd 2]
  have hb := hn'.2
  rw [one_div, Real.log_inv] at hb
  dsimp only [V, Prod.fst, Prod.snd, mul_zero, add_zero]
  change -Real.log p.δ + 1/8 ≤ τ*η*p.ε*N at hb
  linarith only [hb, hstart]

end LongTails.Proofs.LocalizedClippedSubgradient
