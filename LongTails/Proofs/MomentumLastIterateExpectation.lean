import LongTails.Proofs.MomentumLastIterateTrajectory

open MeasureTheory Set InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MomentumConvex

open LongTails.Setups.MomentumLipschitzConvex

open OracleTemplate.SampledConvex (integral_prefix extend measurable_extend extend_agree)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]

noncomputable abbrev prodLaw (p : Measure Ξ) : Measure (ℕ → Ξ) := Measure.infinitePi fun _ : ℕ => p

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma norm_sq_combo_le (a b : E) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ‖c • a + (1 - c) • b‖ ^ 2 ≤ c * ‖a‖ ^ 2 + (1 - c) * ‖b‖ ^ 2 := by
  have h2 : ‖c • a + (1 - c) • b‖ ≤ c * ‖a‖ + (1 - c) * ‖b‖ := by
    calc ‖c • a + (1 - c) • b‖ ≤ ‖c • a‖ + ‖(1 - c) • b‖ := norm_add_le _ _
      _ = c * ‖a‖ + (1 - c) * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
          abs_of_nonneg (by linarith)]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - c)]

omit [MeasurableSpace Ξ] in
lemma integral_combo {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {A B C D : α → ℝ} (hA : Integrable A μ) (hB : Integrable B μ) (hC : Integrable C μ)
    (hD : Integrable D μ) (r1 r2 r3 c : ℝ) :
    Integrable (fun x => A x + r1 * B x + r2 * C x + r3 * D x + c) μ ∧
    ∫ x, (A x + r1 * B x + r2 * C x + r3 * D x + c) ∂μ =
      ∫ x, A x ∂μ + r1 * ∫ x, B x ∂μ + r2 * ∫ x, C x ∂μ + r3 * ∫ x, D x ∂μ + c := by
  have h1 : Integrable (fun x => A x + r1 * B x) μ := hA.add (hB.const_mul r1)
  have h2 : Integrable (fun x => A x + r1 * B x + r2 * C x) μ := h1.add (hC.const_mul r2)
  have h3 : Integrable (fun x => A x + r1 * B x + r2 * C x + r3 * D x) μ := h2.add (hD.const_mul r3)
  refine ⟨h3.add (integrable_const c), ?_⟩
  rw [integral_add h3 (integrable_const c), integral_add h2 (hD.const_mul r3),
    integral_add h1 (hC.const_mul r2), integral_add hA (hB.const_mul r1),
    integral_const_mul, integral_const_mul, integral_const_mul]
  simp

variable {p : Measure Ξ} [IsProbabilityMeasure p] {f : E → ℝ} {Gr : Ξ → E → E} {G : ℝ} {xstar : E}

omit [CompleteSpace E] in
lemma Hyp.grad_sq (h : Hyp p f Gr G xstar) (β γ : ℝ) (N : ℕ) (x0 : E) (k : ℕ) :
    Integrable (fun ξ : ℕ → Ξ => ‖Gr (ξ k) (traj Gr β γ N x0 ξ k).1‖ ^ 2) (prodLaw p) ∧
    ∫ ξ, ‖Gr (ξ k) (traj Gr β γ N x0 ξ k).1‖ ^ 2 ∂(prodLaw p) ≤ G ^ 2 := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  let X : (Fin k → Ξ) → E := fun u => (traj Gr β γ N x0 (extend ω0 u) k).1
  have hX : Measurable X := ((measurable_traj h.meas β γ N x0 k).1).comp (measurable_extend ω0)
  have hXeq : ∀ ξ : ℕ → Ξ, X (fun i : Fin k => ξ i) = (traj Gr β γ N x0 ξ k).1 := fun ξ => by
    simp only [X]; rw [traj_congr Gr β γ N x0 k (extend_agree ω0 ξ)]
  let Φ : E → Ξ → ℝ := fun y ω => ‖Gr ω y‖ ^ 2
  have hΦ : Measurable (Function.uncurry Φ) :=
    (h.meas.comp (measurable_snd.prodMk measurable_fst)).norm.pow_const 2
  have hfun : (fun ξ : ℕ → Ξ => Φ (X (fun i : Fin k => ξ i)) (ξ k)) =
      fun ξ : ℕ → Ξ => ‖Gr (ξ k) (traj Gr β γ N x0 ξ k).1‖ ^ 2 := by
    funext ξ; simp only [Φ]; rw [hXeq]
  have hi := integrable_prefix_of_bdd p k X hX Φ hΦ (fun y ω => sq_nonneg _) (G ^ 2)
    (fun y => ⟨h.sq_int y, h.sq_le y⟩)
  obtain ⟨hin, heq⟩ := integral_prefix p k X hX Φ hΦ hi
  rw [hfun] at hi heq
  refine ⟨hi, ?_⟩
  rw [heq]
  calc ∫ ξ : ℕ → Ξ, (∫ ω, Φ (X (fun i : Fin k => ξ i)) ω ∂p) ∂(prodLaw p)
      ≤ ∫ _ξ : ℕ → Ξ, G ^ 2 ∂(prodLaw p) := integral_mono hin (integrable_const _)
        (fun ξ => h.sq_le _)
    _ = G ^ 2 := by simp

omit [CompleteSpace E] in
lemma Hyp.memLp_grad (h : Hyp p f Gr G xstar) (β γ : ℝ) (N : ℕ) (x0 : E) (k : ℕ) :
    MemLp (fun ξ : ℕ → Ξ => Gr (ξ k) (traj Gr β γ N x0 ξ k).1) 2 (prodLaw p) := by
  have hm : Measurable (fun ξ : ℕ → Ξ => Gr (ξ k) (traj Gr β γ N x0 ξ k).1) :=
    h.meas.comp ((measurable_pi_apply k).prodMk (measurable_traj h.meas β γ N x0 k).1)
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr (h.grad_sq β γ N x0 k).1

omit [CompleteSpace E] in
lemma Hyp.memLp_traj (h : Hyp p f Gr G xstar) (β γ : ℝ) (N : ℕ) (x0 : E) :
    ∀ k, MemLp (fun ξ : ℕ → Ξ => (traj Gr β γ N x0 ξ k).1) 2 (prodLaw p) ∧
      MemLp (fun ξ : ℕ → Ξ => (traj Gr β γ N x0 ξ k).2) 2 (prodLaw p) := by
  intro k
  induction k with
  | zero => exact ⟨memLp_const _, memLp_const _⟩
  | succ k ih =>
    have hm : MemLp (fun ξ : ℕ → Ξ =>
        β • (traj Gr β γ N x0 ξ k).2 + (1 - β) • Gr (ξ k) (traj Gr β γ N x0 ξ k).1) 2 (prodLaw p) :=
      (ih.2.const_smul β).add ((h.memLp_grad β γ N x0 k).const_smul (1 - β))
    simp only [traj]
    exact ⟨ih.1.sub (hm.const_smul _), hm⟩

omit [CompleteSpace E] in
lemma Hyp.memLp_refp (h : Hyp p f Gr G xstar) (β γ : ℝ) (N : ℕ) (x0 : E) :
    ∀ k, MemLp (fun ξ : ℕ → Ξ => refp Gr β γ N x0 xstar ξ k) 2 (prodLaw p) := by
  intro k
  induction k with
  | zero => exact memLp_const _
  | succ k ih =>
    simp only [refp]
    exact (ih.const_smul _).add (((h.memLp_traj β γ N x0 k).1).const_smul _)

omit [CompleteSpace E] in
lemma Hyp.memLp_zed (h : Hyp p f Gr G xstar) (β γ : ℝ) (N : ℕ) (x0 : E) (k : ℕ) :
    MemLp (fun ξ : ℕ → Ξ => zed Gr β γ N x0 ξ k) 2 (prodLaw p) := by
  unfold zed
  exact (h.memLp_traj β γ N x0 k).1.sub (((h.memLp_traj β γ N x0 k).2).const_smul _)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma integrable_sq_sub {U V : (ℕ → Ξ) → E} (hU : MemLp U 2 (prodLaw p))
    (hV : MemLp V 2 (prodLaw p)) : Integrable (fun ξ => ‖U ξ - V ξ‖ ^ 2) (prodLaw p) :=
  (memLp_two_iff_integrable_sq_norm (hU.sub hV).aestronglyMeasurable).mp (hU.sub hV)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma integrable_sq_norm {U : (ℕ → Ξ) → E} (hU : MemLp U 2 (prodLaw p)) :
    Integrable (fun ξ => ‖U ξ‖ ^ 2) (prodLaw p) :=
  (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU

omit [CompleteSpace E] in
lemma Hyp.integrable_gap (h : Hyp p f Gr G xstar) {U : (ℕ → Ξ) → E}
    (hU : MemLp U 2 (prodLaw p)) : Integrable (fun ξ => f (U ξ) - f xstar) (prodLaw p) := by
  have hn : Integrable (fun ξ => ‖U ξ - xstar‖) (prodLaw p) :=
    ((hU.sub (memLp_const xstar)).integrable one_le_two).norm
  refine Integrable.mono' (hn.const_mul G)
    ((h.continuous.comp_aestronglyMeasurable hU.aestronglyMeasurable).sub aestronglyMeasurable_const)
    (Filter.Eventually.of_forall (fun ξ => ?_))
  obtain ⟨h0, h1⟩ := h.gap_bounds (U ξ)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

omit [CompleteSpace E] in
lemma Hyp.moment (h : Hyp p f Gr G xstar) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (γ : ℝ) (N : ℕ)
    (x0 : E) : ∀ k, ∫ ξ, ‖(traj Gr β γ N x0 ξ k).2‖ ^ 2 ∂(prodLaw p) ≤ G ^ 2 := by
  intro k
  induction k with
  | zero => simp [traj, sq_nonneg]
  | succ k ih =>
    obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
    let X : (Fin k → Ξ) → E × E := fun u => traj Gr β γ N x0 (extend ω0 u) k
    have hX : Measurable X :=
      (((measurable_traj h.meas β γ N x0 k).1).prodMk ((measurable_traj h.meas β γ N x0 k).2)).comp
        (measurable_extend ω0)
    have hXeq : ∀ ξ : ℕ → Ξ, X (fun i : Fin k => ξ i) = traj Gr β γ N x0 ξ k := fun ξ => by
      simp only [X]; rw [traj_congr Gr β γ N x0 k (extend_agree ω0 ξ)]
    let Φ : E × E → Ξ → ℝ := fun y ω => ‖β • y.2 + (1 - β) • Gr ω y.1‖ ^ 2
    have hΦ : Measurable (Function.uncurry Φ) := by
      have hg : Measurable (fun r : (E × E) × Ξ => Gr r.2 r.1.1) :=
        h.meas.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
      exact (((measurable_snd.comp measurable_fst).const_smul β).add (hg.const_smul (1 - β))).norm.pow_const 2
    have hfun : (fun ξ : ℕ → Ξ => Φ (X (fun i : Fin k => ξ i)) (ξ k)) =
        fun ξ : ℕ → Ξ => ‖(traj Gr β γ N x0 ξ (k + 1)).2‖ ^ 2 := by
      funext ξ; simp only [Φ, traj]; rw [hXeq]
    have hi : Integrable (fun ξ : ℕ → Ξ => Φ (X (fun i : Fin k => ξ i)) (ξ k)) (prodLaw p) := by
      rw [hfun]; exact integrable_sq_norm (h.memLp_traj β γ N x0 (k + 1)).2
    obtain ⟨hin, heq⟩ := integral_prefix p k X hX Φ hΦ hi
    rw [hfun] at heq
    rw [heq]
    have hb : Integrable (fun ξ : ℕ → Ξ => β * ‖(traj Gr β γ N x0 ξ k).2‖ ^ 2 + (1 - β) * G ^ 2)
        (prodLaw p) :=
      ((integrable_sq_norm (h.memLp_traj β γ N x0 k).2).const_mul β).add (integrable_const _)
    calc ∫ ξ : ℕ → Ξ, (∫ ω, Φ (X (fun i : Fin k => ξ i)) ω ∂p) ∂(prodLaw p)
        ≤ ∫ ξ : ℕ → Ξ, (β * ‖(traj Gr β γ N x0 ξ k).2‖ ^ 2 + (1 - β) * G ^ 2) ∂(prodLaw p) := by
          refine integral_mono hin hb (fun ξ => ?_)
          have := (h.moment_sample (traj Gr β γ N x0 ξ k).1 (traj Gr β γ N x0 ξ k).2 hβ0 hβ1).2
          simp only [Φ]; rw [hXeq]; exact this
      _ = β * ∫ ξ, ‖(traj Gr β γ N x0 ξ k).2‖ ^ 2 ∂(prodLaw p) + (1 - β) * G ^ 2 := by
          rw [integral_add ((integrable_sq_norm (h.memLp_traj β γ N x0 k).2).const_mul β)
            (integrable_const _), integral_const_mul]
          simp
      _ ≤ G ^ 2 := by nlinarith [ih]

end OracleTemplate.MomentumConvex
