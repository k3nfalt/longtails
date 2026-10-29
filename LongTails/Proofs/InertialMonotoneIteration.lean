import LongTails.Proofs.InertialMonotonePotential
import LongTails.Proofs.InertialMonotoneExecution

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.InertialMonotone

lemma finite_prefix_two_blocks {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n b : ℕ) :
    MeasurePreserving (fun ξ : Fin (b + b + n) → Ω =>
      ((fun i : Fin n => ξ ⟨i, by have hi := i.isLt; omega⟩),
        ((fun i : Fin b => ξ ⟨n + i, by have hi := i.isLt; omega⟩),
          (fun i : Fin b => ξ ⟨n + (b + i), by have hi := i.isLt; omega⟩))))
      (Measure.pi fun _ : Fin (b + b + n) => P)
      ((Measure.pi fun _ : Fin n => P).prod
        ((Measure.pi fun _ : Fin b => P).prod (Measure.pi fun _ : Fin b => P))) := by
  have hh := ((MeasurePreserving.id (Measure.pi fun _ : Fin n => P)).prod
    (StochasticGeneralized.two_blocks_preserving P b)).comp
    (StochasticGeneralized.splitStream_preserving P n)
  refine ⟨by fun_prop, ?_⟩
  rw [← (StochasticGeneralized.prefix_preserving P (b + b + n)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact hh.map_eq

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma finiteRun_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (μ η r : ℕ → ℝ) (b : ℕ → ℕ) (state : E × E) (k : ℕ) :
    Measurable (finiteRun g μ η r b state k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    let previous := fun ξ : Fin (calls b (k + 1)) → Ω => finiteRun g μ η r b state k
      (fun i => ξ ⟨i, by simp only [calls]; omega⟩)
    have hpre : Measurable previous := ih.comp (by fun_prop)
    let first := fun ξ : Fin (calls b (k + 1)) → Ω =>
      fun i : Fin (b k) => ξ ⟨calls b k + i, by simp only [calls]; have hi := i.isLt; omega⟩
    let second := fun ξ : Fin (calls b (k + 1)) → Ω =>
      fun i : Fin (b k) => ξ ⟨calls b k + (b k + i), by simp only [calls]; have hi := i.isLt; omega⟩
    have hfirst : Measurable first := by dsimp [first]; fun_prop
    have hsecond : Measurable second := by dsimp [second]; fun_prop
    have hw := (batchTrial_measurable hg (μ k) (η k) (b k)).comp
      (hpre.prodMk (hfirst.prodMk hsecond))
    change Measurable (fun ξ => transported (r k) (previous ξ).1
      (batchTrial g (μ k) (η k) (b k) (previous ξ) (first ξ) (second ξ)))
    unfold transported
    fun_prop

lemma random_state_energy_step [FiniteDimensional ℝ E] [CompleteSpace E]
    {A : Type} [MeasurableSpace A] {M : Measure A} [IsProbabilityMeasure M]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : E → E} (hc : Continuous F) (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫)
    {g : E → Ω → E} {σ L μ η r : ℝ}
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g σ)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ L * ‖a - b‖)
    (hμ : 0 < μ) (hr : 0 < r) (hrmax : r ≤ 1 / 16) (hη : η = 2 * r / μ)
    (hcap : 2 * η * μ + 2 * η ^ 2 * (L + μ) ^ 2 ≤ 1)
    {X : A → E × E} (hX : Measurable X)
    (hXi : Integrable (fun a => energy F hc hm μ hμ (X a)) M)
    {b : ℕ} (hb : 0 < b) :
    let Q := Measure.pi (fun _ : Fin b => P)
    let hnext : 0 < μ * (1 + r / 2) := by positivity
    let f := fun ω : A × ((Fin b → Ω) × (Fin b → Ω)) =>
      energy F hc hm (μ * (1 + r / 2)) hnext
        (transported r (X ω.1).1 (batchTrial g μ η b (X ω.1) ω.2.1 ω.2.2))
    Integrable f (M.prod (Q.prod Q)) ∧ (∫ ω, f ω ∂M.prod (Q.prod Q)) ≤
      (∫ a, energy F hc hm μ hμ (X a) ∂M) + 14 * r ^ 2 * (σ ^ 2 / b) := by
  intro Q hnext f
  let δ := 14 * r ^ 2 * (σ ^ 2 / b)
  have hw := (batchTrial_measurable hg.measurable μ η b).comp
    ((hX.comp measurable_fst).prodMk measurable_snd)
  have hf : Measurable f := by
    apply (energy_continuous F hc hm (μ * (1 + r / 2)) hnext).measurable.comp
    dsimp [transported]
    fun_prop
  have hs (a : A) := batch_energy_step hc hm hg hlip hμ hr hrmax hη hcap (X a) hb
  have hu : Integrable (fun a => energy F hc hm μ hμ (X a) + δ) M :=
    hXi.add (integrable_const _)
  have hi : Integrable f (M.prod (Q.prod Q)) := integrable_nonnegative_kernel hf
    (fun a ω => energy_nonneg F hc hm (μ * (1 + r / 2)) hnext _)
    (fun a => (hs a).1) hu (fun a => (hs a).2)
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi.integral_prod_left hu (fun a => (hs a).2)
  have ha := integral_add hXi (integrable_const δ)
  change (∫ a, ∫ ω, f (a, ω) ∂Q.prod Q ∂M) ≤
    ∫ a, energy F hc hm μ hμ (X a) + δ ∂M at hh
  rw [ha] at hh
  simp only [integral_const, probReal_univ, one_smul] at hh
  rw [integral_prod f hi]
  exact hh

lemma finiteRun_energy_succ [FiniteDimensional ℝ E] [CompleteSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : E → E} (hc : Continuous F) (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫)
    {g : E → Ω → E} {σ L : ℝ}
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g σ)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ L * ‖a - b‖)
    (μ η r : ℕ → ℝ) (b : ℕ → ℕ) (state : E × E) (k : ℕ)
    (hμ : 0 < μ k) (hr : 0 < r k) (hrmax : r k ≤ 1 / 16)
    (hη : η k = 2 * r k / μ k)
    (hcap : 2 * η k * μ k + 2 * (η k) ^ 2 * (L + μ k) ^ 2 ≤ 1)
    (hb : 0 < b k)
    (hi : Integrable (fun ξ => energy F hc hm (μ k) hμ (finiteRun g μ η r b state k ξ))
      (Measure.pi fun _ : Fin (calls b k) => P)) :
    let hnext : 0 < μ k * (1 + r k / 2) := by positivity
    let f := fun ξ => energy F hc hm (μ k * (1 + r k / 2)) hnext
      (finiteRun g μ η r b state (k + 1) ξ)
    Integrable f (Measure.pi fun _ : Fin (calls b (k + 1)) => P) ∧
    (∫ ξ, f ξ ∂Measure.pi (fun _ : Fin (calls b (k + 1)) => P)) ≤
      (∫ ξ, energy F hc hm (μ k) hμ (finiteRun g μ η r b state k ξ)
        ∂Measure.pi (fun _ : Fin (calls b k) => P)) + 14 * (r k) ^ 2 * (σ ^ 2 / b k) := by
  intro hnext f
  have hs := random_state_energy_step hc hm hg hlip hμ hr hrmax hη hcap
    (finiteRun_measurable hg.measurable μ η r b state k) hi hb
  have hlaw := finite_prefix_two_blocks P (calls b k) (b k)
  refine ⟨hlaw.integrable_comp_of_integrable hs.1, ?_⟩
  exact (hlaw.hasLaw.integral_comp hs.1.aestronglyMeasurable).trans_le hs.2

lemma finiteRun_energy_bound [FiniteDimensional ℝ E] [CompleteSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : E → E} (hc : Continuous F) (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫)
    {g : E → Ω → E} {σ L : ℝ}
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g σ)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ L * ‖a - b‖)
    (μ η r : ℕ → ℝ) (b : ℕ → ℕ) (state : E × E) (N : ℕ)
    (hμ : ∀ k, k ≤ N → 0 < μ k)
    (hr : ∀ k, k < N → 0 < r k) (hrmax : ∀ k, k < N → r k ≤ 1 / 16)
    (hη : ∀ k, k < N → η k = 2 * r k / μ k)
    (hcap : ∀ k, k < N → 2 * η k * μ k + 2 * (η k) ^ 2 * (L + μ k) ^ 2 ≤ 1)
    (hb : ∀ k, k < N → 0 < b k)
    (hupdate : ∀ k, k < N → μ (k + 1) = μ k * (1 + r k / 2)) :
    ∀ k (hk : k ≤ N),
      Integrable (fun ξ => energy F hc hm (μ k) (hμ k hk) (finiteRun g μ η r b state k ξ))
        (Measure.pi fun _ : Fin (calls b k) => P) ∧
      (∫ ξ, energy F hc hm (μ k) (hμ k hk) (finiteRun g μ η r b state k ξ)
        ∂Measure.pi (fun _ : Fin (calls b k) => P)) ≤
      energy F hc hm (μ 0) (hμ 0 (Nat.zero_le N)) state +
        ∑ j ∈ Finset.range k, 14 * (r j) ^ 2 * (σ ^ 2 / b j) := by
  intro k
  induction k with
  | zero =>
    intro hk
    simp only [finiteRun]
    refine ⟨integrable_const _, ?_⟩
    simp only [Finset.sum_range_zero, add_zero, integral_const, probReal_univ, one_smul]
    exact le_rfl
  | succ k ih =>
    intro hk
    have hk0 : k ≤ N := by omega
    have hkl : k < N := by omega
    have hi := ih hk0
    have hs := finiteRun_energy_succ hc hm hg hlip μ η r b state k (hμ k hk0)
      (hr k hkl) (hrmax k hkl) (hη k hkl) (hcap k hkl) (hb k hkl) hi.1
    have he := (hupdate k hkl).symm
    simp only [he] at hs
    refine ⟨hs.1, ?_⟩
    rw [Finset.sum_range_succ]
    linarith [hs.2, hi.2]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma iid_run_integral {Ξ : Type} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {p : Measure Ω} [IsProbabilityMeasure p]
    {ξ : ℕ → Ξ → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (g : E → Ω → E) (μ η r : ℕ → ℝ) (b : ℕ → ℕ) (state : E × E) (k : ℕ)
    (φ : E × E → ℝ)
    (hi : Integrable (fun u => φ (finiteRun g μ η r b state k u))
      (Measure.pi fun _ : Fin (calls b k) => p)) :
    Integrable (fun ω => φ (QueryPlan.sampledEval g (fun j => ξ j ω)
      (runPlan μ η r b k state) 0)) P ∧
    (∫ ω, φ (QueryPlan.sampledEval g (fun j => ξ j ω) (runPlan μ η r b k state) 0) ∂P) =
      ∫ u, φ (finiteRun g μ η r b state k u) ∂Measure.pi (fun _ : Fin (calls b k) => p) := by
  simp_rw [runPlan_eval_finiteRun, Nat.zero_add]
  have hlaw := measurePreserving_fst.comp (hξ.prefix_tail_law (calls b k))
  exact ⟨hlaw.integrable_comp_of_integrable hi, hlaw.hasLaw.integral_comp hi.aestronglyMeasurable⟩

end OracleTemplate.InertialMonotone
