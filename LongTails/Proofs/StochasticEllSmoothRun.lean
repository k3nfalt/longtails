import LongTails.Algorithms.StochasticEllSmoothMedoid
import LongTails.Proofs.StochasticEllSmoothStep
import LongTails.Proofs.HighProbabilityAdapted
import LongTails.Proofs.StochasticEllSmoothEstimator
import LongTails.Proofs.SublevelPLBlocks

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.StochasticEllSmoothRun

open LongTails.Setups.EllSmoothNonconvex LongTails.Algorithms.StochasticEllSmoothMedoid
open LongTails.Proofs.StochasticEllSmoothStep LongTails.Proofs.HighProbabilityAdapted

variable {E Z : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def roundMap (ℓ : ℝ → ℝ) (ε : ℝ) (est : E → Z → E) (s : E × Bool) (z : Z) : E × Bool :=
  roundStep ℓ ε s (est s.1 z)

noncomputable def err (f : E → ℝ) (est : E → Z → E) (x : E) (z : Z) : ℝ := ‖est x z - gradient f x‖

noncomputable def excess (f : E → ℝ) (est : E → Z → E) (α : ℝ) (x : E) (z : Z) : ℝ :=
  {z' | α < err f est x z'}.indicator (fun z' => err f est x z') z

lemma excess_nonneg (f : E → ℝ) (est : E → Z → E) (α : ℝ) (x : E) (z : Z) :
    0 ≤ excess f est α x z :=
  Set.indicator_nonneg (fun _ _ => norm_nonneg _) z

lemma err_le (f : E → ℝ) (est : E → Z → E) {α : ℝ} (hα : 0 ≤ α) (x : E) (z : Z) :
    err f est x z ≤ α + excess f est α x z := by
  unfold excess
  by_cases h : α < err f est x z
  · rw [Set.indicator_of_mem (show z ∈ {z' | α < err f est x z'} from h)]
    linarith
  · rw [Set.indicator_of_notMem (show z ∉ {z' | α < err f est x z'} from h)]
    push Not at h
    linarith

variable (ℓ : ℝ → ℝ) (ε : ℝ) (est : E → Z → E) (x0 : E) (b : ℕ → Z)

omit [CompleteSpace E] in
lemma frozen_succ (t : ℕ) (h : (traj (roundMap ℓ ε est) (x0, false) b t).2 = true) :
    traj (roundMap ℓ ε est) (x0, false) b (t + 1) = traj (roundMap ℓ ε est) (x0, false) b t := by
  simp only [traj, roundMap, roundStep, h, ↓reduceIte]

omit [CompleteSpace E] in
lemma frozen_mono {s t : ℕ} (hst : s ≤ t)
    (h : (traj (roundMap ℓ ε est) (x0, false) b s).2 = true) :
    traj (roundMap ℓ ε est) (x0, false) b t = traj (roundMap ℓ ε est) (x0, false) b s := by
  induction t with
  | zero => rw [Nat.le_zero.mp hst]
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have ht := ih (by omega)
      rw [frozen_succ ℓ ε est x0 b t (by rw [ht]; exact h), ht]
    · rw [show s = t + 1 by omega]

lemma frozen_bound (f : E → ℝ) {α : ℝ} (hα : 0 ≤ α) (t : ℕ)
    (h : (traj (roundMap ℓ ε est) (x0, false) b t).2 = true) :
    ‖gradient f (traj (roundMap ℓ ε est) (x0, false) b t).1‖ ≤
      ε / 2 + α + ∑ j ∈ Finset.range t,
        excess f est α (traj (roundMap ℓ ε est) (x0, false) b j).1 (b j) := by
  induction t with
  | zero => simp [traj] at h
  | succ t ih =>
    set s := traj (roundMap ℓ ε est) (x0, false) b t with hs
    have hnn := excess_nonneg f est α s.1 (b t)
    rw [Finset.sum_range_succ]
    by_cases hf : s.2 = true
    · have he := frozen_succ ℓ ε est x0 b t hf
      rw [← hs] at he
      rw [he]
      linarith [ih hf]
    · have hstep : traj (roundMap ℓ ε est) (x0, false) b (t + 1) = roundStep ℓ ε s (est s.1 (b t)) :=
        rfl
      rw [hstep] at h ⊢
      simp only [roundStep, hf, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hv : ‖est s.1 (b t)‖ ≤ ε / 2
      · simp only [hv, ↓reduceIte]
        have he := err_le f est hα s.1 (b t)
        have htri : ‖gradient f s.1‖ ≤ ‖est s.1 (b t)‖ + err f est s.1 (b t) := by
          have := norm_sub_le (est s.1 (b t)) (est s.1 (b t) - gradient f s.1)
          simp only [sub_sub_cancel] at this
          unfold err
          linarith
        have hsum : 0 ≤ ∑ j ∈ Finset.range t,
            excess f est α (traj (roundMap ℓ ε est) (x0, false) b j).1 (b j) :=
          Finset.sum_nonneg fun j _ => excess_nonneg f est α _ _
        linarith
      · simp only [hv, ↓reduceIte] at h
        exact absurd h (by simp)

variable {f : E → ℝ} {ρ Δ : ℝ}

lemma decrease_while_moving (hreg : Regular ℓ ρ) (hρ2 : ρ ≤ 2) (hε : 0 < ε)
    (hg : ∀ y, HasGradientAt f (gradient f y) y) (hd : Differentiable ℝ (gradient f))
    (hH : ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ ℓ ‖gradient f y‖) (t : ℕ)
    (hacc : ∀ j < t, err f est (traj (roundMap ℓ ε est) (x0, false) b j).1 (b j) ≤ ε / 8)
    (hnf : (traj (roundMap ℓ ε est) (x0, false) b t).2 = false) :
    t * (ε ^ 2 / (72 * ℓ ε)) ≤ f x0 - f (traj (roundMap ℓ ε est) (x0, false) b t).1 := by
  induction t with
  | zero => simp [traj]
  | succ t ih =>
    set s := traj (roundMap ℓ ε est) (x0, false) b t with hs
    have hstep : traj (roundMap ℓ ε est) (x0, false) b (t + 1) = roundStep ℓ ε s (est s.1 (b t)) :=
      rfl
    have hsf : s.2 = false := by
      by_contra hc
      have hc' : s.2 = true := by simpa using hc
      have := frozen_succ ℓ ε est x0 b t hc'
      rw [← hs] at this
      rw [this] at hnf
      rw [hnf] at hc'
      exact absurd hc' (by simp)
    have ih' := ih (fun j hj => hacc j (by omega)) hsf
    rw [hstep] at hnf ⊢
    simp only [roundStep, hsf, Bool.false_eq_true, ↓reduceIte] at hnf ⊢
    by_cases hv : ‖est s.1 (b t)‖ ≤ ε / 2
    · simp only [hv, ↓reduceIte] at hnf
      exact absurd hnf (by simp)
    · simp only [hv, ↓reduceIte]
      push Not at hv
      have hv0 : 0 < ‖est s.1 (b t)‖ := lt_trans (by positivity) hv
      have herr : ‖est s.1 (b t) - gradient f s.1‖ ≤ ‖est s.1 (b t)‖ / 4 := by
        have := hacc t (by omega)
        unfold err at this
        linarith
      have hl : 0 < ℓ (3 * ‖est s.1 (b t)‖) := hreg.2.2 _ (by positivity)
      have hdesc := inexact_descent f ℓ s.1 (est s.1 (b t)) hreg.1 hg hd hH hv0 herr hl
      have hlow := inexact_decrease_lower ℓ ρ ε ‖est s.1 (b t)‖ hρ2 hreg hε hv
      push_cast
      rw [add_mul, one_mul]
      linarith

lemma freezes (hreg : Regular ℓ ρ) (hρ2 : ρ ≤ 2) (hε : 0 < ε)
    (hg : ∀ y, HasGradientAt f (gradient f y) y) (hd : Differentiable ℝ (gradient f))
    (hH : ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ ℓ ‖gradient f y‖) (hΔ : ∀ y, f x0 - f y ≤ Δ)
    (T : ℕ) (hT : Δ < T * (ε ^ 2 / (72 * ℓ ε)))
    (hacc : ∀ j < T, err f est (traj (roundMap ℓ ε est) (x0, false) b j).1 (b j) ≤ ε / 8) :
    (traj (roundMap ℓ ε est) (x0, false) b T).2 = true := by
  by_contra hc
  have hnf : (traj (roundMap ℓ ε est) (x0, false) b T).2 = false := by simpa using hc
  have h := decrease_while_moving ℓ ε est x0 b hreg hρ2 hε hg hd hH T hacc hnf
  have := hΔ (traj (roundMap ℓ ε est) (x0, false) b T).1
  linarith

lemma output_bound (hreg : Regular ℓ ρ) (hρ2 : ρ ≤ 2) (hε : 0 < ε)
    (hg : ∀ y, HasGradientAt f (gradient f y) y) (hd : Differentiable ℝ (gradient f))
    (hH : ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ ℓ ‖gradient f y‖) (hΔ : ∀ y, f x0 - f y ≤ Δ)
    (T : ℕ) (hT : Δ < T * (ε ^ 2 / (72 * ℓ ε))) {G0 : ℝ} (hG0 : ‖gradient f x0‖ ≤ G0) :
    ‖gradient f (finish x0 (traj (roundMap ℓ ε est) (x0, false) b T))‖ ≤
      ε / 2 + ε / 8 + ∑ j ∈ Finset.range T,
        excess f est (ε / 8) (traj (roundMap ℓ ε est) (x0, false) b j).1 (b j) +
      G0 * {b' : ℕ → Z | ∃ j < T,
        ε / 8 < err f est (traj (roundMap ℓ ε est) (x0, false) b' j).1 (b' j)}.indicator
          (fun _ => (1 : ℝ)) b := by
  classical
  set s := traj (roundMap ℓ ε est) (x0, false) b T with hs
  have hsum : 0 ≤ ∑ j ∈ Finset.range T,
      excess f est (ε / 8) (traj (roundMap ℓ ε est) (x0, false) b j).1 (b j) :=
    Finset.sum_nonneg fun j _ => excess_nonneg f est _ _ _
  have hind : 0 ≤ {b' : ℕ → Z | ∃ j < T,
      ε / 8 < err f est (traj (roundMap ℓ ε est) (x0, false) b' j).1 (b' j)}.indicator
        (fun _ => (1 : ℝ)) b := Set.indicator_nonneg (fun _ _ => zero_le_one) b
  by_cases hfz : s.2 = true
  · have hf := frozen_bound ℓ ε est x0 b f (α := ε / 8) (by positivity) T hfz
    simp only [finish, hfz, ↓reduceIte]
    have hG : 0 ≤ G0 := (norm_nonneg _).trans hG0
    have := mul_nonneg hG hind
    linarith
  · have hbad : ∃ j < T, ε / 8 < err f est (traj (roundMap ℓ ε est) (x0, false) b j).1 (b j) := by
      by_contra hc
      push Not at hc
      exact hfz (freezes ℓ ε est x0 b hreg hρ2 hε hg hd hH hΔ T hT hc)
    have hfz' : s.2 = false := by simpa using hfz
    simp only [finish, hfz', Bool.false_eq_true, ↓reduceIte]
    rw [Set.indicator_of_mem (show b ∈ {b' : ℕ → Z | ∃ j < T,
      ε / 8 < err f est (traj (roundMap ℓ ε est) (x0, false) b' j).1 (b' j)} from hbad)]
    linarith

section Probability

variable {X : Type*} [MeasurableSpace X] {W : Type*} [MeasurableSpace W]

lemma traj_measurable' {F : X → W → X} (hF : Measurable (Function.uncurry F)) (x0 : X) (n : ℕ) :
    Measurable (fun b : ℕ → W => traj F x0 b n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hF.comp (ih.prodMk (measurable_pi_apply n))

lemma adapted_expectation (μ : Measure W) [IsProbabilityMeasure μ] {F : X → W → X}
    (hF : Measurable (Function.uncurry F)) (x0 : X) {h : X → W → ℝ}
    (hh : Measurable (Function.uncurry h)) (hnn : ∀ x z, 0 ≤ h x z)
    (hi : ∀ x, Integrable (h x) μ) {H : ℝ} (hH : ∀ x, (∫ z, h x z ∂μ) ≤ H) (t : ℕ) :
    Integrable (fun b : ℕ → W => h (traj F x0 b t) (b t)) (Measure.infinitePi fun _ => μ) ∧
      (∫ b, h (traj F x0 b t) (b t) ∂(Measure.infinitePi fun _ => μ)) ≤ H := by
  have hiid := OracleTemplate.StochasticGeneralized.infinitePi_iid μ
  have hind := LongTails.Proofs.AdaptiveOracleConcentration.iid_history_independent
    hiid.measurable hiid.independent t
  have hhist : Measurable (fun b : ℕ → W => fun i : Fin t => b i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hf : Measurable (fun az : (Fin t → W) × W => h (histPoint F x0 t az.1) az.2) :=
    hh.comp (((measurable_histPoint hF x0 t).comp measurable_fst).prodMk measurable_snd)
  have hres := LongTails.Proofs.AdaptiveOracleConcentration.independent_nonnegative_fiber_bound
    (P := Measure.infinitePi fun _ => μ) (p := μ) hhist (measurable_pi_apply t) hind
    (hiid.marginal t) hf (fun az => hnn _ _) (fun a => hi (histPoint F x0 t a))
    (integrable_const H) (fun a => hH (histPoint F x0 t a))
  have heq : (fun b : ℕ → W => h (histPoint F x0 t (fun i : Fin t => b i)) (b t)) =
      fun b => h (traj F x0 b t) (b t) := by
    funext b; rw [histPoint_eq]
  simp only [heq] at hres
  refine ⟨hres.1, hres.2.trans_eq ?_⟩
  simp

lemma adapted_sum (μ : Measure W) [IsProbabilityMeasure μ] {F : X → W → X}
    (hF : Measurable (Function.uncurry F)) (x0 : X) {h : X → W → ℝ}
    (hh : Measurable (Function.uncurry h)) (hnn : ∀ x z, 0 ≤ h x z)
    (hi : ∀ x, Integrable (h x) μ) {H : ℝ} (hH : ∀ x, (∫ z, h x z ∂μ) ≤ H) (T : ℕ) :
    Integrable (fun b : ℕ → W => ∑ t ∈ Finset.range T, h (traj F x0 b t) (b t))
        (Measure.infinitePi fun _ => μ) ∧
      (∫ b, ∑ t ∈ Finset.range T, h (traj F x0 b t) (b t) ∂(Measure.infinitePi fun _ => μ)) ≤
        T * H := by
  have hall := fun t => adapted_expectation μ hF x0 hh hnn hi hH t
  refine ⟨integrable_finsetSum _ fun t _ => (hall t).1, ?_⟩
  rw [integral_finsetSum _ fun t _ => (hall t).1]
  calc ∑ t ∈ Finset.range T, (∫ b, h (traj F x0 b t) (b t) ∂(Measure.infinitePi fun _ => μ))
      ≤ ∑ _t ∈ Finset.range T, H := Finset.sum_le_sum fun t _ => (hall t).2
    _ = T * H := by simp

lemma adapted_union (μ : Measure W) [IsProbabilityMeasure μ] {F : X → W → X}
    (hF : Measurable (Function.uncurry F)) (x0 : X) {A : X → W → Prop}
    (hA : MeasurableSet {xz : X × W | A xz.1 xz.2}) {θ : ℝ}
    (hθ : ∀ x, μ.real {z | A x z} ≤ θ) (T : ℕ) :
    (Measure.infinitePi fun _ => μ).real {b : ℕ → W | ∃ t < T, A (traj F x0 b t) (b t)} ≤
      T * θ := by
  classical
  let h : X → W → ℝ := fun x z => {xz : X × W | A xz.1 xz.2}.indicator (fun _ => (1 : ℝ)) (x, z)
  have hh : Measurable (Function.uncurry h) := (measurable_const.indicator hA)
  have hnn : ∀ x z, 0 ≤ h x z := fun x z => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hsec : ∀ x, MeasurableSet {z | A x z} := fun x =>
    measurable_prodMk_left hA
  have hhx : ∀ x, h x = {z | A x z}.indicator (fun _ => (1 : ℝ)) := by
    intro x; funext z
    by_cases hz : A x z
    · simp [h, Set.indicator, hz]
    · simp [h, Set.indicator, hz]
  have hi : ∀ x, Integrable (h x) μ := fun x => by
    rw [hhx x]; exact (integrable_const _).indicator (hsec x)
  have hH : ∀ x, (∫ z, h x z ∂μ) ≤ θ := fun x => by
    rw [hhx x, integral_indicator_const _ (hsec x), smul_eq_mul, mul_one]; exact hθ x
  have hsum := adapted_sum μ hF x0 hh hnn hi hH T
  set S := {b : ℕ → W | ∃ t < T, A (traj F x0 b t) (b t)}
  have hpt : ∀ b, S.indicator (fun _ => (1 : ℝ)) b ≤
      ∑ t ∈ Finset.range T, h (traj F x0 b t) (b t) := by
    intro b
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      obtain ⟨t, ht, hA'⟩ := hb
      have : h (traj F x0 b t) (b t) = 1 := by simp [h, Set.indicator, hA']
      calc (1 : ℝ) = h (traj F x0 b t) (b t) := this.symm
        _ ≤ _ := Finset.single_le_sum (f := fun t => h (traj F x0 b t) (b t))
            (fun t _ => hnn _ _) (Finset.mem_range.mpr ht)
    · rw [Set.indicator_of_notMem hb]
      exact Finset.sum_nonneg fun t _ => hnn _ _
  have hSm : MeasurableSet S := by
    have : S = ⋃ t ∈ Finset.range T, (fun b : ℕ → W => (traj F x0 b t, b t)) ⁻¹'
        {xz : X × W | A xz.1 xz.2} := by
      ext b; simp [S]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun t _ =>
      ((traj_measurable' hF x0 t).prodMk (measurable_pi_apply t)) hA
  calc (Measure.infinitePi fun _ => μ).real S
      = ∫ b, S.indicator (fun _ => (1 : ℝ)) b ∂(Measure.infinitePi fun _ => μ) := by
        rw [integral_indicator_const _ hSm, smul_eq_mul, mul_one]
    _ ≤ ∫ b, ∑ t ∈ Finset.range T, h (traj F x0 b t) (b t) ∂(Measure.infinitePi fun _ => μ) :=
        integral_mono ((integrable_const _).indicator hSm) hsum.1 hpt
    _ ≤ T * θ := hsum.2

end Probability

section Rounds

open LongTails.Proofs.StochasticEllSmoothEstimator OracleTemplate.MultiplicativeRobustEstimator

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma estimate_reindex (K n : ℕ) (g : E → Ω → E) (x : E) (z : Fin ((2 * K + 2) * n) → Ω) :
    estimate K n (fun i => g x (z i)) =
      medoid (fun i => (1 / (n : ℝ)) • ∑ l : Fin n,
        g x (OracleTemplate.SublevelRobustGradient.reindex (2 * K + 2) n z i l)) := rfl

lemma round_bounds (g : E → Ω → E) (hg : Measurable (Function.uncurry g)) (x u : E)
    (hgi : Integrable (g x) ν) (hmean : (∫ ω, g x ω ∂ν) = u) {p σ : ℝ} (hp1 : 1 < p)
    (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hpi : Integrable (fun ω => ‖g x ω - u‖ ^ p) ν)
    (hmom : (∫ ω, ‖g x ω - u‖ ^ p ∂ν) ≤ σ ^ p) (K n : ℕ) (hK : 3 ≤ K) (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hnα : 3 * σ / (n : ℝ) ^ ((p - 1) / p) ≤ α / 1536) :
    (Measure.pi fun _ : Fin ((2 * K + 2) * n) => ν).real
        {z | α < ‖estimate K n (fun i => g x (z i)) - u‖} ≤ (1 / 2) ^ (2 * K + 2) ∧
      Integrable (fun z : Fin ((2 * K + 2) * n) → Ω =>
        {z | α < ‖estimate K n (fun i => g x (z i)) - u‖}.indicator
          (fun z => ‖estimate K n (fun i => g x (z i)) - u‖) z)
        (Measure.pi fun _ : Fin ((2 * K + 2) * n) => ν) ∧
      (∫ z, {z | α < ‖estimate K n (fun i => g x (z i)) - u‖}.indicator
          (fun z => ‖estimate K n (fun i => g x (z i)) - u‖) z
          ∂(Measure.pi fun _ : Fin ((2 * K + 2) * n) => ν)) ≤ α / 22 * (1 / 2) ^ (K + 1) := by
  set Pn := Measure.pi fun _ : Fin n => ν
  let Xb : (Fin n → Ω) → E := fun ζ => (1 / (n : ℝ)) • ∑ l : Fin n, g x (ζ l)
  have hgx : Measurable (g x) := hg.comp (measurable_const.prodMk measurable_id)
  have hXb : Measurable Xb :=
    (Finset.measurable_sum _ fun l _ => hgx.comp (measurable_pi_apply l)).const_smul _
  have hfm := block_mean_first_moment (P := ν) hgx hgi u hmean hp1 hp2 hσ hpi hmom n hn
  have hmed := medoid_estimate (P := Pn) (X := Xb) hXb u hα hfm.1 (hfm.2.trans hnα) K hK
  have hpres := OracleTemplate.SublevelRobustGradient.reindex_preserving ν (2 * K + 2) n
  set Dm : (Fin (2 * K + 1 + 1) → Fin n → Ω) → ℝ := fun ξ => ‖medoid (fun i => Xb (ξ i)) - u‖
  have hDm : Measurable Dm :=
    ((measurable_medoid.comp (Measurable.of_eval fun i => hXb.comp (measurable_pi_apply i))).sub_const
      u).norm
  set A := {ξ : Fin (2 * K + 1 + 1) → Fin n → Ω | α < Dm ξ}
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hDm
  have hcomp : ∀ z : Fin ((2 * K + 2) * n) → Ω, ‖estimate K n (fun i => g x (z i)) - u‖ =
      Dm (OracleTemplate.SublevelRobustGradient.reindex (2 * K + 2) n z) := fun z => rfl
  have hset : {z : Fin ((2 * K + 2) * n) → Ω | α < ‖estimate K n (fun i => g x (z i)) - u‖} =
      OracleTemplate.SublevelRobustGradient.reindex (2 * K + 2) n ⁻¹' A := by
    ext z; simp only [Set.mem_ofPred_eq, Set.mem_preimage, A, hcomp]
  have hind : ∀ z : Fin ((2 * K + 2) * n) → Ω,
      {z | α < ‖estimate K n (fun i => g x (z i)) - u‖}.indicator
        (fun z => ‖estimate K n (fun i => g x (z i)) - u‖) z =
      A.indicator Dm (OracleTemplate.SublevelRobustGradient.reindex (2 * K + 2) n z) := by
    intro z
    rw [hset]
    simp only [Set.indicator, Set.mem_preimage, hcomp]
  refine ⟨?_, ?_, ?_⟩
  · rw [hset, measureReal_def, hpres.measure_preimage hAm.nullMeasurableSet, ← measureReal_def]
    exact hmed.1
  · simp only [hind]
    have h1 := hmed.2.1
    rw [← hpres.map_eq] at h1
    exact h1.comp_measurable hpres.measurable
  · simp only [hind]
    rw [← integral_map hpres.measurable.aemeasurable
      (by rw [hpres.map_eq]; exact (hDm.indicator hAm).aestronglyMeasurable), hpres.map_eq]
    exact hmed.2.2

end Rounds

end LongTails.Proofs.StochasticEllSmoothRun
