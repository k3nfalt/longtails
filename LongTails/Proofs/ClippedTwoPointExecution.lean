import LongTails.Algorithms.ClippedTwoPoint
import LongTails.Proofs.SampledQueryPlan
import LongTails.Proofs.ScalarClippedAcceleration
import LongTails.Proofs.ClippedVectorMoments

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClippedTwoPointExecution

open LongTails.Algorithms.ClippedTwoPoint OracleTemplate.QueryPlan

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pair_sampled_eval (d : ℕ) (τ γ : ℝ) (x u : E) (g : E → Ω → ℝ)
    (ξ : ℕ → Ω) (m : ℕ) :
    sampledEval g (fun k => ξ (k / 2)) (pairPlan d τ γ x u) (2 * m) =
      estimate d τ γ u (g (x + γ • u) (ξ m)) (g (x - γ • u) (ξ m)) := by
  simp only [pairPlan, sampledEval]
  congr 2 <;> congr 1 <;> omega

lemma batch_sampled_eval (d : ℕ) (τ γ : ℝ) (x : E) {B : ℕ} (u : Fin B → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m : ℕ) :
    sampledEval g (fun k => ξ (k / 2)) (batchPlan d τ γ x u) (2 * m) =
      (B : ℝ)⁻¹ • ∑ i : Fin B, estimate d τ γ (u i)
        (g (x + γ • u i) (ξ (m + i))) (g (x - γ • u i) (ξ (m + i))) := by
  rw [batchPlan, sampledEval_map, sampledEval_traverse]
  simp only [show ∀ i : Fin B, 2 * m + 2 * (i : ℕ) = 2 * (m + i) by intro i; omega,
    pair_sampled_eval, List.sum_ofFn]


lemma accelerated_mix_mem {Q : Set E} (hQ : Convex ℝ Q) {x z : E}
    (hx : x ∈ Q) (hz : z ∈ Q) (t : ℕ) : acceleratedMix t x z ∈ Q := by
  have ht : (0 : ℝ) < t + 2 := by positivity
  apply hQ hx hz (by positivity : 0 ≤ (t : ℝ) / (t + 2)) (by positivity : 0 ≤ 2 / (t + 2 : ℝ))
  field_simp

lemma accelerated_update_mem {Q : Set E} (hQ : Convex ℝ Q) {project : E → E}
    (hp : ∀ x, project x ∈ Q) {state : E × E} (hx : state.1 ∈ Q)
    (h : ℝ) (t : ℕ) (g : E) :
    (acceleratedUpdate project h t state g).1 ∈ Q ∧
      (acceleratedUpdate project h t state g).2 ∈ Q := by
  exact ⟨accelerated_mix_mem hQ hx (hp _) t, hp _⟩

lemma accelerated_mix_continuous (t : ℕ) :
    Continuous (fun state : E × E => acceleratedMix t state.1 state.2) := by
  exact (continuous_fst.const_smul _).add (continuous_snd.const_smul _)

lemma accelerated_update_continuous {project : E → E} (hp : Continuous project)
    (h : ℝ) (t : ℕ) : Continuous (fun sg : (E × E) × E => acceleratedUpdate project h t sg.1 sg.2) := by
  have hn : Continuous (fun sg : (E × E) × E => project (sg.1.2 - ((t + 1 : ℝ) / h) • sg.2)) := hp.comp ((continuous_snd.comp continuous_fst).sub (continuous_snd.const_smul ((t + 1 : ℝ) / h)))
  exact ((accelerated_mix_continuous t).comp ((continuous_fst.comp continuous_fst).prodMk hn)).prodMk hn

lemma round_sampled_eval (d : ℕ) (τ γ h : ℝ) (project : E → E) (t : ℕ)
    (state : E × E) {B : ℕ} (u : Fin B → E) (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m : ℕ) :
    sampledEval g (fun k => ξ (k / 2)) (roundPlan d τ γ h project t state u) (2 * m) =
      acceleratedUpdate project h t state ((B : ℝ)⁻¹ • ∑ i : Fin B,
        estimate d τ γ (u i)
          (g (acceleratedMix t state.1 state.2 + γ • u i) (ξ (m + i)))
          (g (acceleratedMix t state.1 state.2 - γ • u i) (ξ (m + i)))) := by
  rw [roundPlan, sampledEval_map, batch_sampled_eval]


lemma accelerated_mix_weights (t : ℕ) (x z : E) :
    acceleratedMix t x z =
      (((t : ℝ) * (t + 1) / 2) / ((t : ℝ) * (t + 1) / 2 + (t + 1))) • x +
      (((t + 1 : ℝ)) / ((t : ℝ) * (t + 1) / 2 + (t + 1))) • z := by
  have h1 : (t + 1 : ℝ) ≠ 0 := by positivity
  have h2 : (t + 2 : ℝ) ≠ 0 := by positivity
  have h3 : (t : ℝ) * (t + 1) / 2 + (t + 1) ≠ 0 := by positivity
  have he1 : (t : ℝ) / (t + 2) = ((t : ℝ) * (t + 1) / 2) /
      ((t : ℝ) * (t + 1) / 2 + (t + 1)) := by field_simp
  have he2 : 2 / (t + 2 : ℝ) = (t + 1 : ℝ) /
      ((t : ℝ) * (t + 1) / 2 + (t + 1)) := by field_simp
  exact congrArg₂ (fun a b : ℝ => a • x + b • z) he1 he2

lemma accelerated_model_coefficient (t : ℕ) {L h : ℝ} (hL : 0 ≤ L) (hh : 4 * L ≤ h) :
    L * (t + 1 : ℝ) ^ 2 / (2 * ((t : ℝ) * (t + 1) / 2 + (t + 1))) ≤ h / 4 := by
  have ht : (0 : ℝ) < 2 * ((t : ℝ) * (t + 1) / 2 + (t + 1)) := by positivity
  apply (div_le_iff₀ ht).mpr
  have hs := mul_le_mul_of_nonneg_right hh (show 0 ≤ ((t : ℝ) * (t + 1) / 2 + (t + 1)) / 2 by positivity)
  nlinarith [mul_nonneg hL (show (0 : ℝ) ≤ t + 1 by positivity)]


lemma accelerated_update_potential {Q : Set E} (hQ : Convex ℝ Q)
    {project : E → E} (hp : ∀ x, project x ∈ Q)
    (hnearest : ∀ x, ‖x - project x‖ = ⨅ w : Q, ‖x - w‖)
    {f : E → ℝ} {grad : E → E} {L h : ℝ} (hL : 0 ≤ L) (hh : 0 < h) (hcoef : 4 * L ≤ h)
    (hconvex : ∀ x ∈ Q, ∀ y ∈ Q, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hmodel : ∀ x ∈ Q, ∀ y ∈ Q, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    {state : E × E} (hx : state.1 ∈ Q) (hz : state.2 ∈ Q) {u : E} (hu : u ∈ Q)
    (t : ℕ) (g : E) :
    let A := (t : ℝ) * (t + 1) / 2
    let a := (t + 1 : ℝ)
    let y := acceleratedMix t state.1 state.2
    let next := acceleratedUpdate project h t state g
    (A + a) * (f next.1 - f u) + h / 2 * ‖next.2 - u‖ ^ 2 ≤
      A * (f state.1 - f u) + h / 2 * ‖state.2 - u‖ ^ 2 +
        a ^ 2 * ‖g - grad y‖ ^ 2 / h - a * ⟪g - grad y, state.2 - u⟫ := by
  let A := (t : ℝ) * (t + 1) / 2
  let a := (t + 1 : ℝ)
  let znext := project (state.2 - (a / h) • g)
  let y := acceleratedMix t state.1 state.2
  have hmix (x z : E) : (A / (A + a)) • x + (a / (A + a)) • z = acceleratedMix t x z :=
    (accelerated_mix_weights t x z).symm
  have hy : y ∈ Q := accelerated_mix_mem hQ hx hz t
  have hn : znext ∈ Q := hp _
  have hnew : acceleratedMix t state.1 znext ∈ Q := accelerated_mix_mem hQ hx hn t
  have hd : acceleratedMix t state.1 znext - y = (a / (A + a)) • (znext - state.2) := by
    rw [← hmix, show y = (A / (A + a)) • state.1 + (a / (A + a)) • state.2 from (hmix _ _).symm,
      smul_sub]
    abel
  have hs := hmodel y hy (acceleratedMix t state.1 znext) hnew
  rw [hd] at hs
  have hproj := ScalarClippedAcceleration.projection_step hQ hh hu hn
    (hnearest (state.2 - (a / h) • g))
  have hhstep := ScalarClippedAcceleration.accelerated_step
    (A := A) (a := a) (x := state.1) (z := state.2) (u := u)
    (next := znext) (grad := grad y) (g := g)
    (by dsimp [A]; positivity) (by dsimp [a]; positivity)
    (by dsimp [A, a]; positivity) hh (accelerated_model_coefficient t hL hcoef)
    (by simpa only [hmix] using hconvex y hy state.1 hx)
    (by simpa only [hmix] using hconvex y hy u hu)
    (by simpa only [hmix] using hs) hproj
  simpa only [hmix, A, a, y, znext, acceleratedUpdate] using hhstep

lemma solver_calls_eq (B : ℕ → ℕ) (n : ℕ) :
    solverCalls B n = 2 * ∑ j ∈ Finset.range n, B j := by
  induction n with
  | zero => simp [solverCalls]
  | succ n ih => simp only [solverCalls, Finset.sum_range_succ, ih]; omega

lemma solver_sampled_eval (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m n : ℕ) :
    sampledEval g (fun k => ξ (k / 2)) (solverPlan d τ γ h project initial B u n) (2 * m) =
      solverState d τ γ h project initial B u g ξ m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sampledEval g (fun k => ξ (k / 2))
      ((solverPlan d τ γ h project initial B u n).bind
        (fun state => roundPlan d τ γ h project n state (u n))) (2 * m) = _
    rw [sampledEval_bind, ih, solver_calls_eq]
    rw [show 2 * m + 2 * (∑ j ∈ Finset.range n, B j) =
      2 * (m + ∑ j ∈ Finset.range n, B j) by omega, round_sampled_eval]
    rfl

lemma solver_state_mem {Q : Set E} (hQ : Convex ℝ Q) {project : E → E}
    (hp : ∀ x, project x ∈ Q) {initial : E × E}
    (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q)
    (d : ℕ) (τ γ h : ℝ) (B : ℕ → ℕ) (u : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m n : ℕ) :
    (solverState d τ γ h project initial B u g ξ m n).1 ∈ Q ∧
      (solverState d τ γ h project initial B u g ξ m n).2 ∈ Q := by
  induction n with
  | zero => exact ⟨hx, hz⟩
  | succ n ih => exact accelerated_update_mem hQ hp ih.1 h n _

lemma solver_state_prefix (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u v : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ η : ℕ → Ω) (m n : ℕ)
    (hu : ∀ t < n, u t = v t)
    (hξ : ∀ j < ∑ t ∈ Finset.range n, B t, ξ (m + j) = η (m + j)) :
    solverState d τ γ h project initial B u g ξ m n =
      solverState d τ γ h project initial B v g η m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hle : (∑ t ∈ Finset.range n, B t) ≤ ∑ t ∈ Finset.range (n + 1), B t := by
      rw [Finset.sum_range_succ]
      omega
    have hp := ih (fun t ht => hu t (by omega)) (fun j hj => hξ j (lt_of_lt_of_le hj hle))
    simp only [solverState, hp, hu n (Nat.lt_succ_self n)]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hs := hξ ((∑ t ∈ Finset.range n, B t) + (i : ℕ)) (by
      rw [Finset.sum_range_succ]
      exact Nat.add_lt_add_left i.isLt _)
    simp only [Nat.add_assoc] at hs ⊢
    rw [hs]

lemma solver_state_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ γ h : ℝ) {project : E → E} (hp : Continuous project)
    (initial : E × E) (B : ℕ → ℕ) (u : Z → (t : ℕ) → Fin (B t) → E)
    (hu : ∀ t i, Measurable (fun z => u z t i))
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m n : ℕ) :
    Measurable (fun z => solverState d τ γ h project initial B (u z) g (fun j => ξ j z) m n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let state := fun z => solverState d τ γ h project initial B (u z) g (fun j => ξ j z) m n
    let center := fun z => acceleratedMix n (state z).1 (state z).2
    have hc : Measurable center := (accelerated_mix_continuous n).measurable.comp ih
    have he (i : Fin (B n)) : Measurable (fun z => estimate d τ γ (u z n i)
        (g (center z + γ • u z n i) (ξ (m + (∑ j ∈ Finset.range n, B j) + i) z))
        (g (center z - γ • u z n i) (ξ (m + (∑ j ∈ Finset.range n, B j) + i) z))) := by
      have hplus := hg.comp ((hc.add ((hu n i).const_smul γ)).prodMk (hξ (m + (∑ j ∈ Finset.range n, B j) + i)))
      have hminus := hg.comp ((hc.sub ((hu n i).const_smul γ)).prodMk (hξ (m + (∑ j ∈ Finset.range n, B j) + i)))
      exact ClippedVectorMoments.direction_estimate_measurable (hu n i)
        ((hplus.sub hminus).div_const (2 * γ)) d τ
    have havg := (Finset.measurable_sum Finset.univ (fun i _ => he i)).const_smul (B n : ℝ)⁻¹
    exact (accelerated_update_continuous hp h n).measurable.comp (ih.prodMk havg)

lemma solver_finite_history {R : Type*} [MeasurableSpace R] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ γ h : ℝ) {project : E → E} (hp : Continuous project)
    (initial : E × E) (B : ℕ → ℕ) (direction : R → E) (sample : R → Ω)
    (hd : Measurable direction) (hs : Measurable sample) (fallback : R)
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2)) (n : ℕ) :
    ∃ state : (Fin (∑ t ∈ Finset.range n, B t) → R) → E × E,
      Measurable state ∧ ∀ records : ℕ → R,
        state (fun i => records i) = solverState d τ γ h project initial B
          (fun t i => direction (records ((∑ j ∈ Finset.range t, B j) + i)))
          g (fun j => sample (records j)) 0 n := by
  let K := ∑ t ∈ Finset.range n, B t
  let fill := fun (history : Fin K → R) (j : ℕ) =>
    if hj : j < K then history ⟨j, hj⟩ else fallback
  have hfill (j : ℕ) : Measurable (fun history => fill history j) := by
    dsimp only [fill]
    split_ifs with hj
    · exact measurable_pi_apply _
    · exact measurable_const
  refine ⟨fun history => solverState d τ γ h project initial B
    (fun t i => direction (fill history ((∑ j ∈ Finset.range t, B j) + i)))
    g (fun j => sample (fill history j)) 0 n, ?_, ?_⟩
  · exact solver_state_measurable d τ γ h hp initial B _
      (fun t i => hd.comp (hfill _)) g hg _ (fun j => hs.comp (hfill j)) 0 n
  · intro records
    apply solver_state_prefix
    · intro t ht
      funext i
      have hm : (∑ j ∈ Finset.range (t + 1), B j) ≤ K :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt ht))
      have hi : (∑ j ∈ Finset.range t, B j) + (i : ℕ) < K := by
        rw [Finset.sum_range_succ] at hm
        exact lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) hm
      simp only [fill, dite_eq_left hi]
    · intro j hj
      simp [fill, K, hj]

lemma solver_potential {Q : Set E} (hQ : Convex ℝ Q)
    {project : E → E} (hp : ∀ x, project x ∈ Q)
    (hnearest : ∀ x, ‖x - project x‖ = ⨅ w : Q, ‖x - w‖)
    {f : E → ℝ} {grad : E → E} {L h : ℝ} (hL : 0 ≤ L) (hh : 0 < h) (hcoef : 4 * L ≤ h)
    (hconvex : ∀ x ∈ Q, ∀ y ∈ Q, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hmodel : ∀ x ∈ Q, ∀ y ∈ Q, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    {initial : E × E} (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q) {v : E} (hv : v ∈ Q)
    (d : ℕ) (τ γ : ℝ) (B : ℕ → ℕ) (u : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m N : ℕ) :
    let state := solverState d τ γ h project initial B u g ξ m
    let error := fun t =>
      let center := acceleratedMix t (state t).1 (state t).2
      (B t : ℝ)⁻¹ • (∑ i : Fin (B t), estimate d τ γ (u t i)
        (g (center + γ • u t i) (ξ (m + (∑ j ∈ Finset.range t, B j) + i)))
        (g (center - γ • u t i) (ξ (m + (∑ j ∈ Finset.range t, B j) + i)))) - grad center
    ((N : ℝ) * (N + 1) / 2) * (f (solverOutput d τ γ h project initial B u g ξ m N) - f v) ≤
      h / 2 * ‖initial.2 - v‖ ^ 2 +
        (∑ t ∈ Finset.range N, (t + 1 : ℝ) ^ 2 * ‖error t‖ ^ 2) / h -
        ∑ t ∈ Finset.range N, (t + 1 : ℝ) * ⟪error t, (state t).2 - v⟫ := by
  dsimp only
  apply ScalarClippedAcceleration.potential_telescope
    (f := f) (x := fun t => (solverState d τ γ h project initial B u g ξ m t).1)
    (z := fun t => (solverState d τ γ h project initial B u g ξ m t).2)
    (e := _) (u := v) (A := fun t => (t : ℝ) * (t + 1) / 2) (a := fun t => (t + 1 : ℝ)) hh.le (by norm_num)
  intro t
  have hmem := solver_state_mem hQ hp hx hz d τ γ h B u g ξ m t
  have hs := accelerated_update_potential hQ hp hnearest hL hh hcoef hconvex hmodel
    hmem.1 hmem.2 hv t ((B t : ℝ)⁻¹ • ∑ i : Fin (B t), estimate d τ γ (u t i)
      (g (acceleratedMix t (solverState d τ γ h project initial B u g ξ m t).1
        (solverState d τ γ h project initial B u g ξ m t).2 + γ • u t i)
        (ξ (m + (∑ j ∈ Finset.range t, B j) + i)))
      (g (acceleratedMix t (solverState d τ γ h project initial B u g ξ m t).1
        (solverState d τ γ h project initial B u g ξ m t).2 - γ • u t i)
        (ξ (m + (∑ j ∈ Finset.range t, B j) + i))))
  dsimp only at hs
  have he : ((t + 1 : ℕ) : ℝ) * (((t + 1 : ℕ) : ℝ) + 1) / 2 =
      (t : ℝ) * (t + 1) / 2 + (t + 1) := by push_cast; ring
  simpa only [he, solverState] using hs

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma comparison_pair_sampled_eval (s : ℝ) (a b : E) (g : E → Ω → ℝ)
    (ξ : ℕ → Ω) (m : ℕ) :
    sampledEval g (fun k => ξ (k / 2)) (comparisonPairPlan s a b) (2 * m) =
      OracleTemplate.clip s (g a (ξ m) - g b (ξ m)) := by
  simp only [comparisonPairPlan, sampledEval, show 2 * m / 2 = m by omega,
    show (2 * m + 1) / 2 = m by omega]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma selection_sampled_eval (s : ℝ) (a b : E) (T : ℕ) (g : E → Ω → ℝ)
    (ξ : ℕ → Ω) (m : ℕ) :
    sampledEval g (fun k => ξ (k / 2)) (selectionPlan s a b T) (2 * m) =
      selectByDifference a b ((T : ℝ)⁻¹ * ∑ i : Fin T,
        OracleTemplate.clip s (g a (ξ (m + i)) - g b (ξ (m + i)))) := by
  rw [selectionPlan, sampledEval_map, sampledEval_traverse]
  simp only [show ∀ i : Fin T, 2 * m + 2 * (i : ℕ) = 2 * (m + i) by intro i; omega,
    comparison_pair_sampled_eval, List.sum_ofFn]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma selected_value_le {f : E → ℝ} (a b : E) {estimate r : ℝ}
    (hr : 0 ≤ r) (he : |estimate - (f a - f b)| ≤ r) :
    f (selectByDifference a b estimate) ≤ min (f a) (f b) + r := by
  rcases abs_le.mp he with ⟨hl, hu⟩
  unfold selectByDifference
  split_ifs with hs
  · by_cases hab : f a ≤ f b
    · rw [min_eq_left hab]; linarith
    · rw [min_eq_right (le_of_not_ge hab)]; linarith
  · by_cases hab : f a ≤ f b
    · rw [min_eq_left hab]; linarith
    · rw [min_eq_right (le_of_not_ge hab)]; linarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma selected_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace E]
    {a b : Z → E} {estimate : Z → ℝ}
    (ha : Measurable a) (hb : Measurable b) (he : Measurable estimate) :
    Measurable (fun z => selectByDifference (a z) (b z) (estimate z)) :=
  Measurable.ite (measurableSet_le he measurable_const) ha hb

lemma dual_solver_calls_sum (B : ℕ → ℕ) (n : ℕ) :
    dualSolverCalls B n = 4 * ∑ j ∈ Finset.range n, B j := by
  induction n with
  | zero => simp [dualSolverCalls]
  | succ n ih => simp only [dualSolverCalls, Finset.sum_range_succ, ih]; omega

lemma dual_solver_sampled_eval (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u v : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m n : ℕ) :
    sampledEval g (fun k => ξ (k / 2))
      (dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v n) (2 * m) =
      dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B u v g ξ m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sampledEval g (fun k => ξ (k / 2))
      ((dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v n).bind
        (fun states => (roundPlan d τ₁ γ₁ h project n states.1 (u n)).bind
          (fun first => (roundPlan d τ₂ γ₂ h project n states.2 (v n)).map
            (fun second => (first, second))))) (2 * m) = _
    rw [sampledEval_bind, ih, dual_solver_calls_sum, sampledEval_bind, sampledEval_map]
    rw [show 2 * m + 4 * (∑ j ∈ Finset.range n, B j) =
      2 * (m + 2 * ∑ j ∈ Finset.range n, B j) by omega]
    rw [show 2 * (m + 2 * ∑ j ∈ Finset.range n, B j) + 2 * B n =
      2 * (m + 2 * (∑ j ∈ Finset.range n, B j) + B n) by omega]
    rw [round_sampled_eval, round_sampled_eval]
    rfl

lemma adaptive_selection_sampled_eval (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u v : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m N T : ℕ) :
    sampledEval g (fun k => ξ (k / 2))
      (adaptiveSelectionPlan d τ₁ τ₂ γ₁ γ₂ h s project initial B u v N T) (2 * m) =
      adaptiveOutput d τ₁ τ₂ γ₁ γ₂ h s project initial B u v g ξ m N T := by
  rw [adaptiveSelectionPlan, sampledEval_bind, dual_solver_sampled_eval, dual_solver_calls_sum]
  rw [show 2 * m + 4 * (∑ j ∈ Finset.range N, B j) =
    2 * (m + 2 * ∑ j ∈ Finset.range N, B j) by omega, selection_sampled_eval]
  rfl

lemma dual_solver_state_mem {Q : Set E} (hQ : Convex ℝ Q) {project : E → E}
    (hp : ∀ x, project x ∈ Q) {initial : E × E} (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (B : ℕ → ℕ) (u v : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m n : ℕ) :
    let states := dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B u v g ξ m n
    (states.1.1 ∈ Q ∧ states.1.2 ∈ Q) ∧ (states.2.1 ∈ Q ∧ states.2.2 ∈ Q) := by
  induction n with
  | zero => exact ⟨⟨hx, hz⟩, ⟨hx, hz⟩⟩
  | succ n ih =>
    exact ⟨accelerated_update_mem hQ hp ih.1.1 h n _,
      accelerated_update_mem hQ hp ih.2.1 h n _⟩

lemma adaptive_output_mem {Q : Set E} (hQ : Convex ℝ Q) {project : E → E}
    (hp : ∀ x, project x ∈ Q) {initial : E × E} (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ) (B : ℕ → ℕ) (u v : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m N T : ℕ) :
    adaptiveOutput d τ₁ τ₂ γ₁ γ₂ h s project initial B u v g ξ m N T ∈ Q := by
  have hh := dual_solver_state_mem hQ hp hx hz d τ₁ τ₂ γ₁ γ₂ h B u v g ξ m N
  unfold adaptiveOutput selectByDifference
  dsimp only
  split_ifs
  · exact hh.1.1
  · exact hh.2.1

lemma round_state_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ γ h : ℝ) {project : E → E} (hp : Continuous project) (t : ℕ)
    {state : Z → E × E} (hstate : Measurable state) {B : ℕ} (u : Z → Fin B → E)
    (hu : ∀ i, Measurable (fun z => u z i))
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m : ℕ) :
    Measurable (fun z => roundState d τ γ h project t (state z) (u z) g (fun j => ξ j z) m) := by
  let center := fun z => acceleratedMix t (state z).1 (state z).2
  have hc : Measurable center := (accelerated_mix_continuous t).measurable.comp hstate
  have he (i : Fin B) : Measurable (fun z => estimate d τ γ (u z i)
      (g (center z + γ • u z i) (ξ (m + i) z))
      (g (center z - γ • u z i) (ξ (m + i) z))) := by
    have hplus := hg.comp ((hc.add ((hu i).const_smul γ)).prodMk (hξ (m + i)))
    have hminus := hg.comp ((hc.sub ((hu i).const_smul γ)).prodMk (hξ (m + i)))
    exact ClippedVectorMoments.direction_estimate_measurable (hu i)
      ((hplus.sub hminus).div_const (2 * γ)) d τ
  have havg := (Finset.measurable_sum Finset.univ (fun i _ => he i)).const_smul (B : ℝ)⁻¹
  exact (accelerated_update_continuous hp h t).measurable.comp (hstate.prodMk havg)

lemma dual_solver_state_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) {project : E → E} (hp : Continuous project)
    (initial : E × E) (B : ℕ → ℕ) (u v : Z → (t : ℕ) → Fin (B t) → E)
    (hu : ∀ t i, Measurable (fun z => u z t i))
    (hv : ∀ t i, Measurable (fun z => v z t i))
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m n : ℕ) :
    Measurable (fun z => dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B
      (u z) (v z) g (fun j => ξ j z) m n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (round_state_measurable d τ₁ γ₁ h hp n ih.fst (fun z => u z n) (hu n)
      g hg ξ hξ (m + 2 * ∑ j ∈ Finset.range n, B j)).prodMk
      (round_state_measurable d τ₂ γ₂ h hp n ih.snd (fun z => v z n) (hv n)
        g hg ξ hξ (m + 2 * (∑ j ∈ Finset.range n, B j) + B n))

lemma round_state_congr_samples (d : ℕ) (τ γ h : ℝ) (project : E → E) (t : ℕ)
    (state : E × E) {B : ℕ} (u : Fin B → E) (g : E → Ω → ℝ) (ξ η : ℕ → Ω)
    (m : ℕ) (he : ∀ i : Fin B, ξ (m + i) = η (m + i)) :
    roundState d τ γ h project t state u g ξ m =
      roundState d τ γ h project t state u g η m := by
  simp only [roundState, he]

lemma dual_solver_state_prefix (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u v u' v' : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ η : ℕ → Ω) (m n : ℕ)
    (hu : ∀ t < n, u t = u' t) (hv : ∀ t < n, v t = v' t)
    (hξ : ∀ j < 2 * ∑ t ∈ Finset.range n, B t, ξ (m + j) = η (m + j)) :
    dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B u v g ξ m n =
      dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B u' v' g η m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hle : 2 * (∑ t ∈ Finset.range n, B t) ≤
        2 * ∑ t ∈ Finset.range (n + 1), B t := by
      rw [Finset.sum_range_succ]
      omega
    have hp := ih (fun t ht => hu t (by omega)) (fun t ht => hv t (by omega))
      (fun j hj => hξ j (lt_of_lt_of_le hj hle))
    simp only [dualSolverState, hp, hu n (Nat.lt_succ_self n), hv n (Nat.lt_succ_self n)]
    apply Prod.ext
    · apply round_state_congr_samples
      intro i
      have hb : 2 * (∑ t ∈ Finset.range n, B t) + (i : ℕ) <
          2 * ∑ t ∈ Finset.range (n + 1), B t := by
        rw [Finset.sum_range_succ]
        have hi := i.isLt
        omega
      simpa only [Nat.add_assoc] using hξ _ hb
    · apply round_state_congr_samples
      intro i
      have hb : 2 * (∑ t ∈ Finset.range n, B t) + B n + (i : ℕ) <
          2 * ∑ t ∈ Finset.range (n + 1), B t := by
        rw [Finset.sum_range_succ]
        have hi := i.isLt
        omega
      simpa only [Nat.add_assoc] using hξ _ hb

lemma dual_solver_finite_history {R : Type*} [MeasurableSpace R] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) {project : E → E} (hp : Continuous project)
    (initial : E × E) (B : ℕ → ℕ) (direction : R → E) (sample : R → Ω)
    (hd : Measurable direction) (hs : Measurable sample) (fallback : R)
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2)) (n : ℕ) :
    ∃ state : (Fin (2 * ∑ t ∈ Finset.range n, B t) → R) → (E × E) × (E × E),
      Measurable state ∧ ∀ records : ℕ → R,
        state (fun i => records i) = dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B
          (fun t i => direction (records (2 * (∑ j ∈ Finset.range t, B j) + i)))
          (fun t i => direction (records (2 * (∑ j ∈ Finset.range t, B j) + B t + i)))
          g (fun j => sample (records j)) 0 n := by
  let K := 2 * ∑ t ∈ Finset.range n, B t
  let fill := fun (history : Fin K → R) (j : ℕ) =>
    if hj : j < K then history ⟨j, hj⟩ else fallback
  have hfill (j : ℕ) : Measurable (fun history => fill history j) := by
    dsimp only [fill]
    split_ifs with hj
    · exact measurable_pi_apply _
    · exact measurable_const
  refine ⟨fun history => dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B
    (fun t i => direction (fill history (2 * (∑ j ∈ Finset.range t, B j) + i)))
    (fun t i => direction (fill history (2 * (∑ j ∈ Finset.range t, B j) + B t + i)))
    g (fun j => sample (fill history j)) 0 n, ?_, ?_⟩
  · exact dual_solver_state_measurable d τ₁ τ₂ γ₁ γ₂ h hp initial B _ _
      (fun t i => hd.comp (hfill _)) (fun t i => hd.comp (hfill _))
      g hg _ (fun j => hs.comp (hfill j)) 0 n
  · intro records
    apply dual_solver_state_prefix
    · intro t ht
      funext i
      have hm : (∑ j ∈ Finset.range (t + 1), B j) ≤ ∑ j ∈ Finset.range n, B j :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt ht))
      have hi : 2 * (∑ j ∈ Finset.range t, B j) + (i : ℕ) < K := by
        rw [Finset.sum_range_succ] at hm
        have hilt := i.isLt
        dsimp only [K]
        omega
      simp only [fill, dite_eq_left hi]
    · intro t ht
      funext i
      have hm : (∑ j ∈ Finset.range (t + 1), B j) ≤ ∑ j ∈ Finset.range n, B j :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt ht))
      have hi : 2 * (∑ j ∈ Finset.range t, B j) + B t + (i : ℕ) < K := by
        rw [Finset.sum_range_succ] at hm
        have hilt := i.isLt
        dsimp only [K]
        omega
      simp only [fill, dite_eq_left hi]
    · intro j hj
      simp [fill, K, hj]

lemma adaptive_execute {S W : Type} [MeasurableSpace S] [MeasurableSpace W]
    (law : MeasureTheory.ProbabilityMeasure S) (P : MeasureTheory.ProbabilityMeasure (ℕ → W))
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ) (project : E → E) (initial : E × E)
    (B : ℕ → ℕ) (u v : S → (t : ℕ) → Fin (B t) → E) (N T K : ℕ)
    (g : E → W → ℝ) (seed : S) (ξ : ℕ → W) (hK : 2 * T + dualSolverCalls B N ≤ K) :
    OracleTemplate.execute
      { Seed := fun _ => W, law := P, answer := fun _ (_, q) w => g q w }
      (adaptiveAlgorithm law d τ₁ τ₂ γ₁ γ₂ h s project initial B u v N T)
      (fun _ => K) seed (fun k => ξ (k / 2)) =
        adaptiveOutput d τ₁ τ₂ γ₁ γ₂ h s project initial B (u seed) (v seed) g ξ 0 N T := by
  have he := execute_sampledPlan_of_le law P initial.1 initial.1 (2 * T + dualSolverCalls B N) K
    (fun z => adaptiveSelectionPlan d τ₁ τ₂ γ₁ γ₂ h s project initial B (u z) (v z) N T)
    g seed (fun k => ξ (k / 2)) hK
  exact he.trans (adaptive_selection_sampled_eval d τ₁ τ₂ γ₁ γ₂ h s project initial B
    (u seed) (v seed) g ξ 0 N T)

lemma adaptive_output_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ) {project : E → E} (hp : Continuous project)
    (initial : E × E) (B : ℕ → ℕ) (u v : Z → (t : ℕ) → Fin (B t) → E)
    (hu : ∀ t i, Measurable (fun z => u z t i))
    (hv : ∀ t i, Measurable (fun z => v z t i))
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m N T : ℕ) :
    Measurable (fun z => adaptiveOutput d τ₁ τ₂ γ₁ γ₂ h s project initial B
      (u z) (v z) g (fun j => ξ j z) m N T) := by
  let states := fun z => dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B
    (u z) (v z) g (fun j => ξ j z) m N
  have hm : Measurable states := dual_solver_state_measurable d τ₁ τ₂ γ₁ γ₂ h hp
    initial B u v hu hv g hg ξ hξ m N
  have he (i : Fin T) : Measurable (fun z => OracleTemplate.clip s
      (g (states z).1.1 (ξ (m + 2 * (∑ j ∈ Finset.range N, B j) + i) z) -
        g (states z).2.1 (ξ (m + 2 * (∑ j ∈ Finset.range N, B j) + i) z))) := by
    exact (OracleTemplate.measurable_clip s).comp
      ((hg.comp (hm.fst.fst.prodMk (hξ _))).sub (hg.comp (hm.snd.fst.prodMk (hξ _))))
  exact selected_measurable hm.fst.fst hm.snd.fst
    ((Finset.measurable_sum Finset.univ (fun i _ => he i)).const_mul (T : ℝ)⁻¹)

lemma accelerated_path_potential {Q : Set E} (hQ : Convex ℝ Q)
    {project : E → E} (hp : ∀ x, project x ∈ Q)
    (hnearest : ∀ x, ‖x - project x‖ = ⨅ w : Q, ‖x - w‖)
    {f : E → ℝ} {grad : E → E} {L h : ℝ} (hL : 0 ≤ L) (hh : 0 < h) (hcoef : 4 * L ≤ h)
    (hconvex : ∀ x ∈ Q, ∀ y ∈ Q, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hmodel : ∀ x ∈ Q, ∀ y ∈ Q, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (state : ℕ → E × E) (est : ℕ → E)
    (hx : (state 0).1 ∈ Q) (hz : (state 0).2 ∈ Q) {v : E} (hv : v ∈ Q)
    (hstep : ∀ t, state (t + 1) = acceleratedUpdate project h t (state t) (est t)) (N : ℕ) :
    let error := fun t => est t - grad (acceleratedMix t (state t).1 (state t).2)
    ((N : ℝ) * (N + 1) / 2) * (f (state N).1 - f v) ≤
      h / 2 * ‖(state 0).2 - v‖ ^ 2 +
        (∑ t ∈ Finset.range N, (t + 1 : ℝ) ^ 2 * ‖error t‖ ^ 2) / h -
        ∑ t ∈ Finset.range N, (t + 1 : ℝ) * ⟪error t, (state t).2 - v⟫ := by
  have hmem (t : ℕ) : (state t).1 ∈ Q ∧ (state t).2 ∈ Q := by
    induction t with
    | zero => exact ⟨hx, hz⟩
    | succ t ih => rw [hstep]; exact accelerated_update_mem hQ hp ih.1 h t (est t)
  dsimp only
  apply ScalarClippedAcceleration.potential_telescope
    (f := f) (x := fun t => (state t).1) (z := fun t => (state t).2)
    (e := _) (u := v) (A := fun t => (t : ℝ) * (t + 1) / 2)
    (a := fun t => (t + 1 : ℝ)) hh.le (by norm_num)
  intro t
  have hs := accelerated_update_potential hQ hp hnearest hL hh hcoef hconvex hmodel
    (hmem t).1 (hmem t).2 hv t (est t)
  dsimp only at hs
  have he : ((t + 1 : ℕ) : ℝ) * (((t + 1 : ℕ) : ℝ) + 1) / 2 =
      (t : ℝ) * (t + 1) / 2 + (t + 1) := by push_cast; ring
  simpa only [he, hstep] using hs

lemma dual_branch_potential {Q : Set E} (hQ : Convex ℝ Q)
    {project : E → E} (hp : ∀ x, project x ∈ Q)
    (hnearest : ∀ x, ‖x - project x‖ = ⨅ w : Q, ‖x - w‖)
    {f : E → ℝ} {grad : E → E} {L h : ℝ} (hL : 0 ≤ L) (hh : 0 < h) (hcoef : 4 * L ≤ h)
    (hconvex : ∀ x ∈ Q, ∀ y ∈ Q, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hmodel : ∀ x ∈ Q, ∀ y ∈ Q, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    {initial : E × E} (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q) {v : E} (hv : v ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ : ℝ) (B : ℕ → ℕ) (u₁ u₂ : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m N : ℕ) (branch : Bool) :
    let states := dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B u₁ u₂ g ξ m
    let state := fun t => if branch then (states t).1 else (states t).2
    let error := fun t =>
      let center := acceleratedMix t (state t).1 (state t).2
      let γ := if branch then γ₁ else γ₂
      let τ := if branch then τ₁ else τ₂
      let u := if branch then u₁ else u₂
      let start := m + 2 * (∑ j ∈ Finset.range t, B j) + (if branch then 0 else B t)
      (B t : ℝ)⁻¹ • (∑ i : Fin (B t), estimate d τ γ (u t i)
        (g (center + γ • u t i) (ξ (start + i)))
        (g (center - γ • u t i) (ξ (start + i)))) - grad center
    ((N : ℝ) * (N + 1) / 2) * (f (state N).1 - f v) ≤
      h / 2 * ‖initial.2 - v‖ ^ 2 +
        (∑ t ∈ Finset.range N, (t + 1 : ℝ) ^ 2 * ‖error t‖ ^ 2) / h -
        ∑ t ∈ Finset.range N, (t + 1 : ℝ) * ⟪error t, (state t).2 - v⟫ := by
  cases branch <;> dsimp only
  all_goals
    apply accelerated_path_potential hQ hp hnearest hL hh hcoef hconvex hmodel _ _ hx hz hv (N := N)
    intro t
    rfl

lemma pair_plan_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ γ : ℝ) {x u : Z → E} (hx : Measurable x) (hu : Measurable u)
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m : ℕ) :
    Measurable (fun z => sampledEval g (fun j => ξ j z) (pairPlan d τ γ (x z) (u z)) m) := by
  have hplus := hg.comp ((hx.add (hu.const_smul γ)).prodMk (hξ m))
  have hminus := hg.comp ((hx.sub (hu.const_smul γ)).prodMk (hξ (m + 1)))
  exact ClippedVectorMoments.direction_estimate_measurable hu
    ((hplus.sub hminus).div_const (2 * γ)) d τ

lemma batch_plan_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ γ : ℝ) {x : Z → E} (hx : Measurable x) {B : ℕ} (u : Z → Fin B → E)
    (hu : ∀ i, Measurable (fun z => u z i))
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m : ℕ) :
    Measurable (fun z => sampledEval g (fun j => ξ j z) (batchPlan d τ γ (x z) (u z)) m) := by
  simp only [batchPlan, sampledEval_map, sampledEval_traverse, List.sum_ofFn]
  exact (Finset.measurable_sum Finset.univ (fun i _ =>
    pair_plan_measurable d τ γ hx (hu i) g hg ξ hξ (m + 2 * i))).const_smul (B : ℝ)⁻¹

lemma round_plan_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ γ h : ℝ) {project : E → E} (hp : Continuous project) (t : ℕ)
    {state : Z → E × E} (hstate : Measurable state) {B : ℕ} (u : Z → Fin B → E)
    (hu : ∀ i, Measurable (fun z => u z i))
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m : ℕ) :
    Measurable (fun z => sampledEval g (fun j => ξ j z)
      (roundPlan d τ γ h project t (state z) (u z)) m) := by
  simp only [roundPlan, sampledEval_map]
  have hc := (accelerated_mix_continuous t).measurable.comp hstate
  have hgmean := batch_plan_measurable d τ γ hc u hu g hg ξ hξ m
  exact (accelerated_update_continuous hp h t).measurable.comp (hstate.prodMk hgmean)

lemma dual_plan_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) {project : E → E} (hp : Continuous project)
    (initial : E × E) (B : ℕ → ℕ) (u v : Z → (t : ℕ) → Fin (B t) → E)
    (hu : ∀ t i, Measurable (fun z => u z t i))
    (hv : ∀ t i, Measurable (fun z => v z t i))
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m n : ℕ) :
    Measurable (fun z => sampledEval g (fun j => ξ j z)
      (dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B (u z) (v z) n) m) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun z => sampledEval g (fun j => ξ j z)
      ((dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B (u z) (v z) n).bind
        (fun states => (roundPlan d τ₁ γ₁ h project n states.1 (u z n)).bind
          (fun first => (roundPlan d τ₂ γ₂ h project n states.2 (v z n)).map
            (fun second => (first, second))))) m)
    simp only [sampledEval_bind, sampledEval_map]
    exact (round_plan_measurable d τ₁ γ₁ h hp n ih.fst (fun z => u z n) (hu n)
      g hg ξ hξ (m + dualSolverCalls B n)).prodMk
      (round_plan_measurable d τ₂ γ₂ h hp n ih.snd (fun z => v z n) (hv n)
        g hg ξ hξ (m + dualSolverCalls B n + 2 * B n))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma selection_plan_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E]
    (s : ℝ) {a b : Z → E} (ha : Measurable a) (hb : Measurable b) (T : ℕ)
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m : ℕ) :
    Measurable (fun z => sampledEval g (fun j => ξ j z) (selectionPlan s (a z) (b z) T) m) := by
  simp only [selectionPlan, sampledEval_map, sampledEval_traverse, List.sum_ofFn,
    comparisonPairPlan, sampledEval]
  apply selected_measurable ha hb
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i hi
  exact (OracleTemplate.measurable_clip s).comp
    ((hg.comp (ha.prodMk (hξ (m + 2 * i)))).sub
      (hg.comp (hb.prodMk (hξ (m + 2 * i + 1)))))

lemma adaptive_plan_measurable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ) {project : E → E} (hp : Continuous project)
    (initial : E × E) (B : ℕ → ℕ) (u v : Z → (t : ℕ) → Fin (B t) → E)
    (hu : ∀ t i, Measurable (fun z => u z t i))
    (hv : ∀ t i, Measurable (fun z => v z t i))
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2))
    (ξ : ℕ → Z → Ω) (hξ : ∀ j, Measurable (ξ j)) (m N T : ℕ) :
    Measurable (fun z => sampledEval g (fun j => ξ j z)
      (adaptiveSelectionPlan d τ₁ τ₂ γ₁ γ₂ h s project initial B (u z) (v z) N T) m) := by
  simp only [adaptiveSelectionPlan, sampledEval_bind]
  have hm := dual_plan_measurable d τ₁ τ₂ γ₁ γ₂ h hp initial B u v hu hv g hg ξ hξ m N
  exact selection_plan_measurable s hm.fst.fst hm.snd.fst T g hg ξ hξ (m + dualSolverCalls B N)

lemma dual_solver_extended_history {R : Type*} [MeasurableSpace R] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Q : Set E} (hQ : Convex ℝ Q) {project : E → E} (hp : Continuous project)
    (hproject : ∀ x, project x ∈ Q) {initial : E × E}
    (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (B : ℕ → ℕ) (direction : R → E) (sample : R → Ω)
    (hd : Measurable direction) (hs : Measurable sample) (fallback : R)
    (g : E → Ω → ℝ) (hg : Measurable (fun p : E × Ω => g p.1 p.2)) (n K : ℕ)
    (hK : 2 * (∑ t ∈ Finset.range n, B t) ≤ K) :
    ∃ state : (Fin K → R) → (E × E) × (E × E), Measurable state ∧
      (∀ a, ((state a).1.1 ∈ Q ∧ (state a).1.2 ∈ Q) ∧
        ((state a).2.1 ∈ Q ∧ (state a).2.2 ∈ Q)) ∧
      ∀ records : ℕ → R, state (fun i => records i) =
        dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B
          (fun t i => direction (records (2 * (∑ j ∈ Finset.range t, B j) + i)))
          (fun t i => direction (records (2 * (∑ j ∈ Finset.range t, B j) + B t + i)))
          g (fun j => sample (records j)) 0 n := by
  obtain ⟨st, hm, he⟩ := dual_solver_finite_history d τ₁ τ₂ γ₁ γ₂ h hp initial B
    direction sample hd hs fallback g hg n
  let state := fun a : Fin K → R => st (fun i => a (i.castLE hK))
  have hid (records : ℕ → R) : state (fun i => records i) =
      dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B
        (fun t i => direction (records (2 * (∑ j ∈ Finset.range t, B j) + i)))
        (fun t i => direction (records (2 * (∑ j ∈ Finset.range t, B j) + B t + i)))
        g (fun j => sample (records j)) 0 n := by
    exact he records
  refine ⟨state, hm.comp (Measurable.of_eval (fun i => measurable_pi_apply (i.castLE hK))), ?_, hid⟩
  intro a
  let records := fun j : ℕ => if hj : j < K then a ⟨j, hj⟩ else fallback
  have ha : (fun i : Fin K => records i) = a := by
    funext i
    simp only [records, dite_eq_left i.isLt]
  rw [← ha, hid records]
  exact dual_solver_state_mem hQ hproject hx hz d τ₁ τ₂ γ₁ γ₂ h B _ _ g _ 0 n

lemma batch_error_decomposition {B : ℕ} (hB : 0 < B) (values : Fin B → E)
    (mean grad : E) :
    (B : ℝ)⁻¹ • (∑ i, values i) - grad =
      (B : ℝ)⁻¹ • (∑ i, (values i - mean)) + (mean - grad) := by
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_sub, ← Nat.cast_smul_eq_nsmul ℝ B mean, smul_smul, inv_mul_cancel₀ hBr, one_smul]
  abel

lemma batch_sampled_error_decomposition (d : ℕ) (τ γ : ℝ) (x : E)
    {B : ℕ} (hB : 0 < B) (u : Fin B → E) (g : E → Ω → ℝ)
    (ξ : ℕ → Ω) (m : ℕ) (mean grad : E) :
    sampledEval g (fun k => ξ (k / 2)) (batchPlan d τ γ x u) (2 * m) - grad =
      (B : ℝ)⁻¹ • (∑ i : Fin B,
        (estimate d τ γ (u i) (g (x + γ • u i) (ξ (m + i)))
          (g (x - γ • u i) (ξ (m + i))) - mean)) + (mean - grad) := by
  rw [batch_sampled_eval]
  exact batch_error_decomposition hB _ mean grad

lemma round_plan_mem {Q : Set E} (hQ : Convex ℝ Q) {project : E → E}
    (hp : ∀ x, project x ∈ Q) {state : E × E} (hx : state.1 ∈ Q)
    (d : ℕ) (τ γ h : ℝ) (t : ℕ) {B : ℕ} (u : Fin B → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m : ℕ) :
    let result := sampledEval g ξ (roundPlan d τ γ h project t state u) m
    result.1 ∈ Q ∧ result.2 ∈ Q := by
  simp only [roundPlan, sampledEval_map]
  exact accelerated_update_mem hQ hp hx h t _

lemma dual_plan_mem {Q : Set E} (hQ : Convex ℝ Q) {project : E → E}
    (hp : ∀ x, project x ∈ Q) {initial : E × E} (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (B : ℕ → ℕ) (u v : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m n : ℕ) :
    let states := sampledEval g ξ (dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v n) m
    (states.1.1 ∈ Q ∧ states.1.2 ∈ Q) ∧ (states.2.1 ∈ Q ∧ states.2.2 ∈ Q) := by
  induction n with
  | zero => exact ⟨⟨hx, hz⟩, ⟨hx, hz⟩⟩
  | succ n ih =>
    let old := sampledEval g ξ (dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v n) m
    let first := sampledEval g ξ (roundPlan d τ₁ γ₁ h project n old.1 (u n))
      (m + dualSolverCalls B n)
    let second := sampledEval g ξ (roundPlan d τ₂ γ₂ h project n old.2 (v n))
      (m + dualSolverCalls B n + 2 * B n)
    have he : sampledEval g ξ (dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v (n + 1)) m =
        (first, second) := by
      change sampledEval g ξ
        ((dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v n).bind
          (fun states => (roundPlan d τ₁ γ₁ h project n states.1 (u n)).bind
            (fun first => (roundPlan d τ₂ γ₂ h project n states.2 (v n)).map
              (fun second => (first, second))))) m = _
      rw [sampledEval_bind, sampledEval_bind, sampledEval_map]
    dsimp only
    rw [he]
    exact ⟨round_plan_mem hQ hp ih.1.1 d τ₁ γ₁ h n (u n) g ξ (m + dualSolverCalls B n),
      round_plan_mem hQ hp ih.2.1 d τ₂ γ₂ h n (v n) g ξ (m + dualSolverCalls B n + 2 * B n)⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma selection_plan_mem {Q : Set E} {a b : E} (ha : a ∈ Q) (hb : b ∈ Q)
    (s : ℝ) (T : ℕ) (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m : ℕ) :
    sampledEval g ξ (selectionPlan s a b T) m ∈ Q := by
  simp only [selectionPlan, sampledEval_map]
  unfold selectByDifference
  split_ifs <;> assumption

lemma adaptive_plan_mem {Q : Set E} (hQ : Convex ℝ Q) {project : E → E}
    (hp : ∀ x, project x ∈ Q) {initial : E × E} (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ) (B : ℕ → ℕ) (u v : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m N T : ℕ) :
    sampledEval g ξ (adaptiveSelectionPlan d τ₁ τ₂ γ₁ γ₂ h s project initial B u v N T) m ∈ Q := by
  simp only [adaptiveSelectionPlan, sampledEval_bind]
  have hm := dual_plan_mem hQ hp hx hz d τ₁ τ₂ γ₁ γ₂ h B u v g ξ m N
  exact selection_plan_mem hm.1.1 hm.2.1 s T g ξ (m + dualSolverCalls B N)

lemma adaptive_execute_mem {S W : Type} [MeasurableSpace S] [MeasurableSpace W]
    (law : MeasureTheory.ProbabilityMeasure S) (P : MeasureTheory.ProbabilityMeasure (ℕ → W))
    {Q : Set E} (hQ : Convex ℝ Q) {project : E → E} (hp : ∀ x, project x ∈ Q)
    {initial : E × E} (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ) (B : ℕ → ℕ)
    (u v : S → (t : ℕ) → Fin (B t) → E) (N T K : ℕ)
    (g : E → W → ℝ) (seed : S) (ξ : ℕ → W)
    (hK : 2 * T + dualSolverCalls B N ≤ K) :
    OracleTemplate.execute
      { Seed := fun _ => W, law := P, answer := fun _ (_, q) w => g q w }
      (adaptiveAlgorithm law d τ₁ τ₂ γ₁ γ₂ h s project initial B u v N T)
      (fun _ => K) seed ξ ∈ Q := by
  have he := execute_sampledPlan_of_le law P initial.1 initial.1 (2 * T + dualSolverCalls B N) K
    (fun z => adaptiveSelectionPlan d τ₁ τ₂ γ₁ γ₂ h s project initial B (u z) (v z) N T)
    g seed ξ hK
  exact he.symm ▸ adaptive_plan_mem hQ hp hx hz d τ₁ τ₂ γ₁ γ₂ h s B (u seed) (v seed) g ξ 0 N T

end LongTails.Proofs.ClippedTwoPointExecution
