import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.AdamHeavyTailedWindow

open MeasureTheory

namespace LongTails.Proofs.AdamHeavyTailedProcess

open OracleTemplate.StochasticGeneralized

lemma accumulated_abs_bound {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (increment : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    {B : ℝ} (hinc : ∀ n s b, |increment n s b| ≤ B) (k : ℕ) (s : S) (ξ : ℕ → Ω) :
    |accumulated cost next increment k s ξ| ≤ (k : ℝ) * B := by
  induction k generalizing s ξ with
  | zero => simp [accumulated]
  | succ k ih =>
    rw [accumulated]
    calc
      _ ≤ |increment (cost s) s (fun i => ξ i)| +
          |accumulated cost next increment k (next (cost s) s (fun i => ξ i))
            (fun i => ξ (cost s + i))| := abs_add_le _ _
      _ ≤ B + (k : ℝ) * B := add_le_add (hinc _ _ _) (ih _ _)
      _ = ((k + 1 : ℕ) : ℝ) * B := by push_cast; ring

lemma accumulated_integrable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] {cost : S → ℕ}
    {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {increment : (n : ℕ) → S → (Fin n → Ω) → ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hi : ∀ n, Measurable (Function.uncurry (increment n)))
    {B : ℝ} (hb : ∀ n s b, |increment n s b| ≤ B) (k : ℕ) (s : S) :
    Integrable (fun ξ => accumulated cost next increment k s ξ)
      (Measure.infinitePi fun _ : ℕ => p) := by
  apply Integrable.of_bound
    (((accumulated_measurable hc hn hi k).comp measurable_prodMk_left).aestronglyMeasurable)
    ((k : ℝ) * B)
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖accumulated cost next increment k s ξ‖ ≤ _
    rw [Real.norm_eq_abs]
    exact accumulated_abs_bound cost next increment hb k s ξ

lemma accumulated_expectation_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] {cost : S → ℕ}
    {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {increment : (n : ℕ) → S → (Fin n → Ω) → ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hi : ∀ n, Measurable (Function.uncurry (increment n)))
    {B C : ℝ} (hb : ∀ n s b, |increment n s b| ≤ B)
    (hmean : ∀ s, (∫ b, increment (cost s) s b ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ C)
    (k : ℕ) (s : S) :
    (∫ ξ, accumulated cost next increment k s ξ ∂Measure.infinitePi (fun _ : ℕ => p)) ≤
      (k : ℝ) * C := by
  induction k generalizing s with
  | zero => simp [accumulated]
  | succ k ih =>
    let m := cost s
    let F : (Fin m → Ω) × (ℕ → Ω) → ℝ := fun z =>
      increment m s z.1 + accumulated cost next increment k (next m s z.1) z.2
    have hnext : Measurable (fun b : Fin m → Ω => next m s b) :=
      (hn m).comp measurable_prodMk_left
    have hinc : Measurable (fun b : Fin m → Ω => increment m s b) :=
      (hi m).comp measurable_prodMk_left
    have hF : Measurable F :=
      (hinc.comp measurable_fst).add ((accumulated_measurable hc hn hi k).comp
        ((hnext.comp measurable_fst).prodMk measurable_snd))
    have hiinc : Integrable (fun b => increment m s b) (Measure.pi fun _ : Fin m => p) := by
      apply Integrable.of_bound hinc.aestronglyMeasurable B
      exact Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hb m s b
    have hprod : Integrable F ((Measure.pi fun _ : Fin m => p).prod
        (Measure.infinitePi fun _ : ℕ => p)) := by
      apply Integrable.of_bound hF.aestronglyMeasurable (B + (k : ℝ) * B)
      exact Filter.Eventually.of_forall fun z => by
        change ‖increment m s z.1 + accumulated cost next increment k (next m s z.1) z.2‖ ≤ _
        rw [Real.norm_eq_abs]
        exact (abs_add_le _ _).trans (add_le_add (hb _ _ _)
          (accumulated_abs_bound cost next increment hb k _ _))
    have hpoint (b : Fin m → Ω) :
        (∫ ξ, F (b, ξ) ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ increment m s b + (k : ℝ) * C := by
      dsimp [F]
      rw [integral_add (integrable_const _) (accumulated_integrable p hc hn hi hb k _)]
      simp only [integral_const, probReal_univ, one_smul]
      exact add_le_add le_rfl (ih _)
    have hsplit := splitStream_preserving p m
    have he : (fun ξ => accumulated cost next increment (k + 1) s ξ) = F ∘ splitStream m := rfl
    rw [he]
    change (∫ ξ, F (splitStream m ξ) ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ _
    rw [hsplit.integral_comp' F, integral_prod _ hprod]
    calc
      _ ≤ ∫ b, increment m s b + (k : ℝ) * C ∂Measure.pi (fun _ : Fin m => p) :=
        integral_mono hprod.integral_prod_left (hiinc.add (integrable_const _)) hpoint
      _ = (∫ b, increment m s b ∂Measure.pi (fun _ : Fin m => p)) + (k : ℝ) * C := by
        rw [integral_add hiinc (integrable_const _)]
        simp
      _ ≤ C + (k : ℝ) * C := add_le_add (hmean s) le_rfl
      _ = ((k + 1 : ℕ) : ℝ) * C := by push_cast; ring

lemma accumulated_potential_drop {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (F : S → ℝ)
    (k : ℕ) (s : S) (ξ : ℕ → Ω) :
    accumulated cost next (fun n s b => F s - F (next n s b)) k s ξ =
      F s - F (blockTrace cost next s ξ k).1 := by
  induction k generalizing s ξ with
  | zero => simp [accumulated, blockTrace_zero]
  | succ k ih =>
    rw [accumulated, ih, blockTrace_start_succ]
    ring

abbrev WindowState (S κ : Type*) (N : ℕ) := S × ((Fin N → κ → ℝ) × ℕ)

noncomputable def windowAdvance {S Ω κ : Type*} {N : ℕ}
    (next : S → Ω → S) (noise : S → Ω → κ → ℝ)
    (s : WindowState S κ N) (ω : Ω) : WindowState S κ N :=
  (next s.1 ω, ((fun j i => if j.val = s.2.2 then s.2.1 j i + noise s.1 ω i else s.2.1 j i), s.2.2 + 1))

noncomputable def windowPotential {S κ : Type*} [Fintype κ] {N : ℕ}
    (w μ : κ → ℝ) (a : Fin N → ℝ) (τ : ℝ) (i : Fin N) (s : WindowState S κ N) : ℝ :=
  ∑ k, μ k * AdamHeavyTailedWindow.response (w k) a τ i (fun j => s.2.1 j k)

lemma measurable_windowAdvance {S Ω κ : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {N : ℕ} {next : S → Ω → S} {noise : S → Ω → κ → ℝ}
    (hn : Measurable (Function.uncurry next)) (he : Measurable (Function.uncurry noise)) :
    Measurable (Function.uncurry (windowAdvance (N := N) next noise)) := by
  have hs : Measurable (fun z : WindowState S κ N × Ω => (z.1.1, z.2)) := by fun_prop
  apply (hn.comp hs).prodMk
  apply Measurable.prodMk _ (by fun_prop)
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro i
  apply Measurable.ite (measurableSet_eq_fun measurable_const (by fun_prop))
  · exact (by fun_prop : Measurable (fun z : WindowState S κ N × Ω => z.1.2.1 j i)).add
      ((measurable_pi_apply i).comp (he.comp hs))
  · fun_prop

lemma measurable_windowPotential {S κ : Type*} [MeasurableSpace S] [Fintype κ] {N : ℕ}
    (w μ : κ → ℝ) (a : Fin N → ℝ) (τ : ℝ) (i : Fin N) :
    Measurable (windowPotential (S := S) w μ a τ i) := by
  unfold windowPotential AdamHeavyTailedWindow.response
  fun_prop

lemma windowPotential_bound {S κ : Type*} [Fintype κ] {N : ℕ}
    (w μ : κ → ℝ) (a : Fin N → ℝ) {τ : ℝ} (i : Fin N)
    (hw : ∀ k, 0 ≤ w k) (ha : ∀ j, 0 ≤ a j) (hτ : 0 < τ) (hai : 0 < a i)
    (s : WindowState S κ N) :
    |windowPotential w μ a τ i s| ≤ ∑ k, |μ k| * (1 / Real.sqrt (a i)) := by
  unfold windowPotential
  calc
    _ ≤ ∑ k, |μ k * AdamHeavyTailedWindow.response (w k) a τ i (fun j => s.2.1 j k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (AdamHeavyTailedWindow.response_bound (hw k) hτ a _ ha i hai) (abs_nonneg _)

lemma windowAdvance_history {S Ω κ : Type*} {N : ℕ}
    (next : S → Ω → S) (noise : S → Ω → κ → ℝ)
    (s : WindowState S κ N) (ω : Ω) (j : Fin N) (hj : j.val = s.2.2) (i : κ) :
    (fun k => (windowAdvance next noise s ω).2.1 k i) =
      Function.update (fun k => s.2.1 k i) j (s.2.1 j i + noise s.1 ω i) := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [windowAdvance, hj]
  · have hne : k.val ≠ s.2.2 := by
      intro he
      exact hk (Fin.ext (he.trans hj.symm))
    simp [windowAdvance, hk, hne]

lemma windowAdvance_history_finished {S Ω κ : Type*} {N : ℕ}
    (next : S → Ω → S) (noise : S → Ω → κ → ℝ)
    (s : WindowState S κ N) (ω : Ω) (hN : N ≤ s.2.2) :
    (windowAdvance next noise s ω).2.1 = s.2.1 := by
  funext j i
  have hne : j.val ≠ s.2.2 := by have hj := j.isLt; omega
  simp [windowAdvance, hne]

lemma windowAdvance_bias {S Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    (next : S → Ω → S) (noise : S → Ω → κ → ℝ)
    (w μ : κ → ℝ) (a : Fin N → ℝ) {τ p W M : ℝ} (i : Fin N)
    (hw : ∀ k, 0 ≤ w k) (ha : ∀ j, 0 ≤ a j) (hτ : 0 < τ) (hai : 0 < a i)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hint : ∀ s k, Integrable (fun ω => noise s ω k) P)
    (hmean : ∀ s k, ∫ ω, noise s ω k ∂P = 0)
    (hm : ∀ s k, Integrable (fun ω => |noise s ω k| ^ p) P)
    (hmass : ∀ s, (∑ k, ∫ ω, |noise s ω k| ^ p ∂P) ≤ M)
    (hcoef : ∀ j k, |μ k| * ((4 * (Real.sqrt (a j) / (Real.sqrt (w k) + τ)) ^ p) /
      Real.sqrt (a i)) ≤ W) (s : WindowState S κ N) :
    |(∫ ω, windowPotential w μ a τ i (windowAdvance next noise s ω) ∂P) -
      windowPotential w μ a τ i s| ≤ W * M := by
  by_cases hs : s.2.2 < N
  · let j : Fin N := ⟨s.2.2, hs⟩
    have he : (fun ω => windowPotential w μ a τ i (windowAdvance next noise s ω)) =
        fun ω => ∑ k, μ k * AdamHeavyTailedWindow.response (w k) a τ i
          (Function.update (fun l => s.2.1 l k) j (s.2.1 j k + noise s.1 ω k)) := by
      funext ω
      unfold windowPotential
      apply Finset.sum_congr rfl
      intro k _
      rw [windowAdvance_history next noise s ω j rfl k]
    rw [he]
    exact AdamHeavyTailedWindow.joint_coordinate_bias w μ hw hτ a
      (fun k l => s.2.1 l k) ha i j hai hp hp2
      (hint s.1) (hmean s.1) (hm s.1) hW (hcoef j) (hmass s.1)
  · have he (ω : Ω) : windowPotential w μ a τ i (windowAdvance next noise s ω) =
        windowPotential w μ a τ i s := by
      unfold windowPotential
      rw [windowAdvance_history_finished next noise s ω (Nat.le_of_not_gt hs)]
    simp only [he, integral_const, probReal_univ, one_smul, sub_self, abs_zero]
    exact mul_nonneg hW hM

noncomputable def singleNext {S Ω : Type*} (step : S → Ω → S)
    (n : ℕ) (s : S) (b : Fin n → Ω) : S :=
  if h : 0 < n then step s (b ⟨0, h⟩) else s

lemma measurable_singleNext {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {step : S → Ω → S} (hs : Measurable (Function.uncurry step)) (n : ℕ) :
    Measurable (Function.uncurry (singleNext step n)) := by
  change Measurable (fun z : S × (Fin n → Ω) =>
    if h : 0 < n then step z.1 (z.2 ⟨0, h⟩) else z.1)
  by_cases hn : 0 < n
  · simp only [dite_eq_left hn]
    exact hs.comp (show Measurable (fun z : S × (Fin n → Ω) => (z.1, z.2 ⟨0, hn⟩)) by fun_prop)
  · simp only [dite_eq_right hn]
    exact measurable_fst

lemma singleNext_integral {S Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω)  (step : S → Ω → S) (F : S → ℝ) (s : S) :
    (∫ b, F s - F (singleNext step 1 s b) ∂Measure.pi (fun _ : Fin 1 => p)) =
      ∫ ω, F s - F (step s ω) ∂p := by
  have he := (measurePreserving_funUnique p (Fin 1)).integral_comp'
    (fun ω => F s - F (step s ω))
  change (∫ b, F s - F (step s (b default)) ∂Measure.pi (fun _ : Fin 1 => p)) = _ at he
  simpa [singleNext] using he

lemma window_expectation {S Ω κ : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [Fintype κ] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ}
    (next : S → Ω → S) (noise : S → Ω → κ → ℝ)
    (hn : Measurable (Function.uncurry next)) (he : Measurable (Function.uncurry noise))
    (w μ : κ → ℝ) (a : Fin N → ℝ) {τ p W M : ℝ} (i : Fin N)
    (hw : ∀ k, 0 ≤ w k) (ha : ∀ j, 0 ≤ a j) (hτ : 0 < τ) (hai : 0 < a i)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hint : ∀ s k, Integrable (fun ω => noise s ω k) P)
    (hmean : ∀ s k, ∫ ω, noise s ω k ∂P = 0)
    (hm : ∀ s k, Integrable (fun ω => |noise s ω k| ^ p) P)
    (hmass : ∀ s, (∑ k, ∫ ω, |noise s ω k| ^ p ∂P) ≤ M)
    (hcoef : ∀ j k, |μ k| * ((4 * (Real.sqrt (a j) / (Real.sqrt (w k) + τ)) ^ p) /
      Real.sqrt (a i)) ≤ W) (s : WindowState S κ N) :
    (∫ ξ, windowPotential w μ a τ i s - windowPotential w μ a τ i
      (blockTrace (fun _ => 1) (singleNext (windowAdvance next noise)) s ξ N).1
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ (N : ℝ) * (W * M) := by
  let F := windowPotential (S := S) w μ a τ i
  let step := windowAdvance (N := N) next noise
  let B := ∑ k, |μ k| * (1 / Real.sqrt (a i))
  have hF : Measurable F := measurable_windowPotential w μ a τ i
  have hstep : Measurable (Function.uncurry step) := measurable_windowAdvance hn he
  have hFn (s' : WindowState S κ N) : |F s'| ≤ B := windowPotential_bound w μ a i hw ha hτ hai s'
  have hnext (n : ℕ) := measurable_singleNext hstep n
  have hinc (n : ℕ) : Measurable (Function.uncurry
      (fun s' b => F s' - F (singleNext step n s' b))) :=
    (hF.comp measurable_fst).sub (hF.comp (hnext n))
  have hb (n : ℕ) (s' : WindowState S κ N) (b : Fin n → Ω) :
      |F s' - F (singleNext step n s' b)| ≤ 2 * B := by
    have hh : |F s' - F (singleNext step n s' b)| ≤
        |F s'| + |F (singleNext step n s' b)| := by
      simpa using abs_sub_le (F s') 0 (F (singleNext step n s' b))
    linarith [hFn s', hFn (singleNext step n s' b)]
  have hmean' (s' : WindowState S κ N) :
      (∫ b, F s' - F (singleNext step 1 s' b) ∂Measure.pi (fun _ : Fin 1 => P)) ≤ W * M := by
    rw [singleNext_integral]
    have hiF : Integrable (fun ω => F (step s' ω)) P := by
      apply Integrable.of_bound ((hF.comp (hstep.comp measurable_prodMk_left)).aestronglyMeasurable) B
      exact Filter.Eventually.of_forall fun ω => by
        change ‖F (step s' ω)‖ ≤ B
        simpa only [Real.norm_eq_abs] using hFn (step s' ω)
    rw [integral_sub (integrable_const _) hiF, integral_const, probReal_univ, one_smul]
    have hbi := windowAdvance_bias next noise w μ a i hw ha hτ hai hp hp2 hW hM
      hint hmean hm hmass hcoef s'
    have hh : F s' - (∫ ω, F (step s' ω) ∂P) ≤
        |(∫ ω, F (step s' ω) ∂P) - F s'| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact hh.trans hbi
  have hb' := accumulated_expectation_bound P (cost := fun _ : WindowState S κ N => 1)
    (next := singleNext step) (increment := fun n s' b => F s' - F (singleNext step n s' b))
    measurable_const hnext hinc hb hmean' N s
  simpa only [accumulated_potential_drop] using hb'

noncomputable def stateAt {S Ω : Type*} (next : S → Ω → S) (s : S) (ξ : ℕ → Ω) (t : ℕ) : S :=
  (blockTrace (fun _ => 1) (singleNext next) s ξ t).1

lemma single_blockCalls {S Ω : Type*} (next : S → Ω → S) (s : S) (ξ : ℕ → Ω) (t : ℕ) :
    blockCalls (fun _ => 1) (singleNext next) s ξ t = t := by
  simp [blockCalls]

lemma stateAt_zero {S Ω : Type*} (next : S → Ω → S) (s : S) (ξ : ℕ → Ω) :
    stateAt next s ξ 0 = s := rfl

lemma stateAt_succ {S Ω : Type*} (next : S → Ω → S) (s : S) (ξ : ℕ → Ω) (t : ℕ) :
    stateAt next s ξ (t + 1) = next (stateAt next s ξ t) (ξ t) := by
  unfold stateAt
  rw [blockTrace_succ]
  change singleNext next 1 (blockTrace (fun _ => 1) (singleNext next) s ξ t).1
    (fun i => (blockTrace (fun _ => 1) (singleNext next) s ξ t).2 i) = _
  simp only [singleNext, Nat.zero_lt_succ, dite_true]
  rw [blockTrace_tail, single_blockCalls]
  simp

lemma measurable_stateAt {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {next : S → Ω → S} (hn : Measurable (Function.uncurry next)) (s : S) (t : ℕ) :
    Measurable (fun ξ => stateAt next s ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp_rw [stateAt_succ]
    exact hn.comp (ih.prodMk (measurable_pi_apply t))

lemma window_stateAt_source {S Ω κ : Type*} {N : ℕ} (next : S → Ω → S)
    (noise : S → Ω → κ → ℝ) (s : WindowState S κ N) (ξ : ℕ → Ω) (t : ℕ) :
    (stateAt (windowAdvance next noise) s ξ t).1 = stateAt next s.1 ξ t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [stateAt_succ, windowAdvance, ih]

lemma window_stateAt_clock {S Ω κ : Type*} {N : ℕ} (next : S → Ω → S)
    (noise : S → Ω → κ → ℝ) (s : WindowState S κ N) (ξ : ℕ → Ω) (t : ℕ) :
    (stateAt (windowAdvance next noise) s ξ t).2.2 = s.2.2 + t := by
  induction t with
  | zero => simp [stateAt_zero]
  | succ t ih => simp only [stateAt_succ, windowAdvance, ih, Nat.add_assoc]

lemma window_stateAt_history {S Ω κ : Type*} {N : ℕ} (next : S → Ω → S)
    (noise : S → Ω → κ → ℝ) (s : S) (μ : κ → ℝ) (ξ : ℕ → Ω) (t : ℕ)
    (j : Fin N) (i : κ) :
    (stateAt (windowAdvance next noise) (s, ((fun _ => μ), 0)) ξ t).2.1 j i =
      if j.val < t then μ i + noise (stateAt next s ξ j.val) (ξ j.val) i else μ i := by
  induction t with
  | zero => simp [stateAt_zero]
  | succ t ih =>
    rw [stateAt_succ]
    change (if j.val = (stateAt (windowAdvance next noise) (s, ((fun _ => μ), 0)) ξ t).2.2
      then (stateAt (windowAdvance next noise) (s, ((fun _ => μ), 0)) ξ t).2.1 j i +
        noise (stateAt (windowAdvance next noise) (s, ((fun _ => μ), 0)) ξ t).1 (ξ t) i
      else (stateAt (windowAdvance next noise) (s, ((fun _ => μ), 0)) ξ t).2.1 j i) = _
    rw [window_stateAt_clock, window_stateAt_source, ih]
    simp only [Nat.zero_add]
    by_cases he : j.val = t
    · simp [he]
    · have hh : j.val < t + 1 ↔ j.val < t := by omega
      simp [he, hh]

lemma window_terminal_potential {S Ω κ : Type*} [Fintype κ] {N : ℕ}
    (next : S → Ω → S) (noise : S → Ω → κ → ℝ)
    (w μ : κ → ℝ) (a : Fin N → ℝ) (τ : ℝ) (i : Fin N) (s : S) (ξ : ℕ → Ω) :
    windowPotential w μ a τ i (stateAt (windowAdvance next noise) (s, ((fun _ => μ), 0)) ξ N) =
      ∑ k, μ k * AdamHeavyTailedWindow.response (w k) a τ i
        (fun j => μ k + noise (stateAt next s ξ j.val) (ξ j.val) k) := by
  unfold windowPotential
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  funext j
  rw [window_stateAt_history, ite_eq_left j.isLt]

lemma frozen_window_bias {S Ω κ : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [Fintype κ] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ}
    (next : S → Ω → S) (noise : S → Ω → κ → ℝ)
    (hn : Measurable (Function.uncurry next)) (he : Measurable (Function.uncurry noise))
    (w μ : κ → ℝ) (a : Fin N → ℝ) {τ p W M : ℝ} (i : Fin N)
    (hw : ∀ k, 0 ≤ w k) (ha : ∀ j, 0 ≤ a j) (hτ : 0 < τ) (hai : 0 < a i)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hint : ∀ s k, Integrable (fun ω => noise s ω k) P)
    (hmean : ∀ s k, ∫ ω, noise s ω k ∂P = 0)
    (hm : ∀ s k, Integrable (fun ω => |noise s ω k| ^ p) P)
    (hmass : ∀ s, (∑ k, ∫ ω, |noise s ω k| ^ p ∂P) ≤ M)
    (hcoef : ∀ j k, |μ k| * ((4 * (Real.sqrt (a j) / (Real.sqrt (w k) + τ)) ^ p) /
      Real.sqrt (a i)) ≤ W) (s : S) :
    (∫ ξ, (∑ k, μ k * AdamHeavyTailedWindow.response (w k) a τ i (fun _ => μ k)) -
      (∑ k, μ k * AdamHeavyTailedWindow.response (w k) a τ i
        (fun j => μ k + noise (stateAt next s ξ j.val) (ξ j.val) k))
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ (N : ℝ) * (W * M) := by
  have hh := window_expectation P next noise hn he w μ a i hw ha hτ hai hp hp2 hW hM
    hint hmean hm hmass hcoef (s, ((fun _ => μ), 0))
  change (∫ ξ, windowPotential w μ a τ i (s, ((fun _ => μ), 0)) -
    windowPotential w μ a τ i (stateAt (windowAdvance next noise)
      (s, ((fun _ => μ), 0)) ξ N) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _ at hh
  simp_rw [window_terminal_potential] at hh
  simp only [windowPotential] at hh
  exact hh

lemma stateAt_congr {S Ω : Type*} (next : S → Ω → S) (s : S) {ξ ζ : ℕ → Ω} (t : ℕ)
    (h : ∀ k < t, ξ k = ζ k) : stateAt next s ξ t = stateAt next s ζ t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [stateAt_succ, stateAt_succ, ih (fun k hk => h k (by omega)), h t (by omega)]

noncomputable def prefixState {S Ω : Type*} (next : S → Ω → S) (s : S) (ω0 : Ω)
    (n : ℕ) (b : Fin n → Ω) : S :=
  stateAt next s (fun k => if h : k < n then b ⟨k, h⟩ else ω0) n

lemma prefixState_stream {S Ω : Type*} (next : S → Ω → S) (s : S) (ω0 : Ω)
    (n : ℕ) (ξ : ℕ → Ω) : prefixState next s ω0 n (fun i => ξ i) = stateAt next s ξ n := by
  apply stateAt_congr
  intro k hk
  simp [hk]

lemma measurable_prefixState {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {next : S → Ω → S} (hn : Measurable (Function.uncurry next)) (s : S) (ω0 : Ω) (n : ℕ) :
    Measurable (prefixState next s ω0 n) := by
  apply (measurable_stateAt hn s n).comp
  apply Measurable.of_eval
  intro k
  by_cases hk : k < n
  · simp only [dite_eq_left hk]
    exact measurable_pi_apply _
  · simp only [dite_eq_right hk]
    exact measurable_const

lemma stateAt_tail_integral {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (next : S → Ω → S) (s : S) (ω0 : Ω)
    (n : ℕ) (F : S → (ℕ → Ω) → ℝ)
    (hi : Integrable (fun z : (Fin n → Ω) × (ℕ → Ω) => F (prefixState next s ω0 n z.1) z.2)
      ((Measure.pi fun _ : Fin n => P).prod (Measure.infinitePi fun _ : ℕ => P))) :
    (∫ ξ, F (stateAt next s ξ n) (fun k => ξ (n + k)) ∂Measure.infinitePi (fun _ : ℕ => P)) =
      ∫ b, ∫ ξ, F (prefixState next s ω0 n b) ξ ∂Measure.infinitePi (fun _ : ℕ => P)
        ∂Measure.pi (fun _ : Fin n => P) := by
  let H : (Fin n → Ω) × (ℕ → Ω) → ℝ := fun z => F (prefixState next s ω0 n z.1) z.2
  have he : (fun ξ => F (stateAt next s ξ n) (fun k => ξ (n + k))) = H ∘ splitStream n := by
    funext ξ
    dsimp [H, splitStream]
    rw [prefixState_stream]
  rw [he]
  change (∫ ξ, H (splitStream n ξ) ∂Measure.infinitePi (fun _ : ℕ => P)) = _
  rw [(splitStream_preserving P n).integral_comp' H]
  exact integral_prod _ hi

lemma first_two_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω × Ω → ℝ) (hi : Integrable F (P.prod P)) :
    (∫ ξ, F (ξ 0, ξ 1) ∂Measure.infinitePi (fun _ : ℕ => P)) = ∫ ω, ∫ z, F (ω, z) ∂P ∂P := by
  have hp : MeasurePreserving (fun ξ : ℕ → Ω => (ξ 0, ξ 1))
      (Measure.infinitePi fun _ : ℕ => P) (P.prod P) :=
    (measurePreserving_finTwoArrow P).comp (prefix_preserving P 2)
  have hi' : AEStronglyMeasurable F ((Measure.infinitePi fun _ : ℕ => P).map (fun ξ => (ξ 0, ξ 1))) := by
    rw [hp.map_eq]
    exact hi.aestronglyMeasurable
  have he := integral_map hp.measurable.aemeasurable hi'
  rw [hp.map_eq] at he
  exact he.symm.trans (integral_prod F hi)

lemma frozen_window_bias_scaled {S Ω κ : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [Fintype κ] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ}
    (next : S → Ω → S) (noise : S → Ω → κ → ℝ)
    (hn : Measurable (Function.uncurry next)) (he : Measurable (Function.uncurry noise))
    (w μ : κ → ℝ) (a : Fin N → ℝ) {τ p B M : ℝ} (i : Fin N)
    (hw : ∀ k, 0 ≤ w k) (ha : ∀ j, 0 ≤ a j) (hτ : 0 < τ) (hai : 0 < a i)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hint : ∀ s k, Integrable (fun ω => noise s ω k) P)
    (hmean : ∀ s k, ∫ ω, noise s ω k ∂P = 0)
    (hm : ∀ s k, Integrable (fun ω => |noise s ω k| ^ p) P)
    (hmass : ∀ s, (∑ k, ∫ ω, |noise s ω k| ^ p ∂P) ≤ M)
    (hcoef : ∀ j k, |μ k| * ((4 * (Real.sqrt (a j) / (Real.sqrt (w k) + τ)) ^ p) /
      Real.sqrt (a i)) * M ≤ B) (s : S) :
    (∫ ξ, (∑ k, μ k * AdamHeavyTailedWindow.response (w k) a τ i (fun _ => μ k)) -
      (∑ k, μ k * AdamHeavyTailedWindow.response (w k) a τ i
        (fun j => μ k + noise (stateAt next s ξ j.val) (ξ j.val) k))
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ (N : ℝ) * B := by
  let C : Fin N → κ → ℝ := fun j k =>
    |μ k| * ((4 * (Real.sqrt (a j) / (Real.sqrt (w k) + τ)) ^ p) / Real.sqrt (a i))
  by_cases hzero : M = 0
  · let W := ∑ j, ∑ k, C j k
    have hc0 (j : Fin N) (k : κ) : 0 ≤ C j k := by dsimp [C]; positivity
    have hW : 0 ≤ W := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hc0 j k
    have hc (j : Fin N) (k : κ) : C j k ≤ W := by
      exact (Finset.single_le_sum (fun l _ => hc0 j l) (Finset.mem_univ k)).trans
        (Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => hc0 l k) (Finset.mem_univ j))
    have hh := frozen_window_bias P next noise hn he w μ a i hw ha hτ hai hp hp2 hW hM
      hint hmean hm hmass hc s
    calc
      _ ≤ _ := hh
      _ ≤ (N : ℝ) * B := by rw [hzero, mul_zero, mul_zero]; positivity
  · have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    have hc (j : Fin N) (k : κ) : C j k ≤ B / M := (le_div_iff₀ hMp).2 (hcoef j k)
    have hh := frozen_window_bias P next noise hn he w μ a i hw ha hτ hai hp hp2
      (div_nonneg hB hM) hM hint hmean hm hmass hc s
    have heq : B / M * M = B := by field_simp
    simpa only [heq] using hh

set_option maxHeartbeats 400000 in
lemma two_observation_stream_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} {Y : Ω → Ω → ℝ} {D : (ℕ → Ω) → ℝ}
    (hX : Measurable X) (hY : Measurable (Function.uncurry Y)) (hD : Measurable D)
    {μ w a₀ a₁ τ r0 p M : ℝ} (hw : 0 ≤ w) (ha₀ : 0 ≤ a₀) (ha₁ : a₀ ≤ a₁)
    (hτ : 0 < τ) (hr0 : 0 < r0) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hscale : M * r0 ^ p ≤ (Real.sqrt w + τ) ^ 2 * r0 ^ 2)
    (hrr0 : Real.sqrt a₀ ≤ (Real.sqrt w + τ) * r0)
    (hDb : ∀ ξ, Real.sqrt (w + a₀ * (μ + X (ξ 0)) ^ 2 + a₁ * (μ + Y (ξ 0) (ξ 1)) ^ 2) + τ ≤ D ξ)
    (hXi : Integrable (fun ω => |X ω| ^ p) P)
    (hYi : ∀ ω, Integrable (fun z => |Y ω z| ^ p) P)
    (hYm : ∀ ω, (∫ z, |Y ω z| ^ p ∂P) ≤ M) :
    (∫ ξ, μ ^ 2 / (D ξ) ^ 2 ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      3 * μ ^ 2 / (τ * (Real.sqrt w + τ + Real.sqrt a₀ * |μ|)) +
        16 * (∫ ω, |X ω| ^ p ∂P) * r0 ^ p := by
  let D₂ := fun ω z => Real.sqrt (w + a₀ * (μ + X ω) ^ 2 + a₁ * (μ + Y ω z) ^ 2) + τ
  have ha1 : 0 ≤ a₁ := ha₀.trans ha₁
  have hmD : Measurable (Function.uncurry D₂) := by
    exact ((measurable_const.add (measurable_const.mul
      ((measurable_const.add (hX.comp measurable_fst)).pow_const 2))).add
      (measurable_const.mul ((measurable_const.add hY).pow_const 2))).sqrt.add_const τ
  have hA : ∀ ω z, Real.sqrt w + τ ≤ D₂ ω z := by
    intro ω z
    apply add_le_add _ le_rfl
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg ha₀ (sq_nonneg (μ + X ω)), mul_nonneg ha1 (sq_nonneg (μ + Y ω z))]
  have h0 : ∀ ω z, Real.sqrt a₀ * |μ + X ω| ≤ D₂ ω z := by
    intro ω z
    have hs : Real.sqrt a₀ * |μ + X ω| = Real.sqrt (a₀ * (μ + X ω) ^ 2) := by
      rw [Real.sqrt_mul ha₀, Real.sqrt_sq_eq_abs]
    rw [hs]
    apply le_trans (Real.sqrt_le_sqrt (show a₀ * (μ + X ω) ^ 2 ≤ w + a₀ * (μ + X ω) ^ 2 + a₁ * (μ + Y ω z) ^ 2 by
      nlinarith [mul_nonneg ha1 (sq_nonneg (μ + Y ω z))]))
    exact le_add_of_nonneg_right hτ.le
  have h1 : ∀ ω z, Real.sqrt a₀ * |μ + Y ω z| ≤ D₂ ω z := by
    intro ω z
    have hs : Real.sqrt a₀ * |μ + Y ω z| = Real.sqrt (a₀ * (μ + Y ω z) ^ 2) := by
      rw [Real.sqrt_mul ha₀, Real.sqrt_sq_eq_abs]
    rw [hs]
    apply le_trans (Real.sqrt_le_sqrt (show a₀ * (μ + Y ω z) ^ 2 ≤ w + a₀ * (μ + X ω) ^ 2 + a₁ * (μ + Y ω z) ^ 2 by
      nlinarith [mul_nonneg ha₀ (sq_nonneg (μ + X ω)), mul_le_mul_of_nonneg_right ha₁ (sq_nonneg (μ + Y ω z))]))
    exact le_add_of_nonneg_right hτ.le
  have hh := AdamHeavyTailedCancellation.two_observation_integral_uniform (P := P) (Q := P) hX hY hmD hτ
    (le_add_of_nonneg_left (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _) hr0 hp hp2 hM
    hscale hrr0 hA h0 h1 hXi hYi hYm
  have hi₂ := AdamHeavyTailedCancellation.integrable_ratio_square (P := P.prod P) (μ := μ) hmD hτ
    (fun z => (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans (hA z.1 z.2))
  have hfirst := first_two_integral P (fun z : Ω × Ω => μ ^ 2 / (D₂ z.1 z.2) ^ 2) hi₂
  have hhstream := hfirst.trans_le hh
  have hpair : Measurable (fun ξ : ℕ → Ω => (ξ 0, ξ 1)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hm₂ : Measurable (fun ξ : ℕ → Ω => D₂ (ξ 0) (ξ 1)) := hmD.comp hpair
  have hi₂' := AdamHeavyTailedCancellation.integrable_ratio_square (P := Measure.infinitePi (fun _ : ℕ => P))
    (μ := μ) hm₂ hτ (fun ξ => ((le_add_of_nonneg_left (Real.sqrt_nonneg w) : τ ≤ Real.sqrt w + τ).trans (hA (ξ 0) (ξ 1))))
  have hi := AdamHeavyTailedCancellation.integrable_ratio_square (P := Measure.infinitePi (fun _ : ℕ => P))
    (μ := μ) hD hτ (fun ξ => ((le_add_of_nonneg_left (Real.sqrt_nonneg w) : τ ≤ Real.sqrt w + τ).trans (hA (ξ 0) (ξ 1))).trans (hDb ξ))
  apply (integral_mono hi hi₂' (fun ξ => ?_)).trans hhstream
  have hτD : τ ≤ D₂ (ξ 0) (ξ 1) :=
    (le_add_of_nonneg_left (Real.sqrt_nonneg w) : τ ≤ Real.sqrt w + τ).trans (hA (ξ 0) (ξ 1))
  exact div_le_div_of_nonneg_left (sq_nonneg μ) (sq_pos_of_pos (hτ.trans_le hτD))
    (pow_le_pow_left₀ (hτ.le.trans hτD) (hDb ξ) 2)


lemma stateAt_sample_integrable_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {next : S → Ω → S}
    (hn : Measurable (Function.uncurry next)) {F : S → Ω → ℝ}
    (hF : Measurable (Function.uncurry F)) (hF0 : ∀ s ω, 0 ≤ F s ω)
    (hint : ∀ s, Integrable (F s) P) {B : ℝ} (hbound : ∀ s, (∫ ω, F s ω ∂P) ≤ B)
    (s : S) (ω0 : Ω) (n : ℕ) :
    Integrable (fun ξ => F (stateAt next s ξ n) (ξ n)) (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, F (stateAt next s ξ n) (ξ n) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ B := by
  let H := fun z : (Fin n → Ω) × (ℕ → Ω) => F (prefixState next s ω0 n z.1) (z.2 0)
  have hmH : Measurable H := hF.comp
    (((measurable_prefixState hn s ω0 n).comp measurable_fst).prodMk
      ((measurable_pi_apply 0).comp measurable_snd))
  have heval := measurePreserving_eval_infinitePi (fun _ : ℕ => P) 0
  have hi (b : Fin n → Ω) : Integrable (fun ξ => H (b, ξ)) (Measure.infinitePi (fun _ : ℕ => P)) :=
    heval.integrable_comp_of_integrable (hint (prefixState next s ω0 n b))
  have he (b : Fin n → Ω) : (∫ ξ, H (b, ξ) ∂Measure.infinitePi (fun _ : ℕ => P)) =
      ∫ ω, F (prefixState next s ω0 n b) ω ∂P := by
    have hmap : AEStronglyMeasurable (F (prefixState next s ω0 n b))
        ((Measure.infinitePi (fun _ : ℕ => P)).map (Function.eval 0)) := by
      rw [heval.map_eq]
      exact (hint _).aestronglyMeasurable
    have hh := integral_map heval.measurable.aemeasurable hmap
    rw [heval.map_eq] at hh
    exact hh.symm
  have hnH (z : (Fin n → Ω) × (ℕ → Ω)) : ‖H z‖ = H z := Real.norm_of_nonneg (hF0 _ _)
  have houter : Integrable (fun b => ∫ ξ, ‖H (b, ξ)‖ ∂Measure.infinitePi (fun _ : ℕ => P))
      (Measure.pi fun _ : Fin n => P) := by
    apply Integrable.of_bound (hmH.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) B
    exact Filter.Eventually.of_forall fun b => by
      simp_rw [hnH]
      rw [Real.norm_of_nonneg (integral_nonneg fun ξ => hF0 _ _), he]
      exact hbound _
  have hprod : Integrable H ((Measure.pi fun _ : Fin n => P).prod (Measure.infinitePi fun _ : ℕ => P)) :=
    (integrable_prod_iff hmH.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hi, houter⟩
  have hfunc : (fun ξ => F (stateAt next s ξ n) (ξ n)) = H ∘ splitStream n := by
    funext ξ
    dsimp [H, splitStream]
    rw [prefixState_stream]
  refine ⟨?_, ?_⟩
  · rw [hfunc]
    exact (splitStream_preserving P n).integrable_comp_of_integrable hprod
  · rw [hfunc]
    change (∫ ξ, H (splitStream n ξ) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ B
    rw [(splitStream_preserving P n).integral_comp' H, integral_prod _ hprod]
    calc
      _ ≤ ∫ _, B ∂Measure.pi (fun _ : Fin n => P) :=
        integral_mono hprod.integral_prod_left (integrable_const _) (fun b => (he b).trans_le (hbound _))
      _ = B := by simp


lemma stateAt_tail_integral_le {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (next : S → Ω → S) (s : S) (ω0 : Ω)
    (n : ℕ) (F : S → (ℕ → Ω) → ℝ) (B : S → ℝ)
    (hiF : Integrable (fun ξ => F (stateAt next s ξ n) (fun k => ξ (n + k)))
      (Measure.infinitePi fun _ : ℕ => P))
    (hiB : Integrable (fun ξ => B (stateAt next s ξ n)) (Measure.infinitePi fun _ : ℕ => P))
    (hbound : ∀ b : Fin n → Ω,
      (∫ ξ, F (prefixState next s ω0 n b) ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
        B (prefixState next s ω0 n b)) :
    (∫ ξ, F (stateAt next s ξ n) (fun k => ξ (n + k)) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      ∫ ξ, B (stateAt next s ξ n) ∂Measure.infinitePi (fun _ : ℕ => P) := by
  let H := fun z : (Fin n → Ω) × (ℕ → Ω) => F (prefixState next s ω0 n z.1) z.2
  let J := fun z : (Fin n → Ω) × (ℕ → Ω) => B (prefixState next s ω0 n z.1)
  have heF : (fun ξ => F (stateAt next s ξ n) (fun k => ξ (n + k))) = H ∘ splitStream n := by
    funext ξ
    dsimp [H, splitStream]
    rw [prefixState_stream]
  have heB : (fun ξ => B (stateAt next s ξ n)) = J ∘ splitStream n := by
    funext ξ
    dsimp [J, splitStream]
    rw [prefixState_stream]
  rw [heF] at hiF ⊢
  rw [heB] at hiB ⊢
  have hH := ((splitStream_preserving P n).integrable_comp_emb (splitStream n).measurableEmbedding).mp hiF
  have hJ := ((splitStream_preserving P n).integrable_comp_emb (splitStream n).measurableEmbedding).mp hiB
  change (∫ ξ, H (splitStream n ξ) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
    ∫ ξ, J (splitStream n ξ) ∂Measure.infinitePi (fun _ : ℕ => P)
  rw [(splitStream_preserving P n).integral_comp' H, (splitStream_preserving P n).integral_comp' J,
    integral_prod _ hH, integral_prod _ hJ]
  apply integral_mono hH.integral_prod_left hJ.integral_prod_left
  intro b
  simpa [H, J] using hbound b

lemma stateAt_sample_integral_le {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (next : S → Ω → S) (s : S) (ω0 : Ω)
    (n : ℕ) (F : S → Ω → ℝ) (B : S → ℝ)
    (hiF : Integrable (fun ξ => F (stateAt next s ξ n) (ξ n))
      (Measure.infinitePi fun _ : ℕ => P))
    (hiB : Integrable (fun ξ => B (stateAt next s ξ n)) (Measure.infinitePi fun _ : ℕ => P))
    (hint : ∀ b : Fin n → Ω, Integrable (F (prefixState next s ω0 n b)) P)
    (hbound : ∀ b : Fin n → Ω,
      (∫ ω, F (prefixState next s ω0 n b) ω ∂P) ≤ B (prefixState next s ω0 n b)) :
    (∫ ξ, F (stateAt next s ξ n) (ξ n) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      ∫ ξ, B (stateAt next s ξ n) ∂Measure.infinitePi (fun _ : ℕ => P) := by
  have heval := measurePreserving_eval_infinitePi (fun _ : ℕ => P) 0
  have hh := stateAt_tail_integral_le P next s ω0 n (fun s ξ => F s (ξ 0)) B
    (by simpa only [Nat.add_zero] using hiF) hiB (fun b => by
      have hm : AEStronglyMeasurable (F (prefixState next s ω0 n b))
          ((Measure.infinitePi (fun _ : ℕ => P)).map (Function.eval 0)) := by
        rw [heval.map_eq]
        exact (hint b).aestronglyMeasurable
      have he := integral_map heval.measurable.aemeasurable hm
      rw [heval.map_eq] at he
      exact he.symm.trans_le (hbound b))
  simpa only [Nat.add_zero] using hh

end LongTails.Proofs.AdamHeavyTailedProcess
