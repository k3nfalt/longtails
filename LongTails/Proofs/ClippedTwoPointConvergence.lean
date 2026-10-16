import LongTails.Proofs.PairedOracleExecution

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClippedTwoPointConvergence

open LongTails.Algorithms.ClippedTwoPoint
open LongTails.Proofs.ClippedTwoPointExecution

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma accelerated_path_error_bound {Q : Set E} (hQ : Convex ℝ Q)
    {project : E → E} (hp : ∀ x, project x ∈ Q)
    (hnearest : ∀ x, ‖x - project x‖ = ⨅ w : Q, ‖x - w‖)
    {f : E → ℝ} {grad : E → E} {L h D R β C : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (hcoef : 4 * L ≤ h) (hβ : 0 ≤ β)
    (hdiam : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hconvex : ∀ x ∈ Q, ∀ y ∈ Q, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hmodel : ∀ x ∈ Q, ∀ y ∈ Q, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (state : ℕ → E × E) (est noise bias : ℕ → E)
    (hx : (state 0).1 ∈ Q) (hz : (state 0).2 ∈ Q) {v : E} (hv : v ∈ Q)
    (hstep : ∀ t, state (t + 1) = acceleratedUpdate project h t (state t) (est t)) (N : ℕ)
    (he : ∀ t < N, est t - grad (acceleratedMix t (state t).1 (state t).2) = noise t + bias t)
    (hb : ∀ t < N, ‖bias t‖ ≤ β)
    (hn : ‖∑ i : Fin N, (i + 1 : ℝ) •
      (PiLp.single 2 i (noise i) : PiLp 2 (fun _ : Fin N => E))‖ ≤ R)
    (hc : (∑ t ∈ Finset.range N, (t + 1 : ℝ) * ⟪noise t, v - (state t).2⟫) ≤ C) :
    ((N : ℝ) * (N + 1) / 2) * (f (state N).1 - f v) ≤
      h * D ^ 2 / 2 + (R + ((N : ℝ) * (N + 1) / 2) * β) ^ 2 / h +
        C + ((N : ℝ) * (N + 1) / 2) * β * D := by
  have hmem (t : ℕ) : (state t).1 ∈ Q ∧ (state t).2 ∈ Q := by
    induction t with
    | zero => exact ⟨hx, hz⟩
    | succ t ih => rw [hstep]; exact accelerated_update_mem hQ hp ih.1 h t (est t)
  have hsum : (∑ i : Fin N, (i + 1 : ℝ)) = (N : ℝ) * (N + 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (t + 1 : ℝ))]
    exact PairedOracleExecution.accelerated_weights_sum N
  have henergy := WeightedOracleBlocks.biased_block_energy
    (fun i : Fin N => (i + 1 : ℝ)) (fun i => noise i) (fun i => bias i)
    (fun i => by positivity) (fun i => hb i i.isLt) hn
  rw [hsum] at henergy
  have hcomp := WeightedOracleBlocks.biased_comparator
    (fun i : Fin N => (i + 1 : ℝ)) (fun i => noise i) (fun i => bias i)
    (fun i => v - (state i).2) (fun i => by positivity) hβ
    (fun i => hb i i.isLt) (fun i => hdiam v hv _ (hmem i).2)
    (C := C) (by
      rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (t + 1 : ℝ) * ⟪noise t, v - (state t).2⟫)]
      exact hc)
  rw [hsum] at hcomp
  have hpot := accelerated_path_potential hQ hp hnearest hL hh hcoef hconvex hmodel
    state est hx hz hv hstep N
  dsimp only at hpot
  have herr : ∀ t ∈ Finset.range N,
      est t - grad (acceleratedMix t (state t).1 (state t).2) = noise t + bias t :=
    fun t ht => he t (Finset.mem_range.mp ht)
  have henergy_eq : (∑ t ∈ Finset.range N, (t + 1 : ℝ) ^ 2 *
      ‖est t - grad (acceleratedMix t (state t).1 (state t).2)‖ ^ 2) =
      ∑ t ∈ Finset.range N, (t + 1 : ℝ) ^ 2 * ‖noise t + bias t‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [herr t ht]
  rw [henergy_eq] at hpot
  have hsign : (∑ t ∈ Finset.range N, (t + 1 : ℝ) *
      ⟪est t - grad (acceleratedMix t (state t).1 (state t).2), (state t).2 - v⟫) =
      -(∑ t ∈ Finset.range N, (t + 1 : ℝ) * ⟪noise t + bias t, v - (state t).2⟫) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [herr t ht, show (state t).2 - v = -(v - (state t).2) by abel, inner_neg_right]
    ring
  rw [hsign, sub_neg_eq_add] at hpot
  have he' : (∑ t ∈ Finset.range N, (t + 1 : ℝ) ^ 2 * ‖noise t + bias t‖ ^ 2) ≤
      (R + ((N : ℝ) * (N + 1) / 2) * β) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (t + 1 : ℝ) ^ 2 * ‖noise t + bias t‖ ^ 2)] at henergy
    exact henergy
  have hc' : (∑ t ∈ Finset.range N, (t + 1 : ℝ) * ⟪noise t + bias t, v - (state t).2⟫) ≤
      C + ((N : ℝ) * (N + 1) / 2) * β * D := by
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (t + 1 : ℝ) * ⟪noise t + bias t, v - (state t).2⟫)] at hcomp
    exact hcomp
  have hi := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hdiam _ hz v hv) 2) (show 0 ≤ h / 2 by positivity)
  have hd := div_le_div_of_nonneg_right he' hh.le
  linarith only [hpot, hi, hd, hc']

lemma dual_branch_error_bound {Q : Set E} (hQ : Convex ℝ Q)
    {project : E → E} (hp : ∀ x, project x ∈ Q)
    (hnearest : ∀ x, ‖x - project x‖ = ⨅ w : Q, ‖x - w‖)
    {f : E → ℝ} {grad : E → E} {L h D R β C : ℝ} (hL : 0 ≤ L) (hh : 0 < h) (hcoef : 4 * L ≤ h) (hβ : 0 ≤ β)
    (hdiam : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hconvex : ∀ x ∈ Q, ∀ y ∈ Q, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hmodel : ∀ x ∈ Q, ∀ y ∈ Q, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    {initial : E × E} (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q) {v : E} (hv : v ∈ Q)
    (d : ℕ) (τ₁ τ₂ γ₁ γ₂ : ℝ) (B : ℕ → ℕ) (u₁ u₂ : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m N : ℕ) (branch : Bool) (noise bias : ℕ → E) :
    let states := dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B u₁ u₂ g ξ m
    let state := fun t => if branch then (states t).1 else (states t).2
    let est := fun t =>
      let center := acceleratedMix t (state t).1 (state t).2
      let γ := if branch then γ₁ else γ₂
      let τ := if branch then τ₁ else τ₂
      let u := if branch then u₁ else u₂
      let start := m + 2 * (∑ j ∈ Finset.range t, B j) + (if branch then 0 else B t)
      (B t : ℝ)⁻¹ • (∑ i : Fin (B t), estimate d τ γ (u t i)
        (g (center + γ • u t i) (ξ (start + i)))
        (g (center - γ • u t i) (ξ (start + i))))
    (∀ t < N, est t - grad (acceleratedMix t (state t).1 (state t).2) = noise t + bias t) →
    (∀ t < N, ‖bias t‖ ≤ β) →
    (‖∑ i : Fin N, (i + 1 : ℝ) •
      (PiLp.single 2 i (noise i) : PiLp 2 (fun _ : Fin N => E))‖ ≤ R) →
    ((∑ t ∈ Finset.range N, (t + 1 : ℝ) * ⟪noise t, v - (state t).2⟫) ≤ C) →
    ((N : ℝ) * (N + 1) / 2) * (f (state N).1 - f v) ≤
      h * D ^ 2 / 2 + (R + ((N : ℝ) * (N + 1) / 2) * β) ^ 2 / h +
        C + ((N : ℝ) * (N + 1) / 2) * β * D := by
  cases branch <;> dsimp only
  all_goals
    intro he hb hn hc
    apply accelerated_path_error_bound hQ hp hnearest hL hh hcoef hβ hdiam hconvex hmodel
      _ _ noise bias hx hz hv _ N he hb hn hc
    intro t
    rfl

lemma dual_branch_centered_error_bound {Rseed : Type*} [MeasurableSpace Rseed] (law : Measure Rseed) {Q : Set E} (hQ : Convex ℝ Q)
    {project : E → E} (hp : ∀ x, project x ∈ Q)
    (hnearest : ∀ x, ‖x - project x‖ = ⨅ w : Q, ‖x - w‖)
    {f : E → ℝ} {grad : E → E} {L h D R β C : ℝ} (hL : 0 ≤ L) (hh : 0 < h) (hcoef : 4 * L ≤ h) (hβ : 0 ≤ β)
    (hdiam : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hconvex : ∀ x ∈ Q, ∀ y ∈ Q, f x + ⟪grad x, y - x⟫ ≤ f y)
    (hmodel : ∀ x ∈ Q, ∀ y ∈ Q, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    {initial : E × E} (hx : initial.1 ∈ Q) (hz : initial.2 ∈ Q) {v : E} (hv : v ∈ Q)
    (d : ℕ) (τ γ₁ γ₂ : ℝ) (B : ℕ → ℕ) (direction : Rseed → E)
    (sample : Rseed → Ω) (g : E → Ω → ℝ) (records : ℕ → Rseed) (N : ℕ) (branch : Bool)
    (hB : ∀ t < N, 0 < B t)
    (hmean : ∀ x ∈ Q,
      ‖(∫ z, estimate d τ (if branch then γ₁ else γ₂) (direction z)
        (g (x + (if branch then γ₁ else γ₂) • direction z) (sample z))
        (g (x - (if branch then γ₁ else γ₂) • direction z) (sample z)) ∂law) - grad x‖ ≤ β) :
    let u₁ := fun t (i : Fin (B t)) => direction (records (2 * (∑ k ∈ Finset.range t, B k) + i))
    let u₂ := fun t (i : Fin (B t)) => direction (records (2 * (∑ k ∈ Finset.range t, B k) + B t + i))
    let states := dualSolverState d τ τ γ₁ γ₂ h project initial B u₁ u₂ g (fun i => sample (records i)) 0
    let state := fun t => if branch then (states t).1 else (states t).2
    let center := fun t => acceleratedMix t (state t).1 (state t).2
    let kernel := fun x z => estimate d τ (if branch then γ₁ else γ₂) (direction z)
      (g (x + (if branch then γ₁ else γ₂) • direction z) (sample z))
      (g (x - (if branch then γ₁ else γ₂) • direction z) (sample z))
    let noise := fun t => (B t : ℝ)⁻¹ • (∑ i : Fin (B t),
      (kernel (center t) (records (2 * (∑ k ∈ Finset.range t, B k) + ((if branch then 0 else B t) + i))) -
        ∫ fresh, kernel (center t) fresh ∂law))
    (‖∑ i : Fin N, (i + 1 : ℝ) •
      (PiLp.single 2 i (noise i) : PiLp 2 (fun _ : Fin N => E))‖ ≤ R) →
    ((∑ t ∈ Finset.range N, (t + 1 : ℝ) * ⟪noise t, v - (state t).2⟫) ≤ C) →
    ((N : ℝ) * (N + 1) / 2) * (f (state N).1 - f v) ≤
      h * D ^ 2 / 2 + (R + ((N : ℝ) * (N + 1) / 2) * β) ^ 2 / h +
        C + ((N : ℝ) * (N + 1) / 2) * β * D := by
  classical
  intro u₁ u₂ states state center kernel noise hn hc
  let bias := fun t => (∫ fresh, kernel (center t) fresh ∂law) - grad (center t)
  have hmem (t : ℕ) : (state t).1 ∈ Q ∧ (state t).2 ∈ Q := by
    have hm := dual_solver_state_mem hQ hp hx hz d τ τ γ₁ γ₂ h B u₁ u₂ g (fun i => sample (records i)) 0 t
    cases branch
    · exact hm.2
    · exact hm.1
  have hb (t : ℕ) (ht : t < N) : ‖bias t‖ ≤ β :=
    hmean _ (accelerated_mix_mem hQ (hmem t).1 (hmem t).2 t)
  apply dual_branch_error_bound hQ hp hnearest hL hh hcoef hβ hdiam hconvex hmodel
    hx hz hv d τ τ γ₁ γ₂ B u₁ u₂ g (fun i => sample (records i)) 0 N branch noise bias _ hb hn hc
  intro t ht
  have he := batch_error_decomposition (hB t ht)
    (fun i : Fin (B t) => kernel (center t)
      (records (2 * (∑ k ∈ Finset.range t, B k) + ((if branch then 0 else B t) + i))))
    (∫ fresh, kernel (center t) fresh ∂law) (grad (center t))
  cases branch <;> simpa only [noise, bias, kernel, center, state, states, u₁, u₂,
    Bool.false_eq_true, ite_false, ite_true, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using he

end LongTails.Proofs.ClippedTwoPointConvergence
