import LongTails.Proofs.CohypomonotoneNewtonInverse
import LongTails.Proofs.ComponentEnvelopeExecution

namespace LongTails.Proofs.CohypomonotoneNewtonExecution

open LongTails.Algorithms.CohypomonotoneNewton
open LongTails.Proofs.CohypomonotoneNewtonInverse
open OracleTemplate.ComponentEnvelope (Program)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inverseTail_eval (F : E → E) (J : E → E →L[ℝ] E) (M γ : ℝ) (target : E)
    (n : ℕ) (x : E) :
    Program.eval (fun x => (F x, J x)) (inverseTail M γ target n (x, (F x, J x))) =
      let y := (fun x => inverseUpdate M γ target x (F x, J x))^[n] x
      (y, (F y, J y)) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [inverseTail, Program.eval, ih, Function.iterate_succ_apply]

lemma inverseTail_cost (g : E → E × (E →L[ℝ] E)) (M γ : ℝ) (target : E)
    (n : ℕ) (state : E × (E × (E →L[ℝ] E))) :
    Program.cost g (inverseTail M γ target n state) = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp only [inverseTail, Program.cost, ih]

lemma inversePlan_cost (g : E → E × (E →L[ℝ] E)) (M γ ε : ℝ) (target start : E) :
    Program.cost g (inversePlan M γ ε target start) =
      inverseLength M ‖start + γ • (g start).1 - target‖ ε + 1 := by
  simp only [inversePlan, Program.cost, inverseTail_cost]

lemma residual_iterate_bound {X : Type*} (step : X → X) (r : X → ℝ)
    {c B : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hB : 0 ≤ B)
    (hstep : ∀ x, r x ≤ B → r (step x) ≤ c * r x) (x : X) (hx : r x ≤ B) (n : ℕ) :
    r (step^[n] x) ≤ c ^ n * B := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hb : r (step^[n] x) ≤ B :=
        ih.trans (by simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hc0 hc1) hB)
      calc
        r (step (step^[n] x)) ≤ c * r (step^[n] x) := hstep _ hb
        _ ≤ c * (c ^ n * B) := mul_le_mul_of_nonneg_left ih hc0
        _ = c ^ (n + 1) * B := by ring

lemma inversePlan_correct [FiniteDimensional ℝ E] {F : E → E} {J : E → E →L[ℝ] E}
    {M γ ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hT : ∀ x, HasFDerivAt (fun x => x + γ • F x)
      (ContinuousLinearMap.id ℝ E + γ • J x) x)
    (hD : ∀ x y, ‖(ContinuousLinearMap.id ℝ E + γ • J x) -
      (ContinuousLinearMap.id ℝ E + γ • J y)‖ ≤ M * ‖x - y‖)
    (hexp : ∀ x y, ‖x - y‖ ≤ ‖(x + γ • F x) - (y + γ • F y)‖)
    (target start : E) :
    let out := Program.eval (fun x => (F x, J x)) (inversePlan M γ ε target start)
    out.2 = (F out.1, J out.1) ∧ ‖out.1 + γ • F out.1 - target‖ ≤ ε := by
  let B := ‖start + γ • F start - target‖
  let c := 1 - 1 / (2 * max 1 (2 * M * B))
  let step := fun x => inverseUpdate M γ target x (F x, J x)
  have hden : 0 < 2 * max 1 (2 * M * B) := by
    have : 1 ≤ max 1 (2 * M * B) := le_max_left _ _
    positivity
  have hc0 : 0 ≤ c := by
    have hh : 1 / (2 * max 1 (2 * M * B)) ≤ 1 :=
      (div_le_one hden).mpr (by linarith [le_max_left 1 (2 * M * B)])
    dsimp [c]
    linarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have := one_div_pos.mpr hden
    linarith
  have hi := residual_iterate_bound step (fun x => ‖x + γ • F x - target‖)
    hc0 hc1 (norm_nonneg _) (fun x hx => inverseUpdate_residual hM hT hD hexp x target hx)
    start (le_refl B) (inverseLength M B ε)
  have hfin := hi.trans (inverseLength_accuracy (M := M) (norm_nonneg _) hε)
  simp only [inversePlan, Program.eval, inverseTail_eval]
  exact ⟨True.intro, hfin⟩

lemma execute_of_cost_le (p : LongTails.Setups.CohypomonotoneNewton.Public)
    (reply : p.E → p.E × (p.E →L[ℝ] p.E))
    (oracle : OracleTemplate.Oracle p.E (p.E × (p.E →L[ℝ] p.E)))
    (hreply : ∀ history query seed, oracle.answer history (0, query) seed = reply query)
    (K : ℕ) (oracleSeed : (k : ℕ) → oracle.Seed k)
    (hcost : Program.cost reply (plan p) ≤ K) :
    output p oracle K oracleSeed = Program.eval reply (plan p) := by
  unfold output
  erw [OracleTemplate.execute_eq_of_answer_eq oracle reply hreply,
    OracleTemplate.execute_iterate reply (algorithm p) K ()]
  change Program.output p.x0
    ((fun state : Program p.E (p.E × (p.E →L[ℝ] p.E)) p.E =>
      state.update (reply (state.query p.x0)))^[K] (plan p)) = _
  rw [Program.iterate_of_cost_le reply p.x0 K _ hcost]
  rfl

end LongTails.Proofs.CohypomonotoneNewtonExecution
