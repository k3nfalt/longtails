import LongTails.Algorithms.QuasarCubicNewton
import LongTails.Proofs.ComponentEnvelopeExecution

noncomputable section

namespace LongTails.Proofs.QuasarCubicExecution

open LongTails.Algorithms.QuasarCubicNewton
open LongTails.Proofs.QuasarCubicStep
open LongTails.Proofs.QuasarCubicPotential
open OracleTemplate.ComponentEnvelope (Program)
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma bisect_cost (ρ : E → Reply E) (M : ℝ) (x d : E) (fx : ℝ) (j : ℕ) (lo hi : ℝ)
    (dlo : Reply E) : Program.cost ρ (bisect M x d fx j lo hi dlo) = j := by
  induction j generalizing lo hi dlo with
  | zero => rfl
  | succ j ih =>
      simp only [bisect, Program.cost]
      split_ifs <;> simp [ih]

lemma coupling_cost (ρ : E → Reply E) (M : ℝ) (n : ℕ) (x v : E) (dx dv : Reply E) :
    Program.cost ρ (coupling M n x v dx dv) ≤ n := by
  unfold coupling
  split_ifs
  · simp [Program.cost]
  · rw [bisect_cost]

lemma outerStep_cost (ρ : E → Reply E) (M N γ : ℝ) (n : ℕ) (x0 : E) (st : Outer E) :
    Program.cost ρ (outerStep M N γ n x0 st) ≤ n + 2 := by
  simp only [outerStep, Program.cost, Program.cost_bind]
  have := coupling_cost ρ M n st.x (center N x0 st.s) st.data (ρ (center N x0 st.s))
  omega

lemma outerLoop_cost (ρ : E → Reply E) (M N γ : ℝ) (n : ℕ) (x0 : E) (j : ℕ) (st : Outer E) :
    Program.cost ρ (outerLoop M N γ n x0 j st) ≤ j * (n + 2) := by
  induction j generalizing st with
  | zero => simp [outerLoop, Program.cost]
  | succ j ih =>
      simp only [outerLoop, Program.cost_bind]
      have h1 := outerStep_cost ρ M N γ n x0 st
      have h2 := ih (Program.eval ρ (outerStep M N γ n x0 st))
      nlinarith

lemma outerLoop_eval (ρ : E → Reply E) (M N γ : ℝ) (n : ℕ) (x0 : E) (j : ℕ) (st : Outer E) :
    Program.eval ρ (outerLoop M N γ n x0 j st) =
      ((fun s => Program.eval ρ (outerStep M N γ n x0 s))^[j] st).x := by
  induction j generalizing st with
  | zero => rfl
  | succ j ih =>
      simp only [outerLoop, Program.eval_bind, ih, Function.iterate_succ_apply]

lemma plan_cost (p : LongTails.Setups.QuasarConvexHessianLipschitz.Params)
    (ρ : p.E → Reply p.E) :
    Program.cost ρ (plan p) ≤ iterations p * (depth p + 2) + 1 := by
  simp only [plan, Program.cost]
  have := outerLoop_cost ρ (reg p) (est p) p.γ (depth p) p.x0 (iterations p)
    ⟨p.x0, ρ p.x0, 0, 0, 0⟩
  omega

lemma plan_eval (p : LongTails.Setups.QuasarConvexHessianLipschitz.Params)
    (ρ : p.E → Reply p.E) :
    Program.eval ρ (plan p) =
      ((fun s => Program.eval ρ (outerStep (reg p) (est p) p.γ (depth p) p.x0 s))^[iterations p]
        ⟨p.x0, ρ p.x0, 0, 0, 0⟩).x := by
  simp only [plan, Program.eval]
  exact outerLoop_eval ρ _ _ _ _ _ _ _

lemma execute_of_cost_le (p : LongTails.Setups.QuasarConvexHessianLipschitz.Params)
    (ρ : p.E → Reply p.E)
    (oracle : OracleTemplate.Oracle p.E (Reply p.E))
    (hreply : ∀ history query seed, oracle.answer history (0, query) seed = ρ query)
    (K : ℕ) (oracleSeed : (k : ℕ) → oracle.Seed k)
    (hcost : Program.cost ρ (plan p) ≤ K) :
    OracleTemplate.execute oracle (algorithm p) (fun _ => K) () oracleSeed =
      Program.eval ρ (plan p) := by
  erw [OracleTemplate.execute_eq_of_answer_eq oracle ρ hreply,
    OracleTemplate.execute_iterate ρ (algorithm p) K ()]
  change Program.output p.x0
    ((fun state : Program p.E (Reply p.E) p.E =>
      state.update (ρ (state.query p.x0)))^[K] (plan p)) = _
  rw [Program.iterate_of_cost_le ρ p.x0 K _ hcost]
  rfl

section Spec

variable [FiniteDimensional ℝ E] {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E}

omit [FiniteDimensional ℝ E] in
lemma bisect_spec (M : ℝ) (x d : E) (fx : ℝ) (j : ℕ) (lo hi : ℝ)
    (hlo : envelope M (f (x + lo • d), g (x + lo • d), A (x + lo • d)) ≤ fx)
    (hhi : fx < envelope M (f (x + hi • d), g (x + hi • d), A (x + hi • d)))
    (h0 : 0 ≤ lo) (hlh : lo < hi) (h1 : hi ≤ 1) :
    let out := Program.eval (fun q => (f q, g q, A q))
      (bisect M x d fx j lo hi (f (x + lo • d), g (x + lo • d), A (x + lo • d)))
    out.2 = (f (x + out.1 • d), g (x + out.1 • d), A (x + out.1 • d)) ∧
      envelope M out.2 ≤ fx ∧
      fx < envelope M (f (x + (out.1 + (hi - lo) / 2 ^ j) • d),
        g (x + (out.1 + (hi - lo) / 2 ^ j) • d), A (x + (out.1 + (hi - lo) / 2 ^ j) • d)) ∧
      0 ≤ out.1 ∧ out.1 + (hi - lo) / 2 ^ j ≤ 1 ∧ out.1 < 1 := by
  induction j generalizing lo hi with
  | zero =>
      simp only [bisect, Program.eval, pow_zero, div_one, add_sub_cancel]
      exact ⟨by trivial, hlo, hhi, h0, h1, lt_of_lt_of_le hlh h1⟩
  | succ j ih =>
      simp only [bisect, Program.eval]
      set m := (lo + hi) / 2 with hmdef
      split_ifs with hm
      · have := ih m hi hm hhi (by rw [hmdef]; linarith) (by rw [hmdef]; linarith) h1
        have he : (hi - m) / 2 ^ j = (hi - lo) / 2 ^ (j + 1) := by
          simp only [m, pow_succ]; field_simp; ring
        rw [he] at this
        exact this
      · push Not at hm
        have := ih lo m hlo hm h0 (by rw [hmdef]; linarith) (by rw [hmdef]; linarith)
        have he : (m - lo) / 2 ^ j = (hi - lo) / 2 ^ (j + 1) := by
          simp only [m, pow_succ]; field_simp; ring
        rw [he] at this
        exact this

lemma coupling_spec (M : ℝ) (hM : 0 < M) (n : ℕ) (x v : E)
    (hsym : ∀ z, ∀ x y : E, ⟪x, A z y⟫ = ⟪A z x, y⟫) :
    let out := Program.eval (fun q => (f q, g q, A q))
      (coupling M n x v (f x, g x, A x) (f v, g v, A v))
    out.2 = (f (x + out.1 • (v - x)), g (x + out.1 • (v - x)), A (x + out.1 • (v - x))) ∧
      envelope M out.2 ≤ f x ∧ 0 ≤ out.1 ∧ out.1 ≤ 1 ∧
      (out.1 = 1 ∨ (out.1 + 1 / 2 ^ n ≤ 1 ∧ f x < envelope M
        (f (x + (out.1 + 1 / 2 ^ n) • (v - x)), g (x + (out.1 + 1 / 2 ^ n) • (v - x)),
          A (x + (out.1 + 1 / 2 ^ n) • (v - x))))) := by
  simp only [coupling]
  split_ifs with hv
  · simp only [Program.eval]
    have hxv : x + (1 : ℝ) • (v - x) = v := by rw [one_smul]; abel
    rw [hxv]
    exact ⟨by trivial, hv, zero_le_one, le_rfl, Or.inl (by trivial)⟩
  · push Not at hv
    have h0 : x + (0 : ℝ) • (v - x) = x := by simp
    have h1 : x + (1 : ℝ) • (v - x) = v := by rw [one_smul]; abel
    have hlo : envelope M (f (x + (0 : ℝ) • (v - x)), g (x + (0 : ℝ) • (v - x)),
        A (x + (0 : ℝ) • (v - x))) ≤ f x := by
      rw [h0]; exact envelope_le hM x (hsym x)
    have hhi : f x < envelope M (f (x + (1 : ℝ) • (v - x)), g (x + (1 : ℝ) • (v - x)),
        A (x + (1 : ℝ) • (v - x))) := by rw [h1]; exact hv
    have hs := bisect_spec (f := f) (g := g) (A := A) M x (v - x) (f x) n 0 1 hlo hhi
      le_rfl zero_lt_one le_rfl
    rw [h0] at hs
    simp only [sub_zero] at hs
    obtain ⟨ha, hb, hc, hd, he, hf⟩ := hs
    exact ⟨ha, hb, hd, hf.le, Or.inr ⟨he, hc⟩⟩

end Spec

end LongTails.Proofs.QuasarCubicExecution
