import LongTails.Algorithms.HiddenPotential
import LongTails.Proofs.Execution
import LongTails.Proofs.HiddenPotentialConvergence
import LongTails.Proofs.HiddenPotentialBudget

open scoped RealInnerProductSpace

namespace OracleTemplate.HiddenPotential

variable {E : Type*}

def programValue (F : E → E) : Program E → E
  | .done x => x
  | .ask x next => programValue F (next (F x))

def costBound : ℕ → Program E → Prop
  | _, .done _ => True
  | 0, .ask _ _ => False
  | N + 1, .ask _ next => ∀ reply, costBound N (next reply)

lemma costBound_done (N : ℕ) (x : E) : costBound N (.done x) := by
  cases N <;> trivial

lemma costBound_succ {N : ℕ} {p : Program E} (h : costBound N p) :
    costBound (N + 1) p := by
  induction N generalizing p with
  | zero =>
      cases p with
      | done x => trivial
      | ask x next => exact False.elim h
  | succ N ih =>
      cases p with
      | done x => trivial
      | ask x next => exact fun reply => ih (h reply)

lemma costBound_mono {N K : ℕ} {p : Program E} (h : costBound N p) (hNK : N ≤ K) :
    costBound K p := by
  induction K, hNK using Nat.le_induction with
  | base => exact h
  | succ K hK ih => exact costBound_succ ih

lemma program_iteration (F : E → E) (fallback : E) (N : ℕ) (p : Program E)
    (h : costBound N p) :
    (fun q => programUpdate q (F (programQuery fallback q)))^[N] p =
      .done (programValue F p) := by
  induction N generalizing p with
  | zero =>
      cases p with
      | done x => rfl
      | ask x next => exact False.elim h
  | succ N ih =>
      rw [Function.iterate_succ_apply]
      cases p with
      | done x => exact ih (.done x) (costBound_done N x)
      | ask x next => exact ih (next (F x)) (h (F x))

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma innerProgram_cost (β D R : ℝ) (anchor center : E) (next : E → Program E)
    (C : ℕ) (hnext : ∀ out, costBound C (next out)) (T k : ℕ) (state : E × E) :
    costBound (T + C) (innerProgram β D R anchor center next T k state) := by
  induction T generalizing k state with
  | zero => simpa only [Nat.zero_add, innerProgram] using hnext state.1
  | succ T ih =>
      rw [show T + 1 + C = (T + C) + 1 by omega]
      exact fun reply => ih (k + 1) _

lemma stageProgram_cost (β D : ℝ) (T : ℕ) (anchor : E) (next : E → Program E)
    (C : ℕ) (hnext : ∀ out, costBound C (next out)) (H : ℕ) (R : ℝ) (center : E) :
    costBound (H * T + C) (stageProgram β D T anchor next H R center) := by
  induction H generalizing R center with
  | zero => simpa only [Nat.zero_mul, Nat.zero_add, stageProgram] using hnext center
  | succ H ih =>
      rw [show (H + 1) * T + C = T + (H * T + C) by ring]
      exact innerProgram_cost β D R anchor center _ (H * T + C)
        (fun out => ih (R / 2) out) T 0 (center, center)

lemma outerProgram_cost (β D q : ℝ) (T H N : ℕ) (R : ℝ) (anchor : E) :
    costBound (N * (H * T)) (outerProgram β D q T H N R anchor) := by
  induction N generalizing R anchor with
  | zero => simp [outerProgram, costBound]
  | succ N ih =>
      rw [show (N + 1) * (H * T) = H * T + N * (H * T) by ring]
      exact stageProgram_cost β D T anchor _ (N * (H * T))
        (fun out => ih (q * R) out) H R anchor

lemma innerProgram_value (F : E → E) (β D R : ℝ) (anchor center : E)
    (next : E → Program E) (T k : ℕ) (state : E × E) :
    programValue F (innerProgram β D R anchor center next T k state) =
      programValue F (next (innerRun F β D R anchor center T k state).1) := by
  induction T generalizing k state with
  | zero => rfl
  | succ T ih => exact ih (k + 1) _

lemma stageProgram_value (F : E → E) (β D : ℝ) (T : ℕ) (anchor : E)
    (next : E → Program E) (H : ℕ) (R : ℝ) (center : E) :
    programValue F (stageProgram β D T anchor next H R center) =
      programValue F (next (stageRun F β D T anchor H R center)) := by
  induction H generalizing R center with
  | zero => rfl
  | succ H ih =>
      rw [stageProgram, innerProgram_value]
      exact ih (R / 2) _

lemma outerProgram_value (F : E → E) (β D q : ℝ) (T H N : ℕ) (R : ℝ) (anchor : E) :
    programValue F (outerProgram β D q T H N R anchor) =
      outerRun F β D q T H N R anchor := by
  induction N generalizing R anchor with
  | zero => rfl
  | succ N ih =>
      rw [outerProgram, stageProgram_value]
      exact ih (q * R) _

lemma execute_nestedAcceleration (F : E → E) (O : Oracle E E)
    (hO : ∀ k x seed, O.answer k (0, x) seed = F x)
    (β D q R : ℝ) (T H N K : ℕ) (x0 : E) (hK : N * (H * T) ≤ K)
    (ω : (k : ℕ) → O.Seed k) :
    execute O (nestedAcceleration β D q R T H N x0) (fun _ => K) () ω =
      outerRun F β D q T H N R x0 := by
  unfold nestedAcceleration
  rw [execute_eq_of_answer_eq O F hO, execute_iterate]
  change programOutput x0
    ((fun p => programUpdate p (F (programQuery x0 p)))^[K]
      (outerProgram β D q T H N R x0)) = _
  rw [program_iteration F x0 K _ (costBound_mono (outerProgram_cost β D q T H N R x0) hK)]
  exact outerProgram_value F β D q T H N R x0

lemma execute_hidden_accuracy [CompleteSpace E] (F : E → E) (φ : E → ℝ)
    (O : Oracle E E) (hO : ∀ k x seed, O.answer k (0, x) seed = F x)
    {μ L s R ε : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hR : 0 ≤ R) (hε : 0 < ε)
    (hg : ∀ x, HasGradientAt φ (gradient φ x) x)
    (hlip : ∀ x y, ‖gradient φ x - gradient φ y‖ ≤ L * ‖x - y‖)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hresidual : ∀ x y,
      ‖(F x - gradient φ x) - (F y - gradient φ y)‖ ≤ s * ‖x - y‖)
    (x0 xstar : E) (hroot : F xstar = 0) (hdist : ‖x0 - xstar‖ ≤ R)
    (K : ℕ) (ω : (k : ℕ) → O.Seed k) :
    let β := 512 * s
    let m := μ + 511 * s
    let ℓ := L + μ + 512 * s
    let T := ⌈16 * Real.sqrt (ℓ / m)⌉₊
    let H := ⌈Real.log (2 * (μ + β) / μ) / Real.log 2⌉₊
    let N := ⌈2 * (μ + β) / μ * Real.log (2 + R / ε)⌉₊
    N * (H * T) ≤ K →
      ‖execute O (hiddenPotentialOutput μ L s R ε x0) (fun _ => K) () ω - xstar‖ ≤ ε := by
  dsimp only
  intro hK
  unfold hiddenPotentialOutput
  rw [execute_nestedAcceleration F O hO _ _ _ _ _ _ _ K x0 hK ω]
  have hm : 0 < μ + 511 * s := by positivity
  have hℓ : 0 < L + μ + 512 * s := by positivity
  have ht := inner_steps_sufficient hm hℓ
  have hid : μ + 512 * s - s = μ + 511 * s := by ring
  have hc := hidden_outer_convergence F φ hμ hL hs
    (by positivity : 0 ≤ 512 * s) (by positivity : 0 < 2 * (L + μ + 512 * s))
    (by linarith : 2 * (L + 512 * s) ≤ 2 * (L + μ + 512 * s)) hR
    (by rw [hid]; exact hm) (by linarith) hg hlip hstrong hresidual x0 xstar hroot hdist
    _ _ ⌈2 * (μ + 512 * s) / μ * Real.log (2 + R / ε)⌉₊ ht.1
    (by rw [hid]; nlinarith [ht.2]) (stage_steps_sufficient hμ (by positivity))
  exact hc.trans (outer_steps_sufficient hμ (by positivity) hR hε)

end OracleTemplate.HiddenPotential
