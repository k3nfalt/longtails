import LongTails.Proofs.BFGSComposite
import LongTails.Proofs.ExecutionHistory
import LongTails.Proofs.SgdExecution

open Set Finset
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BFGSExecution

open OracleTemplate LongTails.Setups.LinearPredictorBFGS LongTails.Proofs.BFGSRate
open LongTails.Proofs.BFGSComposite LongTails.Proofs.BFGSInequalities
open StochasticGradient (advance)

lemma advance_succ_call {S : Type*} (step : ℕ → S → S) :
    ∀ (n c : ℕ) (s : S), advance step (n + 1) c s = step (c + n) (advance step n c s) := by
  intro n
  induction n with
  | zero => intro c s; rfl
  | succ n ih =>
    intro c s
    rw [advance, ih (c + 1) (step c s), advance]
    congr 1
    omega

variable (q : Params) (I : Instance q.toPublic)
  (O : Oracle (Space q.d × Space q.d) (ℝ × Space q.d) 1) (ξ : (k : ℕ) → O.Seed k)

noncomputable def bfgsStep : ℕ → State q.d → State q.d := fun k st =>
  (bfgs q.L q.x0).update st (executeAnswerAt O (bfgs q.L q.x0) () ξ k ((bfgs q.L q.x0).query st))

noncomputable def run (n : ℕ) : State q.d :=
  advance (bfgsStep q O ξ) (n + 1) 0 ((bfgs q.L q.x0).initial ())

noncomputable def answer (n : ℕ) : ℝ × Space q.d :=
  executeAnswerAt O (bfgs q.L q.x0) () ξ (n + 1)
    (0, ((run q O ξ n).x, direction (run q O ξ n).B (run q O ξ n).g))

lemma run_zero : run q O ξ 0 =
    ⟨q.x0, (executeAnswerAt O (bfgs q.L q.x0) () ξ 0 (0, (q.x0, 0))).2, q.L • 1, true⟩ := rfl

lemma advance_succ_zero {S : Type*} (step : ℕ → S → S) :
    ∀ (n : ℕ) (s : S), advance step (n + 1) 0 s = step n (advance step n 0 s) := by
  intro n s
  have h := advance_succ_call step n 0 s
  rw [zero_add] at h
  exact h

lemma run_succ_step (n : ℕ) : run q O ξ (n + 1) = bfgsStep q O ξ (n + 1) (run q O ξ n) :=
  advance_succ_zero (bfgsStep q O ξ) (n + 1) _

lemma run_started (n : ℕ) : (run q O ξ n).started = true := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [run_succ_step]
    simp only [bfgsStep, bfgs]
    split <;> rfl

lemma run_succ (n : ℕ) : run q O ξ (n + 1) =
    ⟨(run q O ξ n).x + (answer q O ξ n).1 • direction (run q O ξ n).B (run q O ξ n).g,
      (answer q O ξ n).2,
      bfgsUpdate (run q O ξ n).B
        (WithLp.ofLp ((answer q O ξ n).1 • direction (run q O ξ n).B (run q O ξ n).g))
        (WithLp.ofLp ((answer q O ξ n).2 - (run q O ξ n).g)), true⟩ := by
  have hs := run_started q O ξ n
  rw [run_succ_step]
  simp only [bfgsStep, bfgs, hs, ↓reduceIte, answer]

lemma traj_of_run
    (hgrad : ∀ k seed x v, HasGradientAt (objective I) (O.answer k (0, (x, v)) seed).2
      (x + (O.answer k (0, (x, v)) seed).1 • v))
    (hls : ∀ k seed x v, ⟪gradient (objective I) x, v⟫ < 0 →
      0 < (O.answer k (0, (x, v)) seed).1 ∧
      objective I (x + (O.answer k (0, (x, v)) seed).1 • v) ≤
        objective I x + q.c1 * (O.answer k (0, (x, v)) seed).1 * ⟪gradient (objective I) x, v⟫ ∧
      q.c2 * ⟪gradient (objective I) x, v⟫ ≤ ⟪(O.answer k (0, (x, v)) seed).2, v⟫) :
    Traj (objective I) (fun n => (run q O ξ n).x) (fun n => (run q O ξ n).g)
      (fun n => (run q O ξ n).B) (fun n => (answer q O ξ n).1) q.c1 q.c2 := by
  have hg : ∀ n, HasGradientAt (objective I) (run q O ξ n).g (run q O ξ n).x := by
    intro n
    induction n with
    | zero =>
      rw [run_zero]
      have := hgrad (executeIndexedState O (bfgs q.L q.x0) () ξ 0).2
        (ξ (executeIndexedState O (bfgs q.L q.x0) () ξ 0).2.length) q.x0 0
      rw [smul_zero, add_zero] at this
      exact this
    | succ n ih =>
      rw [run_succ]
      exact hgrad _ _ _ _
  refine ⟨hg, fun n => by rw [run_succ], fun n => by rw [run_succ], ?_⟩
  intro n hneg
  have hgr : gradient (objective I) (run q O ξ n).x = (run q O ξ n).g := (hg n).gradient
  have h := hls (executeIndexedState O (bfgs q.L q.x0) () ξ (n + 1)).2
    (ξ (executeIndexedState O (bfgs q.L q.x0) () ξ (n + 1)).2.length) (run q O ξ n).x
    (direction (run q O ξ n).B (run q O ξ n).g) (by rw [hgr]; exact hneg)
  rw [hgr] at h
  have hx : (run q O ξ (n + 1)).x =
      (run q O ξ n).x + (answer q O ξ n).1 • direction (run q O ξ n).B (run q O ξ n).g := by
    rw [run_succ]
  have hg' : (run q O ξ (n + 1)).g = (answer q O ξ n).2 := by rw [run_succ]
  rw [hx, hg']
  exact h

lemma execute_eq_run (K : ℕ) :
    execute O (bfgs q.L q.x0) (fun _ => K + 1) () ξ = (run q O ξ K).x := by
  erw [execute_advance_history]
  rfl

lemma gamma_le (hc1 : 0 < q.c1) (hc12 : q.c1 < q.c2) (hc2 : q.c2 < 1) :
    0 < q.c1 * (1 - q.c2) ∧ q.c1 * (1 - q.c2) ≤ 1 / 4 := by
  refine ⟨mul_pos hc1 (by linarith), ?_⟩
  have h1 : q.c1 * (1 - q.c2) ≤ q.c2 * (1 - q.c2) :=
    mul_le_mul_of_nonneg_right hc12.le (by linarith)
  nlinarith [sq_nonneg (q.c2 - 1 / 2)]

theorem accuracy (hμ : 0 < q.μ) (hμL : q.μ ≤ q.Lh) (hc1 : 0 < q.c1) (hc12 : q.c1 < q.c2)
    (hc2 : q.c2 < 1) (hL : 0 < q.L) (hε : 0 < q.ε)
    (hconv : ConvexOn ℝ univ I.h) {gradH : Space q.m → Space q.m}
    (hgH : ∀ z, HasGradientAt I.h (gradH z) z)
    (hlip : ∀ z w, ‖gradH z - gradH w‖ ≤ q.Lh * ‖z - w‖) (hAL : q.Lh * ‖I.A‖ ^ 2 ≤ q.L)
    {xs : Space q.d} (hmin : IsMinOn (objective I) univ xs) (hdist : ‖q.x0 - xs‖ ≤ q.R)
    (hqg : ∀ x, objective I x ≤ objective I q.x0 →
      q.μ / 2 * ‖I.A x - I.A xs‖ ^ 2 ≤ objective I x - objective I xs)
    (hgrad : ∀ k seed x v, HasGradientAt (objective I) (O.answer k (0, (x, v)) seed).2
      (x + (O.answer k (0, (x, v)) seed).1 • v))
    (hls : ∀ k seed x v, ⟪gradient (objective I) x, v⟫ < 0 →
      0 < (O.answer k (0, (x, v)) seed).1 ∧
      objective I (x + (O.answer k (0, (x, v)) seed).1 • v) ≤
        objective I x + q.c1 * (O.answer k (0, (x, v)) seed).1 * ⟪gradient (objective I) x, v⟫ ∧
      q.c2 * ⟪gradient (objective I) x, v⟫ ≤ ⟪(O.answer k (0, (x, v)) seed).2, v⟫)
    (K : ℕ) (hK : 35 * (q.Lh / (q.μ * q.c1 * (1 - q.c2))) *
      Real.sqrt (q.Lh * q.L * q.R ^ 2 / (q.μ * q.c1 * (1 - q.c2) * q.ε)) ≤ K) :
    objective I (run q O ξ K).x - objective I xs ≤ q.ε := by
  have hLh : 0 < q.Lh := lt_of_lt_of_le hμ hμL
  obtain ⟨hγ0, hγ⟩ := gamma_le q hc1 hc12 hc2
  set γ := q.c1 * (1 - q.c2)
  set κ := q.Lh / q.μ
  have hκ : 1 ≤ κ := by rw [le_div_iff₀ hμ]; linarith
  have P : Prob (objective I) xs q.x0 q.L κ :=
    prob_of_composite hconv hgH hlip hμ hLh hAL hmin hqg
  have T := traj_of_run q I O ξ hgrad hls
  have hmb := main_bound T P rfl hL (by linarith) hc1 hc2
  set D : ℕ → ℝ := fun n => objective I (run q O ξ n).x - objective I xs
  have hPD := posDef_all T (by exact posDef_smul_one hL) hc2
  have hmono : ∀ i, D (i + 1) ≤ D i := fun i => by
    simp only [D]
    linarith [mono T hPD hc1 i]
  have hM : 0 ≤ q.L * q.R ^ 2 := by positivity
  have hd2 : q.L * ‖q.x0 - xs‖ ^ 2 ≤ q.L * q.R ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist 2) hL.le
  have hinit : D 0 ≤ q.L * q.R ^ 2 / 2 := by
    have := initial_gap (x0 := q.x0) hgH hlip hLh.le hAL hmin
    have h2 : q.L / 2 * ‖q.x0 - xs‖ ^ 2 ≤ q.L * q.R ^ 2 / 2 := by linarith
    exact this.trans h2
  have hrec : ∀ k : ℕ, 1 ≤ k →
      D k ≤ Real.exp 1 * (q.L * q.R ^ 2 + 2 * κ * ∑ i ∈ range k, D (i + 1)) /
        (γ * (k : ℝ) ^ 2) := by
    intro k hk
    refine (hmb k hk).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
    have : ‖(run q O ξ 0).x - xs‖ = ‖q.x0 - xs‖ := rfl
    rw [this]
    linarith
  have hboot := bootstrap hM hκ hγ0 hγ hmono hinit hrec
  change D K ≤ q.ε
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    have hs : Real.sqrt (q.Lh * q.L * q.R ^ 2 / (q.μ * q.c1 * (1 - q.c2) * q.ε)) = 0 := by
      have hpos : 0 < 35 * (q.Lh / (q.μ * q.c1 * (1 - q.c2))) := by
        have : 0 < q.μ * q.c1 * (1 - q.c2) := by
          have : 0 < 1 - q.c2 := by linarith
          positivity
        positivity
      push_cast at hK
      have := Real.sqrt_nonneg (q.Lh * q.L * q.R ^ 2 / (q.μ * q.c1 * (1 - q.c2) * q.ε))
      nlinarith
    have hR0 : q.R ^ 2 = 0 := by
      rw [Real.sqrt_eq_zero'] at hs
      have hden : 0 < q.μ * q.c1 * (1 - q.c2) * q.ε := by
        have : 0 < 1 - q.c2 := by linarith
        positivity
      rw [div_le_iff₀ hden, zero_mul] at hs
      have : 0 ≤ q.Lh * q.L * q.R ^ 2 := by positivity
      have h3 : q.Lh * q.L * q.R ^ 2 = 0 := le_antisymm hs this
      have h4 : q.Lh * q.L ≠ 0 := by positivity
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h h4
      · exact h
    rw [hR0, mul_zero, zero_div] at hinit
    linarith
  · have hb := hboot K hKpos
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hden : 0 < q.μ * q.c1 * (1 - q.c2) * q.ε := by
      have : 0 < 1 - q.c2 := by linarith
      positivity
    have hX : 0 ≤ q.Lh * q.L * q.R ^ 2 / (q.μ * q.c1 * (1 - q.c2) * q.ε) := by positivity
    have hsq := Real.sq_sqrt hX
    have hK2 : (35 * (q.Lh / (q.μ * q.c1 * (1 - q.c2)))) ^ 2 *
        (q.Lh * q.L * q.R ^ 2 / (q.μ * q.c1 * (1 - q.c2) * q.ε)) ≤ (K : ℝ) ^ 2 := by
      have h0 : 0 ≤ 35 * (q.Lh / (q.μ * q.c1 * (1 - q.c2))) *
          Real.sqrt (q.Lh * q.L * q.R ^ 2 / (q.μ * q.c1 * (1 - q.c2) * q.ε)) := by positivity
      have := pow_le_pow_left₀ h0 hK 2
      rw [mul_pow, hsq] at this
      exact this
    have key : 1200 * κ ^ 3 * (q.L * q.R ^ 2) / (γ ^ 3 * (K : ℝ) ^ 2) ≤ q.ε := by
      rw [div_le_iff₀ (by positivity)]
      have e1 : (35 * (q.Lh / (q.μ * q.c1 * (1 - q.c2)))) ^ 2 *
          (q.Lh * q.L * q.R ^ 2 / (q.μ * q.c1 * (1 - q.c2) * q.ε)) =
          1225 * κ ^ 3 * (q.L * q.R ^ 2) / (γ ^ 3 * q.ε) := by
        simp only [κ, γ]
        field_simp
        ring
      rw [e1, div_le_iff₀ (by positivity)] at hK2
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ κ ^ 3) hM]
    exact hb.trans key

end LongTails.Proofs.BFGSExecution
