import LongTails.Proofs.PolynomialMixingExecution
import LongTails.Proofs.RobustPilotConfidence
import LongTails.Proofs.PolynomialMixingBlocks

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.PolynomialMixingSelectionLaw

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Algorithms.PolynomialMixingSelection
open LongTails.Proofs.PolynomialMixingTraining LongTails.Proofs.PolynomialMixingAccuracy
open LongTails.Proofs.PolynomialMixingExecution LongTails.Proofs.PolynomialMixingValidation
open LongTails.Algorithms OracleTemplate

variable {q : Params} {g : Point q → ℝ → Space q} {f : Space q → ℝ}

lemma measurable_average (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (average g n) := by
  have h (k : ℕ) : Measurable (state g k) := by
    induction k with
    | zero => exact measurable_const
    | succ k ih =>
      have he : state g (k+1) = Function.uncurry (step g) ∘ (fun ξ => (state g k ξ, ξ k)) := funext (state_succ k)
      rw [he]
      exact (step_measurable hg).comp (ih.prodMk (measurable_pi_apply k))
  exact measurable_project.comp ((measurable_const (a := (n : ℝ)⁻¹)).smul
    ((measurable_fst.comp (measurable_snd.comp measurable_coords)).comp (h n)))

lemma measurable_score (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (fun w : Point q × Path => score g w.1 n w.2) := by
  unfold score
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum
  intro i _
  have hx : Measurable (fun w : Point q × Path => w.1.val) := measurable_subtype_coe.comp measurable_fst
  have hm : Measurable (fun w : Point q × Path => chordPoint q w.1 n i) :=
    measurable_project.comp ((measurable_const (a := (i : ℝ) / n)).smul hx)
  exact (hg.comp (hm.prodMk ((measurable_pi_apply i).comp measurable_snd))).inner hx

lemma measurable_score_at (hg : Measurable (Function.uncurry g)) (n : ℕ) (x : Point q) :
    Measurable (score g x n) := by
  change Measurable ((fun w : Point q × Path => score g w.1 n w.2) ∘ Prod.mk x)
  exact (measurable_score (q := q) (g := g) hg n).comp (measurable_prodMk_left (β := Path) (x := x))

lemma measurable_objective {π : Measure ℝ} [IsProbabilityMeasure π] (h : SubgradientOracle q f g π)
    (hp : 1 < q.p) (hG : 0 ≤ q.G) : Measurable fun x : Point q => f x.val := by
  have hL : LipschitzWith ⟨q.G, hG⟩ (fun x : Point q => f x.val) :=
    LipschitzWith.of_dist_le_mul fun (x y : Point q) => by
      change dist (f x.val) (f y.val) ≤ q.G * dist x.val y.val
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using objective_lipschitz h hp hG x y
  exact hL.continuous.measurable

lemma measurable_trial (hg : Measurable (Function.uncurry g)) (c : Schedule) :
    Measurable (trial g c) := by
  have hx := (measurable_average hg c.samples).comp
    (measurable_pi_apply (0 : Fin (c.trials + 1)) (X := fun _ => Path))
  apply hx.prodMk
  exact (RobustGradient.measurable_pilotCenter c.trials).comp ((measurable_const (a := q.ε / 2)).prodMk
    (Measurable.of_eval fun j : Fin c.trials => (measurable_score hg c.samples).comp
      (hx.prodMk (measurable_pi_apply j.succ))))

lemma measurable_bestPair {W X : Type*} [MeasurableSpace W] [MeasurableSpace X] (n : ℕ)
    {v : Fin n → W → X × ℝ} (hv : ∀ i, Measurable (v i)) {b : W → X × ℝ} (hb : Measurable b) :
    Measurable fun w => MatrixGeneralizedZO.bestPair (List.ofFn fun i => v i w) (b w) := by
  induction n generalizing b with
  | zero => simpa [MatrixGeneralizedZO.bestPair] using hb
  | succ n ih =>
    simp only [List.ofFn_succ, MatrixGeneralizedZO.bestPair]
    exact ih (fun i => hv i.succ) (Measurable.ite
      (measurableSet_lt ((hv 0).snd) hb.snd) (hv 0) hb)

lemma measurable_selected (hg : Measurable (Function.uncurry g)) (c : Schedule) :
    Measurable (selected g c) := by
  have aux {W X : Type} [MeasurableSpace W] [MeasurableSpace X] (x : X) (n : ℕ)
      (v : Fin n → W → X × ℝ) (hv : ∀ i, Measurable (v i)) :
      Measurable fun w => MatrixGeneralizedZO.selectBest x (List.ofFn fun i => v i w) := by
    cases n with
    | zero => exact measurable_const
    | succ n =>
      simp only [List.ofFn_succ, MatrixGeneralizedZO.selectBest]
      exact (measurable_bestPair n (fun i => hv i.succ) (hv 0)).fst
  unfold selected
  exact aux (origin q) c.trials (fun i (w : Fin c.trials → Fin (c.trials+1) → Path) => trial g c (w i)) (fun i => (measurable_trial hg c).comp (measurable_pi_apply i))

lemma best_pair_spec {X : Type*} (v : List (X × ℝ)) (b : X × ℝ) :
    MatrixGeneralizedZO.bestPair v b ∈ b :: v ∧
      ∀ a ∈ b :: v, (MatrixGeneralizedZO.bestPair v b).2 ≤ a.2 := by
  induction v generalizing b with
  | nil => simp [MatrixGeneralizedZO.bestPair]
  | cons a v ih =>
    simp only [MatrixGeneralizedZO.bestPair]
    by_cases h : a.2 < b.2
    · simp only [ite_eq_left h]
      obtain ⟨hm, hl⟩ := ih a
      exact ⟨List.mem_cons_of_mem _ hm, fun w hw => (List.mem_cons.mp hw).elim
        (fun e => e ▸ (hl a (by simp)).trans h.le) (hl w)⟩
    · simp only [ite_eq_right h]
      obtain ⟨hm, hl⟩ := ih b
      constructor
      · rcases List.mem_cons.mp hm with e | e
        · simp [e]
        · simp [e]
      · intro w hw
        rcases List.mem_cons.mp hw with e | e
        · exact e ▸ hl b (by simp)
        rcases List.mem_cons.mp e with e | e
        · exact e ▸ (hl b (by simp)).trans (le_of_not_gt h)
        · exact hl w (List.mem_cons_of_mem _ e)

lemma selected_index {X : Type*} (x : X) {n : ℕ} (v : Fin n → X × ℝ) (hn : 0 < n) :
    ∃ i, MatrixGeneralizedZO.selectBest x (List.ofFn v) = (v i).1 ∧ ∀ j, (v i).2 ≤ (v j).2 := by
  cases n with
  | zero => omega
  | succ n =>
    have h := best_pair_spec (List.ofFn fun i : Fin n => v i.succ) (v 0)
    rw [← List.ofFn_succ] at h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h.1
    refine ⟨i, ?_, fun j => ?_⟩
    · rw [List.ofFn_succ, MatrixGeneralizedZO.selectBest, ← hi]
    · rw [hi]; exact h.2 _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

end LongTails.Proofs.PolynomialMixingSelectionLaw
