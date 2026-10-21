import LongTails.Proofs.TwoSidedPLProcess
import LongTails.Proofs.SgdExecution

open MeasureTheory

namespace OracleTemplate.TwoSidedPL

open StochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

lemma advance_add {State : Type*} (step : ℕ → State → State) :
    ∀ a b c s, advance step (a + b) c s = advance step b (c + a) (advance step a c s) := by
  intro a
  induction a with
  | zero => intro b c s; simp [advance]
  | succ a ih =>
    intro b c s
    rw [show a + 1 + b = (a + b) + 1 by omega, advance, ih, advance]
    congr 1
    omega

variable {E F : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace Ω]

noncomputable def agdaOracle (Gx : E × F → Ω → E) (Gy : E × F → Ω → F) (p : ProbabilityMeasure Ω) :
    Oracle ((E × F) ⊕ (E × F)) (E ⊕ F) :=
  { Seed := fun _ => Ω
    law := ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure Ω)), inferInstance⟩
    answer := fun _ (_, w) ω => Sum.elim (fun z => Sum.inl (Gx z ω)) (fun z => Sum.inr (Gy z ω)) w }

lemma advance_agda (Gx : E × F → Ω → E) (Gy : E × F → Ω → F) (p : ProbabilityMeasure Ω)
    (L μy τ : ℝ) (n : ℕ) (x0 : E) (y0 : F) (j : Fin (n + 1)) (ξ : ℕ → Ω) :
    ∀ t, advance (fun k s => (stochasticSmoothedAgda (2 * L) τ (τ / 32) (τ * μy / 6144) n x0 y0).update s
        ((agdaOracle Gx Gy p).answer []
          ((stochasticSmoothedAgda (2 * L) τ (τ / 32) (τ * μy / 6144) n x0 y0).query s) (ξ k)))
        (2 * t) 0 ((stochasticSmoothedAgda (2 * L) τ (τ / 32) (τ * μy / 6144) n x0 y0).initial j) =
      (j, 2 * t, (path Gx Gy L μy τ x0 y0 ξ t).1, (path Gx Gy L μy τ x0 y0 ξ t).2.1,
        (path Gx Gy L μy τ x0 y0 ξ t).2.2,
        if n + (j : ℕ) ≤ t then ((path Gx Gy L μy τ x0 y0 ξ (n + j)).1,
          (path Gx Gy L μy τ x0 y0 ξ (n + j)).2.1) else (x0, y0)) := by
  intro t
  induction t with
  | zero =>
    simp only [Nat.mul_zero, advance]
    by_cases h : n + (j : ℕ) ≤ 0
    · have hn : n + (j : ℕ) = 0 := by omega
      simp only [hn]
      rfl
    · simp only [h, ite_false]
      rfl
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 2 by ring, advance_add, ih, Nat.zero_add]
    have h0 : (2 * t) % 2 = 0 := by omega
    have h1 : ¬ (2 * t + 1) % 2 = 0 := by omega
    have h2 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    simp only [advance, stochasticSmoothedAgda, agdaOracle, h0, h1, h2, ite_true, ite_false,
      Sum.elim_inl, Sum.elim_inr]
    refine Prod.ext rfl (Prod.ext (show 2 * t + 1 + 1 = 2 * t + 2 by omega)
      (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))))
    by_cases hj : t + 1 = n + (j : ℕ)
    · have h3 : n + (j : ℕ) ≤ t + 1 := le_of_eq hj.symm
      simp only [hj, ite_true]
      rw [← hj]
      split_ifs with hc
      · rfl
      · exact absurd le_rfl hc
    · simp only [hj, ite_false]
      by_cases h4 : n + (j : ℕ) ≤ t
      · have h5 : n + (j : ℕ) ≤ t + 1 := by omega
        simp only [h4, h5, ite_true]
      · have h5 : ¬ n + (j : ℕ) ≤ t + 1 := by omega
        simp only [h4, h5, ite_false]

lemma execute_agda (Gx : E × F → Ω → E) (Gy : E × F → Ω → F) (p : ProbabilityMeasure Ω)
    (L μy τ : ℝ) (n : ℕ) (x0 : E) (y0 : F) (j : Fin (n + 1)) (ξ : ℕ → Ω) :
    execute (agdaOracle Gx Gy p) (stochasticSmoothedAgda (2 * L) τ (τ / 32) (τ * μy / 6144) n x0 y0)
        (fun _ => (2 * (2 * n + 1))) j ξ =
      ((path Gx Gy L μy τ x0 y0 ξ (n + j)).1, (path Gx Gy L μy τ x0 y0 ξ (n + j)).2.1) := by
  erw [execute_advance_of_answer _ _ _ _ _
    (fun k query => (agdaOracle Gx Gy p).answer [] query (ξ k)) (fun _ _ => rfl)]
  have h := advance_agda Gx Gy p L μy τ n x0 y0 j ξ (2 * n + 1)
  have hj : n + (j : ℕ) ≤ 2 * n + 1 := by have := j.isLt; omega
  simp only [hj, ite_true] at h
  rw [h]
  rfl

end OracleTemplate.TwoSidedPL
