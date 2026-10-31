import LongTails.Proofs.SilverNonexpansive
import LongTails.Proofs.UniversalSilverSchedule
import LongTails.Proofs.CyclicGradientStep
import LongTails.Proofs.Execution

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.UniversalSilverConvergence

open OracleTemplate LongTails.Algorithms.SilverSchedule LongTails.Algorithms.UniversalSilver
open LongTails.Proofs.SilverCertificate LongTails.Proofs.SilverTrace
open LongTails.Proofs.SilverNonexpansive LongTails.Proofs.UniversalSilverSchedule
open LongTails.Setups.SmoothConvexQuadraticGrowth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma run_take_mem_nodes (g : E → E) (hs : List ℝ) (x : E) (j : ℕ) :
    run g (hs.take j) x ∈ nodes g hs x := by
  induction hs generalizing x j with
  | nil => simp [run, nodes]
  | cons h hs ih =>
    cases j with
    | zero => simp [run, nodes]
    | succ j =>
      simp only [List.take_succ_cons, run, nodes]
      exact List.mem_cons_of_mem _ (ih _ j)

lemma blocks_nonexpansive (φ : E → ℝ) (g : E → E)
    (hdef : ∀ u v, 0 ≤ defect (φ u) (φ v) u v (g u) (g v)) (z : E) (hz : g z = 0)
    (os : List ℕ) (x : E) :
    ∀ u ∈ nodes g (os.flatMap steps) x, ‖u - z‖ ≤ ‖x - z‖ := by
  induction os generalizing x with
  | nil =>
    intro u hu
    have he : u = x := by simpa only [List.flatMap_nil, nodes, List.mem_singleton] using hu
    rw [he]
  | cons o os ih =>
    intro u hu
    rw [List.flatMap_cons] at hu
    rcases (nodes_append g (steps o) (os.flatMap steps) x u).1 hu with hu | hu
    · exact nonexpansive φ g hdef o x z hz u hu
    · exact (ih _ u hu).trans (nonexpansive φ g hdef o x z hz _ (run_mem_nodes g (steps o) x))

lemma block_contract (φ : E → ℝ) (g : E → E)
    (hdef : ∀ u v, 0 ≤ defect (φ u) (φ v) u v (g u) (g v))
    (Z : E → Prop) (φstar c : ℝ) (hc : 0 < c)
    (hZ : ∀ z, Z z → g z = 0 ∧ φ z = φstar)
    (hqg : ∀ y, ∃ z, Z z ∧ c * ‖y - z‖ ^ 2 ≤ φ y - φstar)
    (o : ℕ) (ho : 1 ≤ (steps o).sum * c) (x z : E) (hzZ : Z z) :
    ∃ z', Z z' ∧ ‖run g (steps o) x - z'‖ ^ 2 ≤ ‖x - z‖ ^ 2 / 2 := by
  obtain ⟨hz, hφz⟩ := hZ z hzZ
  have hcert := certificate φ g hdef o x z hz
  set y := run g (steps o) x
  obtain ⟨z', hz'Z, hq⟩ := hqg y
  refine ⟨z', hz'Z, ?_⟩
  have hS : 0 ≤ (steps o).sum := by rw [steps_sum]; linarith [one_le_pow₀ (M₀ := ℝ) (n := o) (by linarith [ratio_gt_two] : (1 : ℝ) ≤ ratio)]
  have hgap : 0 ≤ φ y - φstar := le_trans (by positivity) hq
  have h1 : 2 * (steps o).sum * (φ y - φstar) ≤ ‖x - z‖ ^ 2 := by
    rw [hφz] at hcert
    have hn : 0 ≤ (steps o).sum * ((steps o).sum + 1) * ‖g y‖ ^ 2 :=
      mul_nonneg (mul_nonneg hS (by linarith)) (sq_nonneg _)
    nlinarith [sq_nonneg ‖y - z‖]
  have h2 : 2 * (φ y - φstar) ≤ 2 * ((steps o).sum * c) * (φ y - φstar) :=
    by nlinarith
  have h3 := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 * (steps o).sum by positivity)
  nlinarith

lemma blocks_decay (φ : E → ℝ) (g : E → E)
    (hdef : ∀ u v, 0 ≤ defect (φ u) (φ v) u v (g u) (g v))
    (Z : E → Prop) (φstar c : ℝ) (hc : 0 < c)
    (hZ : ∀ z, Z z → g z = 0 ∧ φ z = φstar)
    (hqg : ∀ y, ∃ z, Z z ∧ c * ‖y - z‖ ^ 2 ≤ φ y - φstar)
    (m : ℕ) (hm : ∀ o, m ≤ o → 1 ≤ (steps o).sum * c) (os : List ℕ) (x z : E) (hzZ : Z z) :
    ∃ z', Z z' ∧ ‖run g (os.flatMap steps) x - z'‖ ^ 2 ≤
      ‖x - z‖ ^ 2 * (1 / 2) ^ (os.countP (fun o => decide (m ≤ o))) := by
  induction os generalizing x z with
  | nil => exact ⟨z, hzZ, by simp [run]⟩
  | cons o os ih =>
    rw [List.flatMap_cons, run_append, List.countP_cons]
    by_cases ho : m ≤ o
    · obtain ⟨z₁, hz₁, h₁⟩ := block_contract φ g hdef Z φstar c hc hZ hqg o (hm o ho) x z hzZ
      obtain ⟨z₂, hz₂, h₂⟩ := ih (run g (steps o) x) z₁ hz₁
      refine ⟨z₂, hz₂, ?_⟩
      simp only [ho, decide_true, ite_true, pow_succ]
      have hp : 0 ≤ (1 / 2 : ℝ) ^ (os.countP (fun o => decide (m ≤ o))) := by positivity
      calc _ ≤ _ := h₂
        _ ≤ ‖x - z‖ ^ 2 / 2 * (1 / 2) ^ (os.countP (fun o => decide (m ≤ o))) :=
            mul_le_mul_of_nonneg_right h₁ hp
        _ = _ := by ring
    · have hz := (hZ z hzZ).1
      have hy := nonexpansive φ g hdef o x z hz _ (run_mem_nodes g (steps o) x)
      obtain ⟨z₂, hz₂, h₂⟩ := ih (run g (steps o) x) z hzZ
      refine ⟨z₂, hz₂, ?_⟩
      simp only [ho, decide_false]
      have hp : 0 ≤ (1 / 2 : ℝ) ^ (os.countP (fun o => decide (m ≤ o))) := by positivity
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hy 2
      calc _ ≤ _ := h₂
        _ ≤ _ := mul_le_mul_of_nonneg_right hsq hp
        _ = _ := by simp

lemma iterate_method {G : E → E} {L : ℝ} (x0 : E) (a : ℕ) :
    ∀ K, K ≤ (blocks a).length →
      (fun s : ℕ × E => (s.1 + 1, s.2 - (stepsize s.1 / L) • G s.2))^[K] (0, x0) =
        (K, run (fun x => (1 / L) • G x) ((blocks a).take K) x0) := by
  intro K
  induction K with
  | zero => intro _; rfl
  | succ K ih =>
    intro hK
    have hlt : K < (blocks a).length := by omega
    rw [Function.iterate_succ_apply', ih (by omega), List.take_succ_eq_append_getElem hlt,
      run_append, stepsize_eq a K hlt]
    simp only [run, smul_smul, div_eq_mul_inv, one_mul]

variable [CompleteSpace E]

lemma scaled_defect {f : E → ℝ} {G : E → E} {L : ℝ} (hL : 0 < L)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (u v : E) :
    0 ≤ defect (f u / L) (f v / L) u v ((1 / L) • G u) ((1 / L) • G v) := by
  have h := SampledConvex.cocoercive hL hc hg hlip u v
  have he : (1 / L) • G u - (1 / L) • G v = (1 / L) • (G u - G v) := by rw [smul_sub]
  simp only [defect, he, norm_smul, inner_smul_left, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hL), RCLike.conj_to_real]
  have hL2 : 0 < L ^ 2 := by positivity
  have key : ‖G u - G v‖ ^ 2 / L ^ 2 ≤ 2 * (f u / L - f v / L) - 2 * (1 / L * ⟪G v, u - v⟫) := by
    rw [div_le_iff₀ hL2]
    have : (2 * (f u / L - f v / L) - 2 * (1 / L * ⟪G v, u - v⟫)) * L ^ 2 =
        2 * L * (f u - f v - ⟪G v, u - v⟫) := by field_simp
    rw [this]; exact h
  have : (1 / L * ‖G u - G v‖) ^ 2 = ‖G u - G v‖ ^ 2 / L ^ 2 := by field_simp
  linarith

end LongTails.Proofs.UniversalSilverConvergence
