import LongTails.Setups.FiniteDimensionalWeakMinty
import LongTails.Proofs.MintyPrefixField
import LongTails.Proofs.Execution
import LongTails.TemplateLowerBound
import Mathlib.MeasureTheory.Integral.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.MintyPrefixLower

open LongTails.Setups.FiniteDimensionalWeakMinty MintyPrefixField MintyPrefixSearch

abbrev Space (p : Params) := EuclideanSpace ℝ (Fin p.d)

def exactOracle {E : Type*} (F : E → E) : Oracle E E where
  answer _ q _ := F q.2

lemma execute_run {E : Type*} (F : E → E) (A : Algorithm E E E) (n : ℕ)
    (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (exactOracle F) A (fun _ => n) seed ξ =
      A.output ((fun s => A.update s (F (A.query s).2))^[n] (A.initial seed)) := by
  rw [execute_eq_of_answer_eq (exactOracle F) F (fun _ _ _ => rfl)]
  exact execute_iterate F A n seed

lemma run_eq {d m : ℕ} {S : Type*} (step : S → Word d m → S) (n : ℕ) (w : Word d m) (s : S) :
    run step n s w = (fun v => step v w)^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run, Function.iterate_succ_apply, ih]

lemma admissible (p : Params) (hp : spec.valid p) {k m : ℕ} (π : Fin (k+1) ↪ Fin p.d)
    {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hl : 2 * a / s ≤ p.L)
    (hr : 4 * s * m * Real.sqrt (k+1) ≤ p.R) (w : Word (k+1) m) :
    let F := fun x => field π s a w (x - p.x0)
    spec.admissible p F (exactOracle F) := by
  refine ⟨fun _ _ _ => rfl, ?_, p.x0 + root π s w, ?_, ?_, ?_⟩
  · intro x y
    have h := field_lip π hs ha w (x-p.x0) (y-p.x0)
    rw [sub_sub_sub_cancel_right] at h
    exact h.trans (mul_le_mul_of_nonneg_right hl (norm_nonneg _))
  · change field π s a w (p.x0 + root π s w - p.x0) = 0
    rw [add_sub_cancel_left, field_root π hs]
  · rw [add_sub_cancel_left]
    exact (norm_root π hs w).trans hr
  · intro x
    rw [show x - (p.x0 + root π s w) = (x-p.x0) - root π s w by abel]
    rw [neg_mul]
    exact (neg_nonpos_of_nonneg (mul_nonneg hp.2.2.1 (sq_nonneg _))).trans
      (field_minty π hs ha w _)

lemma mean_residual (p : Params) {k m : ℕ} (π : Fin (k+1) ↪ Fin p.d)
    (s : ℝ) (hε : 0 < p.ε) (A : Algorithm (Space p) (Space p) (Space p)) (N : ℕ)
    (hsize : 2 * (4^N * 2^(k+1)) ≤ m^(k+1)) (v : A.State) :
    let F := fun (w : Word (k+1) m) x => field π s (4*p.ε) w (x-p.x0)
    let step := fun z w => A.update z (F w (A.query z).2)
    2 * p.ε * (m:ℝ)^(k+1) ≤ ∑ w, ‖F w (A.output (run step N v w))‖ := by
  classical
  intro F step
  let classif := fun (z : A.State) (i : Fin (k+1)) (a : Fin m) =>
    side (((A.query z).2 - p.x0) (π i) / s) a
  let win := fun (z : A.State) (w : Word (k+1) m) =>
    ∀ i, side ((A.output z - p.x0) (π i) / s) (w i) = .eq
  let good := Finset.univ.filter (fun w => win (run step N v w) w)
  have hb := count step classif win
    (fun z w u hw hu => funext (fun i => near_unique _ _ _ (hw i) (hu i)))
    (fun _ _ _ _ => near_unique _ _ _)
    (fun z i w u hpre hfar he => congrArg (A.update z)
      (same_reply π s _ _ i w u hpre hfar he)) N v 0 good (by omega)
    (fun _ _ _ _ _ h => by omega) (fun w hw => (Finset.mem_filter.mp hw).2)
  let bad := Finset.univ.filter (fun w => ¬ win (run step N v w) w)
  have htotal : good.card + bad.card = m^(k+1) := by
    rw [show good.card + bad.card = _ from Finset.card_filter_add_card_filter_not _]
    simp [Word]
  have hbad : m^(k+1) ≤ 2 * bad.card := by simp only [Nat.sub_zero] at hb; omega
  have hsum : ∑ w ∈ bad, ‖F w (A.output (run step N v w))‖ = bad.card * (4*p.ε) := by
    calc
      _ = ∑ _w ∈ bad, (4*p.ε) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hh := (Finset.mem_filter.mp hw).2
        change ¬(∀ i, _) at hh
        push Not at hh
        obtain ⟨i, hi⟩ := hh
        exact far_norm π s (by positivity) _ i w hi
      _ = _ := by simp
  have hle := Finset.sum_le_univ_sum_of_nonneg (s := bad)
    (fun w => norm_nonneg (F w (A.output (run step N v w))))
  rw [hsum] at hle
  have hreal : (m:ℝ)^(k+1) ≤ 2 * bad.card := by exact_mod_cast hbad
  nlinarith [mul_le_mul_of_nonneg_left hreal hε.le]

lemma average_contradiction {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P] (loss : I → Ω → ℝ) (b ε : ℝ)
    (hc : Fintype.card I * ε < b) (hl : ∀ x, b ≤ ∑ i, loss i x)
    (hw : ∀ i, Integrable (loss i) P ∧ ∫ x, loss i x ∂P ≤ ε) : False := by
  have hs : Integrable (fun x => ∑ i, loss i x) P :=
    integrable_finsetSum _ (fun i _ => (hw i).1)
  have hb := integral_mono (integrable_const (μ := P) b) hs hl
  rw [integral_const, probReal_univ, one_smul, integral_finsetSum _ (fun i _ => (hw i).1)] at hb
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hw i).2)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
  exact hc.not_ge (hb.trans hu)

lemma some_failure (p : Params) (hp : spec.valid p) {k m : ℕ} (π : Fin (k+1) ↪ Fin p.d)
    {s : ℝ} (hs : 0 < s) (hl : 2*(4*p.ε)/s ≤ p.L) (hr : 4*s*m*Real.sqrt (k+1) ≤ p.R)
    (A : Algorithm (Space p) (Space p) (Space p)) (N : ℕ) (hm : 0 < m)
    (hsize : 2 * (4^N * 2^(k+1)) ≤ m^(k+1)) :
    ∃ (F : Space p → Space p), spec.admissible p F (exactOracle F) ∧
      ¬ spec.successful p F (fun w : A.Seed × (ℕ → Unit) =>
        execute (exactOracle F) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩ := by
  classical
  let F := fun (w : Word (k+1) m) x => field π s (4*p.ε) w (x - p.x0)
  let step := fun z w => A.update z (F w (A.query z).2)
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  let loss := fun (w : Word (k+1) m) (v : A.Seed × (ℕ → Unit)) =>
    ‖F w (A.output (run step N (A.initial v.1) w))‖
  have hε := hp.2.2.2.2.1
  by_contra h
  have hw (w : Word (k+1) m) : Integrable (loss w) (P : Measure _) ∧
      (∫ v, loss w v ∂(P : Measure _)) ≤ p.ε := by
    have ha : spec.successful p (F w) (fun v : A.Seed × (ℕ → Unit) =>
        execute (exactOracle (F w)) A (fun _ => N) v.1 v.2) P := by
      by_contra hf
      exact h ⟨F w, admissible p hp π hs (by positivity) hl hr w, hf⟩
    change Integrable (fun v : A.Seed × (ℕ → Unit) =>
      ‖F w (execute (exactOracle (F w)) A (fun _ => N) v.1 v.2)‖) (P : Measure _) ∧
      (∫ v : A.Seed × (ℕ → Unit), ‖F w (execute (exactOracle (F w)) A (fun _ => N) v.1 v.2)‖
        ∂(P : Measure _)) ≤ p.ε at ha
    simpa only [execute_run, loss, run_eq, step] using ha
  have hm' : 0 < (m:ℝ)^(k+1) := by positivity
  apply average_contradiction (P : Measure _) loss (2*p.ε*(m:ℝ)^(k+1)) p.ε _ _ hw
  · simp only [Word, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    nlinarith only [mul_pos hε hm']
  · intro v
    exact mean_residual p π s hε A N hsize (A.initial v.1)

end LongTails.Proofs.MintyPrefixLower
