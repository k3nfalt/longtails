import LongTailsOnline.Proofs.UcbConcentration
import LongTailsOnline.Proofs.UcbCounting

open MeasureTheory ProbabilityTheory

namespace LongTailsOnline.Proofs.Ucb

open LongTailsOnline.Setups.StochasticBandit LongTailsOnline.Algorithms.Ucb

lemma confident_of_not_bad {p : Params} {w : Sample p.k} {t : ℕ} (hw : w ∉ bad p t)
    (i : Arm p.k) (n : ℕ) (hn : 0 < n) (hnt : n ≤ t) :
    |empirical w i n - p.μ i| ≤ radius t n := by
  by_contra hh
  apply hw
  simp only [bad, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range]
  exact ⟨i, n, by omega, hn, lt_of_not_ge hh⟩

lemma regret_step {p : Params} (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1)
    (hbest : ∀ i, p.μ i ≤ p.μ p.best) (w : Sample p.k) {t : ℕ} (ht : t < p.T) :
    gap p (play w t) ≤ potential p (trajectory w (t + 1)).1 -
      potential p (trajectory w t).1 + (if t < p.k + 1 then 1 else 0) +
        (bad p t).indicator (fun _ => (1 : ℝ)) w := by
  classical
  have hmono := potential_increment_nonneg hbest (trajectory w t).1 (play w t)
  have hstep : (trajectory w (t + 1)).1 = increment (trajectory w t).1 (play w t) := rfl
  rw [hstep]
  by_cases hk : t < p.k + 1
  · rw [ite_eq_left hk]
    have hi : 0 ≤ (bad p t).indicator (fun _ => (1 : ℝ)) w := by
      by_cases hw : w ∈ bad p t <;> simp [Set.indicator, hw]
    linarith [gap_le_one hμ (play w t)]
  · rw [ite_eq_right hk]
    by_cases hw : w ∈ bad p t
    · rw [Set.indicator_of_mem hw]
      linarith [gap_le_one hμ (play w t)]
    · rw [Set.indicator_of_notMem hw]
      by_cases hg : 0 < gap p (play w t)
      · have hc := selected_small w ht (by omega) hg (confident_of_not_bad hw)
        rw [potential_increment, ite_eq_left hc]
        linarith
      · have hz : gap p (play w t) = 0 := by linarith [gap_nonneg hbest (play w t)]
        rw [hz]
        linarith

lemma cumulative_regret_le {p : Params} (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1)
    (hbest : ∀ i, p.μ i ≤ p.μ p.best) (w : Sample p.k) {N : ℕ} (hN : N ≤ p.T) :
    (∑ t ∈ Finset.range N, gap p (play w t)) ≤ potential p (trajectory w N).1 +
      (∑ t ∈ Finset.range N, if t < p.k + 1 then (1 : ℝ) else 0) +
        ∑ t ∈ Finset.range N, (bad p t).indicator (fun _ => (1 : ℝ)) w := by
  induction N with
  | zero => simp [trajectory, potential]
  | succ N ih =>
    have hi := ih (by omega)
    have hs := regret_step hμ hbest w (show N < p.T by omega)
    simp only [Finset.sum_range_succ]
    linarith

lemma sum_initialization (N K : ℕ) :
    (∑ t ∈ Finset.range N, if t < K then (1 : ℝ) else 0) ≤ K := by
  classical
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _t ∈ Finset.range K, (1 : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
        exact ht.2
      · intros; norm_num
    _ = _ := by simp

lemma limit_cost_le (p : Params) (hbest : ∀ i, p.μ i ≤ p.μ p.best) (i : Arm p.k) :
    gap p i * limit p i ≤
      if 0 < gap p i then 8 * Real.log (p.T + 1 : ℝ) / gap p i + 2 * gap p i else 0 := by
  by_cases hg : 0 < gap p i
  · rw [ite_eq_left hg]
    have hx : 0 ≤ 8 * Real.log (p.T + 1 : ℝ) / gap p i ^ 2 := by
      apply div_nonneg
      · apply mul_nonneg (by norm_num)
        apply Real.log_nonneg
        have := Nat.cast_nonneg (α := ℝ) p.T
        linarith
      · positivity
    have hc := Nat.ceil_lt_add_one hx
    have hl : (limit p i : ℝ) ≤ 8 * Real.log (p.T + 1 : ℝ) / gap p i ^ 2 + 2 := by
      simp only [limit, ite_eq_left hg, Nat.cast_add, Nat.cast_one]
      linarith
    calc
      _ ≤ gap p i * (8 * Real.log (p.T + 1 : ℝ) / gap p i ^ 2 + 2) :=
        mul_le_mul_of_nonneg_left hl hg.le
      _ = _ := by field_simp
  · have hz : gap p i = 0 := by linarith [gap_nonneg hbest i]
    simp [hz]

noncomputable def cost (p : Params) : ℝ :=
  ∑ i, if 0 < gap p i then 8 * Real.log (p.T + 1 : ℝ) / gap p i + 2 * gap p i else 0

lemma pathwise_regret_le {p : Params} (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1)
    (hbest : ∀ i, p.μ i ≤ p.μ p.best) (w : Sample p.k) :
    (∑ t ∈ Finset.range p.T, gap p (play w t)) ≤ cost p + (p.k + 1 : ℝ) +
      ∑ t ∈ Finset.range p.T, (bad p t).indicator (fun _ => (1 : ℝ)) w := by
  have hi := cumulative_regret_le hμ hbest w (le_refl p.T)
  have hp := potential_le p hbest (trajectory w p.T).1
  have hl : (∑ i, gap p i * limit p i) ≤ cost p :=
    Finset.sum_le_sum fun i _ => limit_cost_le p hbest i
  have he := sum_initialization p.T (p.k + 1)
  push_cast at he
  linarith

@[fun_prop]
lemma measurable_regret (p : Params) : Measurable (regret p) := by
  have hm : Measurable (p.μ) := measurable_of_countable _
  unfold regret
  fun_prop

lemma regret_mem_Icc {p : Params} (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1)
    (hbest : ∀ i, p.μ i ≤ p.μ p.best)
    (h : OnlineTemplate.Trace Unit (Arm p.k) ℝ Unit p.T) : regret p h ∈ Set.Icc (0 : ℝ) p.T := by
  constructor
  · exact Finset.sum_nonneg fun t _ => sub_nonneg.mpr (hbest (h t).2.1)
  · calc
      _ ≤ ∑ _t : Fin p.T, (1 : ℝ) := Finset.sum_le_sum fun t _ => gap_le_one hμ (h t).2.1
      _ = _ := by simp

lemma integrable_regret {p : Params} (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1)
    (hbest : ∀ i, p.μ i ≤ p.μ p.best)
    (law : ProbabilityMeasure (OnlineTemplate.Trace Unit (Arm p.k) ℝ Unit p.T)) :
    Integrable (regret p) law.toMeasure :=
  Integrable.of_mem_Icc 0 p.T (measurable_regret p).aemeasurable
    (ae_of_all _ (regret_mem_Icc hμ hbest))

lemma regret_history (p : Params) (w : Sample p.k) :
    regret p (history w p.T) = ∑ t ∈ Finset.range p.T, gap p (play w t) := by
  simp only [regret, history_apply]
  exact Fin.sum_univ_eq_sum_range (fun t => gap p (play w t)) p.T

lemma expected_regret_le {p : Params} {P : ProbabilityMeasure (Sample p.k)}
    (hP : Sampling p P) (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1)
    (hbest : ∀ i, p.μ i ≤ p.μ p.best) :
    (∫ h, regret p h ∂(OnlineTemplate.execute (algorithm p.k) (environment P) p.T).toMeasure) ≤
      cost p + 5 * (p.k + 1 : ℝ) := by
  classical
  have hi : Integrable (fun w => regret p (history w p.T)) P.toMeasure :=
    Integrable.of_mem_Icc 0 p.T
      ((measurable_regret p).comp (measurable_history p.k p.T)).aemeasurable
      (ae_of_all _ fun w => regret_mem_Icc hμ hbest (history w p.T))
  have hb (t : ℕ) : Integrable ((bad p t).indicator (fun _ : Sample p.k => (1 : ℝ)))
      P.toMeasure := (integrable_const 1).indicator (measurableSet_bad p t)
  have hs := integrable_finsetSum (Finset.range p.T) (fun t _ => hb t)
  rw [execute_history, integral_map (measurable_history p.k p.T).aemeasurable
    (measurable_regret p).aestronglyMeasurable]
  calc
    _ ≤ ∫ w, (cost p + (p.k + 1 : ℝ)) +
        ∑ t ∈ Finset.range p.T, (bad p t).indicator (fun _ => (1 : ℝ)) w ∂P.toMeasure :=
      integral_mono hi ((integrable_const _).add hs) fun w =>
        (regret_history p w).symm ▸ pathwise_regret_le hμ hbest w
    _ = cost p + (p.k + 1 : ℝ) + ∑ t ∈ Finset.range p.T, P.toMeasure.real (bad p t) := by
      rw [integral_add (integrable_const _) hs, integral_const,
        integral_finsetSum _ (fun t _ => hb t)]
      have hbint (t : ℕ) : (∫ w, (bad p t).indicator (fun _ => (1 : ℝ)) w ∂P.toMeasure) =
          P.toMeasure.real (bad p t) := by
        simpa using integral_indicator_const (μ := P.toMeasure) (1 : ℝ) (measurableSet_bad p t)
      simp only [hbint, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ _ := by linarith [sum_measure_bad hP p.T]

end LongTailsOnline.Proofs.Ucb
