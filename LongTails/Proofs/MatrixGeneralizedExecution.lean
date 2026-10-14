import LongTails.Proofs.MatrixGeneralizedRun
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.MatrixGeneralizedZO

open LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth

lemma eval_stepPlan (p : Params) (f : Point p.d → ℝ) (k : ℕ) (x z : Point p.d)
    (s : Fin p.d → Bool) :
    QueryPlan.eval f (stepPlan p k (x, z) s) =
      (xnext p f k (extrapolate p k x z) s, znext p f k (extrapolate p k x z) z s) := rfl

lemma eval_runPlan (p : Params) (f : Point p.d → ℝ) (n : ℕ) : ∀ (k : ℕ)
    (st : Point p.d × Point p.d × Point p.d) (seeds : Fin n → Fin p.d → Bool),
    QueryPlan.eval f (runPlan p n k (st.1, st.2.1) seeds) =
      ((traj p f n k st seeds).1, f (traj p f n k st seeds).1) := by
  induction n with
  | zero => intro k st seeds; rfl
  | succ n ih =>
    intro k st seeds
    simp only [runPlan]
    exact ih (k + 1) (stepAll p f k st (seeds 0)) (fun j => seeds j.succ)

lemma runLength_eq (n : ℕ) : runLength n = 4 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [runLength, ih]; ring

lemma bestPair_le {α : Type*} (g : α → ℝ) : ∀ (l : List (α × ℝ)) (b : α × ℝ),
    (∀ e ∈ b :: l, e.2 = g e.1) →
      g (bestPair l b).1 ≤ g b.1 ∧ ∀ e ∈ l, g (bestPair l b).1 ≤ g e.1
  | [], b, _ => ⟨le_rfl, by simp⟩
  | c :: l, b, h => by
    have hb := h b (by simp)
    have hc := h c (by simp)
    have hrest : ∀ e ∈ (if c.2 < b.2 then c else b) :: l, e.2 = g e.1 := by
      intro e he
      rcases List.mem_cons.mp he with he | he
      · rw [he]; split_ifs
        · exact hc
        · exact hb
      · exact h e (by simp [he])
    obtain ⟨h1, h2⟩ := bestPair_le g l _ hrest
    simp only [bestPair]
    by_cases hcb : c.2 < b.2
    · rw [ite_eq_left hcb] at h1 h2 ⊢
      have hgc : g c.1 ≤ g b.1 := by rw [← hc, ← hb]; exact hcb.le
      refine ⟨h1.trans hgc, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with he | he
      · rw [he]; exact h1
      · exact h2 e he
    · rw [ite_eq_right hcb] at h1 h2 ⊢
      have hgb : g b.1 ≤ g c.1 := by rw [← hc, ← hb]; exact not_lt.mp hcb
      refine ⟨h1, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with he | he
      · rw [he]; exact h1.trans hgb
      · exact h2 e he

lemma uniform_measure_eq {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P : α → Prop) [DecidablePred P] :
    (PMF.uniformOfFintype α).toMeasure {ω | P ω} =
      ENNReal.ofReal (𝔼 ω : α, if P ω then (1 : ℝ) else 0) := by
  rw [PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
  rw [Fintype.expect_eq_sum_div_card]
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ ω : α, if P ω then (1 : ℝ) else 0) = (Fintype.card {ω // P ω} : ℝ) := by
    rw [Finset.sum_boole, Fintype.card_subtype]
  rw [hsum, ENNReal.ofReal_div_of_pos hc]
  simp only [ENNReal.ofReal_natCast]
  congr 2

lemma expect_prod_indep {ι T : Type*} [Fintype ι] [DecidableEq ι] [Fintype T]
    (F : T → ℝ) : (𝔼 ω : ι → T, ∏ j, F (ω j)) = ∏ _j : ι, (𝔼 t : T, F t) := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset T)) (fun _ t => F t)
  rw [Fintype.piFinset_univ] at h
  rw [← h, Finset.prod_const, Finset.card_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, div_pow]
  push_cast
  rfl

lemma half_pow_le_delta {δ : ℝ} (hδ : 0 < δ) :
    (1 / 2 : ℝ) ^ ⌈Real.logb 2 (1 / δ)⌉₊ ≤ δ := by
  set N := ⌈Real.logb 2 (1 / δ)⌉₊
  have hN : Real.logb 2 (1 / δ) ≤ N := Nat.le_ceil _
  have h2 : (1 / δ) ≤ (2 : ℝ) ^ (N : ℝ) := by
    rw [← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) (show 0 < 1 / δ by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hN
  rw [Real.rpow_natCast] at h2
  rw [one_div_pow, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hδ] at h2
  linarith

lemma best_of_ofFn {α : Type*} (g : α → ℝ) (x0 : α) {N : ℕ} (hN : 0 < N)
    (G : Fin N → α × ℝ) (hG : ∀ j, (G j).2 = g (G j).1) (j : Fin N) :
    g (selectBest x0 (List.ofFn G)) ≤ g (G j).1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [List.ofFn_succ]
  simp only [selectBest]
  have hex : ∀ e ∈ G 0 :: List.ofFn (fun i : Fin n => G i.succ), e.2 = g e.1 := by
    intro e he
    rcases List.mem_cons.mp he with he | he
    · rw [he]; exact hG 0
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact hG i.succ
  obtain ⟨h1, h2⟩ := bestPair_le g (List.ofFn (fun i : Fin n => G i.succ)) (G 0) hex
  rcases Fin.eq_zero_or_eq_succ j with hj | ⟨i, rfl⟩
  · rw [hj]; exact h1
  · exact h2 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

lemma numRuns_pos (p : Params) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) : 0 < numRuns p := by
  unfold numRuns
  apply Nat.ceil_pos.mpr
  apply Real.logb_pos (by norm_num)
  rw [lt_div_iff₀ hδ]; linarith

lemma eval_fullPlan (p : Params) (f : Point p.d → ℝ) (seed : Seeds p) :
    QueryPlan.eval f (fullPlan p seed) =
      selectBest p.x0
        (List.ofFn (fun j => QueryPlan.eval f (runPlan p (iterations p) 0 (p.x0, p.x0) (seed j)))) := by
  unfold fullPlan
  rw [QueryPlan.eval_map, QueryPlan.eval_traverse]

end OracleTemplate.MatrixGeneralizedZO
