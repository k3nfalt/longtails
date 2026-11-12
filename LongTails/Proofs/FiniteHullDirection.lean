import LongTails.Algorithms.FiniteHullDirection
import LongTails.Proofs.AdaptiveEntropicExecution
import LongTails.Proofs.AdaptiveEntropicStateMeasurable

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteHullDirection

open LongTails.Algorithms.FiniteHullDirection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

lemma vertex_nonneg (i j : Fin (n + 1)) : 0 ≤ vertex i j := by
  unfold vertex
  split <;> norm_num

lemma vertex_sum (i : Fin (n + 1)) : ∑ j, vertex i j = 1 := by
  simp [vertex]

lemma point_vertex (h : Fin (n + 1) → E) (i : Fin (n + 1)) :
    point h (vertex i) = h i := by
  simp [point, vertex]

lemma step_nonneg (h : Fin (n + 1) → E) (γ : ℝ) (w : Fin (n + 1) → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hw : ∀ i, 0 ≤ w i) (i : Fin (n + 1)) :
    0 ≤ step h γ w i :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr hγ1) (hw i))
    (mul_nonneg hγ (vertex_nonneg _ _))

lemma step_sum (h : Fin (n + 1) → E) (γ : ℝ) (w : Fin (n + 1) → ℝ)
    (hw : ∑ i, w i = 1) : ∑ i, step h γ w i = 1 := by
  simp only [step, Finset.sum_add_distrib, ← Finset.mul_sum, hw, vertex_sum]
  ring

lemma point_step (h : Fin (n + 1) → E) (γ : ℝ) (w : Fin (n + 1) → ℝ) :
    point h (step h γ w) = (1 - γ) • point h w + γ • h (index h w) := by
  simp only [point, step, add_smul, mul_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum]
  rw [show (∑ i, vertex (index h w) i • h i) = h (index h w) from point_vertex h _]

lemma point_norm_le (h : Fin (n + 1) → E) (w : Fin (n + 1) → ℝ) (G : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hh : ∀ i, ‖h i‖ ≤ G) :
    ‖point h w‖ ≤ G := by
  calc
    _ ≤ ∑ i, ‖w i • h i‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * G := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (hh i) (hw i)
    _ = G := by rw [← Finset.sum_mul, hs, one_mul]

lemma index_minimal (h : Fin (n + 1) → E) (w : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ⟪point h w, h (index h w)⟫ ≤ ⟪point h w, h i⟫ :=
  OracleTemplate.AdaptiveHeavyTailSimplex.minimumIndex_le (Nat.succ_pos n)
    (fun j => ⟪point h w, h j⟫) i

lemma gap_nonneg (h : Fin (n + 1) → E) (w : Fin (n + 1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : 0 ≤ gap h w := by
  have hi : ⟪point h w, h (index h w)⟫ ≤ ∑ i, w i * ⟪point h w, h i⟫ := by
    calc
      _ = ∑ i, w i * ⟪point h w, h (index h w)⟫ := by
        rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (index_minimal h w i) (hw i))
  have heq : (∑ i, w i * ⟪point h w, h i⟫) = ‖point h w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    conv_rhs => rhs; unfold point
    simp only [inner_sum, real_inner_smul_right]
  rw [heq] at hi
  exact sub_nonneg.mpr hi

lemma projection_of_gap (h : Fin (n + 1) → E) (w : Fin (n + 1) → ℝ)
    (δ : ℝ) (hg : gap h w ≤ δ ^ 2) (i : Fin (n + 1)) :
    ‖point h w‖ ^ 2 - δ ^ 2 ≤ ⟪h i, point h w⟫ := by
  have hi := index_minimal h w i
  rw [real_inner_comm (point h w) (h i)]
  unfold gap at hg
  linarith

lemma firstPhase_simplex (h : Fin (n + 1) → E) (k : ℕ) :
    (∀ i, 0 ≤ firstPhase h k i) ∧ ∑ i, firstPhase h k i = 1 := by
  induction k with
  | zero => exact ⟨vertex_nonneg 0, vertex_sum 0⟩
  | succ k ih =>
    have hγ : (2 : ℝ) / (k + 2) ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < k + 2)).2
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    exact ⟨step_nonneg h _ _ (by positivity) hγ ih.1, step_sum h _ _ ih.2⟩

lemma secondPhase_simplex (h : Fin (n + 1) → E) (T : ℕ) (hT : 0 < T) (k : ℕ) :
    (∀ i, 0 ≤ secondPhase h T k i) ∧ ∑ i, secondPhase h T k i = 1 := by
  induction k with
  | zero => exact firstPhase_simplex h T
  | succ k ih =>
    have hγ : (1 : ℝ) / T ≤ 1 := by
      apply (div_le_one (by exact_mod_cast hT : (0 : ℝ) < T)).2
      exact_mod_cast hT
    exact ⟨step_nonneg h _ _ (by positivity) hγ ih.1, step_sum h _ _ ih.2⟩

lemma energy_step (h : Fin (n + 1) → E) (w : Fin (n + 1) → ℝ) (γ : ℝ) :
    ‖point h (step h γ w)‖ ^ 2 / 2 = ‖point h w‖ ^ 2 / 2 - γ * gap h w +
      γ ^ 2 / 2 * ‖h (index h w) - point h w‖ ^ 2 := by
  rw [point_step]
  have he : (1 - γ) • point h w + γ • h (index h w) =
      point h w + γ • (h (index h w) - point h w) := by module
  rw [he, norm_add_sq_real, real_inner_smul_right, inner_sub_right,
    real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold gap
  ring

lemma energy_step_bound (h : Fin (n + 1) → E) (w : Fin (n + 1) → ℝ)
    (G γ : ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hh : ∀ i, ‖h i‖ ≤ G) :
    ‖point h (step h γ w)‖ ^ 2 / 2 ≤
      ‖point h w‖ ^ 2 / 2 - γ * gap h w + 2 * G ^ 2 * γ ^ 2 := by
  have hn : ‖h (index h w) - point h w‖ ≤ 2 * G :=
    (norm_sub_le _ _).trans (by linarith [hh (index h w), point_norm_le h w G hw hs hh])
  have hG : 0 ≤ G := (norm_nonneg (h 0)).trans (hh 0)
  have hn2 := sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * G) |>.2 hn
  rw [energy_step]
  nlinarith [mul_nonneg (sq_nonneg γ) (sub_nonneg.mpr hn2)]

lemma energy_gap_le (h : Fin (n + 1) → E) (w u : Fin (n + 1) → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    ‖point h w‖ ^ 2 / 2 - ‖point h u‖ ^ 2 / 2 ≤ gap h w := by
  have hi : ⟪point h w, h (index h w)⟫ ≤ ⟪point h w, point h u⟫ := by
    calc
      _ = ∑ i, u i * ⟪point h w, h (index h w)⟫ := by
        rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ ∑ i, u i * ⟪point h w, h i⟫ :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (index_minimal h w i) (hu i))
      _ = _ := by simp [point, inner_sum, real_inner_smul_right]
  have hn := sq_nonneg ‖point h w - point h u‖
  rw [norm_sub_sq_real] at hn
  unfold gap
  nlinarith

lemma warmup_scalar (G e e' : ℝ) (k : ℕ)
    (he : e ≤ 8 * G ^ 2 / (k + 2))
    (hr : e' ≤ (1 - 2 / (k + 2)) * e + 2 * G ^ 2 * (2 / (k + 2)) ^ 2) :
    e' ≤ 8 * G ^ 2 / (k + 3) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd : (0 : ℝ) < k + 2 := by positivity
  have hc : 0 ≤ 1 - (2 : ℝ) / (k + 2) := by
    apply sub_nonneg.mpr
    apply (div_le_one hd).2
    linarith
  have hm := mul_le_mul_of_nonneg_left he hc
  have hb : (1 - (2 : ℝ) / (k + 2)) * (8 * G ^ 2 / (k + 2)) +
      2 * G ^ 2 * (2 / (k + 2)) ^ 2 ≤ 8 * G ^ 2 / (k + 3) := by
    field_simp
    nlinarith [sq_nonneg G]
  linarith

lemma firstPhase_energy_gap (h : Fin (n + 1) → E) (u : Fin (n + 1) → ℝ)
    (G : ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1)
    (hh : ∀ i, ‖h i‖ ≤ G) (k : ℕ) :
    ‖point h (firstPhase h k)‖ ^ 2 / 2 - ‖point h u‖ ^ 2 / 2 ≤
      8 * G ^ 2 / (k + 2) := by
  induction k with
  | zero =>
      simp only [firstPhase, point_vertex, Nat.cast_zero, zero_add]
      have hG : 0 ≤ G := (norm_nonneg (h 0)).trans (hh 0)
      have hn := (sq_le_sq₀ (norm_nonneg (h 0)) hG).2 (hh 0)
      nlinarith [sq_nonneg ‖point h u‖]
  | succ k ih =>
      have hsimplex := firstPhase_simplex h k
      have hd := energy_step_bound h (firstPhase h k) G (2 / (k + 2))
        hsimplex.1 hsimplex.2 hh
      have hg := energy_gap_le h (firstPhase h k) u hu hs
      have hm := mul_le_mul_of_nonneg_left hg
        (by positivity : (0 : ℝ) ≤ 2 / (k + 2))
      have hr : ‖point h (step h (2 / (k + 2)) (firstPhase h k))‖ ^ 2 / 2 -
          ‖point h u‖ ^ 2 / 2 ≤ (1 - 2 / (k + 2)) *
          (‖point h (firstPhase h k)‖ ^ 2 / 2 - ‖point h u‖ ^ 2 / 2) +
          2 * G ^ 2 * (2 / (k + 2)) ^ 2 := by nlinarith
      convert warmup_scalar G _ _ k ih hr using 1 <;>
        norm_num [firstPhase, Nat.cast_add, Nat.cast_one, add_assoc]

lemma weights_gap_minimal (h : Fin (n + 1) → E) (T : ℕ) (k : ℕ) (hk : k ≤ T) :
    gap h (weights h T) ≤ gap h (secondPhase h T k) := by
  exact OracleTemplate.AdaptiveHeavyTailSimplex.minimumIndex_le (Nat.succ_pos T)
    (fun i : Fin (T + 1) => gap h (secondPhase h T i)) ⟨k, by omega⟩

lemma weights_gap_bound (h : Fin (n + 1) → E) (G : ℝ) (T : ℕ) (hT : 0 < T)
    (hh : ∀ i, ‖h i‖ ≤ G) : gap h (weights h T) ≤ 10 * G ^ 2 / T := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  let energy : ℕ → ℝ := fun k => ‖point h (secondPhase h T k)‖ ^ 2 / 2
  have hd (k : ℕ) : (1 / (T : ℝ)) * gap h (secondPhase h T k) ≤
      energy k - energy (k + 1) + 2 * G ^ 2 * (1 / (T : ℝ)) ^ 2 := by
    have hw := secondPhase_simplex h T hT k
    have hb := energy_step_bound h (secondPhase h T k) G (1 / T) hw.1 hw.2 hh
    change energy (k + 1) ≤ energy k - (1 / (T : ℝ)) * gap h (secondPhase h T k) +
      2 * G ^ 2 * (1 / (T : ℝ)) ^ 2 at hb
    linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range T) => hd k)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_range_sub',
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hmin : (T : ℝ) * gap h (weights h T) ≤
      ∑ k ∈ Finset.range T, gap h (secondPhase h T k) := by
    simpa using Finset.sum_le_sum (fun k (hk : k ∈ Finset.range T) =>
      weights_gap_minimal h T k (Nat.le_of_lt (Finset.mem_range.mp hk)))
  have hmin' := mul_le_mul_of_nonneg_left hmin (by positivity : (0 : ℝ) ≤ 1 / T)
  have hw := secondPhase_simplex h T hT T
  have hfirst := firstPhase_energy_gap h (secondPhase h T T) G hw.1 hw.2 hh T
  change energy 0 - energy T ≤ 8 * G ^ 2 / (T + 2) at hfirst
  have hfrac : 8 * G ^ 2 / ((T : ℝ) + 2) ≤ 8 * G ^ 2 / T :=
    div_le_div_of_nonneg_left (by positivity) hTr (by linarith)
  have hid : (1 / (T : ℝ)) * ((T : ℝ) * gap h (weights h T)) = gap h (weights h T) := by
    field_simp
  rw [hid] at hmin'
  have hcurv : 2 * G ^ 2 * ((T : ℝ) * (1 / (T : ℝ)) ^ 2) = 2 * G ^ 2 / T := by
    field_simp
  rw [hcurv] at hsum
  calc
    _ ≤ energy 0 - energy T + 2 * G ^ 2 / T := hmin'.trans hsum
    _ ≤ 8 * G ^ 2 / T + 2 * G ^ 2 / T := add_le_add (hfirst.trans hfrac) le_rfl
    _ = _ := by ring

section Measurability

open MeasureTheory

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_point : Measurable
    (fun z : (Fin (n + 1) → E) × (Fin (n + 1) → ℝ) => point z.1 z.2) := by
  unfold point
  fun_prop

lemma measurable_index : Measurable
    (fun z : (Fin (n + 1) → E) × (Fin (n + 1) → ℝ) => index z.1 z.2) := by
  apply (OracleTemplate.AdaptiveHeavyTailSimplex.measurable_minimumIndex _).comp
  apply Measurable.of_eval
  intro i
  exact continuous_inner.measurable.comp (measurable_point.prodMk (by fun_prop))

lemma measurable_gap : Measurable
    (fun z : (Fin (n + 1) → E) × (Fin (n + 1) → ℝ) => gap z.1 z.2) := by
  have he : Measurable (fun z : (Fin (n + 1) → E) × Fin (n + 1) => z.1 z.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  have hm : Measurable (fun z : (Fin (n + 1) → E) × (Fin (n + 1) → ℝ) =>
      z.1 (index z.1 z.2)) := he.comp (measurable_fst.prodMk measurable_index)
  exact (measurable_point.norm.pow_const 2).sub
    (continuous_inner.measurable.comp (measurable_point.prodMk hm))

lemma measurable_step (γ : ℝ) : Measurable
    (fun z : (Fin (n + 1) → E) × (Fin (n + 1) → ℝ) => step z.1 γ z.2) := by
  apply Measurable.of_eval
  intro i
  unfold step vertex
  exact (((measurable_pi_apply i).comp measurable_snd).const_mul (1 - γ)).add
    ((Measurable.ite (measurableSet_eq_fun measurable_const (measurable_index (E := E) (n := n)))
      measurable_const measurable_const).const_mul γ)

lemma measurable_firstPhase (k : ℕ) :
    Measurable (fun h : Fin (n + 1) → E => firstPhase h k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact (measurable_step (2 / (k + 2))).comp (measurable_id.prodMk ih)

lemma measurable_secondPhase (T k : ℕ) :
    Measurable (fun h : Fin (n + 1) → E => secondPhase h T k) := by
  induction k with
  | zero => exact measurable_firstPhase T
  | succ k ih => exact (measurable_step (1 / T)).comp (measurable_id.prodMk ih)

lemma measurable_weights (T : ℕ) :
    Measurable (fun h : Fin (n + 1) → E => weights h T) := by
  have hf (k : Fin (T + 1)) : Measurable (fun h : Fin (n + 1) → E =>
      gap h (secondPhase h T k)) := by
    have hp := measurable_secondPhase (E := E) (n := n) T (k : ℕ)
    have hpair : Measurable (fun h : Fin (n + 1) → E => (h, secondPhase h T (k : ℕ))) :=
      measurable_id.prodMk hp
    with_reducible simpa only [Function.comp_def] using
      (measurable_gap (E := E) (n := n)).comp hpair
  have hi : Measurable (fun h : Fin (n + 1) → E =>
      OracleTemplate.AdaptiveHeavyTailSimplex.minimumIndex (Nat.succ_pos T)
        (fun k : Fin (T + 1) => gap h (secondPhase h T k))) := by
    exact (OracleTemplate.AdaptiveHeavyTailSimplex.measurable_minimumIndex
      (Nat.succ_pos T)).comp (Measurable.of_eval hf)
  have he : Measurable (fun z : (Fin (T + 1) → (Fin (n + 1) → ℝ)) × Fin (T + 1) => z.1 z.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  exact he.comp ((Measurable.of_eval (fun k : Fin (T + 1) =>
    measurable_secondPhase (E := E) (n := n) T k)).prodMk hi)

end Measurability

end LongTails.Proofs.FiniteHullDirection
