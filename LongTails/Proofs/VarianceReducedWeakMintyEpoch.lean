import LongTails.Proofs.VarianceReducedWeakMintyOuter
import LongTails.Proofs.RecursiveGradientConvergence

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.VarianceReducedWeakMinty

open LongTails.Setups.FiniteSumWeakMintyInclusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n b j : ℕ} [NeZero n]

lemma stepsPlan_potential (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (η s p c : ℝ) (w : E) (V : E → ℝ) (R : E × E → ℝ)
    (hstep : ∀ x, (𝔼 ξ : StepSeed n b j,
      (V (QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ)).1 +
        c * R (QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ)).2)) ≤
          (1 - p) * V x + p * V w) (q : ℕ) (x : E) :
    (𝔼 ξ : Fin q → StepSeed n b j,
      ((1 - p) * V (QueryPlan.eval (answer F J) (stepsPlan (b := b) (J := j) exact η s p w (operator F w) q ξ x)).1 +
        ((QueryPlan.eval (answer F J) (stepsPlan (b := b) (J := j) exact η s p w (operator F w) q ξ x)).2.map
          (fun st => p * V st.1 + c * R st.2)).sum)) ≤
            (1 - p) * V x + (q : ℝ) * p * V w := by
  induction q generalizing x with
  | zero => simp [stepsPlan, QueryPlan.eval]
  | succ q ih =>
    rw [expect_fin_succ]
    let S := fun a : StepSeed n b j =>
      QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) a)
    have hrec (a : StepSeed n b j) (ξ : Fin q → StepSeed n b j) :
        QueryPlan.eval (answer F J) (stepsPlan exact η s p w (operator F w) (q + 1) (Fin.cons a ξ) x) =
          let rest := QueryPlan.eval (answer F J) (stepsPlan exact η s p w (operator F w) q ξ (S a).1)
          (rest.1, S a :: rest.2) := by
      rw [stepsPlan]
      erw [QueryPlan.eval_bind, QueryPlan.eval_map]
      rfl
    simp only [hrec, List.map_cons, List.sum_cons]
    have hih := Finset.expect_le_expect (s := Finset.univ) (fun a _ => ih (S a).1)
    have hh := hstep x
    change (𝔼 a, (V (S a).1 + c * R (S a).2)) ≤ _ at hh
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at hih hh ⊢
    push_cast
    nlinarith

lemma epochPlan_potential {q : ℕ} [NeZero q]
    (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (η s p c : ℝ) (hp : p = (q : ℝ)⁻¹) (V : E → ℝ) (R : E × E → ℝ)
    (hstep : ∀ x w, (𝔼 ξ : StepSeed n b j,
      (V (QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ)).1 +
        c * R (QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ)).2)) ≤
          (1 - p) * V x + p * V w) (x w : E) :
    (𝔼 ξ : EpochSeed n b j q,
      ((1 - p) * V (QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ)).1.1 +
        V (QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ)).1.2 +
        c * ((QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ)).2.map R).sum)) ≤
          (1 - p) * V x + V w := by
  let S := fun ξ : Fin q → StepSeed n b j =>
    QueryPlan.eval (answer F J) (stepsPlan exact η s p w (operator F w) q ξ x)
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hqp : (q : ℝ) * p = 1 := by rw [hp, mul_inv_cancel₀ hq]
  have hsel (ξ : Fin q → StepSeed n b j) :
      (𝔼 i : Fin q, V ((S ξ).2.getD i.val (w, (w, 0))).1) =
        p * ((S ξ).2.map (fun st => V st.1)).sum := by
    have hh := NonconvexFiniteSum.expect_list_getD (S ξ).2 (w, (w, 0))
      (fun st => V st.1) q (eval_stepsPlan_length exact F J η s p w q ξ x)
    rw [hh, hp]
    ring
  have hsteps := stepsPlan_potential exact F J η s p c w V R (fun x => hstep x w) q x
  simp only [List.sum_map_add, List.sum_map_mul_left, hqp, one_mul] at hsteps
  have he (ξ : EpochSeed n b j q) :
      QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ) =
        (((S ξ.1).1, ((S ξ.1).2.getD ξ.2.val (w, (w, 0))).1), (S ξ.1).2.map Prod.snd) := by
    simp only [epochPlan, QueryPlan.eval_bind, eval_fullPlan, QueryPlan.eval_map]
    rfl
  simp only [he, ← Finset.univ_product_univ, Finset.expect_product]
  simp only [Finset.expect_add_distrib, Fintype.expect_const, hsel, List.map_map,
    Function.comp_def, ← Finset.mul_expect] at hsteps ⊢
  simpa only [S, add_assoc] using hsteps

lemma epochsPlan_potential {q : ℕ} [NeZero q]
    (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (η s p c : ℝ) (V : E × E → ℝ) (R : E × E → ℝ)
    (hepoch : ∀ x w, (𝔼 ξ : EpochSeed n b j q,
      (V (QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ)).1 +
        c * ((QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ)).2.map R).sum)) ≤
          V (x, w)) (M : ℕ) (state : E × E) :
    (𝔼 ξ : Fin M → EpochSeed n b j q,
      (V (QueryPlan.eval (answer F J) (epochsPlan exact η s p M ξ state)).1 +
        c * ((QueryPlan.eval (answer F J) (epochsPlan exact η s p M ξ state)).2.map R).sum)) ≤
          V state := by
  induction M generalizing state with
  | zero => simp [epochsPlan, QueryPlan.eval]
  | succ M ih =>
    rw [expect_fin_succ]
    let S := fun a : EpochSeed n b j q =>
      QueryPlan.eval (answer F J) (epochPlan exact η s p state.1 state.2 a)
    have hrec (a : EpochSeed n b j q) (ξ : Fin M → EpochSeed n b j q) :
        QueryPlan.eval (answer F J) (epochsPlan exact η s p (M + 1) (Fin.cons a ξ) state) =
          let rest := QueryPlan.eval (answer F J) (epochsPlan exact η s p M ξ (S a).1)
          (rest.1, (S a).2 ++ rest.2) := by
      rw [epochsPlan, QueryPlan.eval_bind, QueryPlan.eval_map]
      rfl
    simp only [hrec, List.map_append, List.sum_append, mul_add]
    have hih := Finset.expect_le_expect (s := Finset.univ) (fun a _ => ih (S a).1)
    have hh := hepoch state.1 state.2
    change (𝔼 a, (V (S a).1 + c * ((S a).2.map R).sum)) ≤ V state at hh
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at hih hh ⊢
    linarith

omit [NeZero n] in
lemma outputPlan_expectation {q M : ℕ}
    (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (η s p : ℝ) (x0 : E) (R : E × E → ℝ) :
    (𝔼 ξ : (Fin M → EpochSeed n b j q) × Fin (q * M),
      R (QueryPlan.eval (answer F J) (outputPlan exact η s p x0 ξ))) =
        (𝔼 ξ : Fin M → EpochSeed n b j q,
          ((QueryPlan.eval (answer F J) (epochsPlan exact η s p M ξ (x0, x0))).2.map R).sum) /
            (q * M : ℕ) := by
  simp only [outputPlan, QueryPlan.eval_map, ← Finset.univ_product_univ,
    Finset.expect_product]
  simp only [NonconvexFiniteSum.expect_list_getD _ _ _ _
    (eval_epochsPlan_length exact F J η s p M _ (x0, x0)), div_eq_mul_inv,
    Finset.expect_mul]

lemma outputPlan_bound {q M : ℕ} [NeZero q] [NeZero M]
    (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (η s p c : ℝ) (hc : 0 < c) (x0 : E) (V : E × E → ℝ) (R : E × E → ℝ)
    (hV : ∀ state, 0 ≤ V state)
    (hepoch : ∀ x w, (𝔼 ξ : EpochSeed n b j q,
      (V (QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ)).1 +
        c * ((QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ)).2.map R).sum)) ≤
          V (x, w)) :
    (𝔼 ξ : (Fin M → EpochSeed n b j q) × Fin (q * M),
      R (QueryPlan.eval (answer F J) (outputPlan exact η s p x0 ξ))) ≤
        V (x0, x0) / (c * (q * M : ℕ)) := by
  have hh := epochsPlan_potential exact F J η s p c V R hepoch M (x0, x0)
  have hn := Finset.expect_nonneg (s := Finset.univ) (fun (ξ : Fin M → EpochSeed n b j q) _ =>
    hV (QueryPlan.eval (answer F J) (epochsPlan exact η s p M ξ (x0, x0))).1)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hh
  have hqM : 0 < (q * M : ℕ) := Nat.mul_pos (NeZero.pos q) (NeZero.pos M)
  have hqM' : (0 : ℝ) < (q * M : ℕ) := by exact_mod_cast hqM
  rw [outputPlan_expectation, le_div_iff₀ (mul_pos hc hqM')]
  have hcancel (a : ℝ) : a / (q * M : ℕ) * (c * (q * M : ℕ)) = c * a := by
    field_simp [hqM'.ne']
  rw [hcancel]
  linarith

lemma outputPlan_residual_bound [CompleteSpace E] {q M k : ℕ} [NeZero q] [NeZero M]
    (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E) (A : E → Set E)
    (x0 xstar : E) {η ρ s p L Λ h radius : ℝ}
    (hη : 0 < η) (hL : 0 < L) (hηL : η * L < 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hp : p = (q : ℝ)⁻¹) (hp2 : p ≤ 1 / 2)
    (hrel : ρ = η * (1 - s)) (hh : 0 < h) (hhdef : h = 1 - η ^ 2 * L ^ 2)
    (hb : 0 < b)
    (hsmall : η ^ 2 * (if exact then 0 else Λ ^ 2 / b) / h ≤ s ^ 2 * p / 65536)
    (hpower : (1 - h / 2) ^ k ≤ s ^ 2 / 8192)
    (hJ : ∀ η z, 0 < η → η⁻¹ • (z - J η z) ∈ A (J η z))
    (hA : ∀ x y, ∀ a ∈ A x, ∀ b ∈ A y, 0 ≤ ⟪a - b, x - y⟫)
    (hF : ∀ u v, ‖operator F u - operator F v‖ ≤ L * ‖u - v‖)
    (hvar : ∀ u v, (n : ℝ)⁻¹ * ∑ i, ‖F i u - F i v‖ ^ 2 ≤ Λ ^ 2 * ‖u - v‖ ^ 2)
    (hwm : ∀ y, ∀ v ∈ A y, -ρ * ‖operator F y + v‖ ^ 2 ≤ ⟪operator F y + v, y - xstar⟫)
    (hradius : ‖x0 - xstar‖ ≤ radius) :
    (𝔼 ξ : (Fin M → EpochSeed n b (k + 1) q) × Fin (q * M),
      ‖operator F (QueryPlan.eval (answer F J) (outputPlan exact η s p x0 ξ)).1 +
        (QueryPlan.eval (answer F J) (outputPlan exact η s p x0 ξ)).2‖ ^ 2) ≤
      32 * radius ^ 2 / (s ^ 2 * η ^ 2 * (q * M : ℕ)) := by
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hne := monotone_resolvent_nonexpansive A J hJ hA hη
  have hν : 0 ≤ (if exact then 0 else Λ ^ 2 / b : ℝ) := by split <;> positivity
  have hstep (x w : E) :
      (𝔼 ξ : StepSeed n b (k + 1),
        ‖(QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ)).1 - xstar‖ ^ 2) +
      s ^ 2 * η ^ 2 / 16 * (𝔼 ξ : StepSeed n b (k + 1),
        ‖operator F (QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ)).2.1 +
          (QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ)).2.2‖ ^ 2) ≤
        (1 - p) * ‖x - xstar‖ ^ 2 + p * ‖w - xstar‖ ^ 2 := by
    obtain ⟨t, ht⟩ := picard_fixed_point (J η) (operator F) ((1 - p) • x + p • w)
      hη hL.le hηL hne hF
    exact stepPlan_descent exact F J A x w xstar t hη hs.le hs1 hp0 hp2 hrel hν hh hhdef
      hsmall hne (fun z => hJ η z hη) ht hF hwm
      (fun y => estimator_error_sum_zero exact F w y (NeZero.pos n) hb)
      (fun y => estimator_error_variance exact F w y hb (hvar y w)) k hpower
  let V : E → ℝ := fun x => ‖x - xstar‖ ^ 2
  let R : E × E → ℝ := fun yv => ‖operator F yv.1 + yv.2‖ ^ 2
  let c := s ^ 2 * η ^ 2 / 16
  have hc : 0 < c := by dsimp [c]; positivity
  have hepoch := epochPlan_potential (b := b) (j := k + 1) exact F J η s p c hp V R
    (fun x w => by
      simpa only [V, R, c, Finset.expect_add_distrib, ← Finset.mul_expect] using hstep x w)
  have hV (state : E × E) : 0 ≤ (1 - p) * V state.1 + V state.2 := by
    dsimp [V]
    exact add_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _)
  have hbnd := outputPlan_bound (q := q) (M := M) exact F J η s p c hc x0
    (fun state => (1 - p) * V state.1 + V state.2) R hV hepoch
  have hR : ‖x0 - xstar‖ ^ 2 ≤ radius ^ 2 := by
    nlinarith [norm_nonneg (x0 - xstar)]
  have hinit : (1 - p) * V x0 + V x0 ≤ 2 * radius ^ 2 := by
    dsimp [V]
    nlinarith [mul_nonneg hp0 (sq_nonneg ‖x0 - xstar‖)]
  refine hbnd.trans ?_
  calc
    _ ≤ (2 * radius ^ 2) / (c * (q * M : ℕ)) :=
      div_le_div_of_nonneg_right hinit (by positivity)
    _ = _ := by dsimp [c]; ring

omit [NeZero n] in
lemma seeds_expectation {q M : ℕ} (f : ((Fin M → EpochSeed n b j q) × Fin (q * M)) → ℝ) :
    (𝔼 ξ : Seeds n b j q M, f (ξ.epochs, ξ.selection)) =
      𝔼 ξ : (Fin M → EpochSeed n b j q) × Fin (q * M), f ξ := by
  let e : Seeds n b j q M ≃ (Fin M → EpochSeed n b j q) × Fin (q * M) :=
    { toFun := fun ξ => (ξ.epochs, ξ.selection)
      invFun := fun ξ => ⟨ξ.1, ξ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

end OracleTemplate.VarianceReducedWeakMinty
