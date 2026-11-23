import LongTails.Proofs.ComponentHessianAveraging

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.ComponentHessianInitialization

open OracleTemplate MeasureTheory LongTails.Setups.ConvexFiniteSumMeanSquareHessian
open ComponentHessianInstance ComponentHessianAveraging FullGeneralizedSmoothZeroQuery

variable {p : Params}

noncomputable def needle (i : Fin p.n) (M : ℝ) (z : Point p) : Instance p where
  f j := if j = i then quadratic (p.n * M) z else fun _ => 0
  xstar := z

lemma needle_objective (i : Fin p.n) (hn : 0 < p.n) (M : ℝ) (z x : Point p) :
    objective (needle i M z) x = quadratic M z x := by
  unfold objective needle
  simp only [ite_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, quadratic]
  field_simp

private lemma quadratic_hessian (M : ℝ) (z x : Point p) :
    fderiv ℝ (gradient (quadratic M z)) x = M • ContinuousLinearMap.id ℝ (Point p) := by
  have hg : gradient (quadratic M z) = field M z := funext (fun y => (quadratic_gradient M z y).gradient)
  rw [hg]
  exact (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const z).const_smul M).fderiv

lemma needle_admissible (i : Fin p.n) (hn : 0 < p.n) (M : ℝ) (hM : 0 ≤ M)
    (z : Point p) (hz : ‖z‖ ≤ p.R) :
    spec.admissible p (needle i M z) (exactOracle (needle i M z)) := by
  have ho := funext (needle_objective i hn M z)
  refine ⟨?_, ho ▸ quadratic_convex M hM z, ?_, hz, ?_, fun _ _ _ _ => rfl⟩
  · intro j
    by_cases h : j = i
    · simp only [needle, h, ↓reduceIte]
      exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
    · simp only [needle, h, ↓reduceIte]
      exact contDiff_const
  · intro x y
    have hh (j : Fin p.n) : fderiv ℝ (gradient ((needle i M z).f j)) x =
        fderiv ℝ (gradient ((needle i M z).f j)) y := by
      by_cases h : j = i
      · simp [needle, h, quadratic_hessian]
      · simp [needle, h]
    simp only [hh, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    positivity
  · intro x
    simp only [needle_objective i hn M z]
    exact (quadratic_zero M z).le.trans (quadratic_nonneg M hM z x)

noncomputable def silent (A : Method p) (seed : A.Seed) (t : ℕ) : A.State :=
  (fun s => A.update s 0)^[t] (A.initial seed)

noncomputable def visits (A : Method p) (seed : A.Seed) (T : ℕ) : Finset (Fin p.n) :=
  (Finset.range T).image (fun t => (A.query (silent A seed t)).2.1)

lemma silent_output (i : Fin p.n) (M : ℝ) (z : Point p) (A : Method p)
    (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) (hi : i ∉ visits A seed T) :
    execute (exactOracle (needle i M z)) A (fun _ => T) seed ξ = A.output (silent A seed T) := by
  have hξ : ξ = fun _ => () := Subsingleton.elim _ _
  subst ξ
  let reply := fun q : Fin p.n × Point p => RelativeHessianOracle.jet ((needle i M z).f q.1) q.2
  trans A.output ((fun s => A.update s (reply (A.query s).2))^[T] (A.initial seed))
  · exact execute_iterate reply A T seed
  congr 1
  suffices h : ∀ t, t ≤ T → (fun s => A.update s (reply (A.query s).2))^[t] (A.initial seed) =
      silent A seed t by exact h T le_rfl
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [Function.iterate_succ_apply', ih (by omega)]
    have h : (A.query (silent A seed t)).2.1 ≠ i := fun eq =>
      hi (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), eq⟩)
    have he : reply (A.query (silent A seed t)).2 = 0 := by
      simp [reply, RelativeHessianOracle.jet, needle, h, Prod.zero_eq_mk]
    rw [he]
    exact (Function.iterate_succ_apply' (fun s => A.update s 0) t (A.initial seed)).symm

lemma failure (hn : 0 < p.n) (hd : 0 < p.d) (hR : 0 < p.R) (hε : 0 < p.ε)
    (A : Method p) (b : Fin 1 → ℕ) (hT : 4 * b 0 ≤ p.n) :
    ∃ (J : Instance p) (O : Oracle (Fin p.n × Point p) (Reply p)), spec.admissible p J O ∧
      ¬ spec.successful p J (fun s : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b s.1 s.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  let z : Point p := EuclideanSpace.single ⟨0, hd⟩ p.R
  have hz : ‖z‖ = p.R := by simp [z, abs_of_pos hR]
  let M := 4 * p.ε / p.R^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let I := fun (i : Fin p.n) (s : Bool) => needle i M (if s then z else -z)
  apply extract I A b (by simpa using hn) (by decide) (C := 46 * p.ε)
  · intro i s
    exact needle_admissible i hn M hM _ (by cases s <;> simp [hz])
  · linarith
  intro ω
  let g := fun i s => gap (I i s) A (b 0) ω
  have eval (i : Fin p.n) (s : Bool) :
      g i s = quadratic M (if s then z else -z)
        (execute (exactOracle (I i s)) A (fun _ => b 0) ω.1 ω.2) := by
    dsimp only [g, gap, I]
    rw [needle_objective i hn, needle_objective i hn]
    simp only [needle, quadratic_zero, sub_zero]
  have hg (i : Fin p.n) (s : Bool) : 0 ≤ g i s := eval i s ▸ quadratic_nonneg _ hM _ _
  have pair (i : Fin p.n) (h : i ∉ visits A ω.1 (b 0)) :
      4 * p.ε ≤ g i false + g i true := by
    rw [eval, eval]
    simp only [Bool.false_eq_true, ↓reduceIte, I, silent_output i M _ A _ _ _ h]
    have hh := quadratic_pair M hM z (A.output (silent A ω.1 (b 0)))
    rw [hz, show M * p.R^2 = 4 * p.ε by dsimp [M]; field_simp] at hh
    linarith
  have hv : 4 * (visits A ω.1 (b 0)).card ≤ p.n :=
    (Nat.mul_le_mul_left 4 ((Finset.card_image_le).trans_eq (Finset.card_range _))).trans hT
  have hh := FiniteSumNondualLowerAveraging.finite_gap_average Finset.univ (Finset.univ : Finset Unit)
    (fun i _ => i ∈ visits A ω.1 (b 0)) (fun _ _ => False) (fun i _ => g i false + g i true)
    (4 * p.ε) (by positivity)
    (fun i _ _ _ => add_nonneg (hg i false) (hg i true))
    (fun i _ _ _ hi _ => pair i hi)
    (fun _ _ => by simpa [Finset.sum_boole] using (show (4 : ℝ) * (visits A ω.1 (b 0)).card ≤ p.n by exact_mod_cast hv))
    (fun _ _ => by simp)
  simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_unit, Nat.cast_one, mul_one,
    Fintype.sum_unique] at hh
  change _ ≤ 32 * ∑ i, ∑ s : Bool, g i s
  simp only [Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool]
  simp only [add_comm (g _ false)] at hh
  convert hh using 1
  ring

end LongTails.Proofs.ComponentHessianInitialization
