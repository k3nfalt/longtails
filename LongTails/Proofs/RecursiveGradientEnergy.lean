import LongTails.Proofs.RecursiveGradientStep

open scoped BigOperators

namespace OracleTemplate.NonconvexFiniteSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma recursive_energy_step {n b : ℕ} [NeZero n]
    {f : E → ℝ} {g : Fin n × E → E} {L r : ℝ}
    (hL : 0 < L) (hb : 0 < b) (hr : 0 ≤ r) (hrb : r ≤ b)
    (hg : ∀ x, HasGradientAt f (FiniteSum.fullGradient g x) x)
    (hmean : ∀ x y, (𝔼 i, ‖g (i, x) - g (i, y)‖ ^ 2) ≤ L ^ 2 * ‖x - y‖ ^ 2)
    (x v : E) :
    let y := x - (1 / (2 * L)) • v
    f y + r / (4 * L) *
        (𝔼 seed : Fin b → Fin n,
          ‖v + differenceBatch g b y x (List.ofFn seed) - FiniteSum.fullGradient g y‖ ^ 2) +
        ‖FiniteSum.fullGradient g x‖ ^ 2 / (4 * L) ≤
      f x + (r + 1) / (4 * L) * ‖v - FiniteSum.fullGradient g x‖ ^ 2 := by
  let y := x - (1 / (2 * L)) • v
  have hL0 := hL.ne'
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnorm : ‖y - x‖ ^ 2 = (1 / (2 * L)) ^ 2 * ‖v‖ ^ 2 := by
    rw [show y - x = -(1 / (2 * L)) • v by dsimp [y]; module]
    simp [norm_smul, Real.norm_eq_abs, mul_pow]
  have hv := recursive_estimator_error hb hmean x y v
  rw [hnorm] at hv
  have hc : L ^ 2 * ((1 / (2 * L)) ^ 2 * ‖v‖ ^ 2) / b =
      ‖v‖ ^ 2 / (4 * b) := by field_simp; ring
  rw [hc] at hv
  have hd := inexact_gradient_descent (η := 1 / (2 * L))
    hg (fullGradient_lipschitz_of_mean_square hL.le hmean) x v
  have hd' : f y ≤ f x - ‖FiniteSum.fullGradient g x‖ ^ 2 / (4 * L) -
      ‖v‖ ^ 2 / (8 * L) + ‖v - FiniteSum.fullGradient g x‖ ^ 2 / (4 * L) := by
    convert hd using 1; field_simp; ring
  have hcoeff : r * (‖v‖ ^ 2 / (4 * b)) ≤ ‖v‖ ^ 2 / 4 := by
    calc
      _ = (r * ‖v‖ ^ 2) / (4 * b) := by ring
      _ ≤ ((b : ℝ) * ‖v‖ ^ 2) / (4 * b) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hrb (sq_nonneg ‖v‖)) (by positivity)
      _ = _ := by field_simp
  have hv' := mul_le_mul_of_nonneg_left hv hr
  have hv'' : r *
      (𝔼 seed : Fin b → Fin n,
        ‖v + differenceBatch g b y x (List.ofFn seed) - FiniteSum.fullGradient g y‖ ^ 2) ≤
      r * ‖v - FiniteSum.fullGradient g x‖ ^ 2 + ‖v‖ ^ 2 / 4 := by
    nlinarith only [hv', hcoeff]
  have hv''' := div_le_div_of_nonneg_right hv'' (show 0 ≤ 4 * L by positivity)
  dsimp only
  change f y + _ + _ ≤ _
  dsimp only [y] at hd' hv''' ⊢
  ring_nf at hd' hv''' ⊢
  nlinarith [mul_nonneg (inv_nonneg.mpr hL.le) (sq_nonneg ‖v‖)]

lemma expect_function_succ {A : Type*} [Fintype A] {k : ℕ}
    (h : (Fin (k + 1) → A) → ℝ) :
    (𝔼 seed, h seed) = 𝔼 a : A, 𝔼 seed : Fin k → A, h (Fin.cons a seed) := by
  rw [Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => A)).symm
    h (fun seed => h (Fin.cons seed.1 seed.2))]
  · exact Finset.expect_product Finset.univ Finset.univ _
  · intro seed
    exact congrArg h ((Fin.consEquiv (fun _ : Fin (k + 1) => A)).apply_symm_apply seed).symm

lemma recursiveRun_energy {n b : ℕ} [NeZero n]
    {f : E → ℝ} {g : Fin n × E → E} {L : ℝ}
    (hL : 0 < L) (hb : 0 < b)
    (hg : ∀ x, HasGradientAt f (FiniteSum.fullGradient g x) x)
    (hmean : ∀ x y, (𝔼 i, ‖g (i, x) - g (i, y)‖ ^ 2) ≤ L ^ 2 * ‖x - y‖ ^ 2)
    (k : ℕ) (hk : k ≤ b) (x v : E) :
    (𝔼 seed : Fin k → Fin b → Fin n,
      let result := recursiveRun g (1 / (2 * L)) b x v
        (List.ofFn (fun j => List.ofFn (seed j)))
      f result.1 + (result.2.map (fun z => ‖FiniteSum.fullGradient g z‖ ^ 2)).sum / (4 * L)) ≤
      f x + ((k : ℝ) + 1) / (4 * L) * ‖v - FiniteSum.fullGradient g x‖ ^ 2 := by
  induction k generalizing x v with
  | zero =>
      have h := recursive_energy_step hL hb (r := 0) le_rfl (Nat.cast_nonneg b)
        hg hmean x v
      simpa [recursiveRun] using h
  | succ k ih =>
      let y := x - (1 / (2 * L)) • v
      let w := fun sample : Fin b → Fin n =>
        v + differenceBatch g b y x (List.ofFn sample)
      have htail (sample : Fin b → Fin n) :=
        ih (Nat.le_trans (Nat.le_succ k) hk) y (w sample)
      have hpoint (sample : Fin b → Fin n) :
          (𝔼 seed : Fin k → Fin b → Fin n,
            let result := recursiveRun g (1 / (2 * L)) b y (w sample)
              (List.ofFn (fun j => List.ofFn (seed j)))
            f result.1 + (‖FiniteSum.fullGradient g x‖ ^ 2 +
              (result.2.map (fun z => ‖FiniteSum.fullGradient g z‖ ^ 2)).sum) / (4 * L)) ≤
            f y + ((k : ℝ) + 1) / (4 * L) *
              ‖w sample - FiniteSum.fullGradient g y‖ ^ 2 +
              ‖FiniteSum.fullGradient g x‖ ^ 2 / (4 * L) := by
        simp only [add_div, Finset.expect_add_distrib, Fintype.expect_const] at htail ⊢
        linarith [htail sample]
      have hav := Finset.expect_le_expect (s := Finset.univ) (fun sample _ => hpoint sample)
      have hrb : (k : ℝ) + 1 ≤ b := by exact_mod_cast hk
      have hs := recursive_energy_step hL hb (r := (k : ℝ) + 1) (by positivity)
        hrb hg hmean x v
      rw [expect_function_succ]
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, recursiveRun,
        List.map_cons, List.sum_cons]
      simp only [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect] at hav
      dsimp only at hs
      dsimp [y, w] at hav
      push_cast
      simpa only [Finset.expect_add_distrib, add_assoc] using
        hav.trans (by simpa only [add_assoc] using hs)

end OracleTemplate.NonconvexFiniteSum
