import LongTails.Proofs.RecursiveGradientConvergence

open scoped BigOperators

namespace OracleTemplate.NonconvexFiniteSum

open LongTails.Setups.FiniteSumSmoothNonconvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma recursiveGradient_rate {n b : ℕ} [NeZero n]
    {f : E → ℝ} {g : Fin n × E → E} {L Δ : ℝ}
    (hL : 0 < L) (hb : 0 < b)
    (hg : ∀ x, HasGradientAt f (FiniteSum.fullGradient g x) x)
    (hmean : ∀ x y, (𝔼 i, ‖g (i, x) - g (i, y)‖ ^ 2) ≤ L ^ 2 * ‖x - y‖ ^ 2)
    (k : ℕ) (hk : k ≤ b) (S : ℕ) [NeZero S] (x : E) (lower : ℝ)
    (hlower : ∀ z, lower ≤ f z) (hgap : f x - lower ≤ Δ) :
    (𝔼 seed : RecursiveSeeds n b k S,
      ‖FiniteSum.fullGradient g (execute { answer := fun _ (_, q) _ => g q }
        (recursiveGradient (1 / (2 * L)) b k S x)
        (fun _ => ((2 * b * k + 1 * n) * S)) seed)‖ ^ 2) ≤
      4 * L * Δ / (((k + 1) * S : ℕ) : ℝ) := by
  simp only [execute_recursiveGradient]
  change (𝔼 seed : (Fin S → Fin k → Fin b → Fin n) × Fin ((k + 1) * S),
    ‖FiniteSum.fullGradient g ((recursiveEpochs g (1 / (2 * L)) b x
      (List.ofFn (fun s => List.ofFn (fun j => List.ofFn (seed.1 s j))))).2.getD
        seed.2.val x)‖ ^ 2) ≤ _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp only [expect_list_getD _ x (fun z => ‖FiniteSum.fullGradient g z‖ ^ 2)
    ((k + 1) * S) (recursiveEpochs_length g (1 / (2 * L)) b k S x _)]
  rw [← Finset.expect_div]
  exact div_le_div_of_nonneg_right
    (recursiveEpochs_sum_bound hL hb hg hmean k hk S x lower hlower hgap)
    (Nat.cast_nonneg _)

lemma recursive_budget_accuracy {L Δ ε : ℝ} (hε : 0 < ε)
    (b : ℕ) (hb : 0 < b) :
    let S := max 1 ⌈4 * L * Δ / ((b : ℝ) * ε ^ 2)⌉₊
    4 * L * Δ / ((b : ℝ) * S) ≤ ε ^ 2 := by
  let S := max 1 ⌈4 * L * Δ / ((b : ℝ) * ε ^ 2)⌉₊
  have hS : (0 : ℝ) < S := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hc : 4 * L * Δ / ((b : ℝ) * ε ^ 2) ≤ (S : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈4 * L * Δ / ((b : ℝ) * ε ^ (2 : ℕ))⌉₊))
  have h := (div_le_iff₀ (by positivity : 0 < (b : ℝ) * ε ^ 2)).mp hc
  apply (div_le_iff₀ (by positivity : 0 < (b : ℝ) * S)).mpr
  nlinarith only [h]

lemma recursive_budget_bound {n : ℕ} {L Δ ε : ℝ}
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    let b := Nat.sqrt n + 1
    (n + 2 * b * (b - 1)) * max 1 ⌈4 * L * Δ / ((b : ℝ) * ε ^ 2)⌉₊ ≤
      5 * n + ⌈20 * Real.sqrt (n : ℝ) * L * Δ / ε ^ 2⌉₊ := by
  let b := Nat.sqrt n + 1
  let c := n + 2 * b * (b - 1)
  have hc : c ≤ 5 * n := by
    dsimp [c, b]
    have := Nat.sqrt_le n
    have := Nat.sqrt_le_self n
    nlinarith
  have hb : (0 : ℝ) < b := by dsimp [b]; positivity
  have hs : Real.sqrt (n : ℝ) ≤ b := by
    have hn := Nat.lt_succ_sqrt' n
    have hnR : (n : ℝ) < (b : ℝ) ^ 2 := by exact_mod_cast hn
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ)]
  have hnb : (n : ℝ) ≤ Real.sqrt (n : ℝ) * b := by
    nlinarith [mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (n : ℝ)),
      Real.sq_sqrt (Nat.cast_nonneg n)]
  have hcR : (c : ℝ) ≤ 5 * n := by exact_mod_cast hc
  have hratio : (c : ℝ) / b ≤ 5 * Real.sqrt (n : ℝ) := by
    apply (div_le_iff₀ hb).mpr
    nlinarith
  have ha : 0 ≤ 4 * L * Δ / ((b : ℝ) * ε ^ 2) := by positivity
  have hS : ((max 1 ⌈4 * L * Δ / ((b : ℝ) * ε ^ 2)⌉₊ : ℕ) : ℝ) ≤
      1 + 4 * L * Δ / ((b : ℝ) * ε ^ 2) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (by have := Nat.ceil_lt_add_one ha; linarith)
  have hprod : (c : ℝ) * (4 * L * Δ / ((b : ℝ) * ε ^ 2)) ≤
      20 * Real.sqrt (n : ℝ) * L * Δ / ε ^ 2 := by
    calc
      _ = ((c : ℝ) / b) * (4 * L * Δ / ε ^ 2) := by ring
      _ ≤ (5 * Real.sqrt (n : ℝ)) * (4 * L * Δ / ε ^ 2) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by ring
  have hceil := Nat.le_ceil (20 * Real.sqrt (n : ℝ) * L * Δ / ε ^ 2)
  have hmul := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
  change c * _ ≤ _
  exact_mod_cast (show (c : ℝ) * (max 1 ⌈4 * L * Δ / ((b : ℝ) * ε ^ 2)⌉₊ : ℕ) ≤
      5 * (n : ℝ) + (⌈20 * Real.sqrt (n : ℝ) * L * Δ / ε ^ 2⌉₊ : ℕ) by
    nlinarith)

end OracleTemplate.NonconvexFiniteSum
