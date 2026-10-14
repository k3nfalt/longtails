import LongTails.Proofs.Execution
import LongTails.Algorithms.Accelerated
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.Gradient

open LongTails.Setups.SmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private lemma accelerated_step {f : E → ℝ} {oracle : E → E} {L : ℝ}
    (hL : 0 < L) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (oracle x) x)
    (hlip : ∀ x y, ‖oracle x - oracle y‖ ≤ L * ‖x - y‖)
    (x z u : E) {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hB : 0 < A + a) (haB : a ^ 2 ≤ A + a) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    (A + a) * (f (y - (1 / L) • oracle y) - f u) +
        L / 2 * ‖z - (a / L) • oracle y - u‖ ^ 2 ≤
      A * (f x - f u) + L / 2 * ‖z - u‖ ^ 2 := by
  dsimp only
  let y := (A / (A + a)) • x + (a / (A + a)) • z
  let g := oracle y
  have hx := convex_support hc hg y x
  have hu := convex_support hc hg y u
  have hd := descent hL hg hlip y
  have hid : A • (x - y) + a • (u - y) = a • (u - z) := by
    dsimp [y]
    match_scalars
    all_goals field_simp [hB.ne'] <;> ring
  have hi := congrArg (fun v => ⟪g, v⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hw : (A + a) * (f y - f u) ≤ A * (f x - f u) + a * ⟪g, z - u⟫ := by
    have hx' := mul_le_mul_of_nonneg_left hx hA
    have hu' := mul_le_mul_of_nonneg_left hu ha
    have hn : ⟪g, u - z⟫ = -⟪g, z - u⟫ := by
      rw [← inner_neg_right]
      congr 1
      module
    rw [hn] at hi
    dsimp [g] at hi ⊢
    nlinarith
  have hn : z - (a / L) • g - u = (z - u) - (a / L) • g := by module
  change (A + a) * (f (y - (1 / L) • g) - f u) +
    L / 2 * ‖z - (a / L) • g - u‖ ^ 2 ≤ _
  rw [hn, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← real_inner_comm (z - u) g]
  have hd' := mul_le_mul_of_nonneg_left hd hB.le
  have hn' := mul_le_mul_of_nonneg_right haB (sq_nonneg ‖g‖)
  have hL0 := hL.ne'
  field_simp at ⊢
  field_simp at hd'
  dsimp [g] at *
  nlinarith

lemma accelerated_accuracy (f : E → ℝ) (oracle : E → E)
    (L R ε : ℝ) (x0 xstar : E)
    (hL : 0 < L) (hR : 0 ≤ R) (hε : 0 < ε)
    (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (oracle x) x)
    (hlip : ∀ x y, ‖oracle x - oracle y‖ ≤ L * ‖x - y‖)
    (hdist : ‖x0 - xstar‖ ≤ R) (K : ℕ)
    (hbudget : max 1 ⌈Real.sqrt (2 * L * R ^ 2 / ε)⌉₊ ≤ K) :
    f (execute { answer := fun _ (_, query) _ => oracle query } (accelerated (L, x0)) (fun _ => K)) - f xstar ≤ ε := by
  let alg := accelerated (L, x0)
  let T := fun s => alg.update s (oracle ((alg.query s).2))
  let s := fun k => T^[k] (alg.initial ())
  have hsucc : ∀ k, s (k + 1) = alg.update (s k) (oracle ((alg.query (s k)).2)) := by
    intro k
    exact Function.iterate_succ_apply' T k (alg.initial ())
  have hindex : ∀ k, (s k).1 = k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [hsucc]
      change (s k).1 + 1 = k + 1
      rw [ih]
  have hp : ∀ (k : ℕ), (k : ℝ) * ((k : ℝ) + 1) / 4 * (f (s k).2.1 - f xstar) +
      L / 2 * ‖(s k).2.2 - xstar‖ ^ 2 ≤ L / 2 * ‖x0 - xstar‖ ^ 2 := by
    intro k
    induction k with
    | zero =>
      have hs0 : s 0 = (0, x0, x0) := rfl
      erw [hs0]
      simp
    | succ k ih =>
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hs := accelerated_step hL hc hg hlip (s k).2.1 (s k).2.2 xstar
        (A := (k : ℝ) * ((k : ℝ) + 1) / 4) (a := ((k : ℝ) + 1) / 2)
        (by positivity) (by positivity) (by positivity) (by nlinarith)
      dsimp only at hs
      have he : ((k : ℝ) + 1) * ((k : ℝ) + 1 + 1) / 4 =
          (k : ℝ) * ((k : ℝ) + 1) / 4 + ((k : ℝ) + 1) / 2 := by ring
      simpa only [hsucc, alg, accelerated, acceleratedQuery, hindex,
        Nat.cast_add, Nat.cast_one, he] using hs.trans ih
  erw [execute_iterate]
  change f (s K).2.1 - f xstar ≤ ε
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hbudget)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hrate : f (s K).2.1 - f xstar ≤
      2 * L * ‖x0 - xstar‖ ^ 2 / ((K : ℝ) * ((K : ℝ) + 1)) := by
    apply (le_div_iff₀ (by positivity : 0 < (K : ℝ) * ((K : ℝ) + 1))).mpr
    have hpotential := hp K
    have hn : 0 ≤ L / 2 * ‖(s K).2.2 - xstar‖ ^ 2 := by positivity
    nlinarith
  have hb : Real.sqrt (2 * L * R ^ 2 / ε) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hbudget))
  have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * L * R ^ 2 / ε by positivity)
  have hsq : 2 * L * R ^ 2 / ε ≤ (K : ℝ) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (2 * L * R ^ 2 / ε)]
  have hm := (div_le_iff₀ hε).mp hsq
  have hR2 : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := by
    nlinarith [norm_nonneg (x0 - xstar)]
  have hnum := mul_le_mul_of_nonneg_left hR2 (show 0 ≤ 2 * L by positivity)
  apply hrate.trans
  apply (div_le_iff₀ (by positivity : 0 < (K : ℝ) * ((K : ℝ) + 1))).mpr
  nlinarith

end OracleTemplate.Gradient
