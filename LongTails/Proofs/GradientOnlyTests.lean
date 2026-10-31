import LongTails.Proofs.GradientOnlyAgd
import LongTails.Proofs.GradientQuadrature

namespace LongTails.Proofs.GradientOnlyTests

open scoped RealInnerProductSpace
open LongTails.Algorithms.GradientOnlyGuarded LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.GuardedAcceleratedGeometry LongTails.Proofs.GradientOnlyAgd
open LongTails.Proofs.GradientQuadrature

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma firstTrue_le (P : ℕ → Prop) (n : ℕ) : firstTrue P n ≤ n := by
  induction n with
  | zero => simp [firstTrue]
  | succ n ih =>
    unfold firstTrue
    split_ifs <;> omega

lemma firstTrue_not (P : ℕ → Prop) (n : ℕ) : ∀ k < firstTrue P n, ¬ P k := by
  induction n with
  | zero => intro k hk; simp [firstTrue] at hk
  | succ n ih =>
    intro k hk
    unfold firstTrue at hk
    have hle := firstTrue_le P n
    split_ifs at hk with h₁ h₂
    · exact ih k hk
    · exact ih k (by omega)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact ih k (by omega)
      · subst h; exact h₂

lemma firstTrue_spec (P : ℕ → Prop) (n : ℕ) (h : firstTrue P n < n) : P (firstTrue P n) := by
  induction n with
  | zero => simp [firstTrue] at h
  | succ n ih =>
    unfold firstTrue at h ⊢
    have hle := firstTrue_le P n
    split_ifs at h ⊢ with h₁ h₂
    · exact ih h₁
    · exact h₂
    · omega

lemma xs_succ (t : Tuning) (g : E → E) (c : E) (k : ℕ) (hk : k < t.N) :
    xs t g c (k + 1) = gradientStep t.L (ys t g c k) (regGrad t.α c (ys t g c k) (g (ys t g c k))) :=
  (agd_succ t g c k hk).1

lemma zs_succ (t : Tuning) (g : E → E) (c : E) (k : ℕ) (hk : k < t.N) :
    zs t g c (k + 1) = centerStep t.a t.μ (ys t g c k) (zs t g c k)
      (regGrad t.α c (ys t g c k) (g (ys t g c k))) :=
  (agd_succ t g c k hk).2

lemma stateY_agd (t : Tuning) (g : E → E) (c : E) (k : ℕ) :
    stateY t (agd t g c) k = ys t g c k := rfl

lemma stateX_agd (t : Tuning) (g : E → E) (c : E) (k : ℕ) :
    stateX (agd t g c) k = xs t g c k := rfl

lemma stateG_agd (t : Tuning) (g : E → E) (c : E) (hL : t.L ≠ 0) (k : ℕ) (hk : k < t.N) :
    stateG t (agd t g c) k = regGrad t.α c (ys t g c k) (g (ys t g c k)) := by
  unfold stateG
  rw [stateY_agd, stateX_agd, xs_succ t g c k hk]
  unfold gradientStep
  rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ hL, one_smul]

lemma surrogateOf_nodes (g : E → E) (a b : E) (m : ℕ) :
    surrogateOf (fun j => g (nodes a b m j)) a b = surrogate g a b m := by
  have h : ∀ i : Fin m, ⟪g (nodes a b m (i, 0)) + g (nodes a b m (i, 1)),
      (1 / (2 * (m : ℝ))) • (b - a)⟫ = pieceValue g a b m i := by
    intro i
    simp [nodes, pieceValue]
  unfold surrogateOf surrogate
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  exact Fin.sum_univ_eq_sum_range (pieceValue g a b m) m

lemma reg_bregman (f : E → ℝ) (gv : E) (α : ℝ) (c u v : E) :
    regValue f α c u - regValue f α c v - ⟪regGrad α c v gv, u - v⟫ =
      (f u - f v - ⟪gv, u - v⟫) + α * ‖u - v‖ ^ 2 := by
  unfold regValue regGrad
  have h : ‖u - c‖ ^ 2 = ‖(u - v) + (v - c)‖ ^ 2 := by rw [sub_add_sub_cancel]
  rw [h, norm_add_sq_real, inner_add_left, real_inner_smul_left, real_inner_comm (v - c) (u - v)]
  ring

end General

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma pair_error {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L₃ : ℝ} (hL₃ : 0 ≤ L₃)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L₃ * ‖x - y‖)
    (t : Tuning) (ht : 0 < t.m) (c u v G : E) :
    |pairValue t c u v G (fun j => gradient f (nodes v u t.m j)) -
      (regValue f t.α c u - regValue f t.α c v - ⟪G, u - v⟫)| ≤ L₃ * ‖u - v‖ ^ 4 / t.m ^ 3 := by
  have hs := GradientQuadrature.surrogate_error hf hL₃ hT v u ht
  unfold pairValue
  rw [surrogateOf_nodes]
  unfold regValue
  have he : surrogate (gradient f) v u t.m + t.α * (‖u - c‖ ^ 2 - ‖v - c‖ ^ 2) - ⟪G, u - v⟫ -
      (f u + t.α * ‖u - c‖ ^ 2 - (f v + t.α * ‖v - c‖ ^ 2) - ⟪G, u - v⟫) =
      surrogate (gradient f) v u t.m - (f u - f v) := by ring
  rw [he]
  simpa [norm_sub_rev] using hs

omit [FiniteDimensional ℝ E] in
lemma pass_supports {f : E → ℝ} (t : Tuning) {c u v G : E} {r : Fin t.m × Fin 2 → E} {err : ℝ}
    (hp : passes t c u v G r)
    (herr : |pairValue t c u v G r - (regValue f t.α c u - regValue f t.α c v - ⟪G, u - v⟫)| ≤ err)
    (hsmall : err ≤ t.τ * ‖u - v‖ ^ 2) : supports f t c u v G := by
  unfold passes at hp
  unfold supports
  have h := (abs_le.mp herr).2
  have e1 : (t.μ / 2 + t.τ) * ‖u - v‖ ^ 2 = t.μ / 2 * ‖u - v‖ ^ 2 + t.τ * ‖u - v‖ ^ 2 := by ring
  rw [e1] at hp
  linarith

omit [FiniteDimensional ℝ E] in
lemma fail_deficit {f : E → ℝ} (t : Tuning) {c u v gv : E} {r : Fin t.m × Fin 2 → E} {err : ℝ}
    (hp : ¬ passes t c u v (regGrad t.α c v gv) r)
    (herr : |pairValue t c u v (regGrad t.α c v gv) r -
      (regValue f t.α c u - regValue f t.α c v - ⟪regGrad t.α c v gv, u - v⟫)| ≤ err)
    (hsmall : err ≤ t.τ * ‖u - v‖ ^ 2) (hμ : t.μ = t.α / 2) (hτ : t.τ = t.α / 32) (hα : 0 ≤ t.α) :
    f u - f v - ⟪gv, u - v⟫ ≤ -t.α * ‖u - v‖ ^ 2 / 2 := by
  unfold passes at hp
  push Not at hp
  have h := (abs_le.mp herr).1
  rw [reg_bregman] at h
  set A := t.α * ‖u - v‖ ^ 2
  have hA : 0 ≤ A := by positivity
  have e1 : (t.μ / 2 + t.τ) * ‖u - v‖ ^ 2 = 9 / 32 * A := by rw [hμ, hτ]; ring
  have e2 : t.τ * ‖u - v‖ ^ 2 = A / 32 := by rw [hτ]; ring
  have e3 : -t.α * ‖u - v‖ ^ 2 / 2 = -(A / 2) := by ring
  rw [e1] at hp
  rw [e2] at hsmall
  rw [e3]
  linarith

end Smooth

end LongTails.Proofs.GradientOnlyTests
