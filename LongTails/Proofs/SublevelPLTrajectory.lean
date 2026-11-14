import LongTails.Proofs.SublevelPLDeterministic

open scoped RealInnerProductSpace

namespace OracleTemplate.SublevelRobustGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Hyp (f : E → ℝ) (m L τ α : ℝ) (x0 : E) : Prop where
  hL : 0 < L
  hτ : 0 < τ
  hα1 : 1 ≤ α
  hα2 : α < 2
  hg : ∀ x, HasGradientAt f (gradient f x) x
  hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  hm : ∀ x, m ≤ f x
  hpl : ∀ x, f x ≤ f x0 → f x - m ≤ τ * ‖gradient f x‖ ^ α

lemma step_increase {f : E → ℝ} {m L τ α : ℝ} {x0 : E} (H : Hyp f m L τ α x0) (x v : E) :
    f (x - (1 / L) • v) ≤ f x + ‖v - gradient f x‖ ^ 2 / (2 * L) := by
  have h := pathwise_descent H.hL H.hg H.hlip x v
  have hn : 0 ≤ ‖gradient f x‖ ^ 2 / (2 * L) := by
    have := H.hL
    positivity
  have he : (‖gradient f x‖ ^ 2 - ‖v - gradient f x‖ ^ 2) / (2 * L) =
      ‖gradient f x‖ ^ 2 / (2 * L) - ‖v - gradient f x‖ ^ 2 / (2 * L) := by ring
  linarith

lemma telescope_increase {f : E → ℝ} {m L τ α : ℝ} {x0 : E} (H : Hyp f m L τ α x0)
    (x v : ℕ → E) (hx : ∀ j, x (j + 1) = x j - (1 / L) • v j) (j0 : ℕ) :
    ∀ n, f (x (j0 + n)) ≤ f (x j0) +
      (∑ j ∈ Finset.range n, ‖v (j0 + j) - gradient f (x (j0 + j))‖ ^ 2) / (2 * L)
  | 0 => by simp
  | n + 1 => by
    have ih := telescope_increase H x v hx j0 n
    have hs := step_increase H (x (j0 + n)) (v (j0 + n))
    rw [← hx] at hs
    rw [Finset.sum_range_succ, add_div, show j0 + (n + 1) = j0 + n + 1 by ring]
    linarith

lemma gradient_lower {f : E → ℝ} {m L τ α : ℝ} {x0 : E} (H : Hyp f m L τ α x0)
    {x : E} (hx : f x ≤ f x0) {g : ℝ} (hg0 : 0 < g) (hgap : g ≤ f x - m) :
    (g / τ) ^ (2 / α) ≤ ‖gradient f x‖ ^ 2 := by
  have hpl := H.hpl x hx
  have hα0 : 0 < α := by linarith [H.hα1]
  have hτ := H.hτ
  have h1 : g / τ ≤ ‖gradient f x‖ ^ α := by
    rw [div_le_iff₀ hτ]
    linarith
  have h2 : (g / τ) ^ (2 / α) ≤ (‖gradient f x‖ ^ α) ^ (2 / α) :=
    Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have h3 : (‖gradient f x‖ ^ α) ^ (2 / α) = ‖gradient f x‖ ^ 2 := by
    rw [← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hα0.ne', Real.rpow_two]
  linarith

lemma descend_step {f : E → ℝ} {m L τ α ν ε' : ℝ} {x0 : E} (H : Hyp f m L τ α x0)
    (hε' : 0 < ε') (hν : ν ≤ (ε' / τ) ^ (2 / α) / 8) (x v : E)
    (hx : f x ≤ f x0) (hgap : 2 * ε' ≤ f x - m) (he : ‖v - gradient f x‖ ^ 2 ≤ ν) :
    f (x - (1 / L) • v) - m ≤ (f x - m) - 7 / (16 * L) * τ ^ (-(2 / α)) * (f x - m) ^ (2 / α) ∧
      f (x - (1 / L) • v) ≤ f x := by
  have hL := H.hL
  have hτ := H.hτ
  have hα0 : 0 < α := by linarith [H.hα1]
  have hd := pathwise_descent H.hL H.hg H.hlip x v
  have hgl := gradient_lower H hx (by linarith : 0 < f x - m) le_rfl
  have hgl2 := gradient_lower H hx (by linarith : 0 < 2 * ε') hgap
  have hmono : (ε' / τ) ^ (2 / α) ≤ (2 * ε' / τ) ^ (2 / α) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [div_le_div_iff_of_pos_right hτ]
    linarith
  have hν' : 8 * ν ≤ ‖gradient f x‖ ^ 2 := by
    have : 8 * ν ≤ (ε' / τ) ^ (2 / α) := by linarith
    linarith
  have hpow : (f x - m) ^ (2 / α) = ((f x - m) / τ) ^ (2 / α) * τ ^ (2 / α) := by
    rw [Real.div_rpow (by linarith) hτ.le]
    have : 0 < τ ^ (2 / α) := Real.rpow_pos_of_pos hτ _
    field_simp
  have hτn : τ ^ (-(2 / α)) = (τ ^ (2 / α))⁻¹ := Real.rpow_neg hτ.le _
  have hτp : 0 < τ ^ (2 / α) := Real.rpow_pos_of_pos hτ _
  have hkey : 7 / (16 * L) * τ ^ (-(2 / α)) * (f x - m) ^ (2 / α) ≤
      (‖gradient f x‖ ^ 2 - ‖v - gradient f x‖ ^ 2) / (2 * L) := by
    rw [hpow, hτn]
    have h1 : 7 / (16 * L) * (τ ^ (2 / α))⁻¹ * (((f x - m) / τ) ^ (2 / α) * τ ^ (2 / α)) =
        7 / (16 * L) * ((f x - m) / τ) ^ (2 / α) := by
      field_simp
    rw [h1]
    have h2 : 7 / (16 * L) * ((f x - m) / τ) ^ (2 / α) ≤ 7 / (16 * L) * ‖gradient f x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hgl (by positivity)
    have h3 : 7 / (16 * L) * ‖gradient f x‖ ^ 2 ≤
        (‖gradient f x‖ ^ 2 - ‖v - gradient f x‖ ^ 2) / (2 * L) := by
      have he8 : 8 * ‖v - gradient f x‖ ^ 2 ≤ ‖gradient f x‖ ^ 2 := by linarith
      rw [show 7 / (16 * L) * ‖gradient f x‖ ^ 2 = (7 / 8 * ‖gradient f x‖ ^ 2) / (2 * L) by
        field_simp; ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    linarith
  constructor
  · linarith
  · have : 0 ≤ 7 / (16 * L) * τ ^ (-(2 / α)) * (f x - m) ^ (2 / α) := by
      rw [hτn]
      have : 0 ≤ (f x - m) ^ (2 / α) := Real.rpow_nonneg (by linarith) _
      positivity
    linarith

lemma good_trajectory {f : E → ℝ} {m L τ α ν ε' : ℝ} {x0 : E} (H : Hyp f m L τ α x0)
    (hε' : 0 < ε') (hν : ν ≤ (ε' / τ) ^ (2 / α) / 8) (K : ℕ)
    (hKν : (K : ℝ) * ν / (2 * L) ≤ ε' / 4)
    (hK : 32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * ε' ^ (-(2 - α) / α) ≤ K)
    (x v : ℕ → E) (hx0 : x 0 = x0) (hx : ∀ j, x (j + 1) = x j - (1 / L) • v j)
    (hgood : ∀ j, j < K → ‖v j - gradient f (x j)‖ ^ 2 ≤ ν) :
    f (x K) - m ≤ 9 / 4 * ε' := by
  classical
  have hL := H.hL
  have hτ := H.hτ
  have hα0 : 0 < α := by linarith [H.hα1]
  have hν0 : 0 ≤ ν := by
    have := hgood
    by_cases hK0 : 0 < K
    · exact (sq_nonneg _).trans (hgood 0 hK0)
    · have hK0' : K = 0 := by omega
      subst hK0'
      simp only [Nat.cast_zero] at hK
      have : 0 < 32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * ε' ^ (-(2 - α) / α) := by
        have h2α : 0 < 2 - α := by linarith [H.hα2]
        positivity
      linarith
  by_cases hcase : ∀ j, j ≤ K → 2 * ε' ≤ f (x j) - m
  · exfalso
    have hdesc : ∀ k, k ≤ K → f (x k) ≤ f x0 ∧
        (∀ j, j < k → f (x (j + 1)) - m ≤ (f (x j) - m) -
          7 / (16 * L) * τ ^ (-(2 / α)) * (f (x j) - m) ^ (2 / α)) := by
      intro k
      induction k with
      | zero => intro _; exact ⟨by rw [hx0], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      | succ k ih =>
        intro hk
        obtain ⟨hin, hrec⟩ := ih (by omega)
        have hs := descend_step H hε' hν (x k) (v k) hin (hcase k (by omega))
          (hgood k (by omega))
        rw [← hx] at hs
        refine ⟨hs.2.trans hin, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact hrec j hj
        · subst hj; exact hs.1
    obtain ⟨_, hrec⟩ := hdesc K le_rfl
    have hc : 0 < 7 / (16 * L) * τ ^ (-(2 / α)) := by
      have : 0 < τ ^ (-(2 / α)) := Real.rpow_pos_of_pos hτ _
      positivity
    have hp1 : 1 < 2 / α := by
      rw [lt_div_iff₀ hα0]; linarith [H.hα2]
    have hp2 : 2 / α ≤ 2 := by
      rw [div_le_iff₀ hα0]; linarith [H.hα1]
    have hsum := recursion_sum hc hp1 hp2 (fun j => f (x j) - m) K
      (fun j hj => by have := hcase j hj; linarith) hrec
    have hgK : 2 * ε' ≤ f (x K) - m := hcase K le_rfl
    have hmono : (f (x K) - m) ^ (-(2 / α - 1)) ≤ (2 * ε') ^ (-(2 / α - 1)) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) hgK
      linarith
    exact contradiction_of_large_K hL hτ H.hα1 H.hα2 hε' hK (hsum.trans hmono)
  · simp only [not_forall, not_le, exists_prop] at hcase
    obtain ⟨j0, hj0K, hj0⟩ := hcase
    obtain ⟨n, rfl⟩ : ∃ n, K = j0 + n := ⟨K - j0, by omega⟩
    have ht := telescope_increase H x v hx j0 n
    have hsum : (∑ j ∈ Finset.range n, ‖v (j0 + j) - gradient f (x (j0 + j))‖ ^ 2) ≤ n * ν := by
      calc (∑ j ∈ Finset.range n, ‖v (j0 + j) - gradient f (x (j0 + j))‖ ^ 2)
          ≤ ∑ j ∈ Finset.range n, ν := by
            apply Finset.sum_le_sum
            intro j hj
            exact hgood (j0 + j) (by simp at hj; omega)
        _ = n * ν := by simp
    have hnK : (n : ℝ) ≤ (j0 + n : ℕ) := by exact_mod_cast Nat.le_add_left n j0
    have h1 : (∑ j ∈ Finset.range n, ‖v (j0 + j) - gradient f (x (j0 + j))‖ ^ 2) / (2 * L) ≤
        ε' / 4 := by
      calc _ ≤ (n * ν) / (2 * L) := div_le_div_of_nonneg_right hsum (by positivity)
        _ ≤ ((j0 + n : ℕ) : ℝ) * ν / (2 * L) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hnK hν0
        _ ≤ ε' / 4 := hKν
    linarith

lemma failure_bound {f : E → ℝ} {m L τ α : ℝ} {x0 : E} (H : Hyp f m L τ α x0) (K : ℕ)
    (x v : ℕ → E) (hx0 : x 0 = x0) (hx : ∀ j, x (j + 1) = x j - (1 / L) • v j) :
    f (x K) - m ≤ (f x0 - m) +
      (∑ j ∈ Finset.range K, ‖v j - gradient f (x j)‖ ^ 2) / (2 * L) := by
  have ht := telescope_increase H x v hx 0 K
  simp only [zero_add] at ht
  rw [hx0] at ht
  linarith

end OracleTemplate.SublevelRobustGradient
