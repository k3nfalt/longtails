import LongTails.Proofs.MinimaxLmoStructure
import LongTails.Proofs.MinimaxLmoPath

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MinimaxLmo

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO constantMomentum)
open LongTails.Setups.MinimaxLmo (GeneralizedMinimax clip)
open OracleTemplate.NormBallLMO

section Step

variable {d : ℕ} {N : Seminorm ℝ (Space d)} {R ρ : ℝ} {lmo : Space d → Space d}

lemma lmo_inner_le (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0) (hρ : 0 < ρ)
    (hlmo : IsBallLMO N ρ lmo) (g m : Space d) :
    ⟪g, lmo m⟫ ≤ -(ρ * dualNorm N g) + 2 * ρ * dualNorm N (m - g) := by
  have h1 := lmo_dualNorm hρ hlmo m
  have h2 := inner_le_dualNorm_mul hR hdef (g - m) (lmo m)
  have h3 : N (lmo m) ≤ ρ := hlmo.feasible m
  have h4 : dualNorm N g ≤ dualNorm N m + dualNorm N (g - m) := dualNorm_sub_le hR g m
  have h5 : dualNorm N (g - m) = dualNorm N (m - g) := dualNorm_sub_comm hR g m
  have h6 := dualNorm_nonneg hR (g - m)
  have e : ⟪g, lmo m⟫ = ⟪m, lmo m⟫ + ⟪g - m, lmo m⟫ := by rw [inner_sub_left]; ring
  have h7 : dualNorm N (g - m) * N (lmo m) ≤ dualNorm N (g - m) * ρ := mul_le_mul_of_nonneg_left h3 h6
  nlinarith

end Step

section Pathwise

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N : Seminorm ℝ (Space d₁)} {R ρ : ℝ}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}
  {lmo : Space d₁ → Space d₁}

variable (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)
  (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
  (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
include H hμ hR hdef hL₀ hL₁ hρ hlmo

lemma lmo_step_descent {γ : ℝ} (hγ : 0 ≤ γ) (hloc : L₁ * ((1 + L₀ / μ) * (γ * ρ)) ≤ 1)
    (x m : Space d₁) :
    Phi H hμ (x + γ • lmo m) ≤ Phi H hμ x - γ * ρ * dualNorm N (gPhi H hμ x) +
      2 * (γ * ρ) * dualNorm N (m - gPhi H hμ x) +
      (1 + L₀ / μ) * (L₀ + L₁ * dualNorm N (gPhi H hμ x)) / 2 * (γ * ρ) ^ 2 := by
  have hN : N (γ • lmo m) ≤ γ * ρ := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left (hlmo.feasible m) hγ
  have hN0 := apply_nonneg N (γ • lmo m)
  have hK : 0 ≤ 1 + L₀ / μ := by have := div_nonneg hL₀ hμ.le; linarith
  have hloc' : L₁ * ((1 + L₀ / μ) * N (γ • lmo m)) ≤ 1 := by
    have : L₁ * ((1 + L₀ / μ) * N (γ • lmo m)) ≤ L₁ * ((1 + L₀ / μ) * (γ * ρ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN hK) hL₁
    linarith
  have hd := Phi_descent H hμ hR hdef hL₀ hL₁ x (γ • lmo m) hloc'
  have hi := lmo_inner_le hR hdef hρ hlmo (gPhi H hμ x) m
  rw [inner_smul_right] at hd
  have hcoef : 0 ≤ (1 + L₀ / μ) * (L₀ + L₁ * dualNorm N (gPhi H hμ x)) / 2 := by
    have := dualNorm_nonneg hR (gPhi H hμ x); positivity
  have hq : N (γ • lmo m) ^ 2 ≤ (γ * ρ) ^ 2 := pow_le_pow_left₀ hN0 hN 2
  have hq2 := mul_le_mul_of_nonneg_left hq hcoef
  have hi2 := mul_le_mul_of_nonneg_left hi hγ
  nlinarith

end Pathwise

section Recursions

lemma recursion_sum {a : ℝ} {u δ b : ℕ → ℝ}
    (hrec : ∀ k, u (k + 1) ≤ (1 - a) * (u k + δ k) + a * b (k + 1)) (n : ℕ) :
    a * ∑ k ∈ Finset.range n, u k + u n ≤ u 0 + ∑ j ∈ Finset.range n, ((1 - a) * δ j + a * b (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h := hrec n
      nlinarith

noncomputable def wt (a : ℝ) (k j : ℕ) : ℝ := if j = 0 then (1 - a) ^ k else a * (1 - a) ^ (k - j)

lemma wt_succ_sum {E : Type*} [AddCommGroup E] [Module ℝ E] (a : ℝ) (v : ℕ → E) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1 + 1), wt a (k + 1) j • v j =
      (1 - a) • ∑ j ∈ Finset.range (k + 1), wt a k j • v j + a • v (k + 1) := by
  rw [Finset.sum_range_succ, Finset.smul_sum]
  have hlast : wt a (k + 1) (k + 1) = a := by simp [wt]
  rw [hlast]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [← mul_smul]
  congr 1
  simp only [wt]
  split_ifs with h
  · rw [pow_succ]; ring
  · rw [show k + 1 - j = k - j + 1 by omega, pow_succ]; ring

end Recursions

section Error

variable {d : ℕ} {N : Seminorm ℝ (Space d)} {R : ℝ}

lemma dualNorm_smul_le (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) {c : ℝ} (hc : 0 ≤ c) (u : Space d) :
    dualNorm N (c • u) ≤ c * dualNorm N u := by
  refine dualNorm_le_of fun v hv => ?_
  rw [inner_smul_left, RCLike.conj_to_real]
  exact mul_le_mul_of_nonneg_left (inner_le_dualNorm hR u hv) hc

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N₁ : Seminorm ℝ (Space d₁)}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}
  (lmo : Space d₁ → Space d₁) (γ a β c : ℝ)

noncomputable def cpath (x₁ : Space d₁) (y₁ : Space d₂) (ox : Space d₁ → Space d₂ → Ω → Space d₁)
    (oy : Space d₁ → Space d₂ → Ω → Space d₂) (ξ : ℕ → Ω) : ℕ → Space d₁ × Space d₂ × Space d₁ :=
  gpath lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c) x₁ y₁ ox oy ξ

omit [MeasurableSpace Ω] in
lemma cpath_succ (ξ : ℕ → Ω) (k : ℕ) :
    cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1) =
      ((cpath lmo γ a β c x₁ y₁ ox oy ξ k).1 + γ • lmo (constantMomentum a (k + 1) •
          ox (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1 (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 (ξ k) +
          (1 - constantMomentum a (k + 1)) • (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.2),
        (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 + β • clip c
          (oy (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1 (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 (ξ k)),
        constantMomentum a (k + 1) • ox (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1
          (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 (ξ k) +
          (1 - constantMomentum a (k + 1)) • (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.2) := rfl

noncomputable def xNoise (x₁ : Space d₁) (y₁ : Space d₂) (gx : Space d₁ → Space d₂ → Space d₁)
    (ox : Space d₁ → Space d₂ → Ω → Space d₁) (oy : Space d₁ → Space d₂ → Ω → Space d₂)
    (ξ : ℕ → Ω) (k : ℕ) : Space d₁ :=
  ox (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1 (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 (ξ k) -
    gx (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1 (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1

noncomputable def noiseSum (x₁ : Space d₁) (y₁ : Space d₂) (gx : Space d₁ → Space d₂ → Space d₁)
    (ox : Space d₁ → Space d₂ → Ω → Space d₁) (oy : Space d₁ → Space d₂ → Ω → Space d₂)
    (ξ : ℕ → Ω) (k : ℕ) : Space d₁ :=
  ∑ j ∈ Finset.range (k + 1), wt a k j • xNoise lmo γ a β c x₁ y₁ gx ox oy ξ j

variable (H : GeneralizedMinimax N₁ L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)

noncomputable def mErr (ξ : ℕ → Ω) (k : ℕ) : Space d₁ :=
  (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).2.2 - gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1

noncomputable def xBias (ξ : ℕ → Ω) (k : ℕ) : Space d₁ :=
  gx (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1 (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 -
    gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1

lemma mErr_zero (ξ : ℕ → Ω) :
    mErr lmo γ a β c H hμ ξ 0 - noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ 0 = xBias lmo γ a β c H hμ ξ 0 := by
  simp only [mErr, noiseSum, xNoise, xBias, cpath_succ, constantMomentum, wt]
  rw [zero_add, Finset.sum_range_one]
  simp only [ite_true, one_smul, sub_self, zero_smul, add_zero, pow_zero]
  abel

lemma mErr_succ (ξ : ℕ → Ω) (k : ℕ) :
    mErr lmo γ a β c H hμ ξ (k + 1) - noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ (k + 1) =
      (1 - a) • ((mErr lmo γ a β c H hμ ξ k - noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k) +
        (gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1 -
          gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).1)) +
      a • xBias lmo γ a β c H hμ ξ (k + 1) := by
  have hc : constantMomentum a (k + 1 + 1) = a := by simp [constantMomentum]
  have hZ := wt_succ_sum a (xNoise lmo γ a β c x₁ y₁ gx ox oy ξ) k
  simp only [noiseSum]
  rw [hZ]
  simp only [mErr, xNoise, xBias]
  rw [cpath_succ lmo γ a β c ξ (k + 1), hc]
  simp only
  module

end Error

section Sum

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N : Seminorm ℝ (Space d₁)} {R ρ ζ : ℝ}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}
  {lmo : Space d₁ → Space d₁}

variable (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)
  (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
  (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo) (hζ : ∀ u, dualNorm N u ≤ ζ * ‖u‖)
include H hμ hR hdef hL₀ hL₁ hρ hlmo hζ

theorem pathwise_sum {γ a β c : ℝ} (hγ : 0 ≤ γ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hloc : L₁ * ((1 + L₀ / μ) * (γ * ρ)) ≤ 1) (ξ : ℕ → Ω) (n : ℕ) :
    γ * ρ * ∑ k ∈ Finset.range n, dualNorm N (gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1) ≤
      Phi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ 0).1 - Phi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ n).1 +
      2 * (γ * ρ) / a * (dualNorm N (xBias lmo γ a β c H hμ ξ 0) +
        ∑ j ∈ Finset.range n, ((1 + L₀ / μ) *
          (L₀ + L₁ * dualNorm N (gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ j).1)) * (γ * ρ) +
          a * dualNorm N (xBias lmo γ a β c H hμ ξ (j + 1)))) +
      2 * (γ * ρ) * ζ * ∑ k ∈ Finset.range n, ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖ +
      ∑ k ∈ Finset.range n, (1 + L₀ / μ) *
        (L₀ + L₁ * dualNorm N (gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1)) / 2 * (γ * ρ) ^ 2 := by
  set X : ℕ → Space d₁ := fun k => (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1
  set G : ℕ → ℝ := fun k => dualNorm N (gPhi H hμ (X k))
  set u : ℕ → ℝ := fun k => dualNorm N (mErr lmo γ a β c H hμ ξ k - noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k)
  set s := γ * ρ
  have hs : 0 ≤ s := mul_nonneg hγ hρ.le
  have hK : 1 ≤ 1 + L₀ / μ := by have := div_nonneg hL₀ hμ.le; linarith
  have hstep : ∀ k, X (k + 1) = X k + γ • lmo (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).2.2 := by
    intro k; simp only [X, cpath_succ]
  have hmove : ∀ k, N (X (k + 1) - X k) ≤ s := by
    intro k
    rw [hstep k, add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left (hlmo.feasible _) hγ
  have hdelta : ∀ k, dualNorm N (gPhi H hμ (X k) - gPhi H hμ (X (k + 1))) ≤
      (1 + L₀ / μ) * (L₀ + L₁ * G k) * s := by
    intro k
    have hl : L₁ * ((1 + L₀ / μ) * N (X (k + 1) - X k)) ≤ 1 := by
      have : L₁ * ((1 + L₀ / μ) * N (X (k + 1) - X k)) ≤ L₁ * ((1 + L₀ / μ) * s) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmove k) (by linarith)) hL₁
      linarith
    have h := gPhi_smooth H hμ hR hL₀ hL₁ hK (X k) (X (k + 1)) hl
    rw [dualNorm_sub_comm hR]
    have hG : 0 ≤ (1 + L₀ / μ) * (L₀ + L₁ * G k) := by
      have := dualNorm_nonneg hR (gPhi H hμ (X k)); positivity
    exact h.trans (mul_le_mul_of_nonneg_left (hmove k) hG)
  have hdesc : ∀ k, Phi H hμ (X (k + 1)) ≤ Phi H hμ (X k) - s * G k + 2 * s * (u k +
      ζ * ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖) + (1 + L₀ / μ) * (L₀ + L₁ * G k) / 2 * s ^ 2 := by
    intro k
    have h := lmo_step_descent H hμ hR hdef hL₀ hL₁ hρ hlmo hγ hloc (X k)
      (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).2.2
    rw [← hstep k] at h
    have he : dualNorm N ((cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).2.2 - gPhi H hμ (X k)) ≤
        u k + ζ * ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖ := by
      have e : (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).2.2 - gPhi H hμ (X k) =
          (mErr lmo γ a β c H hμ ξ k - noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k) +
            noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k := by simp only [mErr, X]; abel
      rw [e]
      exact (dualNorm_add_le hR _ _).trans (add_le_add le_rfl (hζ _))
    have h2 := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 * s)
    simp only [G, s] at h ⊢
    linarith
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => hdesc k
  have hrec : ∀ k, u (k + 1) ≤ (1 - a) * (u k + dualNorm N (gPhi H hμ (X k) - gPhi H hμ (X (k + 1)))) +
      a * dualNorm N (xBias lmo γ a β c H hμ ξ (k + 1)) := by
    intro k
    simp only [u]
    rw [mErr_succ lmo γ a β c H hμ ξ k]
    refine (dualNorm_add_le hR _ _).trans (add_le_add ?_ (dualNorm_smul_le hR ha0.le _))
    exact (dualNorm_smul_le hR (by linarith) _).trans
      (mul_le_mul_of_nonneg_left (dualNorm_add_le hR _ _) (by linarith))
  have hrs := recursion_sum (a := a) (u := u)
    (δ := fun k => dualNorm N (gPhi H hμ (X k) - gPhi H hμ (X (k + 1))))
    (b := fun k => dualNorm N (xBias lmo γ a β c H hμ ξ k)) hrec n
  have hu0 : u 0 = dualNorm N (xBias lmo γ a β c H hμ ξ 0) := by
    simp only [u]; rw [mErr_zero lmo γ a β c H hμ ξ]
  have hun : 0 ≤ u n := dualNorm_nonneg hR _
  have hbound : ∑ j ∈ Finset.range n, ((1 - a) * dualNorm N (gPhi H hμ (X j) - gPhi H hμ (X (j + 1))) +
      a * dualNorm N (xBias lmo γ a β c H hμ ξ (j + 1))) ≤
      ∑ j ∈ Finset.range n, ((1 + L₀ / μ) * (L₀ + L₁ * G j) * s +
        a * dualNorm N (xBias lmo γ a β c H hμ ξ (j + 1))) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := hdelta j
    have h2 := dualNorm_nonneg hR (gPhi H hμ (X j) - gPhi H hμ (X (j + 1)))
    have h3 : (1 - a) * dualNorm N (gPhi H hμ (X j) - gPhi H hμ (X (j + 1))) ≤
        dualNorm N (gPhi H hμ (X j) - gPhi H hμ (X (j + 1))) := by nlinarith
    linarith
  have hu_sum : ∑ k ∈ Finset.range n, u k ≤ (1 / a) * (dualNorm N (xBias lmo γ a β c H hμ ξ 0) +
      ∑ j ∈ Finset.range n, ((1 + L₀ / μ) * (L₀ + L₁ * G j) * s +
        a * dualNorm N (xBias lmo γ a β c H hμ ξ (j + 1)))) := by
    rw [hu0] at hrs
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha0]
    linarith
  have hsplit : ∑ k ∈ Finset.range n, (Phi H hμ (X k) - s * G k + 2 * s * (u k +
      ζ * ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖) + (1 + L₀ / μ) * (L₀ + L₁ * G k) / 2 * s ^ 2) =
      ∑ k ∈ Finset.range n, Phi H hμ (X k) - s * ∑ k ∈ Finset.range n, G k +
        2 * s * ∑ k ∈ Finset.range n, u k +
        2 * s * ζ * ∑ k ∈ Finset.range n, ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖ +
        ∑ k ∈ Finset.range n, (1 + L₀ / μ) * (L₀ + L₁ * G k) / 2 * s ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_add]
    ring
  have hfin := mul_le_mul_of_nonneg_left hu_sum (by positivity : (0 : ℝ) ≤ 2 * s)
  have e2 : 2 * s * ((1 / a) * (dualNorm N (xBias lmo γ a β c H hμ ξ 0) +
      ∑ j ∈ Finset.range n, ((1 + L₀ / μ) * (L₀ + L₁ * G j) * s +
        a * dualNorm N (xBias lmo γ a β c H hμ ξ (j + 1))))) =
      2 * s / a * (dualNorm N (xBias lmo γ a β c H hμ ξ 0) +
      ∑ j ∈ Finset.range n, ((1 + L₀ / μ) * (L₀ + L₁ * G j) * s +
        a * dualNorm N (xBias lmo γ a β c H hμ ξ (j + 1)))) := by ring
  rw [hsplit] at hsum
  have hsum2 : ∑ k ∈ Finset.range n, Phi H hμ (X (k + 1)) - ∑ k ∈ Finset.range n, Phi H hμ (X k) =
      Phi H hμ (X n) - Phi H hμ (X 0) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => Phi H hμ (X k)) n]
  simp only [X, G, s] at hsum hsum2 hfin e2 ⊢
  linarith

end Sum

end OracleTemplate.MinimaxLmo
