import LongTails.Setups.HighDimensionalSharpLipschitzConvex
import LongTails.Proofs.SharpChainSharpness
import LongTails.Proofs.SharpChainHiding
import LongTails.Proofs.Execution
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SharpChainLowerBound

open LongTails.Setups.SharpLipschitzConvex MintyChainGeometry SharpChainGeometry
open SharpChainInstance SharpChainMargins SharpChainSharpness

section Generic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma convexOn_of_subgradient (f : F → ℝ) (g : F → F) (h : ∀ x y, f x + ⟪g x, y - x⟫ ≤ f y) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1 := h (a • x + b • y) x
  have h2 := h (a • x + b • y) y
  have e : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
    have : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) =
        (a • x + b • y) - (a + b) • (a • x + b • y) := by
      rw [add_smul]
      simp only [smul_sub]
      abel
    rw [this, hab, one_smul, sub_self]
  have hi : ⟪g (a • x + b • y), a • (x - (a • x + b • y)) + b • (y - (a • x + b • y))⟫ =
      a * ⟪g (a • x + b • y), x - (a • x + b • y)⟫ +
        b * ⟪g (a • x + b • y), y - (a • x + b • y)⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [e, inner_zero_right] at hi
  have hf : f (a • x + b • y) = a * f (a • x + b • y) + b * f (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end Generic

section Instance

variable (p : Params) {k : ℕ} (μ0 c : ℝ) (π : Fin (k + 1) ↪ Fin p.d)

noncomputable def hardFun (x : EuclideanSpace ℝ (Fin p.d)) : ℝ :=
  c * hardValue μ0 p.D π (x - p.x0)

noncomputable def hardGrad (x : EuclideanSpace ℝ (Fin p.d)) : EuclideanSpace ℝ (Fin p.d) :=
  c • (answer μ0 p.D π (x - p.x0)).2

noncomputable def hardOracle : Oracle (EuclideanSpace ℝ (Fin p.d)) (ℝ × EuclideanSpace ℝ (Fin p.d)) where
  answer _ q _ := (hardFun p μ0 c π q.2, hardGrad p μ0 c π q.2)

lemma hardFun_subgradient (hc : 0 ≤ c) (hμ : 0 ≤ μ0) (hμ0 : μ0 ^ 2 < 1) (hD : 0 < p.D)
    (x y : EuclideanSpace ℝ (Fin p.d)) :
    hardFun p μ0 c π x + ⟪hardGrad p μ0 c π x, y - x⟫ ≤ hardFun p μ0 c π y := by
  have h := answer_subgradient μ0 p.D π (x - p.x0) hμ hμ0 hD (y - p.x0)
  rw [sub_sub_sub_cancel_right] at h
  unfold hardFun hardGrad
  rw [real_inner_smul_left]
  nlinarith [mul_le_mul_of_nonneg_left h hc]

lemma hardFun_nonneg (hc : 0 ≤ c) (hμ : 0 ≤ μ0) (x : EuclideanSpace ℝ (Fin p.d)) :
    0 ≤ hardFun p μ0 c π x :=
  mul_nonneg hc (hard_nonneg μ0 p.D π hμ _)

lemma hardFun_target (hμ : 0 ≤ μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < p.D) :
    hardFun p μ0 c π (p.x0 + hardTarget μ0 p.D π) = 0 := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  unfold hardFun
  rw [add_sub_cancel_left, hard_zero_of μ0 p.D π hμ hμ1 hD _ (hardTarget_apply μ0 p.D π)
    (by rw [hardTarget_norm μ0 p.D π hμ0 hD]; linarith), mul_zero]

lemma hard_admissible (hc : 0 < c) (hμ : 0 < μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < p.D)
    (hL : 3 * c = p.L) (hμc : c * (μ0 / 16) = p.μ) :
    spec.admissible p (hardFun p μ0 c π) (hardOracle p μ0 c π) := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  have hsub := hardFun_subgradient p μ0 c π hc.le hμ.le hμ0 hD
  have hG : ∀ x, ‖hardGrad p μ0 c π x‖ ≤ p.L := by
    intro x
    unfold hardGrad
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← hL]
    have := answer_norm μ0 p.D π (x - p.x0) hμ.le (by linarith) hμ0 hD
    nlinarith
  refine ⟨convexOn_of_subgradient _ _ hsub, ?_, ⟨p.x0 + hardTarget μ0 p.D π, ?_, ?_⟩, ?_,
    ⟨hardGrad p μ0 c π, hsub, fun _ _ _ => rfl⟩⟩
  · intro x y
    have h1 := lipschitz_of_subgradient _ _ p.L hsub hG x y
    have h2 := lipschitz_of_subgradient _ _ p.L hsub hG y x
    rw [norm_sub_rev y x] at h1
    rw [abs_le]
    constructor <;> linarith
  · refine isMinOn_univ_iff.mpr fun y => ?_
    rw [hardFun_target p μ0 c π hμ.le hμ1 hD]
    exact hardFun_nonneg p μ0 c π hc.le hμ.le y
  · have e : p.x0 - (p.x0 + hardTarget μ0 p.D π) = -hardTarget μ0 p.D π := by abel
    rw [e, norm_neg, hardTarget_norm μ0 p.D π hμ0 hD]
  · intro x
    obtain ⟨z, hz, hs⟩ := hard_sharp μ0 p.D π hμ hμ1 hD (x - p.x0)
    refine ⟨p.x0 + z, ?_, ?_⟩
    · refine isMinOn_univ_iff.mpr fun y => ?_
      unfold hardFun
      rw [add_sub_cancel_left]
      exact mul_le_mul_of_nonneg_left (isMinOn_univ_iff.mp hz (y - p.x0)) hc.le
    · unfold hardFun
      rw [add_sub_cancel_left]
      have e : x - (p.x0 + z) = x - p.x0 - z := by abel
      rw [e, ← hμc]
      have := mul_le_mul_of_nonneg_left hs hc.le
      nlinarith

lemma execute_hard (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (ℝ × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) (N : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (hardOracle p μ0 c π) A (fun _ => N) seed ξ =
      A.output ((fun s => A.update s (hardFun p μ0 c π (A.query s).2,
        hardGrad p μ0 c π (A.query s).2))^[N] (A.initial seed)) := by
  rw [OracleTemplate.execute_eq_of_answer_eq (hardOracle p μ0 c π)
    (fun x => (hardFun p μ0 c π x, hardGrad p μ0 c π x)) (fun _ _ _ => rfl)]
  exact OracleTemplate.execute_iterate (fun x => (hardFun p μ0 c π x, hardGrad p μ0 c π x)) A N seed

end Instance

section Loss

variable {d k : ℕ} (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d)

lemma coordinate_le_lift (a : Fin (k + 1) → ℝ) (j : Fin (k + 1)) : |a j| ≤ ‖lift π a‖ := by
  have h := PiLp.norm_apply_le (lift π a) (π j)
  rw [lift_apply, Real.norm_eq_abs] at h
  exact h

lemma good_loss (hμ : 0 < μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) (u : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ ≤ 8 * D → |u (π (Fin.last k))| ≤ threshold μ0 D k) :
    μ0 * gap μ0 D k / 4 ≤ hardValue μ0 D π u := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  have hg := gap_pos μ0 D hμ0 hD k
  have hg0 : gap μ0 D k ≤ D := by
    have := gap_anti μ0 D hμ0 hD (Nat.zero_le k)
    unfold gap at this ⊢
    simpa using this
  by_cases hf : 8 * D < ‖u‖
  · have h := coneVal_le_hard μ0 D π u
    unfold coneVal at h
    nlinarith [mul_le_mul_of_nonneg_left hg0 hμ.le, mul_le_mul_of_nonneg_right hμ1 hD.le]
  · have hs := hu (not_lt.mp hf)
    have hk1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
      have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      nlinarith
    have hθ : threshold μ0 D k ≤ gap μ0 D k / 2 := by
      unfold threshold
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hk1 hg.le, mul_le_mul_of_nonneg_right hμ1 hg.le]
    have hr := radialVal_le_hard μ0 D π u
    unfold radialVal at hr
    have hc := coordinate_le_lift π (dev μ0 D π u) (Fin.last k)
    have ht : tgt μ0 D (Fin.last k) = -gap μ0 D k := by
      unfold tgt tgtN
      simp
    have hdev : dev μ0 D π u (Fin.last k) = u (π (Fin.last k)) + gap μ0 D k := by
      unfold dev
      rw [ht]
      ring
    rw [hdev] at hc
    have habs := abs_le.mp hs
    have h3 : gap μ0 D k / 2 ≤ |u (π (Fin.last k)) + gap μ0 D k| := by
      rw [abs_of_pos (by linarith)]
      linarith
    nlinarith

end Loss

section Budget

lemma one_sub_ge_exp (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) : Real.exp (-(2 * x)) ≤ 1 - x := by
  have h := Real.add_one_le_exp (2 * x)
  have hp : 0 < Real.exp (2 * x) := Real.exp_pos _
  have he : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h1 : 1 ≤ (1 - x) * Real.exp (2 * x) := by
    nlinarith [mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 1 - x by linarith),
      mul_nonneg hx (show (0 : ℝ) ≤ 1 - 2 * x by linarith)]
  nlinarith [Real.exp_pos (-(2 * x))]

lemma pow_lower (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) (k : ℕ) :
    Real.exp (-(2 * x * k)) ≤ (1 - x) ^ k := by
  have h : Real.exp (-(2 * x * k)) = Real.exp (-(2 * x)) ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (one_sub_ge_exp x hx hx2) k

lemma gap_lower (μ0 D μ ε : ℝ) (k : ℕ) (hμ0 : 0 ≤ μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D)
    (hμ : 0 < μ) (hε : 0 < ε) (hεD : ε ≤ μ * D)
    (hk : μ0 ^ 2 * k ≤ (1 + Real.log (μ * D / ε)) / 2) : ε / (2 * μ) ≤ gap μ0 D k := by
  have hy : 0 < μ * D / ε := by positivity
  have hp := pow_lower (μ0 ^ 2) (sq_nonneg _) (by nlinarith) k
  have he : Real.exp (-(1 + Real.log (μ * D / ε))) = ε / (Real.exp 1 * (μ * D)) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hy]
    field_simp
  have hm : Real.exp (-(1 + Real.log (μ * D / ε))) ≤ Real.exp (-(2 * μ0 ^ 2 * k)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [he] at hm
  have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have key : ε * Real.exp 1 ≤ 4 * (μ * D) := by
    nlinarith [mul_le_mul_of_nonneg_left he3 hε.le]
  have hsq : (ε / (2 * μ * D)) ^ 2 ≤ ε / (Real.exp 1 * (μ * D)) := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left key (mul_nonneg hε.le (mul_nonneg hμ.le hD.le))]
  have hq : ε / (2 * μ * D) ≤ Real.sqrt ((1 - μ0 ^ 2) ^ k) :=
    Real.le_sqrt_of_sq_le (hsq.trans (hm.trans hp))
  unfold gap
  have e : ε / (2 * μ) = D * (ε / (2 * μ * D)) := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hq hD.le

lemma size_bound (L D ε θ K : ℝ) (hL : 0 < L) (hD : 0 < D) (hε : 0 < ε) (hK : 1 ≤ K)
    (hθ : 3 * ε / (4 * L * K ^ 2) ≤ θ) :
    4 * K ^ 2 * ((8 * D) ^ 2 / θ ^ 2) ≤ 456 * K ^ 6 * (L * D / ε) ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hl : 0 < 3 * ε / (4 * L * K ^ 2) := by positivity
  have h1 : (8 * D) ^ 2 / θ ^ 2 ≤ (8 * D) ^ 2 / (3 * ε / (4 * L * K ^ 2)) ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hl 2) (pow_le_pow_left₀ hl.le hθ 2)
  have h2 : (8 * D) ^ 2 / (3 * ε / (4 * L * K ^ 2)) ^ 2 = 1024 / 9 * K ^ 4 * (L * D / ε) ^ 2 := by
    field_simp
    ring
  rw [h2] at h1
  have h3 : 4 * K ^ 2 * ((8 * D) ^ 2 / θ ^ 2) ≤ 4 * K ^ 2 * (1024 / 9 * K ^ 4 * (L * D / ε) ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 4 * K ^ 2 * (1024 / 9 * K ^ 4 * (L * D / ε) ^ 2) ≤ 456 * K ^ 6 * (L * D / ε) ^ 2 := by
    have : 0 ≤ K ^ 6 * (L * D / ε) ^ 2 := by positivity
    nlinarith
  linarith

lemma dim_aux (K M Q X d : ℝ) (hK : 1 ≤ K) (hM : K ≤ M) (hQ : 1 ≤ Q)
    (hs : X ≤ 456 * K ^ 6 * Q) (hdim : 2 ^ 10 * M ^ 6 * Q ≤ d) : X + K ≤ d := by
  have hM1 : 1 ≤ M := hK.trans hM
  have hK6 : K ^ 6 ≤ M ^ 6 := pow_le_pow_left₀ (by linarith) hM 6
  have hM6 : M ≤ M ^ 6 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 6 := pow_le_pow_right₀ hM1 (by norm_num)
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : K ^ 6 * Q ≤ M ^ 6 * Q := mul_le_mul_of_nonneg_right hK6 hQ0
  have h2 : M ^ 6 * 1 ≤ M ^ 6 * Q := mul_le_mul_of_nonneg_left hQ (by positivity)
  have h3 : 0 ≤ M ^ 6 * Q := mul_nonneg (by positivity) hQ0
  linarith only [hs, h1, h2, h3, hdim, hM, hM6]

end Budget

set_option maxHeartbeats 400000 in
lemma exists_failure (p : Params)
    (hp : LongTails.Setups.HighDimensionalSharpLipschitzConvex.spec.valid p) (N : ℕ)
    (hN : N ≤ ⌊(p.L / p.μ) ^ 2 * (1 + Real.log (p.μ * p.D / p.ε)) / 4608⌋₊)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (ℝ × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (ℝ × EuclideanSpace ℝ (Fin p.d))),
      LongTails.Setups.SharpLipschitzConvex.spec.admissible p f O ∧
        ¬ LongTails.Setups.SharpLipschitzConvex.spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hμ, hLμ, hD, hε, hεD, hdim⟩ := hp
  have hL : 0 < p.L := by linarith
  set μ0 := 48 * p.μ / p.L with hμ0def
  set c := p.L / 3 with hcdef
  have hμ0 : 0 < μ0 := by positivity
  have hμ1 : μ0 ≤ 1 / 2 := by
    rw [hμ0def, div_le_iff₀ hL]
    linarith
  have hc : 0 < c := by positivity
  have hLc : 3 * c = p.L := by rw [hcdef]; ring
  have hμc : c * (μ0 / 16) = p.μ := by
    rw [hcdef, hμ0def]
    field_simp
    ring
  have hy : 1 ≤ p.μ * p.D / p.ε := by rw [le_div_iff₀ hε]; linarith
  have hlog : 0 ≤ Real.log (p.μ * p.D / p.ε) := Real.log_nonneg hy
  have hX : 0 ≤ (p.L / p.μ) ^ 2 * (1 + Real.log (p.μ * p.D / p.ε)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hNr : (N : ℝ) ≤ (p.L / p.μ) ^ 2 * (1 + Real.log (p.μ * p.D / p.ε)) / 4608 :=
    (Nat.cast_le.mpr hN).trans (Nat.floor_le (div_nonneg hX (by norm_num)))
  have hk : μ0 ^ 2 * N ≤ (1 + Real.log (p.μ * p.D / p.ε)) / 2 := by
    have e : μ0 ^ 2 = 2304 / (p.L / p.μ) ^ 2 := by
      rw [hμ0def]
      field_simp
      ring
    rw [e]
    have hq : 0 < (p.L / p.μ) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hq]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4608)] at hNr
    linarith
  have hgap := gap_lower μ0 p.D p.μ p.ε N hμ0.le hμ1 hD hμ hε hεD hk
  set θ := threshold μ0 p.D N with hθdef
  set K : ℝ := (N : ℝ) + 1 with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hθpos : 0 < θ := by
    rw [hθdef]
    unfold threshold
    have := gap_pos μ0 p.D (by nlinarith) hD N
    positivity
  have hθlow : 3 * p.ε / (4 * p.L * K ^ 2) ≤ θ := by
    rw [hθdef]
    unfold threshold
    rw [← hKdef]
    have hm : 24 * p.ε / p.L ≤ μ0 * gap μ0 p.D N := by
      have : μ0 * (p.ε / (2 * p.μ)) = 24 * p.ε / p.L := by
        rw [hμ0def]
        field_simp
        ring
      rw [← this]
      exact mul_le_mul_of_nonneg_left hgap hμ0.le
    have e : 3 * p.ε / (4 * p.L * K ^ 2) = 24 * p.ε / p.L / (32 * K ^ 2) := by
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right hm (by positivity)
  set B := 8 * p.D with hBdef
  set Dc := 4 * ((N + 1 : ℕ) ^ 2 * (B ^ 2 / θ ^ 2)) with hDcdef
  have hB0 : 0 < B := by rw [hBdef]; positivity
  have hDc0 : 0 < Dc := by
    rw [hDcdef]
    positivity
  have hDs : Dc + (N + 1 : ℕ) ≤ p.d := by
    have hs := size_bound p.L p.D p.ε θ K hL hD hε hK hθlow
    have hM : K ≤ 1 + (p.L / p.μ) ^ 2 * (1 + Real.log (p.μ * p.D / p.ε)) := by
      rw [hKdef]
      linarith only [hNr, hX]
    have hQ : 1 ≤ (p.L * p.D / p.ε) ^ 2 := by
      have : 1 ≤ p.L * p.D / p.ε := by
        rw [le_div_iff₀ hε]
        nlinarith [mul_le_mul_of_nonneg_right (show p.μ ≤ p.L by linarith) hD.le]
      exact one_le_pow₀ this
    have hcast : ((N + 1 : ℕ) : ℝ) = K := by simp only [hKdef, Nat.cast_add, Nat.cast_one]
    have hDcK : Dc = 4 * K ^ 2 * ((8 * p.D) ^ 2 / θ ^ 2) := by
      rw [hDcdef, hcast, hBdef]
      ring
    rw [hcast, hDcK]
    exact dim_aux K _ _ _ _ hK hM hQ hs hdim
  have hsize : 4 * ((N + 1 : ℕ) ^ 2 * (B ^ 2 / θ ^ 2)) ≤ Dc := le_of_eq hDcdef.symm
  let full := fun (π : Fin (N + 1) ↪ Fin p.d) (u : EuclideanSpace ℝ (Fin p.d)) =>
    (c * (answer μ0 p.D π u).1, c • (answer μ0 p.D π u).2)
  let part := fun (π : Fin (N + 1) ↪ Fin p.d) (t : ℕ) (u : EuclideanSpace ℝ (Fin p.d)) =>
    (c * (partialAnswer μ0 p.D π t u).1, c • (partialAnswer μ0 p.D π t u).2)
  have hpart : ∀ π ρ : Fin (N + 1) ↪ Fin p.d, ∀ t, (∀ j : Fin (N + 1), j.val ≤ t → π j = ρ j) →
      part π t = part ρ t := by
    intro π ρ t h
    funext u
    simp only [part, partialAnswer_prefix μ0 p.D u π ρ t h]
  have hfull : ∀ π t u, t < N → (‖u‖ ≤ B → ∀ j : Fin (N + 1), t ≤ j.val → |u (π j)| ≤ θ) →
      full π u = part π t u := by
    intro π t u ht hs
    simp only [full, part, answer_eq_partial μ0 p.D π hμ0 hμ1 hD t ht.le u hs]
  let loss := fun (π : Fin (N + 1) ↪ Fin p.d) (s : A.State) =>
    c * hardValue μ0 p.D π (A.output s - p.x0)
  have hnn : ∀ π s, 0 ≤ loss π s := fun π s => mul_nonneg hc.le (hard_nonneg μ0 p.D π hμ0.le _)
  have hloss : ∀ π s, (‖A.output s - p.x0‖ ≤ B →
      |(A.output s - p.x0) (π (Fin.last N))| ≤ θ) → 2 * p.ε ≤ loss π s := by
    intro π s hs
    have h := good_loss μ0 p.D π hμ0 hμ1 hD (A.output s - p.x0) hs
    have h2 := mul_le_mul_of_nonneg_left h hc.le
    have h3 : c * (μ0 * gap μ0 p.D N / 4) = 4 * p.μ * gap μ0 p.D N := by
      have : c * μ0 = 16 * p.μ := by linarith [hμc]
      calc c * (μ0 * gap μ0 p.D N / 4) = c * μ0 * gap μ0 p.D N / 4 := by ring
        _ = _ := by rw [this]; ring
    have h4 : p.ε / 2 ≤ p.μ * gap μ0 p.D N := by
      calc p.ε / 2 = p.μ * (p.ε / (2 * p.μ)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hgap hμ.le
    change 2 * p.ε ≤ c * hardValue μ0 p.D π (A.output s - p.x0)
    linarith
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  obtain ⟨π, hbad⟩ := LongTails.Proofs.SharpChainHiding.exists_failure (d := p.d) (k := N)
    B θ Dc p.ε hB0.le hθpos hDc0 hDs hsize hε full part hpart hfull loss hnn
    (fun s => (A.query s).2 - p.x0) (fun s => A.output s - p.x0) A.update hloss
    (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  refine ⟨hardFun p μ0 c π, hardOracle p μ0 c π,
    hard_admissible p μ0 c π hc hμ0 hμ1 hD hLc hμc, ?_⟩
  have hit : ∀ w : A.Seed × (ℕ → Unit),
      execute (hardOracle p μ0 c π) A (fun _ => N) w.1 w.2 =
        A.output ((fun s => A.update s (full π ((fun s => (A.query s).2 - p.x0) s)))^[N]
          (A.initial w.1)) := by
    intro w
    exact (execute_hard p μ0 c π A N w.1 w.2).trans rfl
  rintro ⟨xstar, hmin, hi, he⟩
  have hfx : hardFun p μ0 c π xstar = 0 := by
    apply le_antisymm _ (hardFun_nonneg p μ0 c π hc.le hμ0.le xstar)
    have := isMinOn_univ_iff.mp hmin (p.x0 + hardTarget μ0 p.D π)
    rwa [hardFun_target p μ0 c π hμ0.le hμ1 hD] at this
  have hout : (fun w : A.Seed × (ℕ → Unit) =>
      hardFun p μ0 c π (execute (hardOracle p μ0 c π) A (fun _ => N) w.1 w.2) -
        hardFun p μ0 c π xstar) =
      fun w => loss π ((fun s => A.update s (full π ((fun s => (A.query s).2 - p.x0) s)))^[N]
        (A.initial w.1)) := by
    funext w
    rw [hit w, hfx, sub_zero]
    try rfl
  apply hbad
  constructor
  · change Integrable (fun w : A.Seed × (ℕ → Unit) =>
      hardFun p μ0 c π (execute (hardOracle p μ0 c π) A (fun _ => N) w.1 w.2) -
        hardFun p μ0 c π xstar) (P : Measure _) at hi
    rw [hout] at hi
    exact hi
  · change (∫ w : A.Seed × (ℕ → Unit),
      hardFun p μ0 c π (execute (hardOracle p μ0 c π) A (fun _ => N) w.1 w.2) -
        hardFun p μ0 c π xstar ∂(P : Measure _)) ≤ p.ε at he
    rw [hout] at he
    exact he

end LongTails.Proofs.SharpChainLowerBound
