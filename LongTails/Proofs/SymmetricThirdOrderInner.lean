import LongTails.Proofs.ThirdOrderBregmanGeometry
import LongTails.Proofs.QuarticBregmanKernel
import LongTails.Proofs.SymmetricThirdOrderMinimizers

namespace LongTails.Proofs.SymmetricThirdOrderInner

open ThirdOrderBregmanGeometry
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma three_point (ρ : E → ℝ) (u p y : E) :
    translatedGap ρ (u - y) y - translatedGap ρ (u - p) p -
      translatedGap ρ (p - y) y = ⟪gradient ρ p - gradient ρ y, u - p⟫ := by
  simp only [translatedGap, add_sub_cancel, inner_sub_left, inner_sub_right]
  ring

lemma robust_step {q ρ : E → ℝ} {u p y e : E} {δ a : ℝ}
    (hδ : 0 < δ) (herr : ‖e‖ ≤ a)
    (hlower : δ / 2 * ‖u - p‖ ^ 2 ≤ translatedGap ρ (u - p) p)
    (hpy : 0 ≤ translatedGap ρ (p - y) y)
    (hu : q y + ⟪gradient q y, u - y⟫ +
      (1 / 2) * translatedGap ρ (u - y) y ≤ q u)
    (hp : q p ≤ q y + ⟪gradient q y, p - y⟫ +
      (3 / 2) * translatedGap ρ (p - y) y)
    (hprox : 0 ≤ ⟪gradient q y + e +
      (2 : ℝ) • (gradient ρ p - gradient ρ y), u - p⟫) :
    q p - q u + (7 / 4) * translatedGap ρ (u - p) p ≤
      (3 / 2) * translatedGap ρ (u - y) y + 2 * a ^ 2 / δ := by
  have ht := three_point ρ u p y
  have he := (real_inner_le_norm e (u - p)).trans
    (mul_le_mul_of_nonneg_right herr (norm_nonneg _))
  have hy : a * ‖u - p‖ ≤ δ / 8 * ‖u - p‖ ^ 2 + 2 * a ^ 2 / δ := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    field_simp
    nlinarith [sq_nonneg (δ * ‖u - p‖ - 4 * a)]
  have hi : ⟪gradient q y, u - y⟫ =
      ⟪gradient q y, u - p⟫ + ⟪gradient q y, p - y⟫ := by
    rw [← inner_add_right]
    congr 1
    abel
  simp only [inner_add_left, real_inner_smul_left] at hprox
  nlinarith

omit [FiniteDimensional ℝ E] in
lemma contraction_iterates {D : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b) (k : ℕ)
    (hstep : ∀ j < k, D (j + 1) ≤ (6 / 7) * D j + (8 / 7) * b) :
    D k ≤ (6 / 7) ^ k * D 0 + 8 * b := by
  induction k with
  | zero => simp only [pow_zero, one_mul]; linarith
  | succ k ih =>
    have hi := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    have hh := hstep k (Nat.lt_succ_self k)
    rw [pow_succ]
    nlinarith

omit [FiniteDimensional ℝ E] in
lemma final_gap_bound {D gap : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b) (k : ℕ)
    (hstep : ∀ j < k, D (j + 1) ≤ (6 / 7) * D j + (8 / 7) * b)
    (hgap : gap (k + 1) + (7 / 4) * D (k + 1) ≤ (3 / 2) * D k + 2 * b)
    (hD : 0 ≤ D (k + 1)) (hinit : (6 / 7) ^ k * D 0 ≤ b) :
    gap (k + 1) ≤ 16 * b := by
  have hi := contraction_iterates hb k hstep
  linarith

open LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Proofs.SymmetricThirdOrderGeometry
open LongTails.Proofs.SymmetricThirdOrderMinimizers

lemma proxPoint_model_step {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ a : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (C : Set E) (fallback c y u : E) (B : E →L[ℝ] E) (g : E)
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C) (hu : u ∈ C)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫)
    (herr : ‖g - gradient (model f c B L δ) (y - c)‖ ≤ a) :
    let p := proxPoint C fallback c y B L δ g
    model f c B L δ (p - c) - model f c B L δ (u - c) +
      (7 / 4) * translatedGap (kernel B L δ) (u - p) (p - c) ≤
      (3 / 2) * translatedGap (kernel B L δ) (u - y) (y - c) + 2 * a ^ 2 / δ := by
  let p := proxPoint C fallback c y B L δ g
  have hpos (v : E) : 0 ≤ ⟪v, B v⟫ := by
    rw [real_inner_comm]
    exact (convex_hessian_nonneg hf hc c v).trans (hB v)
  have hl : δ / 2 * ‖u - p‖ ^ 2 ≤ translatedGap (kernel B L δ) (u - p) (p - c) := by
    have hh := kernel_gap_lower B (δ := δ) hL hsym hpos (p - c) (u - p)
    have hn := mul_nonneg hL (pow_nonneg (norm_nonneg (u - p)) 4)
    linarith
  have hp₀ : 0 ≤ translatedGap (kernel B L δ) (p - y) (y - c) := by
    have hh := kernel_gap_lower B (δ := δ) hL hsym hpos (y - c) (p - y)
    have hn := mul_nonneg hL (pow_nonneg (norm_nonneg (p - y)) 4)
    have hd := mul_nonneg hδ.le (sq_nonneg ‖p - y‖)
    linarith
  have hyu := (model_relative_gap hf hc hL hδ.le hT c B hsym hB (y - c) (u - c)).1
  have hyp := (model_relative_gap hf hc hL hδ.le hT c B hsym hB (y - c) (p - c)).2
  have huc : (u - c) - (y - c) = u - y := by abel
  have hpc : (p - c) - (y - c) = p - y := by abel
  have hup : (u - c) - (p - c) = u - p := by abel
  have hvi := proxPoint_variational C fallback c y B L δ g hC hne hconv hsym u hu
  have hprox : 0 ≤ ⟪gradient (model f c B L δ) (y - c) +
      (g - gradient (model f c B L δ) (y - c)) +
      (2 : ℝ) • (gradient (kernel B L δ) (p - c) - gradient (kernel B L δ) (y - c)),
      (u - c) - (p - c)⟫ := by
    rw [kernel_gradient B L δ hsym, hup]
    have he : gradient (model f c B L δ) (y - c) +
      (g - gradient (model f c B L δ) (y - c)) = g := by abel
    rw [he]
    simpa only [p, two_smul] using hvi
  have hh := robust_step (q := model f c B L δ) (ρ := kernel B L δ)
    (u := u - c) (p := p - c) (y := y - c) hδ herr
    (by rwa [hup]) (by rwa [hpc]) ?_ ?_ hprox
  · simpa only [hup, huc] using hh
  · simp only [translatedGap, add_sub_cancel] at hyu ⊢
    linarith
  · simp only [translatedGap, add_sub_cancel] at hyp ⊢
    linarith

omit [FiniteDimensional ℝ E] in
lemma innerIterate_mem (C : Set E) (fallback c : E) (B : E →L[ℝ] E)
    (L δ : ℝ) (G : ℕ → E → E) (hC : IsCompact C) (hx : fallback ∈ C) (k : ℕ) :
    innerIterate C fallback c B L δ G k ∈ C := by
  cases k with
  | zero => exact hx
  | succ k => exact (proxPoint_spec C fallback c _ B L δ _ hC ⟨fallback, hx⟩).1

lemma measurable_innerIterate {X : Type*} [MeasurableSpace X]
    [MeasurableSpace E] [BorelSpace E]
    (C : Set E) (fallback : E) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (c : X → E) (B : X → E →L[ℝ] E) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (G : ℕ → X → E → E) (hc : Measurable c) (hB : Measurable B)
    (hG : ∀ k, Measurable (fun w : X × E => G k w.1 w.2))
    (hsym : ∀ p x y, ⟪x, B p y⟫ = ⟪B p x, y⟫)
    (hpos : ∀ p v, 0 ≤ ⟪v, B p v⟫) (k : ℕ) :
    Measurable (fun p => innerIterate C fallback (c p) (B p) L δ (fun j => G j p) k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact measurable_proxPoint C fallback hC hne hconv c _ _ B hL hδ hc ih
      ((hG k).comp (measurable_id.prodMk ih)) hB hsym hpos

lemma innerIterate_gap {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ a : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (C : Set E) (fallback c u : E) (B : E →L[ℝ] E) (G : ℕ → E → E)
    (hC : IsCompact C) (hconv : Convex ℝ C) (hx : fallback ∈ C) (hu : u ∈ C)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫)
    (hmin : ∀ v ∈ C, model f c B L δ (u - c) ≤ model f c B L δ (v - c)) (k : ℕ)
    (herr : ∀ j < k + 1,
      ‖G j (innerIterate C fallback c B L δ G j) - gradient (model f c B L δ)
        (innerIterate C fallback c B L δ G j - c)‖ ≤ a)
    (hinit : (6 / 7) ^ k * translatedGap (kernel B L δ) (u - fallback) (fallback - c) ≤ a ^ 2 / δ) :
    model f c B L δ (innerIterate C fallback c B L δ G (k + 1) - c) -
      model f c B L δ (u - c) ≤ 16 * a ^ 2 / δ := by
  let z := innerIterate C fallback c B L δ G
  let D := fun j => translatedGap (kernel B L δ) (u - z j) (z j - c)
  let gap := fun j => model f c B L δ (z j - c) - model f c B L δ (u - c)
  have hpos (v : E) : 0 ≤ ⟪v, B v⟫ := by
    rw [real_inner_comm]
    exact (convex_hessian_nonneg hf hc c v).trans (hB v)
  have hD (j : ℕ) : 0 ≤ D j := by
    have hh := kernel_gap_lower B (δ := δ) hL hsym hpos (z j - c) (u - z j)
    have hn := mul_nonneg hL (pow_nonneg (norm_nonneg (u - z j)) 4)
    have hd := mul_nonneg hδ.le (sq_nonneg ‖u - z j‖)
    dsimp [D]
    linarith
  have hgap (j : ℕ) : 0 ≤ gap j :=
    sub_nonneg.mpr (hmin (z j) (innerIterate_mem C fallback c B L δ G hC hx j))
  have hstep (j : ℕ) (hj : j < k + 1) :
      gap (j + 1) + (7 / 4) * D (j + 1) ≤ (3 / 2) * D j + 2 * a ^ 2 / δ := by
    exact proxPoint_model_step hf hc hL hδ hT C fallback c (z j) u B (G j (z j))
      hC ⟨fallback, hx⟩ hconv hu hsym hB (herr j hj)
  have hcontract (j : ℕ) (hj : j < k) : D (j + 1) ≤ (6 / 7) * D j + (8 / 7) * (a ^ 2 / δ) := by
    have hh := hstep j (Nat.lt_succ_of_lt hj)
    have hn := hgap (j + 1)
    simp only [mul_div_assoc] at hh
    linarith
  have hh := final_gap_bound (D := D) (gap := gap) (div_nonneg (sq_nonneg a) hδ.le) k
    hcontract (by simpa only [mul_div_assoc] using hstep k (Nat.lt_succ_self k)) (hD (k + 1)) hinit
  simpa only [gap, z, mul_div_assoc] using hh

lemma initial_bregman_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (C : Set E) (hconv : Convex ℝ C) (c x u : E) (B : E →L[ℝ] E)
    (hx : x ∈ C) (hu : u ∈ C)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫)
    (hmin : ∀ v ∈ C, model f c B L δ (u - c) ≤ model f c B L δ (v - c)) :
    translatedGap (kernel B L δ) (u - x) (x - c) ≤
      8 * (model f c B L δ (x - c) - model f c B L δ (u - c)) := by
  have hpos (v : E) : 0 ≤ ⟪v, B v⟫ := by
    rw [real_inner_comm]
    exact (convex_hessian_nonneg hf hc c v).trans (hB v)
  have hg : HasGradientAt (fun v => model f c B L δ (v - c))
      (gradient (model f c B L δ) (u - c)) u := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hh := ((model_contDiff hf c B L δ).differentiable (by norm_num) (u - c)).hasGradientAt.hasFDerivAt
    convert hh.comp u ((hasFDerivAt_id u).sub_const c) using 1
    · rfl
    · ext v
      simp
  have hvi := constrained_min_variational (φ := fun v => model f c B L δ (v - c)) hconv hu hmin hg x hx
  have hr := (model_relative_gap hf hc hL hδ hT c B hsym hB (u - c) (x - c)).1
  have he : (x - c) - (u - c) = x - u := by abel
  have he' : (u - c) + (x - u) = x - c := by abel
  rw [he] at hr
  change (1 / 2) * translatedGap (kernel B L δ) (x - u) (u - c) ≤
    model f c B L δ ((u - c) + (x - u)) - model f c B L δ (u - c) -
      ⟪gradient (model f c B L δ) (u - c), x - u⟫ at hr
  rw [he'] at hr
  have hrev := kernel_gap_reverse B hL hδ hsym hpos (u - c) (x - u)
  rw [he', show -(x - u) = u - x by abel] at hrev
  linarith

end LongTails.Proofs.SymmetricThirdOrderInner
