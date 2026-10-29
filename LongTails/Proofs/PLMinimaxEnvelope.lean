import LongTails.Proofs.PLMinimaxProx

open Set InnerProductSpace
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL
open LongTails.Setups.WeaklyConvexHeavyTailed

namespace OracleTemplate.PLMinimax

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma Hyp.slice_weak (H : Hyp f gx gy L μ) (y : F) :
    WeaklyConvexHeavyTailed.WeakSubgradientOn univ L (fun x => f x y) (fun x => gx x y) :=
  fun x _ x' _ => H.lower_x x x' y

omit [FiniteDimensional ℝ E] in
lemma Hyp.value_continuous (H : Hyp f gx gy L μ) : Continuous (maxValue f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨y, hy⟩ := H.attain x
  exact (H.value_hasGradient hy).continuousAt

omit [FiniteDimensional ℝ E] in
lemma Hyp.value_weak (H : Hyp f gx gy L μ) :
    WeaklyConvexHeavyTailed.WeakSubgradientOn univ L (maxValue f) (gradient (maxValue f)) := by
  intro x _ x' _
  obtain ⟨y, hy⟩ := H.attain x
  rw [H.max_value_eq hy, (H.value_hasGradient hy).gradient]
  exact (H.lower_x x x' y).trans (H.le_max_value x' y)

noncomputable def primal (f : E → F → ℝ) (L : ℝ) (z : E) : E :=
  weakProx (maxValue f) L z

noncomputable def innerPrimal (f : E → F → ℝ) (L : ℝ) (z : E) (y : F) : E :=
  weakProx (fun x => f x y) L z

noncomputable def dual (f : E → F → ℝ) (L : ℝ) (z : E) (y : F) : ℝ :=
  weakEnvelope (fun x => f x y) L z

noncomputable def envelope (f : E → F → ℝ) (L : ℝ) (z : E) : ℝ :=
  weakEnvelope (maxValue f) L z

omit [FiniteDimensional ℝ F] in
lemma Hyp.innerPrimal_stationary (H : Hyp f gx gy L μ) (z : E) (y : F) :
    gx (innerPrimal f L z y) y + (2 * L) • (innerPrimal f L z y - z) = 0 :=
  weakProx_stationary H.hL (fun x => H.hgx x y) (H.slice_weak y) z

lemma Hyp.primal_stationary (H : Hyp f gx gy L μ) (z : E) :
    gradient (maxValue f) (primal f L z) + (2 * L) • (primal f L z - z) = 0 := by
  apply weakProx_stationary H.hL _ H.value_weak z
  intro x
  obtain ⟨y, hy⟩ := H.attain x
  rw [(H.value_hasGradient hy).gradient]
  exact H.value_hasGradient hy

omit [FiniteDimensional ℝ F] in
lemma Hyp.dual_le_envelope (H : Hyp f gx gy L μ) (z : E) (y : F) :
    dual f L z y ≤ envelope f L z := by
  have hc : Continuous (fun x => f x y) :=
    continuous_iff_continuousAt.mpr fun x => (H.hgx x y).continuousAt
  have hm := weakProx_min H.hL hc (H.slice_weak y) z (mem_univ (primal f L z))
  change dual f L z y ≤ proxObj (fun x => f x y) L z (primal f L z) at hm
  have hl := H.le_max_value (primal f L z) y
  change dual f L z y ≤ maxValue f (primal f L z) + L * ‖primal f L z - z‖ ^ 2
  apply hm.trans
  change f (primal f L z) y + _ ≤ maxValue f (primal f L z) + _
  linarith

lemma Hyp.envelope_sub_dual (H : Hyp f gx gy L μ) (z : E) (y : F) :
    envelope f L z - dual f L z y ≤ ‖gy (innerPrimal f L z y) y‖ ^ 2 / (2 * μ) := by
  have hm := weakProx_min H.hL H.value_continuous H.value_weak z
    (mem_univ (innerPrimal f L z y))
  obtain ⟨v, hv⟩ := H.attain (innerPrimal f L z y)
  have hp := H.ply (innerPrimal f L z y) y v
  have hgap : maxValue f (innerPrimal f L z y) - f (innerPrimal f L z y) y ≤
      ‖gy (innerPrimal f L z y) y‖ ^ 2 / (2 * μ) := by
    rw [H.max_value_eq hv, le_div_iff₀ (by linarith [H.hμ])]
    linarith
  change envelope f L z ≤ maxValue f (innerPrimal f L z y) + L * ‖innerPrimal f L z y - z‖ ^ 2 at hm
  change envelope f L z - (f (innerPrimal f L z y) y + L * ‖innerPrimal f L z y - z‖ ^ 2) ≤ _
  linarith

lemma Hyp.saddle_exists (H : Hyp f gx gy L μ) (z : E) :
    ∃ y, (∀ v, f (primal f L z) v ≤ f (primal f L z) y) ∧
      innerPrimal f L z y = primal f L z ∧ dual f L z y = envelope f L z := by
  obtain ⟨y, hy⟩ := H.attain (primal f L z)
  have hs := H.primal_stationary z
  rw [(H.value_hasGradient hy).gradient] at hs
  have hm := proxObj_min_of_stationary H.hL.le (H.slice_weak y) hs
  have hc : Continuous (fun x => f x y) :=
    continuous_iff_continuousAt.mpr fun x => (H.hgx x y).continuousAt
  have he : innerPrimal f L z y = primal f L z :=
    WeaklyConvexHeavyTailed.prox_unique (convex_univ) (H.slice_weak y) H.hL
      (mem_univ _) (weakProx_min H.hL hc (H.slice_weak y) z) (mem_univ _) hm
  refine ⟨y, hy, he, ?_⟩
  change f (innerPrimal f L z y) y + L * ‖innerPrimal f L z y - z‖ ^ 2 =
    maxValue f (primal f L z) + L * ‖primal f L z - z‖ ^ 2
  rw [he, H.max_value_eq hy]

omit [FiniteDimensional ℝ F] in
lemma Hyp.innerPrimal_lipschitz (H : Hyp f gx gy L μ) (z : E) (y y' : F) :
    ‖innerPrimal f L z y - innerPrimal f L z y'‖ ≤ ‖y - y'‖ := by
  have hd := proxObj_residual_distance (H.slice_weak y')
    (H.innerPrimal_stationary z y') (innerPrimal f L z y)
  have hs := H.innerPrimal_stationary z y
  have he : gx (innerPrimal f L z y) y' + (2 * L) • (innerPrimal f L z y - z) =
      gx (innerPrimal f L z y) y' - gx (innerPrimal f L z y) y := by
    have hh := eq_neg_of_add_eq_zero_left hs
    rw [hh]
    abel
  rw [he] at hd
  have hl := H.lipx (innerPrimal f L z y) (innerPrimal f L z y) y' y
  simp only [sub_self, norm_zero, zero_add, norm_sub_rev y' y] at hl
  exact (mul_le_mul_iff_right₀ H.hL).mp (hd.trans hl)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma Hyp.upper_y (H : Hyp f gx gy L μ) (x : E) (y y' : F) :
    f x y' ≤ f x y + ⟪gy x y, y' - y⟫ + L / 2 * ‖y' - y‖ ^ 2 :=
  Gradient.smooth_upper_bound (H.hgy x)
    (fun a b => by simpa using H.lipy x x a b) y y'

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma Hyp.lower_y (H : Hyp f gx gy L μ) (x : E) (y y' : F) :
    f x y + ⟪gy x y, y' - y⟫ - L / 2 * ‖y' - y‖ ^ 2 ≤ f x y' := by
  have hh := Gradient.smooth_upper_bound (f := fun y => -f x y) (oracle := fun y => -gy x y)
    (L := L) (fun y => TwoSidedPL.hasGradientAt_neg' (H.hgy x y))
    (fun a b => by rw [neg_sub_neg, norm_sub_rev]; simpa using H.lipy x x a b) y y'
  simp only [inner_neg_left] at hh
  linarith

omit [FiniteDimensional ℝ F] in
lemma Hyp.dual_remainder (H : Hyp f gx gy L μ) (z : E) (y h : F) :
    |dual f L z (y + h) - dual f L z y - ⟪gy (innerPrimal f L z y) y, h⟫| ≤
      2 * L * ‖h‖ ^ 2 := by
  have hc : ∀ v, Continuous (fun x => f x v) :=
    fun v => continuous_iff_continuousAt.mpr fun x => (H.hgx x v).continuousAt
  have hm₁ := weakProx_min H.hL (hc (y + h)) (H.slice_weak (y + h)) z
    (mem_univ (innerPrimal f L z y))
  have hm₂ := weakProx_min H.hL (hc y) (H.slice_weak y) z
    (mem_univ (innerPrimal f L z (y + h)))
  change dual f L z (y + h) ≤ f (innerPrimal f L z y) (y + h) +
    L * ‖innerPrimal f L z y - z‖ ^ 2 at hm₁
  change dual f L z y ≤ f (innerPrimal f L z (y + h)) y +
    L * ‖innerPrimal f L z (y + h) - z‖ ^ 2 at hm₂
  have hu := H.upper_y (innerPrimal f L z y) y (y + h)
  have hl := H.lower_y (innerPrimal f L z (y + h)) y (y + h)
  simp only [add_sub_cancel_left] at hu hl
  have hd := H.innerPrimal_lipschitz z (y + h) y
  simp only [add_sub_cancel_left] at hd
  have hg := H.lipy (innerPrimal f L z (y + h)) (innerPrimal f L z y) y y
  simp only [sub_self, norm_zero, add_zero] at hg
  have hi := (abs_le.mp (abs_real_inner_le_norm
    (gy (innerPrimal f L z (y + h)) y - gy (innerPrimal f L z y) y) h)).1
  rw [inner_sub_left] at hi
  have hg' : ‖gy (innerPrimal f L z (y + h)) y - gy (innerPrimal f L z y) y‖ ≤ L * ‖h‖ :=
    hg.trans (mul_le_mul_of_nonneg_left hd H.hL.le)
  have hi' := mul_le_mul_of_nonneg_right hg' (norm_nonneg h)
  change |(f (innerPrimal f L z (y + h)) (y + h) + L * ‖innerPrimal f L z (y + h) - z‖ ^ 2) -
    (f (innerPrimal f L z y) y + L * ‖innerPrimal f L z y - z‖ ^ 2) - _| ≤ _
  change f (innerPrimal f L z (y + h)) (y + h) + L * ‖innerPrimal f L z (y + h) - z‖ ^ 2 ≤ _ at hm₁
  change f (innerPrimal f L z y) y + L * ‖innerPrimal f L z y - z‖ ^ 2 ≤ _ at hm₂
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg H.hL.le (sq_nonneg ‖h‖)]

omit [FiniteDimensional ℝ F] in
lemma Hyp.dual_hasGradient (H : Hyp f gx gy L μ) (z : E) (y : F) :
    HasGradientAt (dual f L z) (gy (innerPrimal f L z y) y) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  apply hasFDerivAt_of_quadratic_remainder (C := 2 * L)
  intro h
  simpa [Real.norm_eq_abs] using H.dual_remainder z y h

omit [FiniteDimensional ℝ F] in
lemma Hyp.dual_gradient_lipschitz (H : Hyp f gx gy L μ) (z : E) (y y' : F) :
    ‖gy (innerPrimal f L z y) y - gy (innerPrimal f L z y') y'‖ ≤ 2 * L * ‖y - y'‖ := by
  have hl := H.lipy (innerPrimal f L z y) (innerPrimal f L z y') y y'
  have hd := H.innerPrimal_lipschitz z y y'
  nlinarith [mul_le_mul_of_nonneg_left hd H.hL.le]

lemma Hyp.dual_quadratic_growth (H : Hyp f gx gy L μ) (z : E) (y : F) :
    ∃ v, dual f L z v = envelope f L z ∧
      μ * ‖y - v‖ ^ 2 ≤ 16 * (envelope f L z - dual f L z y) := by
  obtain ⟨v₀, _, _, hv₀⟩ := H.saddle_exists z
  have hg : ∀ v, HasGradientAt (fun v => -dual f L z v)
      (-gy (innerPrimal f L z v) v) v :=
    fun v => TwoSidedPL.hasGradientAt_neg' (H.dual_hasGradient z v)
  have he : ∀ v, gradient (fun v => -dual f L z v) v = -gy (innerPrimal f L z v) v :=
    fun v => (hg v).gradient
  have hm : IsMinOn (fun v => -dual f L z v) univ v₀ := by
    intro v _
    change -dual f L z v₀ ≤ -dual f L z v
    rw [hv₀]
    exact neg_le_neg (H.dual_le_envelope z v)
  obtain ⟨v, hv, hd⟩ := PLHessian.quad_growth (L := 2 * L) (μ := μ)
    (by linarith [H.hL]) H.hμ (by linarith [H.hμL, H.hL])
    (fun v => by rw [he]; exact hg v)
    (fun a b => by rw [he, he, neg_sub_neg, norm_sub_rev]; exact H.dual_gradient_lipschitz z a b)
    hm (fun v => by
      rw [he, norm_neg, hv₀]
      have hh := H.envelope_sub_dual z v
      rw [le_div_iff₀ (by linarith [H.hμ])] at hh
      nlinarith) y
  have hv' := hv (mem_univ v₀)
  change -dual f L z v ≤ -dual f L z v₀ at hv'
  have heq : dual f L z v = envelope f L z := by
    rw [hv₀] at hv'
    linarith [H.dual_le_envelope z v]
  refine ⟨v, heq, ?_⟩
  rw [hv₀] at hd
  simpa only [neg_sub_neg] using hd

omit [FiniteDimensional ℝ F] in
lemma Hyp.saddle_of_dual_eq (H : Hyp f gx gy L μ) (z : E) (y : F)
    (hy : dual f L z y = envelope f L z) :
    innerPrimal f L z y = primal f L z ∧
      (∀ v, f (primal f L z) v ≤ f (primal f L z) y) := by
  have hc : Continuous (fun x => f x y) :=
    continuous_iff_continuousAt.mpr fun x => (H.hgx x y).continuousAt
  have hm := weakProx_growth H.hL hc (H.slice_weak y) z (primal f L z)
  change dual f L z y + L / 2 * ‖primal f L z - innerPrimal f L z y‖ ^ 2 ≤
    f (primal f L z) y + L * ‖primal f L z - z‖ ^ 2 at hm
  rw [hy] at hm
  change maxValue f (primal f L z) + L * ‖primal f L z - z‖ ^ 2 + _ ≤ _ at hm
  have hl := H.le_max_value (primal f L z) y
  have hn : ‖primal f L z - innerPrimal f L z y‖ = 0 := by
    have hsq : ‖primal f L z - innerPrimal f L z y‖ ^ 2 = 0 := by
      nlinarith [H.hL, sq_nonneg ‖primal f L z - innerPrimal f L z y‖]
    nlinarith [norm_nonneg (primal f L z - innerPrimal f L z y)]
  have he : innerPrimal f L z y = primal f L z := (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
  refine ⟨he, fun v => (H.le_max_value (primal f L z) v).trans ?_⟩
  nlinarith [mul_nonneg H.hL.le (sq_nonneg ‖primal f L z - innerPrimal f L z y‖)]

lemma Hyp.weighted_primal_residual (H : Hyp f gx gy L μ) (z x : E) (y : F) :
    ‖x - primal f L z‖ ^ 2 ≤
      ‖gx x y + (2 * L) • (x - z)‖ ^ 2 / L ^ 2 + ‖gy x y‖ ^ 2 / (L * μ) := by
  have hm := proxObj_gap_bound H.hL (H.slice_weak y) z x (innerPrimal f L z y)
  have hg := weakProx_growth H.hL H.value_continuous H.value_weak z x
  obtain ⟨v, hv⟩ := H.attain x
  have hp := H.ply x y v
  have hp' : maxValue f x - f x y ≤ ‖gy x y‖ ^ 2 / (2 * μ) := by
    rw [H.max_value_eq hv, le_div_iff₀ (by linarith [H.hμ])]
    linarith
  apply weighted_primal_gap H.hL H.hμ (H.dual_le_envelope z y)
    (value := proxObj (fun x => f x y) L z x)
    (primal := proxObj (maxValue f) L z x)
  · simpa only [proxObj, add_sub_add_right_eq_sub] using hp'
  · exact hm
  · change envelope f L z + L / 2 * ‖x - primal f L z‖ ^ 2 ≤ proxObj (maxValue f) L z x at hg
    linarith

lemma Hyp.shifted_dual_gap (H : Hyp f gx gy L μ) (z z' : E) (y : F)
    (hy : ∀ v, f (primal f L z) v ≤ f (primal f L z) y) :
    envelope f L z' - dual f L z' y ≤ 2 * L * ‖z' - z‖ ^ 2 := by
  have hu := weakProx_min H.hL H.value_continuous H.value_weak z'
    (mem_univ (primal f L z))
  change envelope f L z' ≤ maxValue f (primal f L z) + L * ‖primal f L z - z'‖ ^ 2 at hu
  rw [H.max_value_eq hy] at hu
  have hl := proxObj_gap_bound H.hL (H.slice_weak y) z' (primal f L z)
    (innerPrimal f L z' y)
  have hs := H.primal_stationary z
  rw [(H.value_hasGradient hy).gradient] at hs
  have he : gx (primal f L z) y + (2 * L) • (primal f L z - z') = (2 * L) • (z - z') := by
    have hh := eq_neg_of_add_eq_zero_left hs
    rw [hh, ← smul_neg, ← smul_add]
    congr 1
    abel
  rw [he, norm_smul, Real.norm_of_nonneg (by linarith [H.hL]), norm_sub_rev z z'] at hl
  have hn : ((2 * L) * ‖z' - z‖) ^ 2 / (2 * L) = 2 * L * ‖z' - z‖ ^ 2 := by
    field_simp
  rw [hn] at hl
  change (f (primal f L z) y + L * ‖primal f L z - z'‖ ^ 2) - dual f L z' y ≤ _ at hl
  linarith

lemma Hyp.nearby_saddle (H : Hyp f gx gy L μ) (z z' : E) (y : F)
    (hy : ∀ v, f (primal f L z) v ≤ f (primal f L z) y) :
    ∃ v, (∀ w, f (primal f L z') w ≤ f (primal f L z') v) ∧
      innerPrimal f L z' v = primal f L z' ∧
      μ * ‖y - v‖ ^ 2 ≤ 32 * L * ‖z' - z‖ ^ 2 ∧
      ‖primal f L z' - primal f L z‖ ≤ 2 * ‖z' - z‖ := by
  obtain ⟨v, hv, hd⟩ := H.dual_quadratic_growth z' y
  obtain ⟨he, hm⟩ := H.saddle_of_dual_eq z' v hv
  refine ⟨v, hm, he, ?_, ?_⟩
  · linarith [H.shifted_dual_gap z z' y hy]
  · exact weakProx_lipschitz H.hL H.value_continuous H.value_weak z' z

omit [FiniteDimensional ℝ F] in
lemma Hyp.dual_residual_bound (H : Hyp f gx gy L μ) (z x : E) (y : F) :
    ‖gy (innerPrimal f L z y) y‖ ≤ ‖gx x y + (2 * L) • (x - z)‖ + ‖gy x y‖ := by
  have hd := proxObj_residual_distance (H.slice_weak y) (H.innerPrimal_stationary z y) x
  have hl := H.lipy (innerPrimal f L z y) x y y
  simp only [sub_self, norm_zero, add_zero, norm_sub_rev (innerPrimal f L z y) x] at hl
  have hn := norm_le_norm_sub_add (gy (innerPrimal f L z y) y) (gy x y)
  linarith

lemma Hyp.dual_residual_saddle (H : Hyp f gx gy L μ) (z x : E) (y : F) :
    ∃ v, (∀ w, f (primal f L z) w ≤ f (primal f L z) v) ∧
      μ ^ 2 * ‖y - v‖ ^ 2 ≤
        16 * (‖gx x y + (2 * L) • (x - z)‖ ^ 2 + ‖gy x y‖ ^ 2) := by
  obtain ⟨v, hv, hd⟩ := H.dual_quadratic_growth z y
  have hp := H.envelope_sub_dual z y
  rw [le_div_iff₀ (by linarith [H.hμ])] at hp
  have hd' := mul_le_mul_of_nonneg_left hd H.hμ.le
  have hr := H.dual_residual_bound z x y
  have hs : ‖gy (innerPrimal f L z y) y‖ ^ 2 ≤
      2 * (‖gx x y + (2 * L) • (x - z)‖ ^ 2 + ‖gy x y‖ ^ 2) := by
    have ht := pow_le_pow_left₀ (norm_nonneg _) hr 2
    nlinarith [sq_nonneg (‖gx x y + (2 * L) • (x - z)‖ - ‖gy x y‖)]
  refine ⟨v, (H.saddle_of_dual_eq z v hv).2, ?_⟩
  nlinarith

lemma Hyp.primal_residual_bound (H : Hyp f gx gy L μ) (z x : E) (y : F) :
    μ ^ 2 * ‖x - primal f L z‖ ^ 2 ≤
      ‖gx x y + (2 * L) • (x - z)‖ ^ 2 + ‖gy x y‖ ^ 2 := by
  have hw := H.weighted_primal_residual z x y
  have hμsq : 0 < μ ^ 2 := sq_pos_of_pos H.hμ
  have hd₁ : μ ^ 2 ≤ L ^ 2 := by nlinarith [H.hμ, H.hμL]
  have hd₂ : μ ^ 2 ≤ L * μ := by nlinarith [H.hμ, H.hμL]
  have h₁ := div_le_div_of_nonneg_left (sq_nonneg ‖gx x y + (2 * L) • (x - z)‖) hμsq hd₁
  have h₂ := div_le_div_of_nonneg_left (sq_nonneg ‖gy x y‖) hμsq hd₂
  have ht := hw.trans (add_le_add h₁ h₂)
  rw [← add_div, le_div_iff₀ hμsq] at ht
  nlinarith

lemma Hyp.saddle_residual_bound (H : Hyp f gx gy L μ) (z x : E) (y : F) :
    ∃ v, (∀ w, f (primal f L z) w ≤ f (primal f L z) v) ∧
      μ ^ 2 * (‖x - primal f L z‖ ^ 2 + ‖y - v‖ ^ 2) ≤
        17 * (‖gx x y + (2 * L) • (x - z)‖ ^ 2 + ‖gy x y‖ ^ 2) := by
  obtain ⟨v, hv, hd⟩ := H.dual_residual_saddle z x y
  refine ⟨v, hv, ?_⟩
  nlinarith [H.primal_residual_bound z x y]

noncomputable def inversePrimal (f : E → F → ℝ) (L : ℝ) (x : E) : E :=
  x + (2 * L)⁻¹ • gradient (maxValue f) x

lemma Hyp.primal_inversePrimal (H : Hyp f gx gy L μ) (x : E) :
    primal f L (inversePrimal f L x) = x := by
  have hn : 2 * L ≠ 0 := by have := H.hL; positivity
  have hs : gradient (maxValue f) x + (2 * L) • (x - inversePrimal f L x) = 0 := by
    have he : x - inversePrimal f L x = -((2 * L)⁻¹ • gradient (maxValue f) x) := by simp [inversePrimal]
    rw [he, smul_neg, smul_smul, mul_inv_cancel₀ hn, one_smul, add_neg_cancel]
  apply WeaklyConvexHeavyTailed.prox_unique (convex_univ) H.value_weak H.hL
    (mem_univ _) (weakProx_min H.hL H.value_continuous H.value_weak (inversePrimal f L x))
    (mem_univ _) (proxObj_min_of_stationary H.hL.le H.value_weak hs)

lemma Hyp.inversePrimal_primal (H : Hyp f gx gy L μ) (z : E) :
    inversePrimal f L (primal f L z) = z := by
  have hn : 2 * L ≠ 0 := by have := H.hL; positivity
  have hs := congrArg (fun v => (2 * L)⁻¹ • v) (H.primal_stationary z)
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hn, one_smul, smul_zero] at hs
  unfold inversePrimal
  calc
    primal f L z + (2 * L)⁻¹ • gradient (maxValue f) (primal f L z) =
        ((2 * L)⁻¹ • gradient (maxValue f) (primal f L z) + (primal f L z - z)) + z := by abel
    _ = z := by rw [hs, zero_add]

omit [FiniteDimensional ℝ E] in
lemma Hyp.inversePrimal_lipschitz (H : Hyp f gx gy L μ) (x x' : E) :
    ‖inversePrimal f L x - inversePrimal f L x'‖ ≤ (1 + 2 * L / μ) * ‖x - x'‖ := by
  have hi : 0 ≤ (2 * L)⁻¹ := by have := H.hL; positivity
  have he : inversePrimal f L x - inversePrimal f L x' =
      (x - x') + (2 * L)⁻¹ • (gradient (maxValue f) x - gradient (maxValue f) x') := by
    simp only [inversePrimal, smul_sub]
    abel
  rw [he]
  calc
    ‖(x - x') + (2 * L)⁻¹ • (gradient (maxValue f) x - gradient (maxValue f) x')‖ ≤
        ‖x - x'‖ + ‖(2 * L)⁻¹ • (gradient (maxValue f) x - gradient (maxValue f) x')‖ := norm_add_le _ _
    _ = ‖x - x'‖ + (2 * L)⁻¹ * ‖gradient (maxValue f) x - gradient (maxValue f) x'‖ := by
      rw [norm_smul, Real.norm_of_nonneg hi]
    _ ≤ ‖x - x'‖ + (2 * L)⁻¹ * ((4 * L ^ 2 / μ) * ‖x - x'‖) := by
      gcongr
      exact H.value_gradient_lipschitz x x'
    _ = (1 + 2 * L / μ) * ‖x - x'‖ := by field_simp [H.hL.ne', H.hμ.ne']; ring

end OracleTemplate.PLMinimax
