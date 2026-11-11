import LongTails.Proofs.SmoothConvexFiniteGeometry
import LongTails.Proofs.SmoothConvexFiniteChain
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SmoothConvexFiniteWall

open SmoothConvexFiniteGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def wall (R : ℝ) (x : E) : ℝ := 2 * ‖x‖ ^ 2 - 4 * R ^ 2

noncomputable def localized (R : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  smoothMax (R ^ 2) (f x) (wall R x)

noncomputable def localizedField (R : ℝ) (f : E → ℝ) (df : E → E) (x : E) : E :=
  weight (R ^ 2) (f x) (wall R x) • df x +
    (1 - weight (R ^ 2) (f x) (wall R x)) • ((4 : ℝ) • x)

lemma wall_gradient (R : ℝ) (x : E) : HasGradientAt (wall R) ((4 : ℝ) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul 2).sub_const (4 * R ^ 2) using 1
  · rfl
  · ext v
    simp only [InnerProductSpace.toDual_apply_apply, smul_apply, smul_eq_mul,
      innerSL_apply_apply, real_inner_smul_left]
    ring

omit [CompleteSpace E] in
lemma wall_convex (R : ℝ) : ConvexOn ℝ Set.univ (wall (E := E) R) := by
  have hc := (convexOn_norm (E := E) convex_univ).pow (fun x _ => norm_nonneg x) 2
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hc.2 hx hy ha hb hab
  change ‖a • x + b • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 at h
  change 2 * ‖a • x + b • y‖ ^ 2 - 4 * R ^ 2 ≤
    a * (2 * ‖x‖ ^ 2 - 4 * R ^ 2) + b * (2 * ‖y‖ ^ 2 - 4 * R ^ 2)
  nlinarith [congrArg (fun t => t * (4 * R ^ 2)) hab]

lemma localized_gradient (R : ℝ) (hR : 0 < R) (f : E → ℝ) (df : E → E)
    (hf : ∀ x, HasGradientAt f (df x) x) (x : E) :
    HasGradientAt (localized R f) (localizedField R f df x) x :=
  smoothMax_gradient (R ^ 2) (sq_pos_of_pos hR) f (wall R) x (df x) ((4 : ℝ) • x)
    (hf x) (wall_gradient R x)

omit [CompleteSpace E] in
lemma localized_convex (R : ℝ) (hR : 0 < R) (f : E → ℝ)
    (hf : ConvexOn ℝ Set.univ f) : ConvexOn ℝ Set.univ (localized R f) :=
  smoothMax_convex (R ^ 2) (sq_pos_of_pos hR) f (wall R) hf (wall_convex R)

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma localized_ge (R : ℝ) (hR : 0 < R) (f : E → ℝ) (x : E) :
    f x ≤ localized R f x := (le_max_left _ _).trans (smoothMax_ge _ _ _ (sq_pos_of_pos hR))

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma localized_zero (R : ℝ) (hR : 0 < R) (f : E → ℝ) (x : E)
    (hf : f x = 0) (hx : ‖x‖ ≤ R) : localized R f x = 0 := by
  have hs := pow_le_pow_left₀ (norm_nonneg x) hx 2
  have h := (smoothMax_eq_left (R ^ 2) (f x) (wall R x) (sq_pos_of_pos hR)
    (by dsimp [wall]; nlinarith [sq_nonneg R])).1
  exact h.trans hf

omit [CompleteSpace E] in
lemma localized_outside (R : ℝ) (hR : 0 < R) (f : E → ℝ) (df : E → E)
    (hu : ∀ x, f x ≤ ‖x‖ ^ 2 + R ^ 2) (x : E) (hx : 3 * R ≤ ‖x‖) :
    localized R f x = wall R x ∧ localizedField R f df x = (4 : ℝ) • x := by
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * R) hx 2
  have h := smoothMax_eq_right (R ^ 2) (f x) (wall R x) (sq_pos_of_pos hR)
    (by dsimp [wall]; nlinarith [hu x, sq_nonneg R])
  exact ⟨h.1, by simp only [localizedField, h.2, zero_smul, sub_zero, one_smul, zero_add]⟩

lemma value_lipschitz_ball (f : E → ℝ) (df : E → E) (B M : ℝ)
    (hf : ∀ x, HasGradientAt f (df x) x)
    (hb : ∀ x, ‖x‖ ≤ B → ‖df x‖ ≤ M) (x y : E) (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    |f x - f y| ≤ M * ‖x - y‖ := by
  have h := (convex_closedBall (0 : E) B).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => by
      rw [(InnerProductSpace.toDual ℝ E).norm_map]
      exact hb z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz))
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  exact h

lemma localized_lipschitz_near (R : ℝ) (hR : 0 < R) (f : E → ℝ) (df : E → E)
    (hf : ∀ x, HasGradientAt f (df x) x)
    (hl : ∀ x y, ‖df x - df y‖ ≤ ‖x - y‖)
    (hb : ∀ x, ‖df x‖ ≤ ‖x‖ + R)
    (x y : E) (hx : ‖x‖ ≤ 4 * R) (hy : ‖y‖ ≤ 4 * R) :
    ‖localizedField R f df x - localizedField R f df y‖ ≤ 512 * ‖x - y‖ := by
  have hf' := value_lipschitz_ball f df (4 * R) (5 * R) hf
    (fun z hz => by linarith [hb z]) x y hx hy
  have hg' := value_lipschitz_ball (wall R) (fun z => (4 : ℝ) • z) (4 * R) (16 * R)
    (wall_gradient R) (fun z hz => by
      rw [norm_smul]
      norm_num
      linarith) x y hx hy
  have hn : ‖df y‖ + ‖(4 : ℝ) • y‖ ≤ 21 * R := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    linarith [hb y]
  have hl' : ‖df x - df y‖ ≤ 4 * ‖x - y‖ := by linarith [hl x y, norm_nonneg (x - y)]
  have hr : ‖(4 : ℝ) • x - (4 : ℝ) • y‖ ≤ 4 * ‖x - y‖ := by
    rw [← smul_sub, norm_smul]
    norm_num
  have h := smoothMax_field_lipschitz (R ^ 2) (21 * R) 4 (sq_pos_of_pos hR)
    (by positivity) f (wall R) df (fun z => (4 : ℝ) • z) x y hl' hr (by linarith) hn
  have he : (4 : ℝ) + (21 * R) ^ 2 / R ^ 2 = 445 := by field_simp; ring
  rw [he] at h
  exact h.trans (by nlinarith [norm_nonneg (x - y)])

omit [CompleteSpace E] in
lemma localized_lipschitz_far (R : ℝ) (hR : 0 < R) (f : E → ℝ) (df : E → E)
    (hu : ∀ x, f x ≤ ‖x‖ ^ 2 + R ^ 2) (hb : ∀ x, ‖df x‖ ≤ ‖x‖ + R)
    (x y : E) (hy : 4 * R < ‖y‖) :
    ‖localizedField R f df x - localizedField R f df y‖ ≤ 512 * ‖x - y‖ := by
  rw [(localized_outside R hR f df hu y (by linarith)).2]
  by_cases hx : 3 * R ≤ ‖x‖
  · rw [(localized_outside R hR f df hu x hx).2, ← smul_sub, norm_smul]
    norm_num
    nlinarith [norm_nonneg (x - y)]
  · have hd : R ≤ ‖x - y‖ := by
      have h := norm_sub_norm_le y x
      rw [norm_sub_rev] at h
      linarith
    let t := weight (R ^ 2) (f x) (wall R x)
    have ht : 0 ≤ t := weight_nonneg _ _ _
    have ht' : t ≤ 1 := weight_le_one _ _ _
    have he : localizedField R f df x - (4 : ℝ) • y =
        t • (df x - (4 : ℝ) • x) + (4 : ℝ) • (x - y) := by
      dsimp [localizedField, t]
      module
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    norm_num
    have hn : ‖df x - (4 : ℝ) • x‖ ≤ 16 * R := by
      have h := norm_sub_le (df x) ((4 : ℝ) • x)
      rw [norm_smul] at h
      norm_num at h
      linarith [hb x]
    have hs := mul_le_mul ht' hn (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [norm_nonneg (x - y)]

lemma localized_lipschitz (R : ℝ) (hR : 0 < R) (f : E → ℝ) (df : E → E)
    (hf : ∀ x, HasGradientAt f (df x) x)
    (hl : ∀ x y, ‖df x - df y‖ ≤ ‖x - y‖)
    (hu : ∀ x, f x ≤ ‖x‖ ^ 2 + R ^ 2) (hb : ∀ x, ‖df x‖ ≤ ‖x‖ + R)
    (x y : E) : ‖localizedField R f df x - localizedField R f df y‖ ≤ 512 * ‖x - y‖ := by
  by_cases hx : ‖x‖ ≤ 4 * R
  · by_cases hy : ‖y‖ ≤ 4 * R
    · exact localized_lipschitz_near R hR f df hf hl hb x y hx hy
    · exact localized_lipschitz_far R hR f df hu hb x y (lt_of_not_ge hy)
  · have h := localized_lipschitz_far R hR f df hu hb y x (lt_of_not_ge hx)
    simpa only [norm_sub_rev] using h

open FiniteSumNondualLowerComponents SmoothConvexFiniteChain

noncomputable def objective {d k : ℕ} (L R δ a : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  L / 512 * localized R (hardComponent 1 δ a π (fun _ => (0 : Fin 1)) 0) x

noncomputable def field {d k : ℕ} (L R δ a : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (L / 512) • localizedField R (hardComponent 1 δ a π (fun _ => (0 : Fin 1)) 0)
    (hardGradient 1 δ a π (fun _ => (0 : Fin 1)) 0) x

lemma objective_gradient {d k : ℕ} (L R δ a : ℝ) (hR : 0 < R) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (objective L R δ a π) (field L R δ a π x) x := by
  have h := localized_gradient R hR _ _
    (hardComponent_gradient 1 δ a hδ π (fun _ => (0 : Fin 1)) 0) x
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  unfold objective field
  rw [map_smul]
  exact h.const_mul (L / 512)

lemma objective_convex {d k : ℕ} (L R δ a : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) : ConvexOn ℝ Set.univ (objective L R δ a π) :=
  (localized_convex R hR _ (hardComponent_convex 1 δ a (by norm_num) hδ π
    (fun _ => (0 : Fin 1)) 0)).smul (by positivity : 0 ≤ L / 512)

lemma objective_nonneg {d k : ℕ} (L R δ a : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ objective L R δ a π x :=
  mul_nonneg (by positivity) ((hardComponent_nonneg 1 δ a (by norm_num) π
    (fun _ => (0 : Fin 1)) 0 x).trans (localized_ge R hR _ x))

lemma hiddenPoint_radius {d k : ℕ} (R a : ℝ) (hR : 0 ≤ R)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2) :
    ‖hiddenPoint π a‖ ≤ R := by
  have h := hiddenPoint_norm_sq π a
  nlinarith [norm_nonneg (hiddenPoint π a)]

lemma objective_minimum {d k : ℕ} (L R δ a : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2) :
    objective L R δ a π (hiddenPoint π a) = 0 ∧
      IsMinOn (objective L R δ a π) Set.univ (hiddenPoint π a) := by
  have hz : objective L R δ a π (hiddenPoint π a) = 0 := by
    unfold objective
    rw [localized_zero R hR _ _ (hardComponent_hiddenPoint 1 δ a hδ π
      (fun _ => (0 : Fin 1)) 0) (hiddenPoint_radius R a hR.le π ha), mul_zero]
  exact ⟨hz, fun x _ => hz ▸ objective_nonneg L R δ a hL hR π x⟩

lemma chain_upper_radius {d k : ℕ} (R δ a : ℝ) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) :
    hardComponent 1 δ a π (fun _ => (0 : Fin 1)) 0 x ≤ ‖x‖ ^ 2 + R ^ 2 := by
  have h := chain_upper δ a hδ π x
  nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sq_nonneg a), sq_nonneg R]

lemma field_lipschitz {d k : ℕ} (L R δ a : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2)
    (x y : EuclideanSpace ℝ (Fin d)) : ‖field L R δ a π x - field L R δ a π y‖ ≤ L * ‖x - y‖ := by
  have h := localized_lipschitz R hR _ _
    (hardComponent_gradient 1 δ a hδ π (fun _ => (0 : Fin 1)) 0)
    (fun x y => by simpa only [one_mul] using
      hardGradient_lipschitz 1 δ a (by norm_num) hδ π (fun _ => (0 : Fin 1)) 0 x y)
    (chain_upper_radius R δ a hδ π ha)
    (chain_gradient_bound δ a R hδ π (hiddenPoint_radius R a hR.le π ha)) x y
  unfold field
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ L / 512)]
  have hs := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ L / 512)
  nlinarith

lemma field_outside {d k : ℕ} (L R δ a : ℝ) (hR : 0 < R) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) (hx : 3 * R ≤ ‖x‖) :
    field L R δ a π x = (L / 128) • x := by
  unfold field
  rw [(localized_outside R hR _ _ (chain_upper_radius R δ a hδ π ha) x hx).2, smul_smul]
  congr 1
  ring

lemma objective_gap {d k : ℕ} (L R δ a : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (hscale : ((k : ℝ) + 1) * δ ≤ a / 8) (htail : |x (π (Fin.last k))| ≤ δ / 4) :
    L * a ^ 2 ≤ 8192 * ((k : ℝ) + 1) * objective L R δ a π x := by
  have h := hardComponent_gap 1 δ a (by norm_num) hδ ha π (fun _ => (0 : Fin 1)) x
    k le_rfl hscale htail
  simp only [Fin.sum_univ_one, one_mul] at h
  have hg := localized_ge R hR (hardComponent 1 δ a π (fun _ => (0 : Fin 1)) 0) x
  have hs := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 16 * ((k : ℝ) + 1))
  have hl := mul_le_mul_of_nonneg_left (h.trans hs) hL
  dsimp [objective]
  nlinarith only [hl]

end LongTails.Proofs.SmoothConvexFiniteWall
