import LongTails.Algorithms.HessianAdaptiveCubic
import LongTails.Proofs.CappedCubicModel
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.HessianAdaptiveCubicModel

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic

lemma minimize_spec {E : Type*} [TopologicalSpace E] (C : Set E) (fallback : E)
    (φ : E → ℝ) (hC : IsCompact C) (hne : C.Nonempty) (hφ : ContinuousOn φ C) :
    minimize C fallback φ ∈ C ∧ IsMinOn φ C (minimize C fallback φ) := by
  classical
  have hex : ∃ x ∈ C, IsMinOn φ C x := hC.exists_isMinOn hne hφ
  simpa only [minimize, dite_eq_left hex] using hex.choose_spec

lemma continuous_model {d : ℕ} (z g : Point d) (H : Point d →L[ℝ] Point d) (q c : ℝ) :
    Continuous (model z g H q c) := by
  unfold model
  fun_prop

lemma model_minimize_spec {d : ℕ} (C : ConvexBody (Point d)) (fallback z g : Point d)
    (H : Point d →L[ℝ] Point d) (q c : ℝ) :
    minimize C fallback (model z g H q c) ∈ C ∧
      IsMinOn (model z g H q c) C (minimize C fallback (model z g H q c)) :=
  minimize_spec C fallback _ C.isCompact C.nonempty (continuous_model z g H q c).continuousOn

def modelGradient {d : ℕ} (z g : Point d) (H : Point d →L[ℝ] Point d)
    (q c : ℝ) (x : Point d) : Point d :=
  g + H (x - z) + (2 * q + 3 * c * ‖x - z‖) • (x - z)

lemma model_hasFDerivAt {d : ℕ} (z g : Point d) (H : Point d →L[ℝ] Point d)
    (q c : ℝ) (x : Point d) (hH : ∀ u v, ⟪u, H v⟫ = ⟪H u, v⟫) :
    HasFDerivAt (model z g H q c) (innerSL ℝ (modelGradient z g H q c x)) x := by
  have h := (CappedCubicModel.model_hasFDerivAt H g q (3 * c) (x - z) hH).comp x
    ((hasFDerivAt_id x).sub_const z)
  convert h using 1
  · ext y
    simp only [Function.comp_def, model, CappedCubicModel.model, id_eq]
    ring
  · ext y
    simp [modelGradient]

lemma model_min_variational {d : ℕ} (C : ConvexBody (Point d)) {z g x : Point d}
    {H : Point d →L[ℝ] Point d} {q c : ℝ}
    (hH : ∀ u v, ⟪u, H v⟫ = ⟪H u, v⟫) (hx : x ∈ C)
    (hmin : IsMinOn (model z g H q c) C x) :
    ∀ y ∈ C, 0 ≤ ⟪modelGradient z g H q c x, y - x⟫ := by
  intro y hy
  exact hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
    (model_hasFDerivAt z g H q c x hH).hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (C.convex.segment_subset hx hy))

lemma radial_monotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : 0 ≤ ⟪‖x‖ • x - ‖y‖ • y, x - y⟫ := by
  have hi := mul_le_mul_of_nonneg_left (real_inner_le_norm x y)
    (add_nonneg (norm_nonneg x) (norm_nonneg y))
  have hp := mul_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y))
    (sq_nonneg (‖x‖ - ‖y‖))
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  have hcomm : ⟪y, x⟫ = ⟪x, y⟫ := real_inner_comm _ _
  rw [hcomm]
  nlinarith

lemma continuous_unique_minimizer {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (φ : X → Y → ℝ) (m : X → Y)
    (hφ : Continuous (Function.uncurry φ))
    (hmin : ∀ p y, φ p (m p) ≤ φ p y)
    (hunique : ∀ p y, (∀ z, φ p y ≤ φ p z) → y = m p) : Continuous m := by
  apply continuous_of_isClosed_graph
  have hgraph : Function.graph m = ⋂ y : Y, {z : X × Y | φ z.1 z.2 ≤ φ z.1 y} := by
    ext ⟨p, z⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    change m p = z ↔ ∀ y, φ p z ≤ φ p y
    constructor
    · intro hz y
      simpa only [← hz] using hmin p y
    · intro hz
      exact (hunique p z hz).symm
  rw [hgraph]
  apply isClosed_iInter
  intro y
  exact isClosed_le hφ (hφ.comp (continuous_fst.prodMk continuous_const))

lemma model_strong_monotone {d : ℕ} (z g x y : Point d)
    (H : Point d →L[ℝ] Point d) (q c : ℝ) (hH : IsPSD H) (hc : 0 ≤ c) :
    2 * q * ‖x - y‖ ^ 2 ≤
      ⟪modelGradient z g H q c x - modelGradient z g H q c y, x - y⟫ := by
  have hid : modelGradient z g H q c x - modelGradient z g H q c y =
      H (x - y) + (2 * q) • (x - y) +
        (3 * c) • (‖x - z‖ • (x - z) - ‖y - z‖ • (y - z)) := by
    simp only [modelGradient, map_sub]
    module
  rw [hid, inner_add_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hv := radial_monotone (x - z) (y - z)
  have heq : (x - z) - (y - z) = x - y := by abel
  rw [heq] at hv
  have hp := mul_nonneg (show 0 ≤ 3 * c by positivity) hv
  have hpsd : 0 ≤ ⟪H (x - y), x - y⟫ := by
    rw [real_inner_comm]
    exact hH.2 (x - y)
  linarith

lemma model_min_unique {d : ℕ} (C : ConvexBody (Point d)) {z g x y : Point d}
    {H : Point d →L[ℝ] Point d} {q c : ℝ} (hH : IsPSD H) (hq : 0 < q)
    (hc : 0 ≤ c) (hx : x ∈ C) (hy : y ∈ C)
    (hmx : IsMinOn (model z g H q c) C x) (hmy : IsMinOn (model z g H q c) C y) :
    x = y := by
  have hvx := model_min_variational C hH.1 hx hmx y hy
  have hvy := model_min_variational C hH.1 hy hmy x hx
  have hm := model_strong_monotone z g x y H q c hH hc
  have hi : ⟪modelGradient z g H q c x, y - x⟫ =
      -⟪modelGradient z g H q c x, x - y⟫ := by
    rw [← neg_sub x y, inner_neg_right]
  rw [hi] at hvx
  rw [inner_sub_left] at hm
  have hz : ‖x - y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x - y‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x - y)]))

lemma continuous_model_minimize {X : Type*} [TopologicalSpace X] {d : ℕ}
    (C : ConvexBody (Point d)) (fallback : Point d)
    (z g : X → Point d) (H : X → Point d →L[ℝ] Point d) (q c : X → ℝ)
    (hz : Continuous z) (hg : Continuous g) (hH : Continuous H)
    (hq : Continuous q) (hc : Continuous c)
    (hPSD : ∀ p, IsPSD (H p)) (hqpos : ∀ p, 0 < q p) (hcpos : ∀ p, 0 ≤ c p) :
    Continuous (fun p => minimize C fallback (model (z p) (g p) (H p) (q p) (c p))) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp C.isCompact
  let m : X → C := fun p => ⟨minimize C fallback
    (model (z p) (g p) (H p) (q p) (c p)), (model_minimize_spec C fallback _ _ _ _ _).1⟩
  have hm : Continuous m := by
    apply continuous_unique_minimizer
      (fun p (x : C) => model (z p) (g p) (H p) (q p) (c p) x) m
    · unfold Function.uncurry model
      fun_prop
    · intro p y
      exact (model_minimize_spec C fallback _ _ _ _ _).2 y.property
    · intro p y hy
      apply Subtype.ext
      apply model_min_unique C (hPSD p) (hqpos p) (hcpos p) y.property (m p).property
      · intro x hx
        exact hy ⟨x, hx⟩
      · exact (model_minimize_spec C fallback _ _ _ _ _).2
  exact continuous_subtype_val.comp hm

lemma scaled_model_gradient {d : ℕ} (z g u : Point d)
    (H : Point d →L[ℝ] Point d) (α β κ : ℝ) (hα : 0 ≤ α) :
    modelGradient z g (α • H) (α * β / 2) (κ * α ^ 2 / 3) u =
      g + H (α • (u - z)) + (α * (β + κ * ‖α • (u - z)‖)) • (u - z) := by
  simp only [modelGradient, smul_apply, map_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hα]
  congr 2
  ring

lemma primal_variational {d : ℕ} (C : ConvexBody (Point d)) (fallback z g : Point d)
    (H : Point d →L[ℝ] Point d) (α β κ : ℝ) (hα : 0 ≤ α) (hH : IsPSD H) :
    let u := minimize C fallback (model z g (α • H) (α * β / 2) (κ * α ^ 2 / 3))
    ∀ x ∈ C, 0 ≤ ⟪g + H (α • (u - z)) +
      (α * (β + κ * ‖α • (u - z)‖)) • (u - z), x - u⟫ := by
  dsimp only
  have hm := model_minimize_spec C fallback z g (α • H) (α * β / 2) (κ * α ^ 2 / 3)
  have hs : ∀ x y, ⟪x, (α • H) y⟫ = ⟪(α • H) x, y⟫ := by
    intro x y
    simp only [smul_apply, real_inner_smul_right,
      real_inner_smul_left, hH.1 x y]
  have hv := model_min_variational C hs hm.1 hm.2
  rw [scaled_model_gradient z g _ H α β κ hα] at hv
  exact hv

lemma dual_variational {d : ℕ} (C : ConvexBody (Point d)) (fallback z g : Point d)
    (κ a : ℝ) :
    let v := minimize C fallback (model z g 0 (κ / (2 * a)) 0)
    ∀ x ∈ C, 0 ≤ ⟪g + (κ / a) • (v - z), x - v⟫ := by
  dsimp only
  have hm := model_minimize_spec C fallback z g 0 (κ / (2 * a)) 0
  have hs : ∀ x y : Point d, ⟪x, (0 : Point d →L[ℝ] Point d) y⟫ =
      ⟪(0 : Point d →L[ℝ] Point d) x, y⟫ := by simp
  have hv := model_min_variational C hs hm.1 hm.2
  have he : 2 * (κ / (2 * a)) = κ / a := by ring
  simpa only [modelGradient, zero_apply, add_zero, zero_mul, mul_zero,
    he] using hv

lemma measurable_model_minimize {X : Type*} [MeasurableSpace X] {d : ℕ}
    (C : ConvexBody (Point d)) (fallback : Point d)
    (z g : X → Point d) (H : X → Point d →L[ℝ] Point d) (q c : X → ℝ)
    (hz : Measurable z) (hg : Measurable g) (hH : Measurable H)
    (hq : Measurable q) (hc : Measurable c)
    (hPSD : ∀ p, IsPSD (H p)) (hqpos : ∀ p, 0 < q p) (hcpos : ∀ p, 0 ≤ c p) :
    Measurable (fun p => minimize C fallback (model (z p) (g p) (H p) (q p) (c p))) := by
  let S := {v : (Point d × Point d) × ((Point d →L[ℝ] Point d) × (ℝ × ℝ)) |
    IsPSD v.2.1 ∧ 0 < v.2.2.1 ∧ 0 ≤ v.2.2.2}
  let φ : S → Point d := fun v => minimize C fallback
    (model v.val.1.1 v.val.1.2 v.val.2.1 v.val.2.2.1 v.val.2.2.2)
  have hφ : Continuous φ := continuous_model_minimize C fallback
    (fun v : S => v.val.1.1) (fun v : S => v.val.1.2) (fun v : S => v.val.2.1)
    (fun v : S => v.val.2.2.1) (fun v : S => v.val.2.2.2)
    (continuous_subtype_val.fst.fst) (continuous_subtype_val.fst.snd)
    (continuous_subtype_val.snd.fst) (continuous_subtype_val.snd.snd.fst)
    (continuous_subtype_val.snd.snd.snd)
    (fun v => v.property.1) (fun v => v.property.2.1) (fun v => v.property.2.2)
  let ψ : X → S := fun x => ⟨((z x, g x), (H x, (q x, c x))), hPSD x, hqpos x, hcpos x⟩
  have hψ : Measurable ψ :=
    ((hz.prodMk hg).prodMk (hH.prodMk (hq.prodMk hc))).subtype_mk
  have hcomp : Measurable (φ ∘ ψ) := hφ.measurable.comp hψ
  exact hcomp

lemma isPSD_zero {d : ℕ} : IsPSD (0 : Point d →L[ℝ] Point d) := by
  constructor <;> intros <;> simp

lemma isPSD_smul {d : ℕ} {H : Point d →L[ℝ] Point d} {α : ℝ}
    (hH : IsPSD H) (hα : 0 ≤ α) : IsPSD (α • H) := by
  constructor
  · intro x y
    simp only [smul_apply, real_inner_smul_left, real_inner_smul_right, hH.1 x y]
  · intro x
    simpa only [smul_apply, real_inner_smul_right] using mul_nonneg hα (hH.2 x)

end LongTails.Proofs.HessianAdaptiveCubicModel
