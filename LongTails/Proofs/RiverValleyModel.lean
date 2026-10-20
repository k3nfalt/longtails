import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure Model (K : Submodule ℝ E) [K.HasOrthogonalProjection] (h : E → ℝ) (gh : E → E)
    (Hh : E → E →L[ℝ] E) (φ : E → E) (Jφ : E → E →L[ℝ] E) (DJ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E →L[ℝ] E) (Lh ρh G Luv μ Lv LJ ρJ : ℝ) : Prop where
  hgh : ∀ y, HasGradientAt h (gh y) y
  gh_lip : ∀ y y', ‖gh y - gh y'‖ ≤ Lh * ‖y - y'‖
  hHh : ∀ y, HasFDerivAt gh (Hh y) y
  Hh_lip : ∀ y y', ‖Hh y - Hh y'‖ ≤ ρh * ‖y - y'‖
  gh_bdd : ∀ y, ‖gh y‖ ≤ G
  φK : ∀ y, φ y ∈ K
  hJφ : ∀ y, HasFDerivAt φ (Jφ y) y
  J_lip : ∀ y y', ‖Jφ y - Jφ y'‖ ≤ LJ * ‖y - y'‖
  hDJ : ∀ y, HasFDerivAt Jφ (DJ y) y
  DJ_lip : ∀ y y', ‖DJ y - DJ y'‖ ≤ ρJ * ‖y - y'‖
  A_sym : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫
  A_K : ∀ k ∈ K, A k ∈ K
  A_lower : ∀ k ∈ K, μ * ‖k‖ ^ 2 ≤ ⟪A k, k⟫
  A_upper : ∀ k ∈ K, ‖A k‖ ≤ Lv * ‖k‖
  cross : ∀ y z, ‖A (Jφ y (Kᗮ.starProjection z))‖ ≤ Luv * ‖Kᗮ.starProjection z‖
  μpos : 0 < μ
  μ_le : μ ≤ Lv
  Lh_nn : 0 ≤ Lh
  ρh_nn : 0 ≤ ρh
  G_nn : 0 ≤ G
  Luv_nn : 0 ≤ Luv
  LJ_nn : 0 ≤ LJ
  ρJ_nn : 0 ≤ ρJ

variable {K : Submodule ℝ E} [K.HasOrthogonalProjection] {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}

noncomputable def wv (K : Submodule ℝ E) [K.HasOrthogonalProjection] (φ : E → E) (x : E) : E :=
  K.starProjection x - φ (Kᗮ.starProjection x)

noncomputable def fval (K : Submodule ℝ E) [K.HasOrthogonalProjection] (h : E → ℝ) (φ : E → E)
    (A : E →L[ℝ] E) (x : E) : ℝ :=
  h (Kᗮ.starProjection x) + 1 / 2 * ⟪A (wv K φ x), wv K φ x⟫

noncomputable def gradF (K : Submodule ℝ E) [K.HasOrthogonalProjection] (gh : E → E) (φ : E → E)
    (Jφ : E → E →L[ℝ] E) (A : E →L[ℝ] E) (x : E) : E :=
  Kᗮ.starProjection (gh (Kᗮ.starProjection x)) + A (wv K φ x) -
    Kᗮ.starProjection (ContinuousLinearMap.adjoint (Jφ (Kᗮ.starProjection x)) (A (wv K φ x)))

lemma wv_mem (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ) (x : E) : wv K φ x ∈ K :=
  K.sub_mem (K.starProjection_apply_mem x) (H.φK _)

omit [FiniteDimensional ℝ E] in
lemma inner_K_orth {k z : E} (hk : k ∈ K) : ⟪k, Kᗮ.starProjection z⟫ = 0 :=
  Submodule.inner_right_of_mem_orthogonal hk (Kᗮ.starProjection_apply_mem z)

lemma Model.hasGradient (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ) (x : E) :
    HasGradientAt (fval K h φ A) (gradF K gh φ Jφ A x) x := by
  set Q := Kᗮ.starProjection
  set P := K.starProjection
  have hQ : HasFDerivAt (fun y => Q y) Q x := Q.hasFDerivAt
  have hP : HasFDerivAt (fun y => P y) P x := P.hasFDerivAt
  have hh : HasFDerivAt (fun y => h (Q y))
      ((InnerProductSpace.toDual ℝ E (gh (Q x))).toContinuousLinearMap.comp Q) x :=
    ((H.hgh (Q x)).hasFDerivAt).comp x hQ
  have hφ : HasFDerivAt (fun y => φ (Q y)) ((Jφ (Q x)).comp Q) x := (H.hJφ (Q x)).comp x hQ
  have hw : HasFDerivAt (wv K φ) (P - (Jφ (Q x)).comp Q) x := hP.sub hφ
  have hAw : HasFDerivAt (fun y => A (wv K φ y)) (A.comp (P - (Jφ (Q x)).comp Q)) x :=
    A.hasFDerivAt.comp x hw
  have hq := hAw.inner ℝ hw
  have hf := hh.add (hq.const_mul (1 / 2 : ℝ))
  rw [hasGradientAt_iff_hasFDerivAt]
  have hfe : fval K h φ A = (fun y => h (Q y)) + fun y => 1 / 2 * ⟪A (wv K φ y), wv K φ y⟫ := rfl
  rw [hfe]
  refine hf.congr_fderiv ?_
  ext z
  have hQs : ∀ a b : E, ⟪Q a, b⟫ = ⟪a, Q b⟫ := fun a b => Kᗮ.starProjection_isSymmetric a b
  have hadj : ∀ a b : E, ⟪ContinuousLinearMap.adjoint (Jφ (Q x)) a, b⟫ = ⟪a, Jφ (Q x) b⟫ :=
    fun a b => ContinuousLinearMap.adjoint_inner_left _ _ _
  have hPQ : P z = z - Q z := by
    simp only [P, Q, Submodule.starProjection_orthogonal_val]; abel
  set w := wv K φ x
  have hAwK : A w ∈ K := H.A_K _ (wv_mem H x)
  have h0 : ⟪A w, Q z⟫ = 0 := inner_K_orth hAwK
  have key : ⟪gradF K gh φ Jφ A x, z⟫ = ⟪gh (Q x), Q z⟫ + ⟪A w, P z - Jφ (Q x) (Q z)⟫ := by
    simp only [gradF]
    rw [inner_sub_left, inner_add_left, hQs, hQs (ContinuousLinearMap.adjoint (Jφ (Q x)) (A w)),
      hadj, hPQ, inner_sub_right, inner_sub_right, h0]
    ring
  have key2 : ⟪A (P z - Jφ (Q x) (Q z)), w⟫ = ⟪A w, P z - Jφ (Q x) (Q z)⟫ := by
    rw [H.A_sym, real_inner_comm]
  simp [fderivInnerCLM_apply]
  rw [key, ← map_sub, ← key2]
  ring

end OracleTemplate.RiverValley
