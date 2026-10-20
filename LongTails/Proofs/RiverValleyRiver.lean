import LongTails.Proofs.RiverValleyModel
import LongTails.Proofs.RiverValleyCalculus
import LongTails.Proofs.RiverValleyAlgebra

open scoped RealInnerProductSpace

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection] {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}

noncomputable def Jr (K : Submodule ℝ E) [K.HasOrthogonalProjection] (Jφ : E → E →L[ℝ] E)
    (y : E) : E →L[ℝ] E := (Jφ y).comp Kᗮ.starProjection

noncomputable def ar (K : Submodule ℝ E) [K.HasOrthogonalProjection] (gh : E → E) (y : E) : E :=
  Kᗮ.starProjection (gh y)

noncomputable def mr (K : Submodule ℝ E) [K.HasOrthogonalProjection] (gh : E → E)
    (Jφ : E → E →L[ℝ] E) (y : E) : E := mvec (Jr K Jφ y) (ar K gh y)

omit [FiniteDimensional ℝ E] in
lemma starProj_norm_le (U : Submodule ℝ E) [U.HasOrthogonalProjection] (z : E) :
    ‖U.starProjection z‖ ≤ ‖z‖ :=
  (U.starProjection.le_opNorm z).trans
    (mul_le_of_le_one_left (norm_nonneg _) (Submodule.starProjection_norm_le U))

omit [FiniteDimensional ℝ E] in
lemma starProj_opNorm_le (U : Submodule ℝ E) [U.HasOrthogonalProjection] :
    ‖U.starProjection‖ ≤ 1 := Submodule.starProjection_norm_le U


noncomputable def X1lin (K : Submodule ℝ E) [K.HasOrthogonalProjection] (gh : E → E)
    (Hh : E → E →L[ℝ] E) (Jφ : E → E →L[ℝ] E) (DJ : E → E →L[ℝ] E →L[ℝ] E) (z : E) :
    E →ₗ[ℝ] E where
  toFun δ := (DJ z δ).comp Kᗮ.starProjection (ar K gh z) +
      Jr K Jφ z (Kᗮ.starProjection (Hh z δ)) -
      ((DJ z δ).comp Kᗮ.starProjection
          (ContinuousLinearMap.adjoint (Jr K Jφ z) (mr K gh Jφ z)) +
        Jr K Jφ z (ContinuousLinearMap.adjoint ((DJ z δ).comp Kᗮ.starProjection) (mr K gh Jφ z)))
  map_add' δ δ' := by
    simp only [map_add, ContinuousLinearMap.add_comp, add_apply]
    abel
  map_smul' c δ := by
    simp only [map_smul, ContinuousLinearMap.smul_comp, smul_apply,
      RingHom.id_apply, smul_sub, smul_add]

noncomputable def Dmr (K : Submodule ℝ E) [K.HasOrthogonalProjection] (gh : E → E)
    (Hh : E → E →L[ℝ] E) (Jφ : E → E →L[ℝ] E) (DJ : E → E →L[ℝ] E →L[ℝ] E) (z : E) :
    E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    (((Sinv (Jr K Jφ z)).symm : E →ₗ[ℝ] E).comp (X1lin K gh Hh Jφ DJ z))

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

lemma Jφ_mem (y z : E) : Jφ y z ∈ K :=
  deriv_mem K.closed_of_finiteDimensional H.hJφ H.φK y z

lemma Jφ_river (y z : E) : ‖Jφ y (Kᗮ.starProjection z)‖ ≤ (Luv / μ) * ‖Kᗮ.starProjection z‖ := by
  set v := Jφ y (Kᗮ.starProjection z)
  have hv : v ∈ K := H.Jφ_mem _ _
  have h1 := H.A_lower v hv
  have h2 : ⟪A v, v⟫ ≤ ‖A v‖ * ‖v‖ := real_inner_le_norm _ _
  have h3 : ‖A v‖ ≤ Luv * ‖Kᗮ.starProjection z‖ := H.cross y z
  have hμ := H.μpos
  have key : μ * ‖v‖ ≤ Luv * ‖Kᗮ.starProjection z‖ := by
    by_cases hv0 : ‖v‖ = 0
    · rw [hv0, mul_zero]; exact mul_nonneg H.Luv_nn (norm_nonneg _)
    · have hvp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
      have : μ * ‖v‖ ^ 2 ≤ Luv * ‖Kᗮ.starProjection z‖ * ‖v‖ := by
        nlinarith [mul_le_mul_of_nonneg_right h3 (norm_nonneg v)]
      nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  linarith

lemma Jr_norm (y : E) : ‖Jr K Jφ y‖ ≤ Luv / μ := by
  have hΓ : 0 ≤ Luv / μ := div_nonneg H.Luv_nn H.μpos.le
  refine ContinuousLinearMap.opNorm_le_bound _ hΓ fun z => ?_
  exact (H.Jφ_river y z).trans (mul_le_mul_of_nonneg_left (starProj_norm_le _ z) hΓ)

lemma Jr_sub (y y' : E) : ‖Jr K Jφ y - Jr K Jφ y'‖ ≤ LJ * ‖y - y'‖ := by
  have e : Jr K Jφ y - Jr K Jφ y' = (Jφ y - Jφ y').comp Kᗮ.starProjection := by
    simp [Jr, ContinuousLinearMap.sub_comp]
  rw [e]
  calc _ ≤ ‖Jφ y - Jφ y'‖ * ‖Kᗮ.starProjection‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Jφ y - Jφ y'‖ * 1 := mul_le_mul_of_nonneg_left (starProj_opNorm_le _) (norm_nonneg _)
    _ ≤ LJ * ‖y - y'‖ := by rw [mul_one]; exact H.J_lip y y'

lemma ar_norm (y : E) : ‖ar K gh y‖ ≤ G := (starProj_norm_le _ _).trans (H.gh_bdd y)

lemma ar_sub (y y' : E) : ‖ar K gh y - ar K gh y'‖ ≤ Lh * ‖y - y'‖ := by
  simp only [ar, ← map_sub]
  exact (starProj_norm_le _ _).trans (H.gh_lip y y')

lemma mr_bounds (y : E) :
    ‖mr K gh Jφ y‖ ≤ (Luv / μ) * ‖ar K gh y‖ ∧
      (1 + (Luv / μ) ^ 2) * ⟪mr K gh Jφ y, Jr K Jφ y (ar K gh y)⟫ ≤
        (Luv / μ) ^ 2 * ‖ar K gh y‖ ^ 2 :=
  mvec_bounds _ (div_nonneg H.Luv_nn H.μpos.le) (H.Jr_norm y) _

lemma mr_norm (y : E) : ‖mr K gh Jφ y‖ ≤ (Luv / μ) * G :=
  (H.mr_bounds y).1.trans (mul_le_mul_of_nonneg_left (H.ar_norm y) (div_nonneg H.Luv_nn H.μpos.le))

lemma Ja_sub (y y' : E) :
    ‖Jr K Jφ y (ar K gh y) - Jr K Jφ y' (ar K gh y')‖ ≤ (Luv / μ * Lh + LJ * G) * ‖y - y'‖ := by
  have e : Jr K Jφ y (ar K gh y) - Jr K Jφ y' (ar K gh y') =
      Jr K Jφ y (ar K gh y - ar K gh y') + (Jr K Jφ y - Jr K Jφ y') (ar K gh y') := by
    simp [map_sub]
  rw [e]
  have hΓ : 0 ≤ Luv / μ := div_nonneg H.Luv_nn H.μpos.le
  calc _ ≤ ‖Jr K Jφ y (ar K gh y - ar K gh y')‖ + ‖(Jr K Jφ y - Jr K Jφ y') (ar K gh y')‖ :=
        norm_add_le _ _
    _ ≤ Luv / μ * (Lh * ‖y - y'‖) + LJ * ‖y - y'‖ * G := by
        gcongr
        · exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (H.Jr_norm y) (H.ar_sub y y') (norm_nonneg _) hΓ)
        · exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (H.Jr_sub y y') (H.ar_norm y') (norm_nonneg _)
              (mul_nonneg H.LJ_nn (norm_nonneg _)))
    _ = (Luv / μ * Lh + LJ * G) * ‖y - y'‖ := by ring

lemma S_sub (y y' : E) : ‖Smap (Jr K Jφ y) - Smap (Jr K Jφ y')‖ ≤ 2 * (Luv / μ) * LJ * ‖y - y'‖ := by
  refine (Smap_sub_norm _ _).trans ?_
  have := H.Jr_sub y y'
  have h1 := H.Jr_norm y
  have h2 := H.Jr_norm y'
  have : 0 ≤ ‖y - y'‖ := norm_nonneg _
  calc ‖Jr K Jφ y - Jr K Jφ y'‖ * (‖Jr K Jφ y‖ + ‖Jr K Jφ y'‖)
      ≤ (LJ * ‖y - y'‖) * (Luv / μ + Luv / μ) :=
        mul_le_mul (H.Jr_sub y y') (add_le_add h1 h2) (by positivity)
          (mul_nonneg H.LJ_nn (norm_nonneg _))
    _ = 2 * (Luv / μ) * LJ * ‖y - y'‖ := by ring

lemma mr_lip (y y' : E) :
    ‖mr K gh Jφ y - mr K gh Jφ y'‖ ≤
      (Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G) * ‖y - y'‖ := by
  set J := Jr K Jφ y
  set J' := Jr K Jφ y'
  have e : mr K gh Jφ y - mr K gh Jφ y' =
      (Sinv J).symm (J (ar K gh y) - J' (ar K gh y')) +
        ((Sinv J).symm (J' (ar K gh y')) - (Sinv J').symm (J' (ar K gh y'))) := by
    simp only [mr, mvec, map_sub, J, J']; abel
  rw [e]
  have hΓ : 0 ≤ Luv / μ := div_nonneg H.Luv_nn H.μpos.le
  have hJa : ‖J' (ar K gh y')‖ ≤ Luv / μ * G :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (H.Jr_norm y') (H.ar_norm y')
      (norm_nonneg _) hΓ)
  calc _ ≤ ‖(Sinv J).symm (J (ar K gh y) - J' (ar K gh y'))‖ +
        ‖(Sinv J).symm (J' (ar K gh y')) - (Sinv J').symm (J' (ar K gh y'))‖ := norm_add_le _ _
    _ ≤ (Luv / μ * Lh + LJ * G) * ‖y - y'‖ + 2 * (Luv / μ) * LJ * ‖y - y'‖ * (Luv / μ * G) := by
        gcongr
        · exact (Sinv_norm _ _).trans (H.Ja_sub y y')
        · exact (Sinv_sub _ _ _).trans (mul_le_mul (H.S_sub y y') hJa (norm_nonneg _)
            (by have := H.LJ_nn; positivity))
    _ = _ := by ring


lemma DJ_norm (z : E) : ‖DJ z‖ ≤ LJ := deriv_norm_le H.hDJ H.LJ_nn H.J_lip z

lemma Hh_norm (z : E) : ‖Hh z‖ ≤ Lh := deriv_norm_le H.hHh H.Lh_nn H.gh_lip z

lemma DJr_norm (z δ : E) : ‖(DJ z δ).comp Kᗮ.starProjection‖ ≤ LJ * ‖δ‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by calc ‖DJ z δ‖ * ‖Kᗮ.starProjection‖ ≤ ‖DJ z δ‖ * 1 :=
            mul_le_mul_of_nonneg_left (starProj_opNorm_le _) (norm_nonneg _)
          _ ≤ LJ * ‖δ‖ := by
            rw [mul_one]; exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (H.DJ_norm z) (norm_nonneg _)))

lemma Jr_taylor (z δ : E) :
    ‖Jr K Jφ (z + δ) - Jr K Jφ z - (DJ z δ).comp Kᗮ.starProjection‖ ≤ ρJ * ‖δ‖ ^ 2 := by
  have e : Jr K Jφ (z + δ) - Jr K Jφ z - (DJ z δ).comp Kᗮ.starProjection =
      (Jφ (z + δ) - Jφ z - DJ z δ).comp Kᗮ.starProjection := by
    simp [Jr, ContinuousLinearMap.sub_comp]
  rw [e]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖Jφ (z + δ) - Jφ z - DJ z δ‖ * ‖Kᗮ.starProjection‖
      ≤ ‖Jφ (z + δ) - Jφ z - DJ z δ‖ * 1 :=
        mul_le_mul_of_nonneg_left (starProj_opNorm_le _) (norm_nonneg _)
    _ ≤ ρJ * ‖δ‖ ^ 2 := by rw [mul_one]; exact taylor_lip H.hDJ H.ρJ_nn H.DJ_lip z δ

lemma ar_taylor (z δ : E) :
    ‖ar K gh (z + δ) - ar K gh z - Kᗮ.starProjection (Hh z δ)‖ ≤ ρh * ‖δ‖ ^ 2 := by
  simp only [ar, ← map_sub]
  exact (starProj_norm_le _ _).trans (taylor_lip H.hHh H.ρh_nn H.Hh_lip z δ)

lemma X1_norm (z δ : E) :
    ‖X1lin K gh Hh Jφ DJ z δ‖ ≤
      (Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G) * ‖δ‖ := by
  have hΓ : 0 ≤ Luv / μ := div_nonneg H.Luv_nn H.μpos.le
  set Γ := Luv / μ
  set D := (DJ z δ).comp Kᗮ.starProjection
  set J := Jr K Jφ z
  set m := mr K gh Jφ z
  have hD := H.DJr_norm z δ
  have hJ : ‖J‖ ≤ Γ := H.Jr_norm z
  have hm : ‖m‖ ≤ Γ * G := H.mr_norm z
  have ha : ‖ar K gh z‖ ≤ G := H.ar_norm z
  have hδ := norm_nonneg δ
  have hG := H.G_nn
  have hLJ := H.LJ_nn
  have t1 : ‖D (ar K gh z)‖ ≤ LJ * ‖δ‖ * G :=
    (D.le_opNorm _).trans (mul_le_mul hD ha (norm_nonneg _) (by positivity))
  have t2 : ‖J (Kᗮ.starProjection (Hh z δ))‖ ≤ Γ * (Lh * ‖δ‖) :=
    (J.le_opNorm _).trans (mul_le_mul hJ ((starProj_norm_le _ _).trans
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (H.Hh_norm z) hδ))) (norm_nonneg _) hΓ)
  have t3 : ‖D (ContinuousLinearMap.adjoint J m)‖ ≤ LJ * ‖δ‖ * (Γ * (Γ * G)) :=
    (D.le_opNorm _).trans (mul_le_mul hD ((ContinuousLinearMap.le_opNorm _ _).trans
      (by rw [adjoint_norm]; exact mul_le_mul hJ hm (norm_nonneg _) hΓ)) (norm_nonneg _)
      (by positivity))
  have t4 : ‖J (ContinuousLinearMap.adjoint D m)‖ ≤ Γ * (LJ * ‖δ‖ * (Γ * G)) :=
    (J.le_opNorm _).trans (mul_le_mul hJ ((ContinuousLinearMap.le_opNorm _ _).trans
      (by rw [adjoint_norm]; exact mul_le_mul hD hm (norm_nonneg _) (by positivity)))
      (norm_nonneg _) hΓ)
  show ‖D (ar K gh z) + J (Kᗮ.starProjection (Hh z δ)) -
      (D (ContinuousLinearMap.adjoint J m) + J (ContinuousLinearMap.adjoint D m))‖ ≤ _
  calc _ ≤ ‖D (ar K gh z)‖ + ‖J (Kᗮ.starProjection (Hh z δ))‖ +
        (‖D (ContinuousLinearMap.adjoint J m)‖ + ‖J (ContinuousLinearMap.adjoint D m)‖) :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ LJ * ‖δ‖ * G + Γ * (Lh * ‖δ‖) + (LJ * ‖δ‖ * (Γ * (Γ * G)) + Γ * (LJ * ‖δ‖ * (Γ * G))) := by
        gcongr
    _ = _ := by ring

lemma mr_second (z δ : E) :
    ‖mr K gh Jφ (z + δ) - mr K gh Jφ z - Dmr K gh Hh Jφ DJ z δ‖ ≤
      (G * ρJ + LJ * Lh + Luv / μ * ρh + Luv / μ * G * (2 * (Luv / μ) * ρJ + LJ ^ 2) +
        2 * (Luv / μ) * LJ * (Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G)) * ‖δ‖ ^ 2 := by
  have hΓ : 0 ≤ Luv / μ := div_nonneg H.Luv_nn H.μpos.le
  set Γ := Luv / μ
  set J := Jr K Jφ z
  set J' := Jr K Jφ (z + δ)
  set D := (DJ z δ).comp Kᗮ.starProjection
  set a := ar K gh z
  set a' := ar K gh (z + δ)
  set m := mr K gh Jφ z
  set m' := mr K gh Jφ (z + δ)
  set X1 := X1lin K gh Hh Jφ DJ z δ
  set X := J' a' - J a - (Smap J' - Smap J) m
  have hSm : Smap J m = J a := Smap_Sinv J _
  have hSm' : Smap J' m' = J' a' := Smap_Sinv J' _
  have hmX : m' - m = (Sinv J').symm X := by
    apply Smap_injective J'
    rw [Smap_Sinv, map_sub, hSm']
    simp only [X, sub_apply, hSm]
    abel
  have hD : Dmr K gh Hh Jφ DJ z δ = (Sinv J).symm X1 := rfl
  have hXX : X - X1 = (J' - J - D) a' + D (a' - a) + J (a' - a - Kᗮ.starProjection (Hh z δ)) -
      ((J' - J - D) (ContinuousLinearMap.adjoint J' m) + J (ContinuousLinearMap.adjoint (J' - J - D) m) +
        D (ContinuousLinearMap.adjoint (J' - J) m)) := by
    simp only [X, X1, X1lin, LinearMap.coe_mk, AddHom.coe_mk, Smap, map_sub,
      sub_apply, add_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, D, J, J', a, a', m]
    abel
  have hδ := norm_nonneg δ
  have hG := H.G_nn
  have hLJ := H.LJ_nn
  have hρJ := H.ρJ_nn
  have hT : ‖J' - J - D‖ ≤ ρJ * ‖δ‖ ^ 2 := H.Jr_taylor z δ
  have hDn : ‖D‖ ≤ LJ * ‖δ‖ := H.DJr_norm z δ
  have hJ : ‖J‖ ≤ Γ := H.Jr_norm z
  have hJ' : ‖J'‖ ≤ Γ := H.Jr_norm (z + δ)
  have hm : ‖m‖ ≤ Γ * G := H.mr_norm z
  have ha' : ‖a'‖ ≤ G := H.ar_norm _
  have hda : ‖a' - a‖ ≤ Lh * ‖δ‖ := by
    have := H.ar_sub (z + δ) z; rwa [add_sub_cancel_left] at this
  have hdJ : ‖J' - J‖ ≤ LJ * ‖δ‖ := by
    have := H.Jr_sub (z + δ) z; rwa [add_sub_cancel_left] at this
  have hta := H.ar_taylor z δ
  have hadj : ∀ T : E →L[ℝ] E, ‖ContinuousLinearMap.adjoint T m‖ ≤ ‖T‖ * (Γ * G) := by
    intro T
    calc _ ≤ ‖ContinuousLinearMap.adjoint T‖ * ‖m‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖T‖ * (Γ * G) := by
        rw [adjoint_norm]; exact mul_le_mul_of_nonneg_left hm (norm_nonneg _)
  have hXXn : ‖X - X1‖ ≤ (G * ρJ + LJ * Lh + Γ * ρh + Γ * G * (2 * Γ * ρJ + LJ ^ 2)) * ‖δ‖ ^ 2 := by
    rw [hXX]
    have e1 : ‖(J' - J - D) a'‖ ≤ ρJ * ‖δ‖ ^ 2 * G :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hT ha' (norm_nonneg _) (by positivity))
    have e2 : ‖D (a' - a)‖ ≤ LJ * ‖δ‖ * (Lh * ‖δ‖) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hDn hda (norm_nonneg _) (by positivity))
    have e3 : ‖J (a' - a - Kᗮ.starProjection (Hh z δ))‖ ≤ Γ * (ρh * ‖δ‖ ^ 2) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hJ hta (norm_nonneg _) hΓ)
    have e4 : ‖(J' - J - D) (ContinuousLinearMap.adjoint J' m)‖ ≤ ρJ * ‖δ‖ ^ 2 * (Γ * (Γ * G)) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hT ((hadj J').trans
        (mul_le_mul_of_nonneg_right hJ' (by positivity))) (norm_nonneg _) (by positivity))
    have e5 : ‖J (ContinuousLinearMap.adjoint (J' - J - D) m)‖ ≤ Γ * (ρJ * ‖δ‖ ^ 2 * (Γ * G)) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hJ ((hadj _).trans
        (mul_le_mul_of_nonneg_right hT (by positivity))) (norm_nonneg _) hΓ)
    have e6 : ‖D (ContinuousLinearMap.adjoint (J' - J) m)‖ ≤ LJ * ‖δ‖ * (LJ * ‖δ‖ * (Γ * G)) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hDn ((hadj _).trans
        (mul_le_mul_of_nonneg_right hdJ (by positivity))) (norm_nonneg _) (by positivity))
    calc _ ≤ ‖(J' - J - D) a'‖ + ‖D (a' - a)‖ + ‖J (a' - a - Kᗮ.starProjection (Hh z δ))‖ +
          (‖(J' - J - D) (ContinuousLinearMap.adjoint J' m)‖ +
            ‖J (ContinuousLinearMap.adjoint (J' - J - D) m)‖ +
            ‖D (ContinuousLinearMap.adjoint (J' - J) m)‖) :=
          (norm_sub_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))
            ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)))
      _ ≤ ρJ * ‖δ‖ ^ 2 * G + LJ * ‖δ‖ * (Lh * ‖δ‖) + Γ * (ρh * ‖δ‖ ^ 2) +
          (ρJ * ‖δ‖ ^ 2 * (Γ * (Γ * G)) + Γ * (ρJ * ‖δ‖ ^ 2 * (Γ * G)) +
            LJ * ‖δ‖ * (LJ * ‖δ‖ * (Γ * G))) := by gcongr
      _ = _ := by ring
  have hX1 := H.X1_norm z δ
  have hS : ‖Smap J' - Smap J‖ ≤ 2 * Γ * LJ * ‖δ‖ := by
    have := H.S_sub (z + δ) z; rwa [add_sub_cancel_left] at this
  have e : m' - m - Dmr K gh Hh Jφ DJ z δ =
      (Sinv J').symm (X - X1) + ((Sinv J').symm X1 - (Sinv J).symm X1) := by
    rw [hmX, hD, show (Sinv J').symm (X - X1) = (Sinv J').symm X - (Sinv J').symm X1 from
      map_sub _ _ _]; abel
  rw [e]
  calc _ ≤ ‖(Sinv J').symm (X - X1)‖ + ‖(Sinv J').symm X1 - (Sinv J).symm X1‖ := norm_add_le _ _
    _ ≤ (G * ρJ + LJ * Lh + Γ * ρh + Γ * G * (2 * Γ * ρJ + LJ ^ 2)) * ‖δ‖ ^ 2 +
        2 * Γ * LJ * ‖δ‖ * ((Γ * Lh + LJ * G + 2 * Γ ^ 2 * LJ * G) * ‖δ‖) := by
        gcongr
        · exact (Sinv_norm _ _).trans hXXn
        · exact (Sinv_sub _ _ _).trans (mul_le_mul hS hX1 (norm_nonneg _) (by positivity))
    _ = _ := by ring

end Model

end OracleTemplate.RiverValley
