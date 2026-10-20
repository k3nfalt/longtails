import LongTails.Proofs.RiverValleyRiver
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection]

omit [FiniteDimensional ℝ E] in
lemma P_add_Q (x : E) : K.starProjection x + Kᗮ.starProjection x = x := by
  rw [Submodule.starProjection_orthogonal_val]; abel

omit [FiniteDimensional ℝ E] in
lemma Q_of_mem {v : E} (hv : v ∈ K) : Kᗮ.starProjection v = 0 := by
  rw [Submodule.starProjection_orthogonal_val, (Submodule.starProjection_eq_self_iff).mpr hv,
    sub_self]

omit [FiniteDimensional ℝ E] in
lemma P_of_mem {v : E} (hv : v ∈ K) : K.starProjection v = v :=
  (Submodule.starProjection_eq_self_iff).mpr hv

omit [FiniteDimensional ℝ E] in
lemma Q_of_orth {v : E} (hv : v ∈ Kᗮ) : Kᗮ.starProjection v = v :=
  (Submodule.starProjection_eq_self_iff).mpr hv

omit [FiniteDimensional ℝ E] in
lemma P_of_orth {v : E} (hv : v ∈ Kᗮ) : K.starProjection v = 0 := by
  have h := P_add_Q (K := K) v
  rw [Q_of_orth hv] at h
  simpa using h

omit [FiniteDimensional ℝ E] in
lemma Q_mem (x : E) : Kᗮ.starProjection x ∈ Kᗮ := Kᗮ.starProjection_apply_mem x

omit [FiniteDimensional ℝ E] in
lemma Q_idem (x : E) : Kᗮ.starProjection (Kᗮ.starProjection x) = Kᗮ.starProjection x :=
  Q_of_orth (Q_mem x)

lemma adj_Q : ContinuousLinearMap.adjoint (Kᗮ.starProjection) = Kᗮ.starProjection :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr Kᗮ.starProjection_isSymmetric).adjoint_eq

lemma adjJ_eq (Jφ : E → E →L[ℝ] E) (y v : E) :
    ContinuousLinearMap.adjoint (Jr K Jφ y) v =
      Kᗮ.starProjection (ContinuousLinearMap.adjoint (Jφ y) v) := by
  simp only [Jr, ContinuousLinearMap.adjoint_comp, adj_Q, ContinuousLinearMap.comp_apply]

lemma adjJ_mem (Jφ : E → E →L[ℝ] E) (y v : E) :
    ContinuousLinearMap.adjoint (Jr K Jφ y) v ∈ Kᗮ := by
  rw [adjJ_eq]; exact Q_mem _

omit [FiniteDimensional ℝ E] in
lemma ar_inner (gh : E → E) (x d : E) (hd : d ∈ Kᗮ) : ⟪gh x, d⟫ = ⟪ar K gh x, d⟫ := by
  have h1 := P_add_Q (K := K) (gh x)
  have h0 : ⟪K.starProjection (gh x), d⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem _) hd
  calc ⟪gh x, d⟫ = ⟪K.starProjection (gh x) + Kᗮ.starProjection (gh x), d⟫ := by rw [h1]
    _ = ⟪ar K gh x, d⟫ := by rw [inner_add_left, h0, zero_add]; rfl

omit [FiniteDimensional ℝ E] in
lemma Jr_orth (Jφ : E → E →L[ℝ] E) (y d : E) (hd : d ∈ Kᗮ) : Jr K Jφ y d = Jφ y d := by
  rw [Jr, ContinuousLinearMap.comp_apply, Q_of_orth hd]

variable {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}

lemma gradF_eq (x : E) :
    gradF K gh φ Jφ A x = ar K gh (Kᗮ.starProjection x) + A (wv K φ x) -
      ContinuousLinearMap.adjoint (Jr K Jφ (Kᗮ.starProjection x)) (A (wv K φ x)) := by
  rw [adjJ_eq]; rfl

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

lemma Aw_mem (x : E) : A (wv K φ x) ∈ K := H.A_K _ (wv_mem H x)

lemma Q_step (x : E) (η : ℝ) (ζ : E) :
    Kᗮ.starProjection (x - η • (gradF K gh φ Jφ A x + ζ)) = Kᗮ.starProjection x -
      η • (ar K gh (Kᗮ.starProjection x) -
        ContinuousLinearMap.adjoint (Jr K Jφ (Kᗮ.starProjection x)) (A (wv K φ x)) +
          Kᗮ.starProjection ζ) := by
  rw [gradF_eq, map_sub, map_smul, map_add, map_sub, map_add, Q_of_mem (H.Aw_mem x),
    Q_of_orth (adjJ_mem Jφ _ _), ar, Q_idem]
  congr 2; abel

lemma P_step (x : E) (η : ℝ) (ζ : E) :
    K.starProjection (x - η • (gradF K gh φ Jφ A x + ζ)) = K.starProjection x -
      η • (A (wv K φ x) + K.starProjection ζ) := by
  rw [gradF_eq, map_sub, map_smul, map_add, map_sub, map_add, P_of_mem (H.Aw_mem x),
    P_of_orth (adjJ_mem Jφ _ _), ar, P_of_orth (Q_mem _)]
  congr 2; abel



lemma potential_path (x : E) (η : ℝ) (ζ : E) (x' d : E)
    (hx' : x' = x - η • (gradF K gh φ Jφ A x + ζ))
    (hdd : d = Kᗮ.starProjection x' - Kᗮ.starProjection x) :
    h (Kᗮ.starProjection x') + ⟪mr K gh Jφ (Kᗮ.starProjection x'), wv K φ x'⟫ ≤
      h (Kᗮ.starProjection x) + ⟪mr K gh Jφ (Kᗮ.starProjection x), wv K φ x⟫ -
        η * (‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 - ⟪mr K gh Jφ (Kᗮ.starProjection x),
          Jr K Jφ (Kᗮ.starProjection x) (ar K gh (Kᗮ.starProjection x))⟫) -
        η * ⟪ar K gh (Kᗮ.starProjection x), Kᗮ.starProjection ζ⟫ -
        η * ⟪mr K gh Jφ (Kᗮ.starProjection x), K.starProjection ζ -
          Jr K Jφ (Kᗮ.starProjection x) (Kᗮ.starProjection ζ)⟫ -
        ⟪mr K gh Jφ (Kᗮ.starProjection x), φ (Kᗮ.starProjection x + d) -
          φ (Kᗮ.starProjection x) - Jφ (Kᗮ.starProjection x) d⟫ + Lh / 2 * ‖d‖ ^ 2 +
        ⟪mr K gh Jφ (Kᗮ.starProjection x + d) - mr K gh Jφ (Kᗮ.starProjection x), wv K φ x'⟫ := by
  set y := Kᗮ.starProjection x
  set a := ar K gh y
  set J := Jr K Jφ y
  set m := mr K gh Jφ y
  set w := wv K φ x
  set r := φ (y + d) - φ y - Jφ y d
  have hQ := H.Q_step x η ζ
  have hP := H.P_step x η ζ
  rw [← hx'] at hQ hP
  have hd : d = -(η • (a - ContinuousLinearMap.adjoint J (A w) + Kᗮ.starProjection ζ)) := by
    rw [hdd, hQ]; abel
  have hdm : d ∈ Kᗮ := by rw [hdd]; exact Kᗮ.sub_mem (Q_mem _) (Q_mem _)
  have hyd : Kᗮ.starProjection x' = y + d := by rw [hdd]; abel
  have hw' : wv K φ x' = w - η • (A w + K.starProjection ζ) - J d - r := by
    simp only [wv, hP, hyd, r, w, Jr_orth Jφ y d hdm, J]; abel
  have hh := Gradient.smooth_upper_bound H.hgh H.gh_lip y (y + d)
  rw [add_sub_cancel_left, ar_inner gh y d hdm] at hh
  have hSm : Smap J m = J a := Smap_Sinv J _
  have hS : ⟪m, A w⟫ + ⟪m, J (ContinuousLinearMap.adjoint J (A w))⟫ = ⟪J a, A w⟫ := by
    rw [← hSm, Smap_symm]
    simp [Smap, inner_add_right]
  have hadj : ⟪a, ContinuousLinearMap.adjoint J (A w)⟫ = ⟪J a, A w⟫ :=
    ContinuousLinearMap.adjoint_inner_right _ _ _
  have e1 : ⟪mr K gh Jφ (Kᗮ.starProjection x'), wv K φ x'⟫ =
      ⟪m, w⟫ + ⟪m, wv K φ x' - w⟫ + ⟪mr K gh Jφ (y + d) - m, wv K φ x'⟫ := by
    rw [hyd, inner_sub_left, inner_sub_right]; ring
  have e2 : ⟪m, wv K φ x' - w⟫ = -η * ⟪m, A w⟫ - η * ⟪m, K.starProjection ζ⟫ - ⟪m, J d⟫ -
      ⟪m, r⟫ := by
    rw [hw']
    simp only [inner_sub_right, inner_smul_right, inner_add_right]
    ring
  have e3 : ⟪m, J d⟫ = -η * (⟪m, J a⟫ - ⟪m, J (ContinuousLinearMap.adjoint J (A w))⟫ +
      ⟪m, J (Kᗮ.starProjection ζ)⟫) := by
    rw [hd]; simp only [map_neg, map_smul, map_add, map_sub, inner_neg_right, inner_smul_right,
      inner_add_right, inner_sub_right]; ring
  have e4 : ⟪a, d⟫ = -η * (‖a‖ ^ 2 - ⟪a, ContinuousLinearMap.adjoint J (A w)⟫ +
      ⟪a, Kᗮ.starProjection ζ⟫) := by
    rw [hd]; simp only [inner_neg_right, inner_smul_right, inner_add_right, inner_sub_right,
      real_inner_self_eq_norm_sq]; ring
  have key : h (y + d) ≤ h y - η * ‖a‖ ^ 2 + η * ⟪J a, A w⟫ - η * ⟪a, Kᗮ.starProjection ζ⟫ +
      Lh / 2 * ‖d‖ ^ 2 := by
    rw [e4, hadj] at hh; linarith
  have hS' : η * ⟪m, A w⟫ + η * ⟪m, J (ContinuousLinearMap.adjoint J (A w))⟫ =
      η * ⟪J a, A w⟫ := by rw [← hS]; ring
  rw [e1, e2, e3, hyd]
  simp only [inner_sub_right]
  linear_combination key - hS'


lemma w_path (x : E) (η : ℝ) (ζ : E) (x' d : E)
    (hx' : x' = x - η • (gradF K gh φ Jφ A x + ζ))
    (hdd : d = Kᗮ.starProjection x' - Kᗮ.starProjection x) :
    wv K φ x' = (wv K φ x - η • (A (wv K φ x) + Jr K Jφ (Kᗮ.starProjection x)
        (ContinuousLinearMap.adjoint (Jr K Jφ (Kᗮ.starProjection x)) (A (wv K φ x)))) +
        η • Jr K Jφ (Kᗮ.starProjection x) (ar K gh (Kᗮ.starProjection x))) -
      η • (K.starProjection ζ - Jr K Jφ (Kᗮ.starProjection x) (Kᗮ.starProjection ζ)) -
      (φ (Kᗮ.starProjection x + d) - φ (Kᗮ.starProjection x) - Jφ (Kᗮ.starProjection x) d) := by
  set y := Kᗮ.starProjection x
  set J := Jr K Jφ y
  have hQ := H.Q_step x η ζ
  have hP := H.P_step x η ζ
  rw [← hx'] at hQ hP
  have hdm : d ∈ Kᗮ := by rw [hdd]; exact Kᗮ.sub_mem (Q_mem _) (Q_mem _)
  have hyd : Kᗮ.starProjection x' = y + d := by rw [hdd]; abel
  have hd : d = -(η • (ar K gh y - ContinuousLinearMap.adjoint J (A (wv K φ x)) +
      Kᗮ.starProjection ζ)) := by rw [hdd, hQ]; abel
  have hJd : Jφ y d = J d := (Jr_orth Jφ y d hdm).symm
  simp only [wv, hP, hyd]
  rw [hJd, hd]
  simp only [map_neg, map_smul, map_add, map_sub, smul_add, smul_sub, wv]
  abel

lemma adjJA_norm (x : E) :
    ‖ContinuousLinearMap.adjoint (Jr K Jφ (Kᗮ.starProjection x)) (A (wv K φ x))‖ ≤
      Luv * ‖wv K φ x‖ := by
  set J := Jr K Jφ (Kᗮ.starProjection x)
  set w := wv K φ x
  set v := ContinuousLinearMap.adjoint J (A w)
  have hv : ‖v‖ ^ 2 = ⟪A w, J v⟫ := by
    rw [← real_inner_self_eq_norm_sq]; exact ContinuousLinearMap.adjoint_inner_left _ _ _
  have hJv : ⟪A w, J v⟫ = ⟪w, A (J v)⟫ := H.A_sym _ _
  have hcross : ‖A (J v)‖ ≤ Luv * ‖v‖ := by
    have := H.cross (Kᗮ.starProjection x) v
    have hvo : v ∈ Kᗮ := adjJ_mem Jφ _ _
    rw [Q_of_orth hvo] at this
    simpa [J, Jr, Q_of_orth hvo] using this
  have h2 : ⟪w, A (J v)⟫ ≤ ‖w‖ * (Luv * ‖v‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hcross (norm_nonneg _))
  by_cases hv0 : ‖v‖ = 0
  · rw [hv0]; exact mul_nonneg H.Luv_nn (norm_nonneg _)
  · have hvp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
    nlinarith

lemma A_cocoercive {k : E} (hk : k ∈ K) : ‖A k‖ ^ 2 ≤ Lv * ⟪A k, k⟫ := by
  have hAk : A k ∈ K := H.A_K k hk
  have hLv : 0 < Lv := lt_of_lt_of_le H.μpos H.μ_le
  set t := 1 / Lv
  have hz : k - t • A k ∈ K := K.sub_mem hk (K.smul_mem t hAk)
  have h0 := le_trans (mul_nonneg H.μpos.le (sq_nonneg _)) (H.A_lower _ hz)
  have hsym : ⟪A (A k), k⟫ = ⟪A k, A k⟫ := H.A_sym _ _
  have hup : ⟪A (A k), A k⟫ ≤ Lv * ‖A k‖ ^ 2 :=
    (real_inner_le_norm _ _).trans (by
      have := H.A_upper (A k) hAk
      nlinarith [norm_nonneg (A k), norm_nonneg (A (A k))])
  rw [map_sub, map_smul] at h0
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, hsym, real_inner_self_eq_norm_sq] at h0
  have ht : t * Lv = 1 := by simp [t, hLv.ne']
  have ht0 : 0 ≤ t := by positivity
  have h2 := mul_le_mul_of_nonneg_left hup (sq_nonneg t)
  have h3 : t ^ 2 * (Lv * ‖A k‖ ^ 2) = t * ‖A k‖ ^ 2 := by
    calc t ^ 2 * (Lv * ‖A k‖ ^ 2) = t * (t * Lv) * ‖A k‖ ^ 2 := by ring
      _ = t * ‖A k‖ ^ 2 := by rw [ht, mul_one]
  have key : 0 ≤ ⟪A k, k⟫ - t * ‖A k‖ ^ 2 := by
    nlinarith [h2, h3, h0]
  have : ‖A k‖ ^ 2 = Lv * (t * ‖A k‖ ^ 2) := by rw [← mul_assoc, mul_comm Lv t, ht, one_mul]
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) hLv.le

end Model

end OracleTemplate.RiverValley
