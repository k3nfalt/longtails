import LongTails.Proofs.SpectralGradient
import LongTails.Proofs.TemporalSpectralResponse

open scoped RealInnerProductSpace

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
lemma symmetric_step_bound (H : E →L[ℝ] E) (hs : H.toLinearMap.IsSymmetric)
    {η K : ℝ} (hK : 0 ≤ K)
    (he : ∀ i, |1 - η * hs.eigenvalues rfl i| ≤ K) (x : E) :
    ‖x - η • H x‖ ≤ K * ‖x‖ := by
  let b := hs.eigenvectorBasis rfl
  have hh : x - η • H x =
      TemporalDiscrepancy.diagonalMap b (fun i => 1 - η * hs.eigenvalues rfl i) x := by
    apply b.repr.injective
    ext i
    rw [TemporalDiscrepancy.diagonalMap_coordinate]
    simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [show b.repr (H x) i = hs.eigenvalues rfl i * b.repr x i from
      hs.eigenvectorBasis_apply_self_apply rfl x i]
    ring
  rw [hh]
  exact TemporalDiscrepancy.diagonalMap_bound b _ hK he x

omit [CompleteSpace E] in
lemma probe_step_bound (H : E →L[ℝ] E) (hs : H.toLinearMap.IsSymmetric)
    {μ L : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hlo : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪H x, x⟫)
    (hhi : ∀ x, ⟪H x, x⟫ ≤ L * ‖x‖ ^ 2) (x : E) :
    ‖x - (1 / (2 * L)) • H x‖ ≤ (1 - μ / (2 * L)) * ‖x‖ := by
  have hL : 0 < L := hμ.trans_le hμL
  have hm : μ / (2 * L) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  apply symmetric_step_bound H hs (sub_nonneg.mpr hm)
  intro i
  have he := TemporalDiscrepancy.spectral_eigenvalue_bounds H hs hlo hhi i
  rw [abs_of_nonneg]
  · have hh := div_le_div_of_nonneg_right he.1 (by positivity : 0 ≤ 2 * L)
    simpa [div_eq_mul_inv, mul_comm] using sub_le_sub_left hh 1
  · have hh : hs.eigenvalues rfl i / (2 * L) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [he.2])
    simpa [div_eq_mul_inv, mul_comm] using sub_nonneg.mpr hh

omit [CompleteSpace E] in
lemma correction_step_bound (H : E →L[ℝ] E) (hs : H.toLinearMap.IsSymmetric)
    {μ L β : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hβ : μ ≤ β)
    (hlo : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪H x, x⟫)
    (hhi : ∀ x, ⟪H x, x⟫ ≤ L * ‖x‖ ^ 2) (x : E) :
    ‖x - (1 / β) • H x‖ ≤ (L / μ) * ‖x‖ := by
  have hL : 0 < L := hμ.trans_le hμL
  have hβ0 : 0 < β := hμ.trans_le hβ
  have hk : 1 ≤ L / μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  apply symmetric_step_bound H hs (by positivity)
  intro i
  have he := TemporalDiscrepancy.spectral_eigenvalue_bounds H hs hlo hhi i
  have h0 : 0 ≤ hs.eigenvalues rfl i / β := div_nonneg (hμ.le.trans he.1) hβ0.le
  have h1 : hs.eigenvalues rfl i / β ≤ L / μ :=
    div_le_div₀ hL.le he.2 hμ hβ
  rw [abs_le]
  constructor <;> simp only [one_div_mul_eq_div] <;> linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma sweep_coordinate (C : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hc : ∀ x, l (C x) = c * l x) (rs : List ℝ) (x : E) :
    l (sweep C rs x) = (rs.map (fun r => r * c + (1 - r))).prod * l x := by
  induction rs generalizing x with
  | nil => simp [sweep]
  | cons r rs ih =>
    rw [sweep_cons]
    simp only [map_add, map_smul, smul_eq_mul, ih, hc, List.map_cons, List.prod_cons]
    ring

omit [CompleteSpace E] in
lemma spectral_sweep_annihilates (H : E →L[ℝ] E) (hs : H.toLinearMap.IsSymmetric)
    {a : ℝ} (ha : a ≠ 0) (he : ∀ i, hs.eigenvalues rfl i ≠ 0) (x : E) :
    sweep (LinearMap.id - a • H.toLinearMap)
      (List.ofFn (fun i : Fin (Module.finrank ℝ E) => 1 / (a * hs.eigenvalues rfl i))) x = 0 := by
  let b := hs.eigenvectorBasis rfl
  apply b.repr.injective
  ext i
  let l : E →ₗ[ℝ] ℝ := {
    toFun := fun y => b.repr y i
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  have hl (y : E) : l y = b.repr y i := rfl
  have hc (y : E) : l ((LinearMap.id - a • H.toLinearMap : E →ₗ[ℝ] E) y) =
      (1 - a * hs.eigenvalues rfl i) * l y := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, map_sub, map_smul, smul_eq_mul, hl,
      PiLp.sub_apply, PiLp.smul_apply]
    rw [show b.repr (H y) i = hs.eigenvalues rfl i * b.repr y i from
      hs.eigenvectorBasis_apply_self_apply rfl y i]
    ring
  have hh := sweep_coordinate (LinearMap.id - a • H.toLinearMap) l
    (1 - a * hs.eigenvalues rfl i) hc
    (List.ofFn (fun j : Fin (Module.finrank ℝ E) => 1 / (a * hs.eigenvalues rfl j))) x
  have hz : (List.map (fun r => r * (1 - a * hs.eigenvalues rfl i) + (1 - r))
      (List.ofFn (fun j : Fin (Module.finrank ℝ E) => 1 / (a * hs.eigenvalues rfl j)))).prod = 0 := by
    apply List.prod_eq_zero
    apply List.mem_map.mpr
    refine ⟨1 / (a * hs.eigenvalues rfl i), ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · field_simp [ha, he i]; ring
  rw [hz, zero_mul] at hh
  simpa only [hl, map_zero, PiLp.zero_apply] using hh

end OracleTemplate.SpectralGradient
