import LongTails.Algorithms.Muon
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
open MeasureTheory Matrix Filter Topology
namespace OracleTemplate.Muon
variable {m n : ℕ}

section Abstract
variable (A : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) (lam c : Fin n → ℝ)

theorem frob_eq_trace (X : Matrix (Fin m) (Fin n) ℝ) :
    ∑ p, ∑ q, A p q * X p q = (Aᵀ * X).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem gram_diag (hVV : Vᵀ * V = 1) (hAV : Aᵀ * A * V = V * diagonal lam) :
    (A * V)ᵀ * (A * V) = diagonal lam := by
  open Matrix Topology Filter in
  (
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hAV, ← Matrix.mul_assoc, hVV,
      Matrix.one_mul])

theorem trace_orth (hVV : Vᵀ * V = 1) (hAV : Aᵀ * A * V = V * diagonal lam) :
    (Aᵀ * (A * V * diagonal c * Vᵀ)).trace = ∑ i, lam i * c i := by
  open Matrix Topology Filter in
  (
    have e : Aᵀ * (A * V * diagonal c * Vᵀ) = (Aᵀ * A * V * diagonal c) * Vᵀ := by
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, hAV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hVV, Matrix.one_mul,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal])

theorem trace_orth_sq (hVV : Vᵀ * V = 1) (hAV : Aᵀ * A * V = V * diagonal lam) :
    ((A * V * diagonal c * Vᵀ)ᵀ * (A * V * diagonal c * Vᵀ)).trace = ∑ i, c i ^ 2 * lam i := by
  open Matrix Topology Filter in
  (
    have e : (A * V * diagonal c * Vᵀ)ᵀ * (A * V * diagonal c * Vᵀ) =
        V * (diagonal c * ((A * V)ᵀ * (A * V)) * diagonal c) * Vᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
        Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hVV, Matrix.one_mul, gram_diag A V lam hVV hAV,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    exact Finset.sum_congr rfl (fun i _ => by ring))

theorem orth_mulVec_sq (hVV : Vᵀ * V = 1) (hAV : Aᵀ * A * V = V * diagonal lam) (x : Fin n → ℝ) :
    ((A * V * diagonal c * Vᵀ) *ᵥ x) ⬝ᵥ ((A * V * diagonal c * Vᵀ) *ᵥ x) =
      ∑ i, c i ^ 2 * lam i * (Vᵀ *ᵥ x) i ^ 2 := by
  open Matrix Topology Filter in
  (
    set y := diagonal c *ᵥ (Vᵀ *ᵥ x)
    have e : (A * V * diagonal c * Vᵀ) *ᵥ x = (A * V) *ᵥ y := by
      simp only [y, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose,
      gram_diag A V lam hVV hAV]
    simp only [y, dotProduct, Matrix.diagonal_transpose, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl (fun i _ => by ring))

theorem parseval (hVV' : V * Vᵀ = 1) (x : Fin n → ℝ) :
    (Vᵀ *ᵥ x) ⬝ᵥ (Vᵀ *ᵥ x) = x ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_transpose, hVV', Matrix.transpose_one, Matrix.one_mulVec]

end Abstract
theorem norm_toLp_sq (w : Fin n → ℝ) : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n))‖ ^ 2 = w ⬝ᵥ w := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

theorem mulVec_dot_le (M : Matrix (Fin m) (Fin n) ℝ) (u : Fin n → ℝ) :
    (M *ᵥ u) ⬝ᵥ (M *ᵥ u) ≤
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ^ 2 * (u ⬝ᵥ u) := by
  open Matrix Topology Filter in
  (
    set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
    have h := T.le_opNorm (WithLp.toLp 2 u)
    have hT : T (WithLp.toLp 2 u) = WithLp.toLp 2 (M *ᵥ u) := rfl
    rw [hT] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [norm_toLp_sq, mul_pow, norm_toLp_sq] at h2
    exact h2)

theorem dot_le_sqrt (u w : Fin n → ℝ) : u ⬝ᵥ w ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (w ⬝ᵥ w) := by
  open Matrix Topology Filter in
  (
    have h := real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 w)
    rw [EuclideanSpace.inner_toLp_toLp] at h
    have hu : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ = Real.sqrt (u ⬝ᵥ u) := by
      rw [← norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)]
    have hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n))‖ = Real.sqrt (w ⬝ᵥ w) := by
      rw [← norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)]
    rw [hu, hw, star_trivial, dotProduct_comm] at h
    exact h)

theorem inner_mat_trace (A X : Mat m n) : inner ℝ A X = ((toMatrix A)ᵀ * toMatrix X).trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp [toMatrix, mul_comm]

theorem unitary_data (W : Mat m n) :
    let V : Matrix (Fin n) (Fin n) ℝ :=
      ((Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    Vᵀ * V = 1 ∧ V * Vᵀ = 1 ∧ (toMatrix W)ᵀ * toMatrix W * V = V * diagonal (gramEigenvalues W) ∧
      ∀ q i, V q i = (rightSingularVectors W i) q := by
  open Matrix Topology Filter in
  (
    intro V
    set hH := Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)
    have hU := hH.eigenvectorUnitary.2
    have hU1 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have hU2 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have hs : star V = Vᵀ := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [hs] at hU1 hU2
    refine ⟨hU2, hU1, ?_, fun q i => ?_⟩
    · have hsp := hH.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at hsp
      have hc : (toMatrix W)ᵀ = (toMatrix W)ᴴ := (Matrix.conjTranspose_eq_transpose_of_trivial _).symm
      rw [hc, hsp]
      change V * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star V * V = V * diagonal (gramEigenvalues W)
      rw [hs, Matrix.mul_assoc, hU2, Matrix.mul_one]
      rfl
    · exact hH.eigenvectorUnitary_apply q i)

theorem toMatrix_ofMatrix (M : Matrix (Fin m) (Fin n) ℝ) : toMatrix (ofMatrix M) = M := by
  exact rfl

theorem toMatrix_orthogonalize (W : Mat m n) :
    let V : Matrix (Fin n) (Fin n) ℝ :=
      ((Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    toMatrix (orthogonalize W) = toMatrix W * V *
      diagonal (fun i => if 0 < singularValues W i then (singularValues W i)⁻¹ else 0) * Vᵀ := by
  intro V
  obtain ⟨-, -, -, hcol0⟩ := unitary_data W
  have hcol : ∀ q i, V q i = (rightSingularVectors W i) q := hcol0
  ext p q
  change (∑ i, (if 0 < singularValues W i then (singularValues W i)⁻¹ else 0) •
    Matrix.vecMulVec (Matrix.mulVec (toMatrix W) (rightSingularVectors W i).ofLp)
      (rightSingularVectors W i).ofLp) p q = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, smul_eq_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [hcol]
  split_ifs <;> ring

theorem coef_mul_eig (x : ℝ) (hx : 0 ≤ x) :
    (if 0 < Real.sqrt x then (Real.sqrt x)⁻¹ else 0) * x = Real.sqrt x := by
  split_ifs with h
  · have hs := Real.sq_sqrt hx
    field_simp
    nlinarith [hs]
  · have : Real.sqrt x = 0 := le_antisymm (not_lt.mp h) (Real.sqrt_nonneg x)
    rw [this, zero_mul]

theorem coef_sq_mul_eig (x : ℝ) (hx : 0 ≤ x) :
    (if 0 < Real.sqrt x then (Real.sqrt x)⁻¹ else 0) ^ 2 * x = if 0 < x then 1 else 0 := by
  by_cases h : 0 < x
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr h
    simp only [hs, h, ite_true]
    rw [inv_pow, Real.sq_sqrt hx, inv_mul_cancel₀ h.ne']
  · have hs : ¬ 0 < Real.sqrt x := by rwa [Real.sqrt_pos]
    simp only [hs, h, ite_false]
    ring

theorem inner_orthogonalize (W : Mat m n) : inner ℝ W (orthogonalize W) = nuclearNorm W := by
  obtain ⟨hVV, -, hAV, -⟩ := unitary_data W
  rw [inner_mat_trace, toMatrix_orthogonalize, trace_orth _ _ _ _ hVV hAV]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  exact coef_mul_eig _ ((Matrix.posSemidef_conjTranspose_mul_self (toMatrix W)).eigenvalues_nonneg i)

theorem norm_orthogonalize_sq (W : Mat m n) :
    ‖orthogonalize W‖ ^ 2 = ∑ i, if 0 < gramEigenvalues W i then (1 : ℝ) else 0 := by
  obtain ⟨hVV, -, hAV, -⟩ := unitary_data W
  rw [← real_inner_self_eq_norm_sq, inner_mat_trace, toMatrix_orthogonalize, trace_orth_sq _ _ _ _ hVV hAV]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact coef_sq_mul_eig _ ((Matrix.posSemidef_conjTranspose_mul_self (toMatrix W)).eigenvalues_nonneg i)

theorem count_pos_le_m (W : Mat m n) :
    (∑ i, if 0 < gramEigenvalues W i then (1 : ℝ) else 0) ≤ m := by
  classical
  obtain ⟨hVV, -, hAV, -⟩ := unitary_data W
  set V : Matrix (Fin n) (Fin n) ℝ :=
      ((Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hg := gram_diag (toMatrix W) V (gramEigenvalues W) hVV hAV
  let S := {i : Fin n // 0 < gramEigenvalues W i}
  let w : S → EuclideanSpace ℝ (Fin m) := fun i => WithLp.toLp 2 (fun p => (toMatrix W * V) p i.1)
  have hin : ∀ i j : S, inner ℝ (w i) (w j) = if i.1 = j.1 then gramEigenvalues W i.1 else 0 := by
    intro i j
    have := congrFun (congrFun hg j.1) i.1
    rw [Matrix.mul_apply] at this
    simp only [Matrix.transpose_apply, Matrix.diagonal_apply] at this
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [dotProduct, star_trivial]
    rw [this]
    by_cases h : i.1 = j.1
    · simp only [h, ite_true]
    · simp only [h, Ne.symm h, ite_false]
  have hli : LinearIndependent ℝ w := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => ?_) (fun i j hij => ?_)
    · intro h0
      have := hin i i
      rw [h0, inner_zero_left] at this
      simp only [ite_true] at this
      exact (ne_of_gt i.2) this.symm
    · show inner ℝ (w i) (w j) = 0
      rw [hin]
      simp only [show i.1 ≠ j.1 from fun h => hij (Subtype.ext h), ite_false]
  have hc := hli.fintype_card_le_finrank
  rw [finrank_euclideanSpace_fin] at hc
  have hsum : (∑ i, if 0 < gramEigenvalues W i then (1 : ℝ) else 0) = (Fintype.card S : ℝ) := by
    rw [Fintype.card_subtype, Finset.sum_boole]
  rw [hsum]
  exact_mod_cast hc

theorem count_pos_le_n (W : Mat m n) :
    (∑ i, if 0 < gramEigenvalues W i then (1 : ℝ) else 0) ≤ n := by
  calc (∑ i, if 0 < gramEigenvalues W i then (1 : ℝ) else 0) ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => by split_ifs <;> norm_num)
    _ = n := by simp

theorem norm_orthogonalize_sq_le (W : Mat m n) : ‖orthogonalize W‖ ^ 2 ≤ (min m n : ℕ) := by
  rw [norm_orthogonalize_sq]
  rcases le_total m n with h | h
  · rw [min_eq_left h]; exact count_pos_le_m W
  · rw [min_eq_right h]; exact count_pos_le_n W

theorem spectralNorm_orthogonalize_le (W : Mat m n) : spectralNorm (orthogonalize W) ≤ 1 := by
  open Matrix Topology Filter in
  (
    obtain ⟨hVV, hVV', hAV, -⟩ := unitary_data W
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [one_mul]
    have hx : x = WithLp.toLp 2 x.ofLp := rfl
    rw [hx]
    change ‖(WithLp.toLp 2 (toMatrix (orthogonalize W) *ᵥ x.ofLp) : EuclideanSpace ℝ (Fin m))‖ ≤ _
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [norm_toLp_sq, norm_toLp_sq, toMatrix_orthogonalize, orth_mulVec_sq _ _ _ _ hVV hAV]
    rw [← parseval _ hVV' x.ofLp]
    simp only [dotProduct]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hce : (if 0 < singularValues W i then (singularValues W i)⁻¹ else 0) ^ 2 * gramEigenvalues W i =
        if 0 < gramEigenvalues W i then 1 else 0 :=
      coef_sq_mul_eig _ ((Matrix.posSemidef_conjTranspose_mul_self (toMatrix W)).eigenvalues_nonneg i)
    rw [hce]
    split_ifs <;> nlinarith [mul_self_nonneg ((((Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x.ofLp) i)])

theorem singularValues_nonneg (W : Mat m n) (i : Fin n) : 0 ≤ singularValues W i := by
  exact Real.sqrt_nonneg _

theorem nuclearNorm_nonneg (W : Mat m n) : 0 ≤ nuclearNorm W := by
  exact Finset.sum_nonneg (fun i _ => singularValues_nonneg W i)

theorem spectralNorm_nonneg (X : Mat m n) : 0 ≤ spectralNorm X := by
  exact norm_nonneg _

theorem inner_le_nuclearNorm_mul_spectralNorm (A X : Mat m n) :
    inner ℝ A X ≤ nuclearNorm A * spectralNorm X := by
  open Matrix Topology Filter in
  (
    obtain ⟨hVV, hVV', hAV, -⟩ := unitary_data A
    set V : Matrix (Fin n) (Fin n) ℝ :=
        ((Matrix.isHermitian_conjTranspose_mul_self (toMatrix A)).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    have hg := gram_diag (toMatrix A) V (gramEigenvalues A) hVV hAV
    set M := toMatrix A
    set N := toMatrix X
    have htr : (Mᵀ * N).trace = ((M * V)ᵀ * (N * V)).trace := by
      have e : (M * V)ᵀ * (N * V) = Vᵀ * (Mᵀ * N * V) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [e]
      conv_rhs => rw [Matrix.trace_mul_comm]
      rw [Matrix.mul_assoc (Mᵀ * N) V Vᵀ, hVV', Matrix.mul_one]
    rw [inner_mat_trace, htr]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    unfold nuclearNorm
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hcs := dot_le_sqrt (fun p => (M * V) p i) (fun p => (N * V) p i)
    have h1 : (fun p => (M * V) p i) ⬝ᵥ (fun p => (M * V) p i) = gramEigenvalues A i := by
      have := congrFun (congrFun hg i) i
      rw [Matrix.mul_apply] at this
      simp only [Matrix.transpose_apply, Matrix.diagonal_apply_eq] at this
      exact this
    have hcolN : (fun p => (N * V) p i) = N *ᵥ (fun q => V q i) := by
      funext p
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hv : (fun q => V q i) ⬝ᵥ (fun q => V q i) = 1 := by
      have := congrFun (congrFun hVV i) i
      rw [Matrix.mul_apply] at this
      simp only [Matrix.transpose_apply, Matrix.one_apply_eq] at this
      exact this
    have h2 := mulVec_dot_le N (fun q => V q i)
    rw [hv, mul_one, ← hcolN] at h2
    have h3 : Real.sqrt ((fun p => (N * V) p i) ⬝ᵥ (fun p => (N * V) p i)) ≤ spectralNorm X := by
      rw [Real.sqrt_le_left (spectralNorm_nonneg X)]
      exact h2
    rw [h1] at hcs
    calc ∑ p, (M * V) p i * (N * V) p i = (fun p => (M * V) p i) ⬝ᵥ (fun p => (N * V) p i) := rfl
      _ ≤ _ := hcs
      _ ≤ singularValues A i * spectralNorm X :=
          mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _))

theorem nuclearNorm_le_sqrt_mul_norm (A : Mat m n) :
    nuclearNorm A ≤ Real.sqrt (min m n : ℕ) * ‖A‖ := by
  rw [← inner_orthogonalize]
  refine (real_inner_le_norm _ _).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)]
  exact norm_orthogonalize_sq_le A

theorem nuclearNorm_le_add_inner (A B : Mat m n) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := by
  rw [← inner_orthogonalize (A + B), inner_add_left]
  have hs := spectralNorm_orthogonalize_le (A + B)
  have h1 := inner_le_nuclearNorm_mul_spectralNorm A (orthogonalize (A + B))
  have h2 := inner_le_nuclearNorm_mul_spectralNorm B (orthogonalize (A + B))
  nlinarith [nuclearNorm_nonneg A, nuclearNorm_nonneg B]

theorem toMatrix_smul (c : ℝ) (X : Mat m n) : toMatrix (c • X) = c • toMatrix X := by
  exact rfl

theorem spectralNorm_smul (c : ℝ) (X : Mat m n) : spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [toMatrix_smul, map_smul, map_smul, norm_smul, Real.norm_eq_abs]

theorem abs_inner_le_nuclearNorm_mul_spectralNorm (A X : Mat m n) :
    |inner ℝ A X| ≤ nuclearNorm A * spectralNorm X := by
  rw [abs_le]
  refine ⟨?_, inner_le_nuclearNorm_mul_spectralNorm A X⟩
  have h := inner_le_nuclearNorm_mul_spectralNorm A ((-1 : ℝ) • X)
  rw [inner_smul_right, spectralNorm_smul] at h
  norm_num at h
  linarith

theorem nuclearNorm_smul_le (c : ℝ) (A : Mat m n) : nuclearNorm (c • A) ≤ |c| * nuclearNorm A := by
  rw [← inner_orthogonalize (c • A), inner_smul_left]
  have hs := spectralNorm_orthogonalize_le (c • A)
  have h1 := abs_inner_le_nuclearNorm_mul_spectralNorm A (orthogonalize (c • A))
  have h2 : (starRingEnd ℝ) c * inner ℝ A (orthogonalize (c • A)) ≤
      |c| * |inner ℝ A (orthogonalize (c • A))| := by
    rw [conj_trivial, ← abs_mul]
    exact le_abs_self _
  have h3 : |inner ℝ A (orthogonalize (c • A))| ≤ nuclearNorm A := by
    nlinarith [nuclearNorm_nonneg A, spectralNorm_nonneg (orthogonalize (c • A))]
  exact h2.trans (mul_le_mul_of_nonneg_left h3 (abs_nonneg c))

theorem nuclearNorm_sub_le (A B : Mat m n) : nuclearNorm (A - B) ≤ nuclearNorm A + nuclearNorm B := by
  rw [sub_eq_add_neg]
  refine (nuclearNorm_le_add_inner A (-B)).trans ?_
  have := nuclearNorm_smul_le (-1) B
  rw [neg_one_smul] at this
  norm_num at this
  linarith

theorem nuclearNorm_sub_comm_le (A B : Mat m n) : nuclearNorm (A - B) ≤ nuclearNorm (B - A) := by
  have := nuclearNorm_smul_le (-1) (B - A)
  rw [neg_one_smul, neg_sub] at this
  norm_num at this
  exact this

theorem orthogonalize_eq_of_svd (W : Mat m n) {k : ℕ} (U : Matrix (Fin m) (Fin k) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) (s : Fin k → ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hs : ∀ l, 0 < s l) (hW : toMatrix W = U * diagonal s * Vᵀ) :
    toMatrix (orthogonalize W) = U * Vᵀ := by
  open Matrix Topology Filter in
  (
    obtain ⟨hEE, hEE', hAE, -⟩ := unitary_data W
    set E : Matrix (Fin n) (Fin n) ℝ :=
        ((Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    set c : Fin n → ℝ := fun i => if 0 < singularValues W i then (singularValues W i)⁻¹ else 0
    have hgram : (toMatrix W)ᵀ * toMatrix W = V * diagonal (fun l => s l * s l) * Vᵀ := by
      rw [hW]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
        Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal s) (diagonal s),
        Matrix.diagonal_mul_diagonal]
    have hkey : toMatrix W * E * diagonal c = U * Vᵀ * E := by
      ext p i
      set e : Fin n → ℝ := fun r => E r i
      set y : Fin k → ℝ := Vᵀ *ᵥ e
      have heig : ((toMatrix W)ᵀ * toMatrix W) *ᵥ e = gramEigenvalues W i • e := by
        funext r
        have h := congrFun (congrFun hAE r) i
        rw [Matrix.mul_diagonal] at h
        change (((toMatrix W)ᵀ * toMatrix W) *ᵥ e) r = _ at h
        rw [h, Pi.smul_apply, smul_eq_mul, mul_comm]
      have hy : ∀ l, s l * s l * y l = gramEigenvalues W i * y l := by
        have h1 : Vᵀ *ᵥ (((toMatrix W)ᵀ * toMatrix W) *ᵥ e) = Vᵀ *ᵥ (gramEigenvalues W i • e) := by rw [heig]
        rw [hgram, Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h1
        rw [show Vᵀ * (V * diagonal (fun l => s l * s l) * Vᵀ) = diagonal (fun l => s l * s l) * Vᵀ by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul]] at h1
        rw [← Matrix.mulVec_mulVec] at h1
        intro l
        have h2 := congrFun h1 l
        rw [Matrix.mulVec_diagonal] at h2
        exact h2
      have hcy : ∀ l, c i * (s l * y l) = y l := by
        intro l
        by_cases hyl : y l = 0
        · rw [hyl]; ring
        · have hl : gramEigenvalues W i = s l * s l := by
            have := hy l
            exact (mul_right_cancel₀ hyl this).symm
          have hsv : singularValues W i = s l := by
            change Real.sqrt (gramEigenvalues W i) = s l
            rw [hl, Real.sqrt_mul_self (hs l).le]
          have hc : c i = (s l)⁻¹ := by
            simp only [c, hsv, hs l, ite_true]
          rw [hc, ← mul_assoc, inv_mul_cancel₀ (hs l).ne', one_mul]
      have hAe : toMatrix W *ᵥ e = U *ᵥ (diagonal s *ᵥ y) := by
        rw [hW, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have lhs : (toMatrix W * E * diagonal c) p i = c i * (toMatrix W *ᵥ e) p := by
        rw [Matrix.mul_diagonal, mul_comm]
        rfl
      have rhs : (U * Vᵀ * E) p i = (U *ᵥ y) p := by
        rw [show y = Vᵀ *ᵥ e from rfl, Matrix.mulVec_mulVec]
        rfl
      have hd : c i • (diagonal s *ᵥ y) = y := by
        funext l
        rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
        exact hcy l
      rw [lhs, rhs, hAe]
      conv_rhs => rw [← hd]
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    rw [toMatrix_orthogonalize]
    change toMatrix W * E * diagonal c * Eᵀ = U * Vᵀ
    rw [hkey, Matrix.mul_assoc, hEE', Matrix.mul_one])

theorem nuclearNorm_eq_of_svd (W : Mat m n) {k : ℕ} (U : Matrix (Fin m) (Fin k) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) (s : Fin k → ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hs : ∀ l, 0 < s l) (hW : toMatrix W = U * diagonal s * Vᵀ) :
    nuclearNorm W = ∑ l, s l := by
  open Matrix Topology Filter in
  (
    rw [← inner_orthogonalize, inner_mat_trace, orthogonalize_eq_of_svd W U V s hU hV hs hW, hW]
    have e : (U * diagonal s * Vᵀ)ᵀ * (U * Vᵀ) = V * (diagonal s * Vᵀ) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
        Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hV, Matrix.mul_one, Matrix.trace_diagonal])

theorem newton_scalar_tendsto (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Tendsto (fun k : ℕ => (fun t : ℝ => t * (3 - x * t ^ 2) / 2)^[k] 1) atTop (𝓝 (Real.sqrt x)⁻¹) := by
  open Matrix Topology Filter in
  (
    set φ : ℝ → ℝ := fun t => t * (3 - x * t ^ 2) / 2
    set g : ℝ → ℝ := fun u => u * (3 - u ^ 2) / 2
    set u : ℕ → ℝ := fun k => Real.sqrt x * φ^[k] 1
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hsx1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx1
    have hrec : ∀ k, u (k + 1) = g (u k) := by
      intro k
      simp only [u, g, φ, Function.iterate_succ_apply']
      generalize (fun t => t * (3 - x * t ^ 2) / 2)^[k] 1 = t
      rw [mul_pow, Real.sq_sqrt hx0.le]
      ring
    have hbd : ∀ k, 0 < u k ∧ u k ≤ 1 := by
      intro k
      induction k with
      | zero => simp only [u, Function.iterate_zero_apply, mul_one]; exact ⟨hsx, hsx1⟩
      | succ k ih =>
        rw [hrec]
        obtain ⟨h0, h1⟩ := ih
        refine ⟨?_, ?_⟩
        · simp only [g]; nlinarith
        · simp only [g]; nlinarith [sq_nonneg (u k - 1)]
    have hmono : Monotone u := by
      refine monotone_nat_of_le_succ (fun k => ?_)
      rw [hrec]
      obtain ⟨h0, h1⟩ := hbd k
      simp only [g]; nlinarith
    have hbdd : BddAbove (Set.range u) := ⟨1, by rintro _ ⟨k, rfl⟩; exact (hbd k).2⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    set L := ⨆ k, u k
    have hL0 : 0 < L := lt_of_lt_of_le (hbd 0).1 (le_ciSup hbdd 0)
    have hgL : g L = L := by
      have h1 : Tendsto (fun k => u (k + 1)) atTop (𝓝 L) := hlim.comp (tendsto_add_atTop_nat 1)
      have h2 : Tendsto (fun k => u (k + 1)) atTop (𝓝 (g L)) := by
        simp only [hrec]
        exact ((continuous_id.mul (continuous_const.sub (continuous_id.pow 2))).div_const 2).continuousAt.tendsto.comp hlim
      exact tendsto_nhds_unique h2 h1
    have hL1 : L = 1 := by
      simp only [g] at hgL
      have : L * (L ^ 2 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hL0.ne'
      · nlinarith [sq_nonneg (L - 1), (show L ≤ 1 from ciSup_le (fun k => (hbd k).2))]
    rw [hL1] at hlim
    have : Tendsto (fun k => (Real.sqrt x)⁻¹ * u k) atTop (𝓝 ((Real.sqrt x)⁻¹ * 1)) := hlim.const_mul _
    rw [mul_one] at this
    refine this.congr (fun k => ?_)
    simp only [u]
    field_simp)

theorem continuous_toMatrix : Continuous (toMatrix : Mat m n → Matrix (Fin m) (Fin n) ℝ) := by
  exact continuous_pi fun i => continuous_pi fun j => PiLp.continuous_apply 2 _ (i, j)

theorem continuous_ofMatrix : Continuous (ofMatrix : Matrix (Fin m) (Fin n) ℝ → Mat m n) := by
  exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem conj_mul_conj (E X Z : Matrix (Fin n) (Fin n) ℝ) (hEE : Eᵀ * E = 1) :
    (E * X * Eᵀ) * (E * Z * Eᵀ) = E * (X * Z) * Eᵀ := by
  open Matrix Topology Filter in
  (
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Eᵀ E, hEE, Matrix.one_mul])

theorem newton_matrix_eq (E : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (hEE : Eᵀ * E = 1)
    (hEE' : E * Eᵀ = 1) (k : ℕ) :
    (fun Y => (1 / 2 : ℝ) • (Y * ((3 : ℝ) • 1 - (E * diagonal d * Eᵀ) * Y * Y)))^[k] 1 =
      E * diagonal (fun i => (fun t : ℝ => t * (3 - d i * t ^ 2) / 2)^[k] 1) * Eᵀ := by
  open Matrix Topology Filter in
  (
    induction k with
    | zero =>
      simp only [Function.iterate_zero_apply]
      rw [show (diagonal fun _ : Fin n => (1 : ℝ)) = 1 from Matrix.diagonal_one, Matrix.mul_one, hEE']
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      set D : Fin n → ℝ := fun i => (fun t : ℝ => t * (3 - d i * t ^ 2) / 2)^[k] 1
      have h3 : (3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) = E * diagonal (fun _ => (3 : ℝ)) * Eᵀ := by
        rw [show (diagonal fun _ : Fin n => (3 : ℝ)) = (3 : ℝ) • 1 by
          ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]]
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hEE']
      rw [h3, conj_mul_conj _ _ _ hEE, conj_mul_conj _ _ _ hEE, ← Matrix.sub_mul, ← Matrix.mul_sub,
        conj_mul_conj _ _ _ hEE, ← Matrix.smul_mul, ← Matrix.mul_smul]
      congr 2
      ext i j
      simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.diagonal_apply,
        Function.iterate_succ_apply', D, smul_eq_mul]
      by_cases h : i = j
      · subst h; simp [Finset.sum_ite_eq, Finset.sum_ite_eq']; ring
      · simp [h])

theorem entry_conj_diag (M : Matrix (Fin m) (Fin n) ℝ) (E : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (p : Fin m) (q : Fin n) : (M * diagonal d * Eᵀ) p q = ∑ i, M p i * d i * E q i := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

theorem gram_entry_sq (W : Mat m n) (i : Fin n) :
    let E : Matrix (Fin n) (Fin n) ℝ :=
      ((Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    ∑ p, (toMatrix W * E) p i * (toMatrix W * E) p i = gramEigenvalues W i := by
  intro E
  obtain ⟨hVV, -, hAV, -⟩ := unitary_data W
  have hg := gram_diag (toMatrix W) E (gramEigenvalues W) hVV hAV
  have := congrFun (congrFun hg i) i
  rw [Matrix.mul_apply] at this
  simp only [Matrix.transpose_apply, Matrix.diagonal_apply_eq] at this
  exact this

theorem gramEigenvalues_le (W : Mat m n) (i : Fin n) : gramEigenvalues W i ≤ ‖W‖ ^ 2 := by
  open Matrix Topology Filter in
  (
    obtain ⟨hVV, hVV', hAV, -⟩ := unitary_data W
    set E : Matrix (Fin n) (Fin n) ℝ :=
        ((Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    have hg := gram_diag (toMatrix W) E (gramEigenvalues W) hVV hAV
    have hnorm : ‖W‖ ^ 2 = ∑ j, gramEigenvalues W j := by
      rw [← real_inner_self_eq_norm_sq, inner_mat_trace, ← Matrix.trace_diagonal, ← hg]
      have e : (toMatrix W * E)ᵀ * (toMatrix W * E) = Eᵀ * ((toMatrix W)ᵀ * toMatrix W * E) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [e]
      conv_rhs => rw [Matrix.trace_mul_comm]
      rw [Matrix.mul_assoc ((toMatrix W)ᵀ * toMatrix W) E Eᵀ, hVV', Matrix.mul_one]
    rw [hnorm]
    exact Finset.single_le_sum (fun j _ => (Matrix.posSemidef_conjTranspose_mul_self (toMatrix W)).eigenvalues_nonneg j)
      (Finset.mem_univ i))

theorem measurable_orthogonalize : Measurable (orthogonalize : Mat m n → Mat m n) := by
  open Matrix Topology Filter in
  (
    let c : Mat m n → ℝ := fun W => 1 + ‖W‖ ^ 2
    have hc : ∀ W, 0 < c W := fun W => by positivity
    let Bt : Mat m n → Matrix (Fin n) (Fin n) ℝ := fun W => (c W)⁻¹ • ((toMatrix W)ᵀ * toMatrix W)
    let Y : ℕ → Mat m n → Matrix (Fin n) (Fin n) ℝ := fun k W =>
      (fun Z => (1 / 2 : ℝ) • (Z * ((3 : ℝ) • 1 - Bt W * Z * Z)))^[k] 1
    let F : ℕ → Mat m n → Mat m n := fun k W => ofMatrix ((Real.sqrt (c W))⁻¹ • (toMatrix W * Y k W))
    have hcc : Continuous c := continuous_const.add (continuous_norm.pow 2)
    have hBt : Continuous Bt :=
      (hcc.inv₀ (fun W => (hc W).ne')).smul
        (continuous_toMatrix.matrix_transpose.matrix_mul continuous_toMatrix)
    have hY : ∀ k, Continuous (Y k) := by
      intro k
      induction k with
      | zero => exact continuous_const
      | succ k ih =>
        have e : Y (k + 1) = fun W => (1 / 2 : ℝ) • (Y k W * ((3 : ℝ) • 1 - Bt W * Y k W * Y k W)) := by
          funext W
          exact Function.iterate_succ_apply' _ _ _
        rw [e]
        exact (ih.matrix_mul (continuous_const.sub ((hBt.matrix_mul ih).matrix_mul ih))).const_smul (1 / 2 : ℝ)
    have hF : ∀ k, Continuous (F k) := fun k =>
      continuous_ofMatrix.comp (((hcc.sqrt).inv₀ (fun W => (Real.sqrt_pos.mpr (hc W)).ne')).smul
        (continuous_toMatrix.matrix_mul (hY k)))
    have hlim : ∀ W, Tendsto (fun k => F k W) atTop (𝓝 (orthogonalize W)) := by
      intro W
      obtain ⟨hVV, hVV', hAV, -⟩ := unitary_data W
      set E : Matrix (Fin n) (Fin n) ℝ :=
        ((Matrix.isHermitian_conjTranspose_mul_self (toMatrix W)).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
      set lam := gramEigenvalues W
      set d : Fin n → ℝ := fun i => lam i / c W
      have hgram : (toMatrix W)ᵀ * toMatrix W = E * diagonal lam * Eᵀ := by
        rw [← hAV, Matrix.mul_assoc, hVV', Matrix.mul_one]
      have hB : Bt W = E * diagonal d * Eᵀ := by
        change (c W)⁻¹ • ((toMatrix W)ᵀ * toMatrix W) = _
        rw [hgram, ← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 2
        ext i j
        simp only [Matrix.smul_apply, Matrix.diagonal_apply, d, smul_eq_mul]
        split_ifs <;> simp [div_eq_inv_mul]
      have hYk : ∀ k, Y k W = E * diagonal (fun i => (fun t : ℝ => t * (3 - d i * t ^ 2) / 2)^[k] 1) * Eᵀ := by
        intro k
        change (fun Z => (1 / 2 : ℝ) • (Z * ((3 : ℝ) • 1 - Bt W * Z * Z)))^[k] 1 = _
        rw [hB]
        exact newton_matrix_eq E d hVV hVV' k
      set σ : ℕ → Fin n → ℝ := fun k i =>
        (Real.sqrt (c W))⁻¹ * (fun t : ℝ => t * (3 - d i * t ^ 2) / 2)^[k] 1
      have hFk : ∀ k, F k W = ofMatrix (toMatrix W * E * diagonal (σ k) * Eᵀ) := by
        intro k
        change ofMatrix ((Real.sqrt (c W))⁻¹ • (toMatrix W * Y k W)) = _
        rw [hYk]
        have hd : diagonal (σ k) = (Real.sqrt (c W))⁻¹ •
            diagonal (fun i => (fun t : ℝ => t * (3 - d i * t ^ 2) / 2)^[k] 1) := by
          rw [← Matrix.diagonal_smul]
          rfl
        rw [hd]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      set coef : Fin n → ℝ := fun i => if 0 < singularValues W i then (singularValues W i)⁻¹ else 0
      have horth : orthogonalize W = ofMatrix (toMatrix W * E * diagonal coef * Eᵀ) := by
        rw [← toMatrix_orthogonalize W]
        rfl
      have hzero : ∀ i, lam i = 0 → ∀ p, (toMatrix W * E) p i = 0 := by
        intro i hi p
        have h := gram_entry_sq W i
        change ∑ p, (toMatrix W * E) p i * (toMatrix W * E) p i = lam i at h
        rw [hi] at h
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => mul_self_nonneg ((toMatrix W * E) p i))).mp h p
          (Finset.mem_univ p)
        exact mul_self_eq_zero.mp this
      have hM : Tendsto (fun k => toMatrix W * E * diagonal (σ k) * Eᵀ) atTop
          (𝓝 (toMatrix W * E * diagonal coef * Eᵀ)) := by
        refine tendsto_pi_nhds.2 (fun p => tendsto_pi_nhds.2 (fun q => ?_))
        simp only [entry_conj_diag]
        refine tendsto_finsetSum _ (fun i _ => ?_)
        have hl0 : 0 ≤ lam i := (Matrix.posSemidef_conjTranspose_mul_self (toMatrix W)).eigenvalues_nonneg i
        rcases hl0.lt_or_eq with hpos | hz
        · have hd0 : 0 < d i := div_pos hpos (hc W)
          have hd1 : d i ≤ 1 := by
            rw [div_le_one (hc W)]
            have := gramEigenvalues_le W i
            change lam i ≤ ‖W‖ ^ 2 at this
            change lam i ≤ 1 + ‖W‖ ^ 2
            linarith
          have ht := newton_scalar_tendsto (d i) hd0 hd1
          have hval : (Real.sqrt (c W))⁻¹ * (Real.sqrt (d i))⁻¹ = coef i := by
            have hs : 0 < singularValues W i := Real.sqrt_pos.mpr hpos
            simp only [coef, hs, ite_true]
            change (Real.sqrt (c W))⁻¹ * (Real.sqrt (lam i / c W))⁻¹ = (Real.sqrt (lam i))⁻¹
            rw [Real.sqrt_div hpos.le, ← mul_inv, mul_div_cancel₀ _ (Real.sqrt_pos.mpr (hc W)).ne']
          rw [← hval]
          exact (tendsto_const_nhds.mul (tendsto_const_nhds.mul ht)).mul tendsto_const_nhds
        · rw [hzero i hz.symm p]
          simp only [zero_mul]
          exact tendsto_const_nhds
      rw [horth]
      simp only [hFk]
      exact (continuous_ofMatrix.tendsto _).comp hM
    exact measurable_of_tendsto_metrizable (fun k => (hF k).measurable) (tendsto_pi_nhds.2 hlim))

theorem measurable_nuclearNorm : Measurable (nuclearNorm : Mat m n → ℝ) := by
  have e : (nuclearNorm : Mat m n → ℝ) = fun W => inner ℝ W (orthogonalize W) :=
    funext fun W => (inner_orthogonalize W).symm
  rw [e]
  exact Measurable.inner measurable_id measurable_orthogonalize

end OracleTemplate.Muon
