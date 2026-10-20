import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.SpectralMirrorGeometry

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable {ι : Type*} [Fintype ι]

noncomputable def energy (b : OrthonormalBasis ι ℝ V) (X : V →L[ℝ] W) : ℝ :=
  (∑ i, ‖X (b i)‖ ^ 2) / 2

noncomputable def pairing (b : OrthonormalBasis ι ℝ V) (G : V →L[ℝ] W) :
    (V →L[ℝ] W) →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (G (b i))).comp (ContinuousLinearMap.apply ℝ W (b i))

lemma pairing_apply (b : OrthonormalBasis ι ℝ V) (G X : V →L[ℝ] W) :
    pairing b G X = ∑ i, inner ℝ (G (b i)) (X (b i)) := by
  simp [pairing]

lemma energy_hasFDerivAt (b : OrthonormalBasis ι ℝ V) (X : V →L[ℝ] W) :
    HasFDerivAt (energy b) (pairing b X) X := by
  have hh := (HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((ContinuousLinearMap.apply ℝ W (b i)).hasFDerivAt (x := X)).norm_sq)).const_mul (1 / 2)
  convert hh using 1
  · funext Y
    simp [energy, Finset.sum_apply]
    ring
  · ext Y
    simp [pairing, Finset.mul_sum]

lemma energy_bregman (b : OrthonormalBasis ι ℝ V) (X Y : V →L[ℝ] W) :
    energy b Y - energy b X - fderiv ℝ (energy b) X (Y - X) = energy b (Y - X) := by
  rw [(energy_hasFDerivAt b X).fderiv, pairing_apply]
  simp only [energy, sub_apply]
  simp_rw [norm_sub_sq_real, inner_sub_right]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hi : (∑ i, inner ℝ (X (b i)) (Y (b i))) =
      ∑ i, inner ℝ (Y (b i)) (X (b i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_comm _ _
  simp_rw [real_inner_self_eq_norm_sq]
  rw [hi]
  ring

lemma energy_upper (b : OrthonormalBasis ι ℝ V) (X : V →L[ℝ] W) :
    energy b X ≤ (Fintype.card ι : ℝ) * ‖X‖ ^ 2 / 2 := by
  have hh : ∑ i, ‖X (b i)‖ ^ 2 ≤ ∑ _i : ι, ‖X‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    simpa only [b.orthonormal.norm_eq_one i, mul_one] using X.le_opNorm (b i)
  simpa [energy] using div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2)

lemma opNorm_sq_le_columns (b : OrthonormalBasis ι ℝ V) (X : V →L[ℝ] W) :
    ‖X‖ ^ 2 ≤ ∑ i, ‖X (b i)‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ‖X (b i)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hop : ‖X‖ ≤ Real.sqrt (∑ i, ‖X (b i)‖ ^ 2) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro v hv
    have hrepr : X v = ∑ i, (inner ℝ (b i) v) • X (b i) := by
      simp_rw [← map_smul]
      rw [← map_sum]
      rw [b.sum_repr']
    have ht : ‖X v‖ ≤ ∑ i, ‖inner ℝ (b i) v‖ * ‖X (b i)‖ := by
      rw [hrepr]
      simpa only [norm_smul] using norm_sum_le Finset.univ
        (fun i => (inner ℝ (b i) v) • X (b i))
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => ‖inner ℝ (b i) v‖) (fun i => ‖X (b i)‖)
    rw [b.sum_sq_norm_inner_right, hv] at hcs
    norm_num only [one_pow, one_mul] at hcs
    have ht0 : 0 ≤ ∑ i, ‖inner ℝ (b i) v‖ * ‖X (b i)‖ := by positivity
    have hs := (sq_le_sq₀ (norm_nonneg _) ht0).mpr ht
    apply (Real.le_sqrt (norm_nonneg _) hS).mpr
    exact hs.trans hcs
  have hh := (sq_le_sq₀ (norm_nonneg X) (Real.sqrt_nonneg _)).mpr hop
  simpa only [Real.sq_sqrt hS] using hh

lemma energy_strongly_convex (b : OrthonormalBasis ι ℝ V) (X Y : V →L[ℝ] W) :
    (1 : ℝ) / 2 * ‖Y - X‖ ^ 2 ≤
      energy b Y - energy b X - fderiv ℝ (energy b) X (Y - X) := by
  rw [energy_bregman]
  have hh := opNorm_sq_le_columns b (Y - X)
  dsimp [energy]
  linarith

variable {κ : Type*} [Fintype κ]

noncomputable def coordinates (b : OrthonormalBasis ι ℝ V)
    (c : OrthonormalBasis κ ℝ W) (X : V →L[ℝ] W) : Matrix κ ι ℝ :=
  fun i j => inner ℝ (c i) (X (b j))

lemma pairing_trace (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis κ ℝ W)
    (G X : V →L[ℝ] W) :
    pairing b G X = Matrix.trace ((coordinates b c G).transpose * coordinates b c X) := by
  rw [pairing_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, coordinates]
  apply Finset.sum_congr rfl
  intro j _
  rw [← c.sum_inner_mul_inner (G (b j)) (X (b j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (G (b j)) (c i)]

lemma energy_adjoint [CompleteSpace V] [CompleteSpace W]
    (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis κ ℝ W) (X : V →L[ℝ] W) :
    energy b X = energy c X.adjoint := by
  unfold energy
  congr 1
  calc
    ∑ j, ‖X (b j)‖ ^ 2 = ∑ j, ∑ i, ‖inner ℝ (c i) (X (b j))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (c.sum_sq_norm_inner_right _).symm
    _ = ∑ i, ∑ j, ‖inner ℝ (b j) (X.adjoint (c i))‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [X.adjoint_inner_right, real_inner_comm]
    _ = ∑ i, ‖X.adjoint (c i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact b.sum_sq_norm_inner_right _

lemma energy_upper_min [CompleteSpace V] [CompleteSpace W]
    (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis κ ℝ W) (X : V →L[ℝ] W) :
    energy b X ≤ (min (Fintype.card ι) (Fintype.card κ) : ℝ) * ‖X‖ ^ 2 / 2 := by
  have h₁ := energy_upper b X
  have h₂ := energy_upper c X.adjoint
  rw [← energy_adjoint b c X] at h₂
  simp only [ContinuousLinearMap.adjoint.norm_map] at h₂
  rcases le_total (Fintype.card ι) (Fintype.card κ) with h | h
  · simpa only [min_eq_left (show (Fintype.card ι : ℝ) ≤ (Fintype.card κ : ℝ) by exact_mod_cast h)] using h₁
  · simpa only [min_eq_right (show (Fintype.card κ : ℝ) ≤ (Fintype.card ι : ℝ) by exact_mod_cast h)] using h₂

lemma pairing_add (b : OrthonormalBasis ι ℝ V) (X Y : V →L[ℝ] W) :
    pairing b (X + Y) = pairing b X + pairing b Y := by
  ext Z
  simp [pairing_apply, inner_add_left, Finset.sum_add_distrib]

lemma pairing_sub (b : OrthonormalBasis ι ℝ V) (X Y : V →L[ℝ] W) :
    pairing b (X - Y) = pairing b X - pairing b Y := by
  ext Z
  simp [pairing_apply, inner_sub_left, Finset.sum_sub_distrib]

lemma pairing_smul (b : OrthonormalBasis ι ℝ V) (a : ℝ) (X : V →L[ℝ] W) :
    pairing b (a • X) = a • pairing b X := by
  ext Z
  simp [pairing_apply, inner_smul_left, Finset.mul_sum]

lemma pairing_eq_zero (b : OrthonormalBasis ι ℝ V) (X : V →L[ℝ] W)
    (hX : pairing b X = 0) : X = 0 := by
  have hh := congrArg (fun g : (V →L[ℝ] W) →L[ℝ] ℝ => g X) hX
  simp only [pairing_apply, real_inner_self_eq_norm_sq, zero_apply] at hh
  have hb := opNorm_sq_le_columns b X
  rw [hh] at hb
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg X])

lemma quadratic_mirror_minimizer (b : OrthonormalBasis ι ℝ V)
    (X Z G : V →L[ℝ] W) (γ : ℝ)
    (hm : ∀ Y, γ * pairing b G Z + energy b Z - energy b X - pairing b X (Z - X) ≤
      γ * pairing b G Y + energy b Y - energy b X - pairing b X (Y - X)) :
    Z = X - γ • G := by
  let f := fun Y => γ * pairing b G Y + energy b Y - energy b X - pairing b X (Y - X)
  have hd : HasFDerivAt f (γ • pairing b G + pairing b Z - pairing b X) Z := by
    convert ((((pairing b G).hasFDerivAt.const_mul γ).add (energy_hasFDerivAt b Z)).sub_const
      (energy b X)).sub ((pairing b X).hasFDerivAt.comp Z ((hasFDerivAt_id Z).sub_const X)) using 1
    · funext Y
      simp [f, Pi.sub_apply, Function.comp_def, map_sub]
    · simp
  have hlocal : IsLocalMin f Z := Filter.Eventually.of_forall hm
  have hz := hlocal.fderiv_eq_zero
  rw [hd.fderiv] at hz
  have he : pairing b (γ • G + Z - X) = 0 := by
    simpa only [pairing_sub, pairing_add, pairing_smul] using hz
  have hh := pairing_eq_zero b _ he
  have hx : Z = X - γ • G := by
    apply eq_sub_iff_add_eq.mpr
    have ht := sub_eq_zero.mp hh
    simpa only [add_comm] using ht
  exact hx

end LongTails.Proofs.SpectralMirrorGeometry
