import LongTails.Proofs.HiddenDecompositionLinear
import LongTails.Proofs.HiddenDecompositionResistance
import LongTails.Proofs.Execution
import LongTails.Setups.HiddenPotentialStronglyMonotone

open scoped RealInnerProductSpace

namespace OracleTemplate.HiddenDecompositionLowerBound

open HiddenDecompositionLinear HiddenDecompositionResistance

variable {ι : Type*} [Fintype ι]

lemma krylov_polynomial_representation (ζ : ι → ℂ) (b : EuclideanSpace ℂ ι)
    (n : ℕ) {x : EuclideanSpace ℂ ι} (hx : x ∈ krylov (diagonal ζ) b n) :
    ∃ p : Polynomial ℝ, p.degree < (n : WithBot ℕ) ∧ x = polynomialVector ζ b p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      refine ⟨Polynomial.X ^ j.val, ?_, (polynomialVector_power ζ b j.val).symm⟩
      rw [Polynomial.degree_X_pow]
      exact_mod_cast j.isLt
  | zero =>
      refine ⟨0, by simp, (polynomialVector_zero ζ b).symm⟩
  | add x y _ _ hx hy =>
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := hy
      exact ⟨p + q, (Polynomial.degree_add_le p q).trans_lt (max_lt hp hq),
        (polynomialVector_add ζ b p q).symm⟩
  | smul r x _ hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      exact ⟨r • p, (Polynomial.degree_smul_le r p).trans_lt hp,
        (polynomialVector_smul ζ b r p).symm⟩

lemma residual_polynomial_degree {p : Polynomial ℝ} {n : ℕ}
    (hp : p.degree < (n : WithBot ℕ)) :
    (1 - Polynomial.X * p).natDegree ≤ n := by
  by_cases hz : p = 0
  · simp [hz]
  have hn := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hp
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · have hh : (Polynomial.X * p).natDegree ≤
        (Polynomial.X : Polynomial ℝ).natDegree + p.natDegree := Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_X] at hh
    omega

lemma polynomial_lower_to_krylov (ζ : ι → ℂ) (u : EuclideanSpace ℂ ι)
    {n : ℕ} {δ : ℝ}
    (hlower : ∀ p : Polynomial ℝ, p.natDegree ≤ n → p.eval 0 = 1 →
      δ ≤ ‖polynomialVector ζ u p‖)
    (x : EuclideanSpace ℂ ι) (hx : x ∈ krylov (diagonal ζ) (diagonal ζ u) n) :
    δ ≤ ‖x - u‖ := by
  obtain ⟨p, hp, rfl⟩ := krylov_polynomial_representation ζ (diagonal ζ u) n hx
  have hh := hlower (1 - Polynomial.X * p) (residual_polynomial_degree hp) (by simp)
  rw [polynomialVector_sub, polynomialVector_one, ← polynomialVector_diagonal] at hh
  rwa [norm_sub_rev] at hh

lemma finite_deterministic_lower (n : ℕ) (μ L s R : ℝ)
    (hμ : 0 < μ) (hμs : μ ≤ s) (hsL : 4 * s ≤ L) (hR : 0 < R)
    (alg : Algorithm
      (EuclideanSpace ℂ (HiddenDecompositionPolynomial.SpectralIndex (2 * n + 2)))
      (EuclideanSpace ℂ (HiddenDecompositionPolynomial.SpectralIndex (2 * n + 2)))
      (EuclideanSpace ℂ (HiddenDecompositionPolynomial.SpectralIndex (2 * n + 2))))
    (seed : alg.Seed) :
    ∃ (ζ : HiddenDecompositionPolynomial.SpectralIndex (2 * n + 2) → ℂ)
      (u : EuclideanSpace ℂ (HiddenDecompositionPolynomial.SpectralIndex (2 * n + 2)))
      (U : EuclideanSpace ℂ (HiddenDecompositionPolynomial.SpectralIndex (2 * n + 2)) ≃ₗᵢ[ℝ]
        EuclideanSpace ℂ (HiddenDecompositionPolynomial.SpectralIndex (2 * n + 2))),
      (∀ i, μ ≤ (ζ i).re ∧ (ζ i).re ≤ L ∧ |(ζ i).im| ≤ s) ∧ ‖u‖ = R ∧
      R / (3 * Real.exp (6 * ((2 * n + 2 : ℕ) : ℝ) * μ / Real.sqrt (L * s))) ≤
        ‖execute { answer := fun _ query _ => rotatedField (diagonal ζ) (diagonal ζ u) U query.2 }
          alg (fun _ => n) seed - U u‖ := by
  obtain ⟨ζ, v, hbox, hv, hp⟩ := finite_linear_witness (2 * n + 2) μ L s hμ hμs hsL
  let u := R • v
  let δ := R / (3 * Real.exp (6 * ((2 * n + 2 : ℕ) : ℝ) * μ / Real.sqrt (L * s)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpoly : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * n + 2 → p.eval 0 = 1 →
      δ ≤ ‖polynomialVector ζ u p‖ := by
    intro p hdeg hz
    have h := mul_le_mul_of_nonneg_left (hp p hdeg hz) hR.le
    dsimp [u, δ]
    rw [polynomialVector_smul_root, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR.le]
    simpa only [mul_one_div] using h
  obtain ⟨U, hU⟩ := resisting_error (diagonal ζ) u
    (diagonal_injective ζ hμ (fun i => (hbox i).1))
    (alg.initial seed) (fun state => (alg.query state).2) alg.update alg.output n hδ
    (fun x hx => polynomial_lower_to_krylov ζ u hpoly x hx)
  refine ⟨ζ, u, U, hbox, ?_, ?_⟩
  · dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR.le, hv, mul_one]
  · rw [execute_iterate]
    exact hU

lemma gradient_comp_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℝ] E) {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (x : E) :
    HasGradientAt (fun y => f (U.symm y)) (U (g (U.symm x))) x := by
  have h := (hg (U.symm x)).hasFDerivAt.comp x
    U.symm.toLinearIsometry.toContinuousLinearMap.hasFDerivAt
  change HasFDerivAt _ (InnerProductSpace.toDual ℝ E (U (g (U.symm x)))) x
  convert h using 1
  · rfl
  · ext v
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      LinearIsometry.coe_toContinuousLinearMap]
    have he := U.inner_map_map (g (U.symm x)) (U.symm v)
    change ⟪U (g (U.symm x)), v⟫ = ⟪g (U.symm x), U.symm v⟫
    simpa only [U.apply_symm_apply] using he

lemma rotate_strong {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : E ≃ₗᵢ[ℝ] E) (F : E → E) {μ : ℝ}
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) :
    ∀ x y, μ * ‖x - y‖ ^ 2 ≤
      ⟪U (F (U.symm x)) - U (F (U.symm y)), x - y⟫ := by
  intro x y
  have h := hstrong (U.symm x) (U.symm y)
  have hn : ‖U.symm x - U.symm y‖ = ‖x - y‖ := by rw [← map_sub, U.symm.norm_map]
  rw [hn] at h
  have he := U.inner_map_map (F (U.symm x) - F (U.symm y)) (U.symm x - U.symm y)
  simp only [map_sub, U.apply_symm_apply] at he
  rwa [← he] at h

lemma rotate_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : E ≃ₗᵢ[ℝ] E) (F : E → E) {L : ℝ}
    (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖U (F (U.symm x)) - U (F (U.symm y))‖ ≤ L * ‖x - y‖ := by
  intro x y
  rw [← map_sub, U.norm_map]
  have h := hlip (U.symm x) (U.symm y)
  simpa only [← map_sub, U.symm.norm_map] using h

set_option maxHeartbeats 800000 in
lemma rotated_diagonal_model (ζ : ι → ℂ) {μ L s : ℝ}
    (hμ : 0 < μ) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hζ : ∀ i, μ ≤ (ζ i).re ∧ (ζ i).re ≤ L ∧ |(ζ i).im| ≤ s)
    (u : EuclideanSpace ℂ ι) (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι) :
    let F := rotatedField (diagonal ζ) (diagonal ζ u) U
    (∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) ∧
    F (U u) = 0 ∧
    ∃ φ : EuclideanSpace ℂ ι → ℝ,
      (∀ x, HasGradientAt φ (gradient φ x) x) ∧
      (∀ x y, ‖gradient φ x - gradient φ y‖ ≤ L * ‖x - y‖) ∧
      (∀ x y, ‖(F x - gradient φ x) - (F y - gradient φ y)‖ ≤ s * ‖x - y‖) ∧
      (∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪gradient φ x - gradient φ y, x - y⟫) ∧
      (∀ x y, 0 ≤ ⟪(F x - gradient φ x) - (F y - gradient φ y), x - y⟫) := by
  dsimp only
  let G := fun x => diagonal ζ (x - u)
  have hF : ∀ x, rotatedField (diagonal ζ) (diagonal ζ u) U x = U (G (U.symm x)) := by
    intro x
    simp only [rotatedField, G, map_sub]
  have hGs : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫ := by
    intro x y
    have h := diagonal_strong ζ (fun i => (hζ i).1) (x - u) (y - u)
    simpa only [sub_sub_sub_cancel_right] using h
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rw [hF, hF]
    exact rotate_strong U G hGs x y
  · simp [rotatedField]
  · obtain ⟨φ, hg, hgrad, hlip, hres⟩ := diagonal_potential_decomposition ζ hL hs
      (fun i => ⟨hμ.le.trans (hζ i).1, (hζ i).2⟩) u
    let ψ := fun x => φ (U.symm x)
    have hψ := gradient_comp_isometry U hg
    have hgψ : ∀ x, gradient ψ x = U (gradient φ (U.symm x)) := fun x => (hψ x).gradient
    refine ⟨ψ, (fun x => by rw [hgψ]; exact hψ x), ?_, ?_, ?_, ?_⟩
    · intro x y
      rw [hgψ, hgψ]
      exact rotate_lipschitz U (gradient φ) hlip x y
    · intro x y
      rw [hF, hF, hgψ, hgψ, ← map_sub, ← map_sub]
      exact rotate_lipschitz U (fun x => G x - gradient φ x) hres x y
    · have hbase : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪gradient φ x - gradient φ y, x - y⟫ := by
        intro x y
        rw [hgrad, hgrad]
        have h := diagonal_strong (fun i => ((ζ i).re : ℂ))
          (fun i => by simpa using (hζ i).1) (x - u) (y - u)
        simpa only [sub_sub_sub_cancel_right] using h
      intro x y
      rw [hgψ, hgψ]
      exact rotate_strong U (gradient φ) hbase x y
    · have hbase : ∀ x y, (0 : ℝ) * ‖x - y‖ ^ 2 ≤
          ⟪(G x - gradient φ x) - (G y - gradient φ y), x - y⟫ := by
        intro x y
        rw [hgrad, hgrad, zero_mul]
        have h := diagonal_residual_inner ζ (x - u) (y - u)
        simpa only [sub_sub_sub_cancel_right] using h.ge
      intro x y
      rw [hF, hF, hgψ, hgψ, ← map_sub, ← map_sub]
      simpa only [zero_mul] using rotate_strong U (fun x => G x - gradient φ x) hbase x y

noncomputable def hardParameters (n : ℕ) (μ L s R ε : ℝ) :
    LongTails.Setups.HiddenPotentialStronglyMonotone.Public where
  E := EuclideanSpace ℂ (HiddenDecompositionPolynomial.SpectralIndex (2 * n + 2))
  L := L
  x0 := 0
  μ := μ
  s := s
  R := R
  ε := ε

set_option maxHeartbeats 800000 in
lemma combined_oracle_lower_bound (n : ℕ) (μ L s R ε : ℝ)
    (hμ : 0 < μ) (hμs : μ ≤ s) (hsL : 4 * s ≤ L) (hR : 0 < R) (hε : 0 < ε)
    (alg : Algorithm (hardParameters n μ L s R ε).E (hardParameters n μ L s R ε).E
      (hardParameters n μ L s R ε).E) (seed : alg.Seed) :
    let p := hardParameters n μ L s R ε
    LongTails.Setups.HiddenPotentialStronglyMonotone.spec.valid p ∧
    ∃ (F : p.E → p.E) (xstar : p.E),
      LongTails.Setups.HiddenPotentialStronglyMonotone.spec.admissible p F
        { answer := fun _ query _ => F query.2 } ∧
      F xstar = 0 ∧ ‖xstar‖ = R ∧
      R / (3 * Real.exp (6 * ((2 * n + 2 : ℕ) : ℝ) * μ / Real.sqrt (L * s))) ≤
        ‖execute { answer := fun _ query _ => F query.2 } alg (fun _ => n) seed - xstar‖ ∧
      ∃ φ : p.E → ℝ,
        (∀ x, HasGradientAt φ (gradient φ x) x) ∧
        (∀ x y, ‖gradient φ x - gradient φ y‖ ≤ L * ‖x - y‖) ∧
        (∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪gradient φ x - gradient φ y, x - y⟫) ∧
        (∀ x y, ‖(F x - gradient φ x) - (F y - gradient φ y)‖ ≤ s * ‖x - y‖) ∧
        (∀ x y, 0 ≤ ⟪(F x - gradient φ x) - (F y - gradient φ y), x - y⟫) := by
  dsimp only
  have hs : 0 ≤ s := hμ.le.trans hμs
  have hL : 0 ≤ L := by linarith
  refine ⟨⟨hμ, hL, hs, hR.le, hε⟩, ?_⟩
  obtain ⟨ζ, u, U, hbox, hunorm, herror⟩ :=
    finite_deterministic_lower n μ L s R hμ hμs hsL hR alg seed
  obtain ⟨hstrong, hroot, φ, hg, hlip, hres, hgs, hmono⟩ :=
    rotated_diagonal_model ζ hμ hL hs hbox u U
  refine ⟨rotatedField (diagonal ζ) (diagonal ζ u) U, U u, ?_, hroot, ?_, herror,
    φ, hg, hlip, hgs, hres, hmono⟩
  · refine ⟨(fun _ _ _ => rfl), hstrong, ⟨φ, hg, hlip, hres⟩, U u, hroot, ?_⟩
    change ‖0 - U u‖ ≤ R
    simpa only [zero_sub, norm_neg, U.norm_map, hunorm] using (le_refl R)
  · change ‖U u‖ = R
    exact (U.norm_map u).trans hunorm

end OracleTemplate.HiddenDecompositionLowerBound
