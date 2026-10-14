import LongTails.Proofs.TemporalDifferenceResponse
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import LongTails.Proofs.QuadraticTemporalEnergy

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.TemporalDiscrepancy

open LongTails.Setups.QuadraticTemporalDiscrepancy

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [Fintype ι]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma accelerated_momentum_identity {θ μ : ℝ} (hθ : 1 + θ ≠ 0)
    (s : E × E) (g : E) :
    θ • (acceleratedUpdate θ μ s g).2 =
      (acceleratedUpdate θ μ s g).1 - (1 - θ) • s.1 := by
  have hq : (1 + θ) • acceleratedQuery θ s = s.1 + θ • s.2 := by
    simp only [acceleratedQuery, smul_smul, mul_one_div_cancel hθ, one_smul]
  have hh : θ • (acceleratedUpdate θ μ s g).2 -
      ((acceleratedUpdate θ μ s g).1 - (1 - θ) • s.1) =
      (1 - θ) • (s.1 + θ • s.2 - (1 + θ) • acceleratedQuery θ s) := by
    simp only [acceleratedUpdate]
    module
  rw [hq, sub_self, smul_zero] at hh
  exact sub_eq_zero.mp hh

lemma scalar_impulse_identification (r c a : ℝ) (x : ℕ → ℝ)
    (h0 : x 0 = a) (h1 : x 1 = (2 * r * c) * a)
    (hrec : ∀ n, x (n + 2) = (2 * r * c) * x (n + 1) - r ^ 2 * x n) :
    ∀ n, x n = a * chebyshevImpulse r c n := by
  apply Nat.twoStepInduction
  · simpa [chebyshevImpulse] using h0
  · simpa [chebyshevImpulse, mul_comm, mul_left_comm, mul_assoc] using h1
  · intro n hn hn1
    rw [hrec, hn, hn1, chebyshev_impulse_recurrence]
    ring

lemma characteristic_middle_bounds {μ L θ eig : ℝ}
    (hμ : 0 < μ) (hθ : 0 ≤ θ)
    (heig : μ ≤ eig) (heigL : eig ≤ L) (hstep : θ ^ 2 * L ≤ μ) :
    0 ≤ (1 - θ ^ 2 * eig / μ) / (1 + θ) ∧
      (1 - θ ^ 2 * eig / μ) / (1 + θ) ≤ 1 - θ := by
  have hden : 0 < 1 + θ := by linarith
  have hhi : θ ^ 2 * eig / μ ≤ 1 := by
    apply (div_le_one hμ).mpr
    exact (mul_le_mul_of_nonneg_left heigL (sq_nonneg θ)).trans hstep
  have hlo : θ ^ 2 ≤ θ ^ 2 * eig / μ := by
    apply (le_div_iff₀ hμ).mpr
    exact mul_le_mul_of_nonneg_left heig (sq_nonneg θ)
  constructor
  · exact div_nonneg (by linarith) hden.le
  · apply (div_le_iff₀ hden).mpr
    nlinarith

omit [FiniteDimensional ℝ E] in
lemma transition_eigen_coordinate (A : E →L[ℝ] E) (l : E →ₗ[ℝ] ℝ)
    (μ θ eig : ℝ) (hl : ∀ x, l (A.adjoint (A x)) = eig * l x) (s : E × E) :
    l (transition A μ θ s).1 =
      ((1 - θ ^ 2 * eig / μ) / (1 + θ)) * (l s.1 + θ * l s.2) := by
  rw [transition_apply]
  change l (acceleratedQuery θ s - (θ ^ 2 / μ) • A.adjoint (A (acceleratedQuery θ s))) = _
  rw [map_sub, map_smul, hl]
  simp only [acceleratedQuery, map_smul, map_add, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
lemma transition_eigen_recurrence (A : E →L[ℝ] E) (l : E →ₗ[ℝ] ℝ)
    (μ θ eig : ℝ) (hθ : 1 + θ ≠ 0)
    (hl : ∀ x, l (A.adjoint (A x)) = eig * l x) (s : E × E) :
    l (transition A μ θ (transition A μ θ s)).1 =
      (2 * ((1 - θ ^ 2 * eig / μ) / (1 + θ))) * l (transition A μ θ s).1 -
        (((1 - θ ^ 2 * eig / μ) / (1 + θ)) * (1 - θ)) * l s.1 := by
  have hh := congrArg l (accelerated_momentum_identity (μ := μ) hθ s
    (A.adjoint (A (acceleratedQuery θ s))))
  rw [← transition_apply] at hh
  simp only [map_smul, map_sub, smul_eq_mul] at hh
  rw [transition_eigen_coordinate A l μ θ eig hl, hh]
  ring

omit [FiniteDimensional ℝ E] in
lemma transition_impulse_coordinate (A : E →L[ℝ] E) (l : E →ₗ[ℝ] ℝ)
    (μ θ eig r c : ℝ) (hθ : 1 + θ ≠ 0)
    (hl : ∀ x, l (A.adjoint (A x)) = eig * l x)
    (hm : r * c = (1 - θ ^ 2 * eig / μ) / (1 + θ))
    (hr : r ^ 2 = ((1 - θ ^ 2 * eig / μ) / (1 + θ)) * (1 - θ)) (e : E) (n : ℕ) :
    l (((transition A μ θ : (E × E) → E × E)^[n]) (injection μ θ e)).1 =
      (-(θ ^ 2 / μ) * l e) * chebyshevImpulse r c n := by
  let x := fun k => l (((transition A μ θ : (E × E) → E × E)^[k]) (injection μ θ e)).1
  apply scalar_impulse_identification r c (-(θ ^ 2 / μ) * l e) x
  · simp [x, injection, map_smul]
  · simp only [x, Function.iterate_one]
    rw [transition_eigen_coordinate A l μ θ eig hl]
    simp only [injection, ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_eq_mul]
    rw [show 2 * r * c = 2 * (r * c) by ring, hm]
    ring
  · intro k
    simpa only [x, Function.iterate_succ_apply', hr, mul_assoc, hm] using
      transition_eigen_recurrence A l μ θ eig hθ hl
        (((transition A μ θ : (E × E) → E × E)^[k]) (injection μ θ e))

def diagonalMap (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) : E →L[ℝ] E :=
  (b.toBasis.constr ℝ (fun i => c i • b i)).toContinuousLinearMap

omit [CompleteSpace E] in
lemma diagonalMap_apply (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (x : E) :
    diagonalMap b c x = ∑ i, (c i * b.repr x i) • b i := by
  change (b.toBasis.constr ℝ (fun i => c i • b i)) x = _
  simp only [Module.Basis.constr_apply_fintype,
    Module.Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply, smul_smul, mul_comm]

omit [CompleteSpace E] in
lemma diagonalMap_coordinate (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (x : E) (i : ι) :
    b.repr (diagonalMap b c x) i = c i * b.repr x i := by
  classical
  rw [diagonalMap_apply, map_sum]
  simp [OrthonormalBasis.repr_self, Pi.single_apply, mul_ite]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma basis_norm_sq (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, (b.repr x i) ^ 2 := by
  rw [← b.repr.norm_map x, EuclideanSpace.real_norm_sq_eq]

omit [CompleteSpace E] in
lemma diagonalMap_bound (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) (x : E) :
    ‖diagonalMap b c x‖ ≤ C * ‖x‖ := by
  have hh : ‖diagonalMap b c x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
    rw [basis_norm_sq b, basis_norm_sq b, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [diagonalMap_coordinate, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_abs (c i)) ▸ pow_le_pow_left₀ (abs_nonneg (c i)) (hc i) 2)
      (sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  simpa only [mul_pow] using hh

omit [CompleteSpace E] in
lemma diagonalMap_comp (b : OrthonormalBasis ι ℝ E) (c d : ι → ℝ) :
    (diagonalMap b c).comp (diagonalMap b d) = diagonalMap b (fun i => c i * d i) := by
  ext x
  apply b.repr.injective
  ext i
  simp only [ContinuousLinearMap.comp_apply, diagonalMap_coordinate]
  ring

omit [CompleteSpace E] in
lemma diagonalMap_sub (b : OrthonormalBasis ι ℝ E) (c d : ι → ℝ) :
    diagonalMap b c - diagonalMap b d = diagonalMap b (fun i => c i - d i) := by
  ext x
  apply b.repr.injective
  ext i
  simp only [sub_apply, map_sub, PiLp.sub_apply, diagonalMap_coordinate]
  ring

def spectralImpulse (b : OrthonormalBasis ι ℝ E) (r c : ι → ℝ) (n : ℕ) : E →L[ℝ] E :=
  diagonalMap b (fun i => chebyshevImpulse (r i) (c i) n)

omit [CompleteSpace E] in
lemma spectral_impulse_bound (b : OrthonormalBasis ι ℝ E) (r c : ι → ℝ)
    {q : ℝ} (hq : 0 ≤ q) (hr : ∀ i, 0 ≤ r i) (hrq : ∀ i, r i ≤ q)
    (hc : ∀ i, |c i| ≤ 1) (n : ℕ) (x : E) :
    ‖spectralImpulse b r c n x‖ ≤ ((n + 1) * q ^ n) * ‖x‖ := by
  exact diagonalMap_bound b _ (by positivity)
    (fun i => chebyshev_impulse_abs_bound (hr i) (hrq i) (hc i) n) x

omit [CompleteSpace E] in
lemma spectral_impulse_difference_bound (b : OrthonormalBasis ι ℝ E) (r c : ι → ℝ)
    {q : ℝ} (hq : 0 ≤ q) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hc : ∀ i, |c i| ≤ 1) (hd : ∀ i, |r i * c i - 1| ≤ 2 * (1 - r i))
    (hrq : ∀ i, Real.sqrt (r i) ≤ q) (n : ℕ) (x : E) :
    ‖(spectralImpulse b r c (n + 1) - spectralImpulse b r c n) x‖ ≤
      (5 * q ^ n) * ‖x‖ := by
  simp only [spectralImpulse, diagonalMap_sub]
  exact diagonalMap_bound b _ (by positivity)
    (fun i => chebyshev_difference_envelope (hr i) (hr1 i) (hc i) (hd i) (hrq i) n) x

omit [CompleteSpace E] in
lemma spectral_impulse_recurrence (b : OrthonormalBasis ι ℝ E) (r c : ι → ℝ)
    (n : ℕ) :
    spectralImpulse b r c (n + 2) =
      (diagonalMap b (fun i => 2 * r i * c i)).comp (spectralImpulse b r c (n + 1)) -
        (diagonalMap b (fun i => r i ^ 2)).comp (spectralImpulse b r c n) := by
  simp only [spectralImpulse, diagonalMap_comp, diagonalMap_sub]
  congr 1
  funext i
  exact chebyshev_impulse_recurrence (r i) (c i) n

lemma transition_impulse_spectral (A : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (eig r c : ι → ℝ) (μ θ : ℝ) (hθ : 1 + θ ≠ 0)
    (hl : ∀ i x, b.repr (A.adjoint (A x)) i = eig i * b.repr x i)
    (hm : ∀ i, r i * c i = (1 - θ ^ 2 * eig i / μ) / (1 + θ))
    (hr : ∀ i, r i ^ 2 = ((1 - θ ^ 2 * eig i / μ) / (1 + θ)) * (1 - θ))
    (e : E) (n : ℕ) :
    (((transition A μ θ : (E × E) → E × E)^[n]) (injection μ θ e)).1 =
      -(θ ^ 2 / μ) • spectralImpulse b r c n e := by
  apply b.repr.injective
  ext i
  have hli (x : E) : b.toBasis.coord i (A.adjoint (A x)) = eig i * b.toBasis.coord i x := by
    simpa only [Module.Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply] using hl i x
  have hh := transition_impulse_coordinate A (b.toBasis.coord i) μ θ (eig i)
    (r i) (c i) hθ hli (hm i) (hr i) e n
  simp only [Module.Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply] at hh
  rw [hh]
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul, spectralImpulse, diagonalMap_coordinate]
  ring

def positionImpulse (A : E →L[ℝ] E) (μ θ : ℝ) (n : ℕ) : E →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E E).comp ((transition A μ θ ^ n).comp (injection μ θ))

omit [FiniteDimensional ℝ E] in
lemma positionImpulse_apply (A : E →L[ℝ] E) (μ θ : ℝ) (n : ℕ) (e : E) :
    positionImpulse A μ θ n e =
      (((transition A μ θ : (E × E) → E × E)^[n]) (injection μ θ e)).1 := by
  change ((transition A μ θ ^ n) (injection μ θ e)).1 = _
  rw [FunLike.coe_pow_eq_iterate]

lemma position_difference_bound (A : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (eig : ι → ℝ) {μ L θ : ℝ} (hμ : 0 < μ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hstep : θ ^ 2 * L ≤ μ)
    (heig : ∀ i, μ ≤ eig i ∧ eig i ≤ L)
    (hl : ∀ i x, b.repr (A.adjoint (A x)) i = eig i * b.repr x i)
    (n : ℕ) (e : E) :
    ‖(positionImpulse A μ θ (n + 1) - positionImpulse A μ θ n) e‖ ≤
      (5 * θ ^ 2 / μ) * (Real.sqrt (1 - θ)) ^ n * ‖e‖ := by
  let m := fun i => (1 - θ ^ 2 * eig i / μ) / (1 + θ)
  let r := fun i => Real.sqrt (m i * (1 - θ))
  let c := fun i => m i / r i
  have hp (i : ι) : 0 ≤ r i ∧ r i ≤ 1 - θ ∧ |c i| ≤ 1 ∧ r i * c i = m i ∧
      r i ^ 2 = m i * (1 - θ) ∧ |r i * c i - 1| ≤ 2 * (1 - r i) := by
    obtain ⟨hm0, hm1⟩ := characteristic_middle_bounds hμ hθ
      (heig i).1 (heig i).2 hstep
    exact accelerated_characteristic_parameters hθ hθ1 hm0 hm1
  have hrep (k : ℕ) : positionImpulse A μ θ k e =
      -(θ ^ 2 / μ) • spectralImpulse b r c k e := by
    rw [positionImpulse_apply]
    exact transition_impulse_spectral A b eig r c μ θ (by positivity) hl
      (fun i => (hp i).2.2.2.1) (fun i => (hp i).2.2.2.2.1) e k
  have hh := spectral_impulse_difference_bound b r c (Real.sqrt_nonneg (1 - θ))
    (fun i => (hp i).1) (fun i => ((hp i).2.1).trans (by linarith))
    (fun i => (hp i).2.2.1) (fun i => (hp i).2.2.2.2.2)
    (fun i => Real.sqrt_le_sqrt (hp i).2.1) n e
  rw [sub_apply, hrep, hrep, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ θ ^ 2 / μ)]
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ θ ^ 2 / μ by positivity)
  simpa only [sub_apply, mul_assoc, mul_comm, mul_left_comm,
    div_eq_mul_inv] using hm

lemma balanced_position_bound (A : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (eig : ι → ℝ) {μ L θ D : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hstep : θ ^ 2 * L ≤ μ) (hD : 0 ≤ D)
    (heig : ∀ i, μ ≤ eig i ∧ eig i ≤ L)
    (hl : ∀ i x, b.repr (A.adjoint (A x)) i = eig i * b.repr x i)
    (e : ℕ → E) (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ D) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, positionImpulse A μ θ (n - 1 - i) (e i)‖ ≤
      11 * θ * D / μ := by
  let q := Real.sqrt (1 - θ)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    dsimp [q]
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by nlinarith)
  have hq2 : q ^ 2 = 1 - θ := Real.sq_sqrt (by linarith)
  have hden : 0 < 1 - q := by linarith
  have hzero (x : E) : ‖positionImpulse A μ θ 0 x‖ ≤ (θ ^ 2 / μ) * ‖x‖ := by
    simp [positionImpulse_apply, injection, norm_smul, abs_of_pos hμ]
  have hh := balanced_convolution_bound (positionImpulse A μ θ) e
    (show 0 ≤ θ ^ 2 / μ by positivity) (show 0 ≤ 5 * θ ^ 2 / μ by positivity)
    hq hq1 hD hzero (position_difference_bound A b eig hμ hθ.le hθ1 hstep heig hl) he n
  have hid : θ / (1 - q) = 1 + q := (div_eq_iff hden.ne').mpr (by nlinarith)
  have hc : θ ^ 2 / μ + (5 * θ ^ 2 / μ) / (1 - q) ≤ 11 * θ / μ := by
    calc
      _ = θ / μ * (θ + 5 * (θ / (1 - q))) := by ring
      _ = θ / μ * (θ + 5 * (1 + q)) := by rw [hid]
      _ ≤ θ / μ * 11 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  exact hh.trans (by simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_right hc hD)

lemma balanced_state_position (A : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (eig : ι → ℝ) {μ L θ D : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hstep : θ ^ 2 * L ≤ μ) (hD : 0 ≤ D)
    (heig : ∀ i, μ ≤ eig i ∧ eig i ≤ L)
    (hl : ∀ i x, b.repr (A.adjoint (A x)) i = eig i * b.repr x i)
    (v : ℕ → E × E) (e : ℕ → E) (hzero : v 0 = 0)
    (hrec : ∀ k, v (k + 1) = transition A μ θ (v k) + injection μ θ (e k))
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ D) (n : ℕ) :
    ‖(v n).1‖ ≤ 11 * θ * D / μ := by
  have hh := congrArg (ContinuousLinearMap.fst ℝ E E)
    (linear_response_formula (transition A μ θ) (injection μ θ) v e hrec n)
  simp only [hzero, map_zero, zero_add, map_sum] at hh
  change (v n).1 = ∑ i ∈ Finset.range n, positionImpulse A μ θ (n - 1 - i) (e i) at hh
  rw [hh]
  exact balanced_position_bound A b eig hμ hθ hθ1 hstep hD heig hl e he n

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma query_bound_of_momentum {μ θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s : E × E) (g : E) :
    ‖acceleratedQuery θ (acceleratedUpdate θ μ s g)‖ ≤
      2 * ‖(acceleratedUpdate θ μ s g).1‖ + ‖s.1‖ := by
  have hd : 0 < 1 + θ := by linarith
  have hm := accelerated_momentum_identity (μ := μ) hd.ne' s g
  have he : acceleratedQuery θ (acceleratedUpdate θ μ s g) =
      (1 / (1 + θ)) •
        ((2 : ℝ) • (acceleratedUpdate θ μ s g).1 - (1 - θ) • s.1) := by
    simp only [acceleratedQuery]
    rw [hm]
    congr 1
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (1 + θ))]
  have hb := norm_sub_le ((2 : ℝ) • (acceleratedUpdate θ μ s g).1) ((1 - θ) • s.1)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by linarith : 0 ≤ 1 - θ)] at hb
  calc
    _ ≤ (1 / (1 + θ)) * (2 * ‖(acceleratedUpdate θ μ s g).1‖ + (1 - θ) * ‖s.1‖) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ _ := by
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hd).mpr
      nlinarith [norm_nonneg (acceleratedUpdate θ μ s g).1, norm_nonneg s.1]

lemma balanced_state_query (A : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (eig : ι → ℝ) {μ L θ D : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hstep : θ ^ 2 * L ≤ μ) (hD : 0 ≤ D)
    (heig : ∀ i, μ ≤ eig i ∧ eig i ≤ L)
    (hl : ∀ i x, b.repr (A.adjoint (A x)) i = eig i * b.repr x i)
    (v : ℕ → E × E) (e : ℕ → E) (hzero : v 0 = 0)
    (hrec : ∀ k, v (k + 1) = transition A μ θ (v k) + injection μ θ (e k))
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ D) (n : ℕ) :
    ‖acceleratedQuery θ (v n)‖ ≤ 33 * θ * D / μ := by
  cases n with
  | zero => simp [hzero, acceleratedQuery]; positivity
  | succ n =>
      have hh := query_bound_of_momentum (μ := μ) hθ.le hθ1 (v n)
        (A.adjoint (A (acceleratedQuery θ (v n))) + e n)
      rw [forced_transition, ← hrec] at hh
      have hn := balanced_state_position A b eig hμ hθ hθ1 hstep hD heig hl v e hzero hrec he n
      have hn' := balanced_state_position A b eig hμ hθ hθ1 hstep hD heig hl v e hzero hrec he (n + 1)
      calc
        _ ≤ 2 * (11 * θ * D / μ) + 11 * θ * D / μ :=
          hh.trans (add_le_add (mul_le_mul_of_nonneg_left hn' (by norm_num)) hn)
        _ = _ := by ring

omit [CompleteSpace E] in
lemma diagonalMap_inner (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (x y : E) :
    ⟪diagonalMap b c x, y⟫ = ⟪x, diagonalMap b c y⟫ := by
  simp only [diagonalMap_apply, sum_inner, inner_sum, real_inner_smul_left,
    inner_smul_right, OrthonormalBasis.repr_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm x (b i)]
  ring

lemma diagonalMap_adjoint (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) :
    (diagonalMap b c).adjoint = diagonalMap b c := by
  exact (show (diagonalMap b c).toLinearMap.IsSymmetric from diagonalMap_inner b c).clm_adjoint_eq

omit [CompleteSpace E] in
lemma spectral_diagonalization (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) :
    H = diagonalMap (hH.eigenvectorBasis rfl) (hH.eigenvalues rfl) := by
  ext x
  apply (hH.eigenvectorBasis rfl).repr.injective
  ext i
  rw [diagonalMap_coordinate]
  exact hH.eigenvectorBasis_apply_self_apply rfl x i

omit [CompleteSpace E] in
lemma spectral_eigenvalue_bounds (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {μ L : ℝ}
    (hlo : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪H x, x⟫)
    (hhi : ∀ x, ⟪H x, x⟫ ≤ L * ‖x‖ ^ 2)
    (i : Fin (Module.finrank ℝ E)) :
    μ ≤ hH.eigenvalues rfl i ∧ hH.eigenvalues rfl i ≤ L := by
  have hl := hlo (hH.eigenvectorBasis rfl i)
  have hu := hhi (hH.eigenvectorBasis rfl i)
  change μ * ‖hH.eigenvectorBasis rfl i‖ ^ 2 ≤
    ⟪H.toLinearMap (hH.eigenvectorBasis rfl i), hH.eigenvectorBasis rfl i⟫ at hl
  change ⟪H.toLinearMap (hH.eigenvectorBasis rfl i), hH.eigenvectorBasis rfl i⟫ ≤
    L * ‖hH.eigenvectorBasis rfl i‖ ^ 2 at hu
  simp only [hH.apply_eigenvectorBasis, real_inner_smul_left, real_inner_self_eq_norm_sq,
    OrthonormalBasis.norm_eq_one, one_pow, mul_one] at hl hu
  exact ⟨hl, hu⟩

lemma spectral_factorization (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (hp : ∀ x, 0 ≤ ⟪H x, x⟫) :
    ∃ A : E →L[ℝ] E, A.adjoint.comp A = H := by
  let b := hH.eigenvectorBasis rfl
  let eig : Fin (Module.finrank ℝ E) → ℝ := hH.eigenvalues rfl
  have heig (i : Fin (Module.finrank ℝ E)) : 0 ≤ eig i := by
    have hh := hp (b i)
    change 0 ≤ ⟪H.toLinearMap (b i), b i⟫ at hh
    simpa [eig, b, hH.apply_eigenvectorBasis, real_inner_smul_left,
      real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one] using hh
  refine ⟨diagonalMap b (fun i => Real.sqrt (eig i)), ?_⟩
  rw [diagonalMap_adjoint, diagonalMap_comp]
  have he : (fun i => Real.sqrt (eig i) * Real.sqrt (eig i)) = eig := by
    funext i
    exact Real.mul_self_sqrt (heig i)
  rw [he]
  exact (spectral_diagonalization H hH).symm

end OracleTemplate.TemporalDiscrepancy
