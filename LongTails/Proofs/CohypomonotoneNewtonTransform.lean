import LongTails.Proofs.CohypomonotoneNewtonInverse
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

open Filter Topology
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CohypomonotoneNewtonTransform

open LongTails.Algorithms.CohypomonotoneNewton
open LongTails.Proofs.CohypomonotoneNewtonGeometry
open LongTails.Proofs.CohypomonotoneNewtonInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma right_inverse_lipschitz {T V : E → E}
    (hexp : ∀ x y, ‖x - y‖ ≤ ‖T x - T y‖) (hright : ∀ y, T (V y) = y) :
    LipschitzWith 1 V := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, hright, NNReal.coe_one, one_mul] using hexp (V x) (V y)

lemma right_inverse_derivative {T V : E → E} {D : E → E →L[ℝ] E}
    (hT : ∀ x, HasFDerivAt T (D x) x)
    (hexp : ∀ x y, ‖x - y‖ ≤ ‖T x - T y‖) (hright : ∀ y, T (V y) = y) (y : E) :
    HasFDerivAt V (linearInverse (D (V y))) y := by
  have hl : ∀ v, ‖v‖ ≤ ‖D (V y) v‖ :=
    expansive_derivative (hT (V y)) (fun x => hexp x (V y))
  have hi := HasFDerivAt.of_comp_of_leftInverse
    (right_inverse_lipschitz hexp hright).continuous.continuousAt
    (hT (V y)) (hasFDerivAt_id y) (Eventually.of_forall hright)
    (linearInverse_left (D (V y)) hl)
  simpa only [ContinuousLinearMap.comp_id] using hi

lemma graph_derivative {F V : E → E} {J : E → E →L[ℝ] E} {γ : ℝ}
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hexp : ∀ x y, ‖x - y‖ ≤ ‖(x + γ • F x) - (y + γ • F y)‖)
    (hright : ∀ y, V y + γ • F (V y) = y) (y : E) :
    HasFDerivAt (fun y => F (V y)) (graphJacobian γ (J (V y))) y := by
  have ht : ∀ x, HasFDerivAt (fun x => x + γ • F x)
      (ContinuousLinearMap.id ℝ E + γ • J x) x :=
    fun x => (hasFDerivAt_id x).add ((hF x).const_smul γ)
  exact (hF (V y)).comp y (right_inverse_derivative ht hexp hright y)

omit [FiniteDimensional ℝ E] in
lemma graph_monotone {F V : E → E} {ρ γ : ℝ} (hγ : ρ ≤ γ)
    (hco : ∀ x y, -ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hright : ∀ y, V y + γ • F (V y) = y) (x y : E) :
    0 ≤ ⟪F (V x) - F (V y), x - y⟫ := by
  have hh := shifted_cocoercive (γ := γ) hco (V x) (V y)
  rw [hright, hright] at hh
  exact (mul_nonneg (sub_nonneg.mpr hγ) (sq_nonneg _)).trans hh

omit [FiniteDimensional ℝ E] in
lemma graph_lipschitz {F V : E → E} {ρ γ : ℝ} (hγ : ρ < γ)
    (hco : ∀ x y, -ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hright : ∀ y, V y + γ • F (V y) = y) (x y : E) :
    ‖F (V x) - F (V y)‖ ≤ (1 / (γ - ρ)) * ‖x - y‖ := by
  have hh := shifted_cocoercive (γ := γ) hco (V x) (V y)
  rw [hright, hright] at hh
  have hc := real_inner_le_norm (F (V x) - F (V y)) (x - y)
  by_cases hz : ‖F (V x) - F (V y)‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖F (V x) - F (V y)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hb : (γ - ρ) * ‖F (V x) - F (V y)‖ ≤ ‖x - y‖ := by nlinarith
    have hd : 0 < γ - ρ := sub_pos.mpr hγ
    have he : (1 / (γ - ρ)) * ‖x - y‖ = ‖x - y‖ / (γ - ρ) := by ring
    rw [he]
    exact (le_div_iff₀ hd).mpr (by nlinarith only [hb])

lemma graphJacobian_difference (J K : E →L[ℝ] E) (γ : ℝ)
    (hJ : ∀ v, ‖v‖ ≤ ‖v + γ • J v‖)
    (hK : ∀ v, ‖v‖ ≤ ‖v + γ • K v‖) :
    ‖graphJacobian γ J - graphJacobian γ K‖ ≤ ‖J - K‖ := by
  let A := ContinuousLinearMap.id ℝ E + γ • J
  let B := ContinuousLinearMap.id ℝ E + γ • K
  have ha : ∀ v, ‖v‖ ≤ ‖A v‖ := hJ
  have hb : ∀ v, ‖v‖ ≤ ‖B v‖ := hK
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  let z := linearInverse A u
  let v := linearInverse B u
  have hz : z + γ • J z = u := linearInverse_right A ha u
  have hv : v + γ • K v = u := linearInverse_right B hb u
  have hid : (J z - K v) + γ • J (J z - K v) = (J - K) v := by
    have h1 := congrArg J hz
    have h2 := congrArg J hv
    simp only [map_add, map_smul] at h1 h2
    simp only [map_sub, smul_sub, sub_apply]
    linear_combination (norm := module) h1 - h2
  have hl := hJ (J z - K v)
  rw [hid] at hl
  have hvn : ‖v‖ ≤ ‖u‖ := (hb v).trans_eq (congrArg norm (linearInverse_right B hb u))
  have hnorm := (J - K).le_opNorm v
  have hm := mul_le_mul_of_nonneg_left hvn (norm_nonneg (J - K))
  change ‖J z - K v‖ ≤ ‖J - K‖ * ‖u‖
  exact hl.trans (hnorm.trans hm)

lemma graph_jacobian_lipschitz {F V : E → E} {J : E → E →L[ℝ] E} {γ H : ℝ}
    (hF : ∀ x, HasFDerivAt F (J x) x) (hH : 0 ≤ H)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ H * ‖x - y‖)
    (hexp : ∀ x y, ‖x - y‖ ≤ ‖(x + γ • F x) - (y + γ • F y)‖)
    (hright : ∀ y, V y + γ • F (V y) = y) (x y : E) :
    ‖graphJacobian γ (J (V x)) - graphJacobian γ (J (V y))‖ ≤ H * ‖x - y‖ := by
  have ht : ∀ x, HasFDerivAt (fun x => x + γ • F x)
      (ContinuousLinearMap.id ℝ E + γ • J x) x :=
    fun x => (hasFDerivAt_id x).add ((hF x).const_smul γ)
  have hl : ∀ x v, ‖v‖ ≤ ‖v + γ • J x v‖ :=
    fun x => expansive_derivative (ht x) (fun y => hexp y x)
  have hv : ‖V x - V y‖ ≤ ‖x - y‖ := by
    simpa only [hright] using hexp (V x) (V y)
  exact (graphJacobian_difference _ _ γ (hl _) (hl _)).trans
    ((hJ _ _).trans (mul_le_mul_of_nonneg_left hv hH))

omit [FiniteDimensional ℝ E] in
lemma monotone_derivative {G : E → E} {J : E →L[ℝ] E} {x : E}
    (hG : HasFDerivAt G J x)
    (hmono : ∀ y, 0 ≤ ⟪G y - G x, y - x⟫) (v : E) : 0 ≤ ⟪J v, v⟫ := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun t : ℝ => G (x + t • v)) (J v) 0 := by
    have hx : HasFDerivAt G J ((fun t : ℝ => x + t • v) 0) := by simpa using hG
    exact hx.comp_hasDerivAt (0 : ℝ) hline
  have ht : Tendsto (fun t : ℝ =>
      ⟪t⁻¹ • (G (x + (0 + t) • v) - G (x + (0 : ℝ) • v)), v⟫)
      (𝓝[>] 0) (𝓝 ⟪J v, v⟫) :=
    Filter.Tendsto.inner hd.tendsto_slope_zero_right tendsto_const_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with t (htpos : 0 < t)
  simp only [zero_add, zero_smul, add_zero, real_inner_smul_left]
  have hh := hmono (x + t • v)
  rw [add_sub_cancel_left, real_inner_smul_right] at hh
  have hi : 0 ≤ ⟪G (x + t • v) - G x, v⟫ := by nlinarith
  exact mul_nonneg (inv_nonneg.mpr htpos.le) hi

lemma affinePoint_spec (D : E →L[ℝ] E) {a : ℝ} (ha : 0 ≤ a)
    (hmono : ∀ v, 0 ≤ ⟪D v, v⟫) (c n f : E) :
    let w := affinePoint a c n f D
    w + a • (f + D (w - n)) = c ∧ ‖w - n‖ ≤ ‖c - n - a • f‖ := by
  let A := ContinuousLinearMap.id ℝ E + a • D
  let v := linearSolve A (c - n - a • f)
  have hl : ∀ u, ‖u‖ ≤ ‖A u‖ := fun u =>
    shifted_norm_lower (ρ := 0) (γ := a) (by simpa using ha) ha (by simpa using hmono u)
  have hv : v + a • D v = c - n - a • f := linearSolve_eq A _ hl
  change (n + v) + a • (f + D (n + v - n)) = c ∧ ‖n + v - n‖ ≤ _
  rw [add_sub_cancel_left]
  constructor
  · rw [smul_add]
    linear_combination (norm := module) hv
  · exact (hl v).trans_eq (congrArg norm (linearSolve_eq A _ hl))

lemma exists_graph_inverse {F : E → E} {J : E → E →L[ℝ] E} {ρ γ : ℝ}
    (hF : ∀ x, HasFDerivAt F (J x) x) (hγ : 2 * ρ ≤ γ) (hγ0 : 0 ≤ γ)
    (hco : ∀ x y, -ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫) :
    ∃ V : E → E, (∀ y, V y + γ • F (V y) = y) ∧
      (∀ x, V (x + γ • F x) = x) := by
  have ht : ∀ x, HasFDerivAt (fun x => x + γ • F x)
      (ContinuousLinearMap.id ℝ E + γ • J x) x :=
    fun x => (hasFDerivAt_id x).add ((hF x).const_smul γ)
  have he := shifted_expansive hγ hγ0 hco
  have hs := expansive_surjective ht he
  choose V hv using hs
  dsimp only at hv
  refine ⟨V, hv, ?_⟩
  intro x
  have hh := he (V (x + γ • F x)) x
  rw [hv, sub_self, norm_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

lemma graphJacobian_norm {F V : E → E} {J : E → E →L[ℝ] E} {ρ γ L : ℝ}
    (hF : ∀ x, HasFDerivAt F (J x) x) (hγ : ρ < γ) (hL : 0 ≤ L)
    (hbound : 1 / (γ - ρ) ≤ L)
    (hco : ∀ x y, -ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hexp : ∀ x y, ‖x - y‖ ≤ ‖(x + γ • F x) - (y + γ • F y)‖)
    (hright : ∀ y, V y + γ • F (V y) = y) (y : E) :
    ‖graphJacobian γ (J (V y))‖ ≤ L := by
  apply (graph_derivative hF hexp hright y).le_of_lip' hL
  apply Filter.Eventually.of_forall
  intro x
  exact (graph_lipschitz hγ hco hright x y).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))

lemma graphJacobian_at_sample {F V : E → E} {J : E → E →L[ℝ] E} {γ : ℝ}
    (hleft : ∀ x, V (x + γ • F x) = x) (x : E) :
    F (V (x + γ • F x)) = F x ∧
      graphJacobian γ (J (V (x + γ • F x))) = graphJacobian γ (J x) := by
  simp only [hleft, and_self]

end LongTails.Proofs.CohypomonotoneNewtonTransform
