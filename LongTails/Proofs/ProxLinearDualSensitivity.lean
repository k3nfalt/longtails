import Mathlib.Analysis.InnerProductSpace.Adjoint
import LongTails.Proofs.Clipping
import Mathlib.Tactic
import Mathlib.Topology.Maps.Proper.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ProxLinearDualSensitivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma variational_solution_distance {A B : E → E} {u v : E} {κ : ℝ}
    (hstrong : κ * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫)
    (hu : 0 ≤ ⟪A u, v - u⟫)
    (hv : 0 ≤ ⟪B v, u - v⟫) :
    κ * ‖u - v‖ ≤ ‖A v - B v‖ := by
  have hneg : ⟪A u, v - u⟫ = -⟪A u, u - v⟫ := by
    rw [← inner_neg_right]
    congr 1
    abel
  have hsplit : ⟪A u - A v, u - v⟫ =
      ⟪A u, u - v⟫ - ⟪B v, u - v⟫ + ⟪B v - A v, u - v⟫ := by
    simp only [inner_sub_left]
    ring
  have hc := real_inner_le_norm (B v - A v) (u - v)
  rw [norm_sub_rev (B v) (A v)] at hc
  have hmul : κ * ‖u - v‖ ^ 2 ≤ ‖A v - B v‖ * ‖u - v‖ := by
    rw [hneg] at hu
    rw [hsplit] at hstrong
    linarith
  by_cases hzero : ‖u - v‖ = 0
  · simp only [hzero, mul_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

lemma variational_solution_scaled_distance {A B : E → E} {u v : E} {κ s : ℝ}
    (hs : 0 ≤ s)
    (hstrong : κ * ‖u - v‖ ^ 2 ≤ s * ⟪A u - A v, u - v⟫)
    (hu : 0 ≤ ⟪A u, v - u⟫) (hv : 0 ≤ ⟪B v, u - v⟫) :
    κ * ‖u - v‖ ≤ s * ‖A v - B v‖ := by
  have hstrong' : κ * ‖u - v‖ ^ 2 ≤ ⟪s • A u - s • A v, u - v⟫ := by
    rw [← smul_sub, real_inner_smul_left]
    exact hstrong
  have hu' : 0 ≤ ⟪s • A u, v - u⟫ := by
    rw [real_inner_smul_left]
    exact mul_nonneg hs hu
  have hv' : 0 ≤ ⟪s • B v, u - v⟫ := by
    rw [real_inner_smul_left]
    exact mul_nonneg hs hv
  have h := variational_solution_distance (A := fun x => s • A x)
    (B := fun x => s • B x) hstrong' hu' hv'
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] at h
  exact h

lemma nonneg_linear_coefficient {a b : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t * a + t ^ 2 * b) : 0 ≤ a := by
  by_contra hn
  have ha : a < 0 := lt_of_not_ge hn
  by_cases hb : b ≤ -a / 2
  · have h1 := h 1 zero_lt_one le_rfl
    nlinarith
  · have hbpos : 0 < b := by linarith
    let t := -a / (2 * b)
    have ht : 0 < t := div_pos (neg_pos.mpr ha) (mul_pos (by norm_num) hbpos)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      apply (div_le_one (by positivity)).2
      linarith
    have htb : t * b = -a / 2 := by
      dsimp [t]
      field_simp
    have htpoly := h t ht ht1
    have heq : t * a + t ^ 2 * b = t * (a / 2) := by
      calc
        t * a + t ^ 2 * b = t * (a + t * b) := by ring
        _ = t * (a / 2) := by rw [htb]; ring
    rw [heq] at htpoly
    have hneg : t * (a / 2) < 0 := mul_neg_of_pos_of_neg ht (by linarith)
    linarith

lemma norm_add_smul_sq (u v : E) (t : ℝ) :
    ‖u + t • v‖ ^ 2 = ‖u‖ ^ 2 + 2 * t * ⟪u, v⟫ + t ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right]
  ring

lemma quadratic_min_directional {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (T : E →L[ℝ] F) (g : F) (c u d : E) (η τ : ℝ)
    (hmin : ∀ t : ℝ, 0 < t → t ≤ 1 →
      η / 2 * ‖g + T u‖ ^ 2 - ⟪c, u⟫ + τ / 2 * ‖u‖ ^ 2 ≤
      η / 2 * ‖g + T (u + t • d)‖ ^ 2 - ⟪c, u + t • d⟫ +
        τ / 2 * ‖u + t • d‖ ^ 2) :
    0 ≤ η * ⟪g + T u, T d⟫ - ⟪c, d⟫ + τ * ⟪u, d⟫ := by
  apply nonneg_linear_coefficient
    (b := η / 2 * ‖T d‖ ^ 2 + τ / 2 * ‖d‖ ^ 2)
  intro t ht ht1
  have h := hmin t ht ht1
  have heq : g + T (u + t • d) = (g + T u) + t • T d := by
    simp only [map_add, map_smul]
    abel
  rw [heq, norm_add_smul_sq, norm_add_smul_sq, inner_add_right,
    real_inner_smul_right] at h
  nlinarith

section Adjoint

variable [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def quadraticGradient (T : E →L[ℝ] F) (g : F) (c : E) (η τ : ℝ)
    (u : E) : E := η • T.adjoint (g + T u) - c + τ • u

lemma quadraticGradient_difference (T : E →L[ℝ] F) (g : F) (c u v : E) (η τ : ℝ) :
    quadraticGradient T g c η τ u - quadraticGradient T g c η τ v =
      η • T.adjoint (T (u - v)) + τ • (u - v) := by
  simp only [quadraticGradient, map_add, map_sub]
  module

lemma quadraticGradient_inner (T : E →L[ℝ] F) (g : F) (c u v : E) (η τ : ℝ) :
    ⟪quadraticGradient T g c η τ u - quadraticGradient T g c η τ v, u - v⟫ =
      η * ‖T (u - v)‖ ^ 2 + τ * ‖u - v‖ ^ 2 := by
  rw [quadraticGradient_difference, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

lemma quadraticGradient_direction (T : E →L[ℝ] F) (g : F) (c u d : E) (η τ : ℝ) :
    ⟪quadraticGradient T g c η τ u, d⟫ =
      η * ⟪g + T u, T d⟫ - ⟪c, d⟫ + τ * ⟪u, d⟫ := by
  simp only [quadraticGradient, inner_add_left, inner_sub_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]

lemma adjoint_composition_error_le (T S : E →L[ℝ] F) (g h : F) (u : E)
    {B G Λ : ℝ} (hB : 0 ≤ B) (hT : ‖T‖ ≤ B) (hS : ‖S‖ ≤ B)
    (hh : ‖h‖ ≤ G) (hu : ‖u‖ ≤ Λ) :
    ‖T.adjoint (g + T u) - S.adjoint (h + S u)‖ ≤
      B * ‖g - h‖ + (G + 2 * B * Λ) * ‖T - S‖ := by
  have hTa (a : F) : ‖T.adjoint a‖ ≤ B * ‖a‖ := by
    have hn : ‖T.adjoint‖ ≤ B := by simpa using hT
    exact (T.adjoint.le_opNorm a).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hDa (a : F) : ‖(T - S).adjoint a‖ ≤ ‖T - S‖ * ‖a‖ := by
    have hn : ‖(T - S).adjoint‖ = ‖T - S‖ := ContinuousLinearMap.adjoint.norm_map (T - S)
    simpa only [hn] using ((T - S).adjoint.le_opNorm a)
  have hSu : ‖S u‖ ≤ B * Λ :=
    (S.le_opNorm u).trans (mul_le_mul hS hu (norm_nonneg _) hB)
  have hDu : ‖(T - S) u‖ ≤ ‖T - S‖ * Λ :=
    ((T - S).le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
  have heq : T.adjoint (g + T u) - S.adjoint (h + S u) =
      T.adjoint (g - h) + T.adjoint ((T - S) u) + (T - S).adjoint (h + S u) := by
    simp only [map_add, map_sub, sub_apply]
    abel
  rw [heq]
  calc
    ‖T.adjoint (g - h) + T.adjoint ((T - S) u) + (T - S).adjoint (h + S u)‖ ≤
        ‖T.adjoint (g - h)‖ + ‖T.adjoint ((T - S) u)‖ +
          ‖(T - S).adjoint (h + S u)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ B * ‖g - h‖ + B * (‖T - S‖ * Λ) + ‖T - S‖ * (G + B * Λ) := by
      apply add_le_add
      · exact add_le_add (hTa _) ((hTa _).trans (mul_le_mul_of_nonneg_left hDu hB))
      · exact (hDa _).trans (mul_le_mul_of_nonneg_left
          ((norm_add_le _ _).trans (add_le_add hh hSu)) (norm_nonneg _))
    _ = B * ‖g - h‖ + (G + 2 * B * Λ) * ‖T - S‖ := by ring

lemma quadraticGradient_error (T S : E →L[ℝ] F) (g h : F) (c d u : E)
    {η τ B G Λ : ℝ} (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hT : ‖T‖ ≤ B) (hS : ‖S‖ ≤ B) (hh : ‖h‖ ≤ G) (hu : ‖u‖ ≤ Λ) :
    ‖quadraticGradient T g c η 0 u - quadraticGradient S h d η τ u‖ ≤
      η * (B * ‖g - h‖ + (G + 2 * B * Λ) * ‖T - S‖) + ‖c - d‖ + τ * Λ := by
  have heq : quadraticGradient T g c η 0 u - quadraticGradient S h d η τ u =
      η • (T.adjoint (g + T u) - S.adjoint (h + S u)) - (c - d) - τ • u := by
    simp only [quadraticGradient, zero_smul]
    module
  rw [heq]
  have he := adjoint_composition_error_le T S g h u hB hT hS hh hu
  calc
    ‖η • (T.adjoint (g + T u) - S.adjoint (h + S u)) - (c - d) - τ • u‖ ≤
        ‖η • (T.adjoint (g + T u) - S.adjoint (h + S u))‖ + ‖c - d‖ + ‖τ • u‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = η * ‖T.adjoint (g + T u) - S.adjoint (h + S u)‖ + ‖c - d‖ + τ * ‖u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hη, abs_of_nonneg hτ]
    _ ≤ η * (B * ‖g - h‖ + (G + 2 * B * Λ) * ‖T - S‖) + ‖c - d‖ + τ * Λ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left he hη) le_rfl)
        (mul_le_mul_of_nonneg_left hu hτ)

lemma fullrank_dual_distance (T S : E →L[ℝ] F) (g h : F) (c d u v : E)
    {η τ H : ℝ} (hη : 0 ≤ η) (hH : 0 ≤ H)
    (hlower : ∀ z, ‖z‖ ≤ H * ‖T z‖)
    (hu : 0 ≤ ⟪quadraticGradient T g c η 0 u, v - u⟫)
    (hv : 0 ≤ ⟪quadraticGradient S h d η τ v, u - v⟫) :
    η * ‖u - v‖ ≤ H ^ 2 *
      ‖quadraticGradient T g c η 0 v - quadraticGradient S h d η τ v‖ := by
  have hsq : ‖u - v‖ ^ 2 ≤ (H * ‖T (u - v)‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hH (norm_nonneg _))).2 (hlower _)
  have hprod := mul_le_mul_of_nonneg_left hsq hη
  have hstrong : η * ‖u - v‖ ^ 2 ≤ H ^ 2 *
      ⟪quadraticGradient T g c η 0 u - quadraticGradient T g c η 0 v, u - v⟫ := by
    rw [quadraticGradient_inner]
    nlinarith
  exact variational_solution_scaled_distance (sq_nonneg H) hstrong hu hv

lemma fullrank_primal_step_error (T S : E →L[ℝ] F) (g h : F) (c d u v : E)
    {η τ B G Λ H : ℝ} (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hT : ‖T‖ ≤ B) (hS : ‖S‖ ≤ B) (hh : ‖h‖ ≤ G) (hvnorm : ‖v‖ ≤ Λ)
    (hlower : ∀ z, ‖z‖ ≤ H * ‖T z‖)
    (hu : 0 ≤ ⟪quadraticGradient T g c η 0 u, v - u⟫)
    (hv : 0 ≤ ⟪quadraticGradient S h d η τ v, u - v⟫) :
    ‖(-η) • (g + T u) - (-η) • (h + S v)‖ ≤
      η * (1 + B ^ 2 * H ^ 2) * ‖g - h‖ +
      η * (Λ + B * H ^ 2 * (G + 2 * B * Λ)) * ‖T - S‖ +
      B * H ^ 2 * ‖c - d‖ + B * H ^ 2 * Λ * τ := by
  have hdist := fullrank_dual_distance T S g h c d u v hη hH hlower hu hv
  have herr := quadraticGradient_error T S g h c d v hη hτ hB hT hS hh hvnorm
  have hdist' : η * ‖u - v‖ ≤ H ^ 2 *
      (η * (B * ‖g - h‖ + (G + 2 * B * Λ) * ‖T - S‖) + ‖c - d‖ + τ * Λ) :=
    hdist.trans (mul_le_mul_of_nonneg_left herr (sq_nonneg H))
  have hTuv : ‖T (u - v)‖ ≤ B * ‖u - v‖ :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hDv : ‖(T - S) v‖ ≤ ‖T - S‖ * Λ :=
    ((T - S).le_opNorm v).trans (mul_le_mul_of_nonneg_left hvnorm (norm_nonneg _))
  have heq : g + T u - (h + S v) = (g - h) + T (u - v) + (T - S) v := by
    simp only [map_sub, sub_apply]
    abel
  have hn : ‖g + T u - (h + S v)‖ ≤ ‖g - h‖ + B * ‖u - v‖ + ‖T - S‖ * Λ := by
    rw [heq]
    exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add le_rfl hTuv) hDv)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη]
  have hscaled := mul_le_mul_of_nonneg_left hn hη
  have hdistB := mul_le_mul_of_nonneg_left hdist' hB
  nlinarith

end Adjoint

lemma clipping_nonexpansive {B : ℝ} (hB : 0 ≤ B) (v w : E) :
    ‖OracleTemplate.clip B v - OracleTemplate.clip B w‖ ≤ ‖v - w‖ := by
  let u := OracleTemplate.clip B v
  let z := OracleTemplate.clip B w
  let A : E → E := fun x => x - v
  let D : E → E := fun x => x - w
  have hstrong : 1 * ‖u - z‖ ^ 2 ≤ ⟪A u - A z, u - z⟫ := by
    have heq : A u - A z = u - z := by dsimp [A]; abel
    rw [heq, real_inner_self_eq_norm_sq, one_mul]
  have hu : 0 ≤ ⟪A u, z - u⟫ := by
    have h := OracleTemplate.inner_clip_residual_nonpos hB
      (OracleTemplate.norm_clip_le hB w) v
    have heq : A u = -(v - u) := by dsimp [A]; abel
    rw [heq, inner_neg_left]
    exact neg_nonneg.mpr h
  have hz : 0 ≤ ⟪D z, u - z⟫ := by
    have h := OracleTemplate.inner_clip_residual_nonpos hB
      (OracleTemplate.norm_clip_le hB v) w
    have heq : D z = -(w - z) := by dsimp [D]; abel
    rw [heq, inner_neg_left]
    exact neg_nonneg.mpr h
  have hd := variational_solution_distance hstrong hu hz
  have heq : A z - D z = w - v := by dsimp [A, D]; abel
  rw [heq, norm_sub_rev w v, one_mul] at hd
  exact hd

lemma continuous_clipping {B : ℝ} (hB : 0 ≤ B) :
    Continuous (OracleTemplate.clip (E := E) B) := by
  have h : LipschitzWith 1 (OracleTemplate.clip (E := E) B) :=
    LipschitzWith.of_dist_le_mul fun v w => by
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using clipping_nonexpansive hB v w
  exact h.continuous

lemma continuous_unique_minimizer {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] (q : X → Y → ℝ) (m : X → Y)
    (hq : Continuous (fun p : X × Y => q p.1 p.2))
    (hmin : ∀ x y, q x (m x) ≤ q x y)
    (hunique : ∀ x y, (∀ z, q x y ≤ q x z) → m x = y) : Continuous m := by
  apply continuous_of_isClosed_graph
  have heq : m.graph = {p : X × Y | ∀ y, q p.1 p.2 ≤ q p.1 y} := by
    ext p
    change (m p.1 = p.2) ↔ ∀ y, q p.1 p.2 ≤ q p.1 y
    constructor
    · intro h
      rw [← h]
      exact hmin p.1
    · exact hunique p.1 p.2
  rw [heq, Set.ofPred_forall]
  apply isClosed_iInter
  intro y
  exact isClosed_le hq (hq.comp (continuous_fst.prodMk continuous_const))

end LongTails.Proofs.ProxLinearDualSensitivity
