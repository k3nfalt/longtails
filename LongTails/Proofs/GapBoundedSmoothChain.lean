import LongTails.Proofs.GapBoundedSmoothDual
import LongTails.Proofs.GeneralizedSmoothHardChainRadius

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.GapBoundedSmoothChain

open CompactConjugate GeneralizedSmoothHardDual GeneralizedSmoothHardTransfer

noncomputable def shift (m : ℕ) (b : ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => (2 * (m : ℝ) - i.val) * b)

noncomputable def objective {m : ℕ} (L G b : ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  value (feasible (fun _ => G)) (GapBoundedSmoothDual.quadratic L) (x + shift m b)

noncomputable def field {m : ℕ} (L G b : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  maximizer (feasible (fun _ => G)) (GapBoundedSmoothDual.quadratic L) (x + shift m b)

lemma shift_bounds {m : ℕ} (b : ℝ) (hb : 0 ≤ b) (i : Fin m) :
    (m : ℝ) * b ≤ shift m b i ∧ shift m b i ≤ 2 * (m : ℝ) * b := by
  have hi : (i.val : ℝ) ≤ m := by exact_mod_cast i.isLt.le
  change (m : ℝ) * b ≤ (2 * (m : ℝ) - i.val) * b ∧ (2 * (m : ℝ) - i.val) * b ≤ 2 * (m : ℝ) * b
  constructor <;> nlinarith [Nat.cast_nonneg i.val (α := ℝ)]

lemma objective_nonnegative {m : ℕ} (L G b : ℝ) (hG : 0 < G)
    (x : EuclideanSpace ℝ (Fin m)) : 0 ≤ objective L G b x :=
  GapBoundedSmoothDual.value_nonnegative L G hG _

lemma objective_zero {m : ℕ} (L G b : ℝ) (hL : 0 < L) (hG : 0 < G)
    (x : EuclideanSpace ℝ (Fin m)) (hx : ∀ i, x i + shift m b i ≤ 0) :
    objective L G b x = 0 :=
  GapBoundedSmoothDual.value_zero L G hL hG _ hx

lemma vertex_bound {m : ℕ} (L G b : ℝ) (hG : 0 < G)
    (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    G * (x i + shift m b i) - G ^ 2 / (2 * L) ≤ objective L G b x := by
  have hK := feasible_compact (fun _ : Fin m => G) G (fun _ => hG) hG.le (fun _ => le_rfl)
  have hh := (maximizer_spec hK ⟨0, feasible_zero _⟩
    (GapBoundedSmoothDual.quadratic_continuous L).continuousOn (x + shift m b)).2
    (GeneralizedSmoothHardChain.vertex_feasible (fun _ => G) (fun _ => hG) i)
  have hv : GeneralizedSmoothHardChain.vertex (fun _ : Fin m => G) i =
      EuclideanSpace.single i G := by
    ext j
    simp [GeneralizedSmoothHardChain.vertex, PiLp.single_apply, eq_comm]
  rw [hv] at hh
  change ⟪x + shift m b, EuclideanSpace.single i G⟫ -
    GapBoundedSmoothDual.quadratic L (EuclideanSpace.single i G) ≤ objective L G b x at hh
  simpa [GapBoundedSmoothDual.quadratic, EuclideanSpace.inner_single_right,
    PiLp.norm_single, Real.norm_eq_abs, sq_abs] using hh

lemma origin_upper {m : ℕ} (L G b : ℝ) (hL : 0 < L) (hG : 0 < G) (hb : 0 ≤ b) :
    objective (m := m) L G b 0 ≤ 2 * (m : ℝ) * b * G := by
  let z := field (m := m) L G b 0
  have hz : z ∈ feasible (fun _ => G) := (maximizer_spec
    (feasible_compact (fun _ : Fin m => G) G (fun _ => hG) hG.le (fun _ => le_rfl))
    ⟨0, feasible_zero _⟩ (GapBoundedSmoothDual.quadratic_continuous L).continuousOn _).1
  have hs := feasible_sum_le (fun _ => G) G (fun _ => hG) hG.le (fun _ => le_rfl) z hz
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (shift_bounds b hb i).2 (hz.1 i))
  rw [← Finset.mul_sum] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hi : ⟪shift m b, z⟫ = ∑ i, shift m b i * z i := by
    simp [PiLp.inner_apply, mul_comm]
  have hd : 0 ≤ GapBoundedSmoothDual.quadratic L z := by
    unfold GapBoundedSmoothDual.quadratic
    positivity
  change ⟪0 + shift m b, z⟫ - GapBoundedSmoothDual.quadratic L z ≤ _
  rw [zero_add, hi]
  linarith

lemma field_tail_zero {m : ℕ} (L G b τ : ℝ) (hL : 0 < L) (hG : 0 < G)
    (hb : 0 ≤ b) (hsep : G / L + 2 * τ < b) (x : EuclideanSpace ℝ (Fin m))
    (j l : Fin m) (hjl : j < l) (hxj : -τ ≤ x j) (hxl : x l ≤ τ) :
    field L G b x l = 0 := by
  have hu := maximizer_spec
    (feasible_compact (fun _ : Fin m => G) G (fun _ => hG) hG.le (fun _ => le_rfl))
    ⟨0, feasible_zero _⟩ (GapBoundedSmoothDual.quadratic_continuous L).continuousOn (x + shift m b)
  apply GapBoundedSmoothDual.optimizer_tail_zero L G hL hG _ _ hu.1 hu.2 j l (ne_of_lt hjl)
  have hij : (j.val : ℝ) + 1 ≤ l.val := by exact_mod_cast hjl
  change G / L < x j + (2 * (m : ℝ) - j.val) * b -
    (x l + (2 * (m : ℝ) - l.val) * b)
  nlinarith

lemma objective_hasGradientAt {m : ℕ} (L G b : ℝ) (hL : 0 < L) (hG : 0 < G)
    (x : EuclideanSpace ℝ (Fin m)) : HasGradientAt (objective L G b) (field L G b x) x := by
  have hh := GapBoundedSmoothDual.value_gradient L G hL hG (x + shift m b)
  rw [hasGradientAt_iff_hasFDerivAt]
  have ht := hh.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (shift m b))
  convert ht using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_id, field]

lemma field_lipschitz {m : ℕ} (L G b : ℝ) (hL : 0 < L) (hG : 0 < G)
    (x y : EuclideanSpace ℝ (Fin m)) : ‖field L G b x - field L G b y‖ ≤ L * ‖x - y‖ := by
  have hh := (GapBoundedSmoothDual.field_lipschitz (m := m) L G hL hG).dist_le_mul
    (x + shift m b) (y + shift m b)
  change ‖field L G b x - field L G b y‖ ≤ L * ‖(x + shift m b) - (y + shift m b)‖ at hh
  simpa only [add_sub_add_right_eq_sub] using hh

lemma field_bounded {m : ℕ} (L G b : ℝ) (hG : 0 < G)
    (x : EuclideanSpace ℝ (Fin m)) : ‖field L G b x‖ ≤ G := by
  exact feasible_norm_bound (fun _ => G) G (fun _ => hG) hG.le (fun _ => le_rfl) _
    (maximizer_spec
      (feasible_compact (fun _ : Fin m => G) G (fun _ => hG) hG.le (fun _ => le_rfl))
      ⟨0, feasible_zero _⟩ (GapBoundedSmoothDual.quadratic_continuous L).continuousOn _).1

lemma objective_convex {m : ℕ} (L G b : ℝ) (hG : 0 < G) :
    ConvexOn ℝ univ (objective (m := m) L G b) := by
  have hc := value_convex
    (feasible_compact (fun _ : Fin m => G) G (fun _ => hG) hG.le (fun _ => le_rfl))
    ⟨0, feasible_zero _⟩ (GapBoundedSmoothDual.quadratic_continuous L).continuousOn
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c ha hc' hac
  have hh := hc.2 (mem_univ (x + shift m b)) (mem_univ (y + shift m b)) ha hc' hac
  have he : a • (x + shift m b) + c • (y + shift m b) =
      (a • x + c • y) + shift m b := by
    calc
      _ = (a • x + c • y) + (a + c) • shift m b := by simp only [smul_add, add_smul]; abel
      _ = _ := by rw [hac, one_smul]
  rw [he] at hh
  exact hh

lemma shift_norm {m : ℕ} (b : ℝ) (hb : 0 ≤ b) :
    ‖shift m b‖ ≤ Real.sqrt m * (2 * (m : ℝ) * b) := by
  apply GeneralizedSmoothHardChainRadius.norm_bound_of_coordinate_bound _ _ (by positivity)
  intro i
  have hh := shift_bounds b hb i
  exact abs_le.mpr ⟨(by nlinarith [Nat.cast_nonneg m (α := ℝ)]), hh.2⟩

end LongTails.Proofs.GapBoundedSmoothChain
