import LongTails.Proofs.GeneralizedSmoothHardTransfer
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.GapBoundedSmoothDual

open CompactConjugate GeneralizedSmoothHardDual GeneralizedSmoothHardTransfer

noncomputable def quadratic {m : ℕ} (L : ℝ) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ‖z‖ ^ 2 / (2 * L)

lemma quadratic_segment {m : ℕ} (L t : ℝ) (u v : EuclideanSpace ℝ (Fin m)) :
    quadratic L ((1 - t) • u + t • v) =
      (1 - t) * quadratic L u + t * quadratic L v -
        (‖u - v‖ ^ 2 / (2 * L)) * t * (1 - t) := by
  simp only [quadratic, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
    real_inner_comm v u]
  ring

lemma optimizer_growth {m : ℕ} (L G : ℝ) (a u v : EuclideanSpace ℝ (Fin m))
    (hu : u ∈ feasible (fun _ => G)) (hv : v ∈ feasible (fun _ => G))
    (hopt : IsMaxOn (fun z => ⟪a, z⟫ - quadratic L z) (feasible (fun _ => G)) u) :
    ⟪a, v⟫ - quadratic L v + ‖u - v‖ ^ 2 / (2 * L) ≤ ⟪a, u⟫ - quadratic L u := by
  apply maximizer_growth_of_segment
  · intro t ht
    exact (quadratic_segment L t u v).le
  · intro t ht
    exact hopt ((feasible_convex (fun _ => G)) hu hv
      (sub_nonneg.mpr ht.2) ht.1 (by ring))

lemma quadratic_continuous {m : ℕ} (L : ℝ) :
    Continuous (quadratic L : EuclideanSpace ℝ (Fin m) → ℝ) := by
  unfold quadratic
  fun_prop

lemma value_gradient {m : ℕ} (L G : ℝ) (hL : 0 < L) (hG : 0 < G)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (value (feasible (fun _ => G)) (quadratic L))
      (maximizer (feasible (fun _ => G)) (quadratic L) x) x := by
  have hK := feasible_compact (fun _ : Fin m => G) G (fun _ => hG) hG.le (fun _ => le_rfl)
  have hne : (feasible (fun _ : Fin m => G)).Nonempty := ⟨0, feasible_zero _⟩
  have hc : ContinuousOn (quadratic L) (feasible (fun _ : Fin m => G)) :=
    (quadratic_continuous L).continuousOn
  apply value_hasGradientAt hK hne hc L hL
  intro a v hv
  have hu := maximizer_spec hK hne hc a
  exact optimizer_growth L G a _ v hu.1 hv hu.2

lemma field_lipschitz {m : ℕ} (L G : ℝ) (hL : 0 < L) (hG : 0 < G) :
    LipschitzWith ⟨L, hL.le⟩ (maximizer (feasible (fun _ : Fin m => G)) (quadratic L)) := by
  have hK := feasible_compact (fun _ : Fin m => G) G (fun _ => hG) hG.le (fun _ => le_rfl)
  have hne : (feasible (fun _ : Fin m => G)).Nonempty := ⟨0, feasible_zero _⟩
  have hc : ContinuousOn (quadratic L) (feasible (fun _ : Fin m => G)) :=
    (quadratic_continuous L).continuousOn
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hu := maximizer_spec hK hne hc a
  have hv := maximizer_spec hK hne hc b
  have h1 := optimizer_growth L G a _ _ hu.1 hv.1 hu.2
  have h2 := optimizer_growth L G b _ _ hv.1 hu.1 hv.2
  rw [norm_sub_rev (maximizer _ _ b)] at h2
  exact maximizer_distance_bound _ a b _ _ L hL h1 h2

lemma coordinate_bound {m : ℕ} (G : ℝ) (hG : 0 < G)
    (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ feasible (fun _ => G)) (i : Fin m) : z i ≤ G := by
  have hs := feasible_sum_le (fun _ => G) G (fun _ => hG) hG.le (fun _ => le_rfl) z hz
  exact (Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ i)).trans hs

lemma value_nonnegative {m : ℕ} (L G : ℝ) (hG : 0 < G)
    (x : EuclideanSpace ℝ (Fin m)) : 0 ≤ value (feasible (fun _ => G)) (quadratic L) x := by
  have hK := feasible_compact (fun _ : Fin m => G) G (fun _ => hG) hG.le (fun _ => le_rfl)
  have hh := (maximizer_spec hK ⟨0, feasible_zero _⟩ (quadratic_continuous L).continuousOn x).2
    (feasible_zero _)
  change ⟪x, (0 : EuclideanSpace ℝ (Fin m))⟫ - quadratic L 0 ≤ value _ _ x at hh
  simpa [quadratic] using hh

lemma value_zero {m : ℕ} (L G : ℝ) (hL : 0 < L) (hG : 0 < G)
    (x : EuclideanSpace ℝ (Fin m)) (hx : ∀ i, x i ≤ 0) :
    value (feasible (fun _ => G)) (quadratic L) x = 0 := by
  apply le_antisymm _ (value_nonnegative L G hG x)
  have hK := feasible_compact (fun _ : Fin m => G) G (fun _ => hG) hG.le (fun _ => le_rfl)
  let z := maximizer (feasible (fun _ => G)) (quadratic L) x
  have hz : z ∈ feasible (fun _ => G) :=
    (maximizer_spec hK ⟨0, feasible_zero _⟩ (quadratic_continuous L).continuousOn x).1
  have hi : ⟪x, z⟫ ≤ 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_nonpos
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (hz.1 i) (hx i)
  have hd : 0 ≤ quadratic L z := by unfold quadratic; positivity
  change ⟪x, z⟫ - quadratic L z ≤ 0
  linarith

lemma quadratic_line_derivative {m : ℕ} (L : ℝ)
    (z w : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => quadratic L (z + t • w)) (⟪z, w⟫ / L) 0 := by
  have hc : HasDerivAt (fun t : ℝ => z + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
  convert hc.norm_sq.div_const (2 * L) using 1
  · simp [quadratic]
  · simp
    ring

lemma optimizer_tail_zero {m : ℕ} (L G : ℝ) (hL : 0 < L) (hG : 0 < G)
    (a z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ feasible (fun _ => G))
    (hopt : IsMaxOn (fun v => ⟪a, v⟫ - quadratic L v) (feasible (fun _ => G)) z)
    (j l : Fin m) (hjl : j ≠ l) (hgap : G / L < a j - a l) : z l = 0 := by
  apply le_antisymm _ (hz.1 l)
  by_contra hh
  have hzl : 0 < z l := lt_of_not_ge hh
  let w := transfer (fun _ => G) j l
  have hi : HasDerivAt (fun t : ℝ => ⟪a, z + t • w⟫) ⟪a, w⟫ 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const ⟪a, w⟫).const_add ⟪a, z⟫ using 1
    · ext t
      simp only [inner_add_right, real_inner_smul_right, id_eq]
    · simp
  have hh := derivative_nonpositive_of_right_max _ _ (z l / G) (div_pos hzl hG)
    (hi.sub (quadratic_line_derivative L z w)) (fun t ht => by
      have ho := hopt (transfer_feasible (fun _ => G) (fun _ => hG) j l hjl z hz t ht)
      change ⟪a, z + t • w⟫ - quadratic L (z + t • w) ≤ ⟪a, z⟫ - quadratic L z at ho
      simpa only [Pi.sub_apply, zero_smul, add_zero] using ho)
  change ⟪a, transfer (fun _ => G) j l⟫ -
    ⟪z, transfer (fun _ => G) j l⟫ / L ≤ 0 at hh
  rw [transfer_inner, transfer_inner] at hh
  have hc := coordinate_bound G hG z hz j
  have hb : G * z j - G * z l ≤ G * G := by nlinarith [hz.1 l]
  have hd := div_le_div_of_nonneg_right hb hL.le
  have hg := mul_lt_mul_of_pos_left hgap hG
  have he : G * (G / L) = G * G / L := by ring
  rw [he] at hg
  nlinarith only [hh, hd, hg]

end LongTails.Proofs.GapBoundedSmoothDual
