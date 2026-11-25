import LongTails.Proofs.RhoSmoothHardInstance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.RhoSmoothHardOracle

open FiniteSumNondualLowerComponents GeneralizedSmoothCoordinateEmbedding GeneralizedSmoothChainPrefix
open RhoSmoothHardChain RhoSmoothHardSmoothed RhoSmoothHardParameters RhoSmoothHardInstance
open AdaptivePolynomialLocalization
open LongTails.Setups.RhoSmoothConvexFull

section

variable {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
  (A G ρ L₀ L₁ g σ θ : ℝ) (hA : 0 < A) (hG : 0 < G) (hρ : 1 < ρ) (hρ2 : ρ ≤ 2)
  (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hAG : A * (ρ - 1) = 2 * G / L₀) (hGL : G ^ ρ * L₁ = L₀)
  (hg : 0 < g) (hθ : 0 ≤ θ) (hσ : 3 * θ + 2 * A < σ) (hδ : 2 * φ.rOut ≤ θ)

include hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg hθ hσ hδ

lemma truncated_objective_eq (r : Fin m) (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, r ≤ i → |x i| ≤ θ / 2) :
    smoothObjective φ A G ρ g σ (truncate r.val x) = smoothObjective φ A G ρ g σ x := by
  symm
  apply smoothObjective_prefix_eq φ A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg θ hθ hσ hδ r
    x (truncate r.val x)
  · intro i hi
    simp only [truncate, WithLp.ofLp_toLp, show i.val ≤ r.val from hi, ↓reduceIte]
  · exact (abs_le.mp (hx r le_rfl)).1
  · intro i hi
    exact (abs_le.mp (hx i hi.le)).2
  · intro i hi
    simp only [truncate, WithLp.ofLp_toLp, show ¬ i.val ≤ r.val from by omega, ↓reduceIte]
    linarith

lemma truncated_field_eq (r : Fin m) (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, r ≤ i → |x i| ≤ θ / 2) :
    truncate r.val (smoothField φ A G ρ g σ (truncate r.val x)) = smoothField φ A G ρ g σ x := by
  have he : smoothField φ A G ρ g σ x = smoothField φ A G ρ g σ (truncate r.val x) := by
    apply smoothField_prefix_eq φ A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg θ hθ hσ hδ r
      x (truncate r.val x)
    · intro i hi
      simp only [truncate, WithLp.ofLp_toLp, show i.val ≤ r.val from hi, ↓reduceIte]
    · exact (abs_le.mp (hx r le_rfl)).1
    · intro i hi
      exact (abs_le.mp (hx i hi.le)).2
    · intro i hi
      simp only [truncate, WithLp.ofLp_toLp, show ¬ i.val ≤ r.val from by omega, ↓reduceIte]
      linarith
  rw [← he]
  apply truncate_eq_self
  intro i hi
  exact smoothField_tail_zero φ A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg θ hθ hσ hδ r x
    (abs_le.mp (hx r le_rfl)).1 (fun l hl => (abs_le.mp (hx l hl.le)).2) i hi

end

noncomputable def radius (p : Params) : ℝ := 4 * width p

noncomputable def thresh (p : Params) : ℝ := cap p / 2

section

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hmM : m ≤ links p)

noncomputable def partialReply (π : Fin m ↪ Fin p.d) (r : ℕ) (x : EuclideanSpace ℝ (Fin p.d)) :
    EuclideanSpace ℝ (Fin p.d) :=
  if 4 * width p ≤ ‖x‖ then coefficient p m • x else
    let v := (coordinateMap π).adjoint
      (truncate r (smoothField (kernel p hp m) (cap p) (scale p) p.ρ (last p) (6 * cap p)
        (truncate r (coordinateMap π x))))
    v + AdaptivePolynomialHinge.mixing (degree p)
      ((wall (coefficient p m) (width p) x - smoothObjective (kernel p hp m) (cap p) (scale p) p.ρ
        (last p) (6 * cap p) (truncate r (coordinateMap π x))) / (coefficient p m * width p ^ 2)) •
        (coefficient p m • x - v)

include hp

lemma radius_pos : 0 < radius p := by
  have := width_pos p hp
  unfold radius
  positivity

lemma thresh_pos : 0 < thresh p := by
  have := cap_pos p hp
  unfold thresh
  positivity


lemma partialReply_prefix (π ρ : Fin m ↪ Fin p.d) (r : ℕ) (x : EuclideanSpace ℝ (Fin p.d))
    (h : ∀ i, i.val ≤ r → π i = ρ i) :
    partialReply p hp m π r x = partialReply p hp m ρ r x := by
  unfold partialReply
  rw [truncate_prefix π ρ r h x, adjoint_truncate_prefix π ρ r h]

include hmM

lemma partialReply_eq (π : Fin m ↪ Fin p.d) (r : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : ‖x‖ < radius p → ∀ i, r ≤ i → |x (π i)| ≤ thresh p) :
    partialReply p hp m π r.val x = field p hp m hmM π x := by
  obtain ⟨hA, hG, hρ, hρ2, hL₀, hL₁, hAG, hGL, hg⟩ := chain_hyps p hp
  have hδ : 2 * (kernel p hp m).rOut ≤ cap p := kernel_margin p m
  have hσ : 3 * cap p + 2 * cap p < 6 * cap p := by linarith
  unfold partialReply
  split_ifs with hfar
  · exact (field_exterior p hp m hmM π x hfar).symm
  · have hcoords : ∀ i, r ≤ i → |coordinateMap π x i| ≤ cap p / 2 :=
      hx (by unfold radius; linarith [not_le.mp hfar])
    rw [truncated_objective_eq (kernel p hp m) _ _ _ _ _ _ _ _ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg
        hA.le hσ hδ r _ hcoords,
      truncated_field_eq (kernel p hp m) _ _ _ _ _ _ _ _ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg
        hA.le hσ hδ r _ hcoords]
    rfl

lemma objective_near_gap (π : Fin m ↪ Fin p.d) (i : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : |x (π i)| ≤ thresh p) : 3 * p.ε ≤ objective p hp m hmM π x := by
  obtain ⟨hA, hG, hρ, hρ2, hL₀, hL₁, hAG, hGL, hg⟩ := chain_hyps p hp
  have hδ : 2 * (kernel p hp m).rOut ≤ cap p := kernel_margin p m
  have hh := smooth_gap (kernel p hp m) (cap p) (scale p) p.ρ (p.L0 / 512) (p.L1 / 512)
    (last p) (6 * cap p) hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg (cap p) (by linarith) hδ i
    (coordinateMap π x) (by exact (abs_le.mp hx).1)
  have ha := objective_above p hp m hmM π x
  have he : last p * (6 * cap p - cap p - cap p) = 4 * p.ε := by
    unfold last
    field_simp
    ring
  have hε := ε_pos p hp
  change smoothObjective (kernel p hp m) (cap p) (scale p) p.ρ (last p) (6 * cap p)
    (coordinateMap π x) ≤ objective p hp m hmM π x at ha
  linarith

lemma objective_far_gap (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : radius p ≤ ‖x‖) : 3 * p.ε ≤ objective p hp m hmM π x := by
  let a := coefficient p m
  let B := width p
  have ha : 0 < a := coefficient_pos p hp m
  have hB : 0 < B := width_pos p hp
  have hnorm : (4 * B) ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (show 0 ≤ 4 * B by positivity) hx 2
  have hw : 6 * a * B ^ 2 ≤ wall a B x - a * B ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ a / 2 by positivity)
    have hz : 0 ≤ a * B ^ 2 := by positivity
    unfold wall
    nlinarith only [hh, hz]
  have habove := value_above_wall (seed p hp m hmM π).f (degree p) (degree_valid p) a B
    (a * B ^ 2) (by positivity) x
  change wall a B x - a * B ^ 2 ≤ objective p hp m hmM π x at habove
  have hl := far_large p hp m
  linarith

lemma dimension_ok :
    (m : ℝ) + 2 * (m : ℝ) ^ 2 * (radius p ^ 2 / thresh p ^ 2) ≤ p.d := by
  have h := dimension_sufficient p hp m hmM
  unfold radius thresh
  exact h

end

end LongTails.Proofs.RhoSmoothHardOracle
