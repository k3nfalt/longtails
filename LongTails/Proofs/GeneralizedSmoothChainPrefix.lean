import LongTails.Proofs.GeneralizedSmoothCoordinateEmbedding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GeneralizedSmoothChainPrefix

open FiniteSumNondualLowerComponents GeneralizedSmoothCoordinateEmbedding GeneralizedSmoothSmoothedChain

noncomputable def truncate {m : ℕ} (r : ℕ) (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => if i.val ≤ r then x i else 0)

lemma truncate_prefix {d m : ℕ} (π ρ : Fin m ↪ Fin d) (r : ℕ)
    (h : ∀ i, i.val ≤ r → π i = ρ i) (x : EuclideanSpace ℝ (Fin d)) :
    truncate r (coordinateMap π x) = truncate r (coordinateMap ρ x) := by
  ext i
  by_cases hi : i.val ≤ r
  · simp [truncate, coordinateMap, hi, h i hi]
  · simp [truncate, hi]

lemma adjoint_truncate_prefix {d m : ℕ} (π ρ : Fin m ↪ Fin d) (r : ℕ)
    (h : ∀ i, i.val ≤ r → π i = ρ i) (z : EuclideanSpace ℝ (Fin m)) :
    (coordinateMap π).adjoint (truncate r z) = (coordinateMap ρ).adjoint (truncate r z) := by
  apply adjoint_prefix_eq π ρ (r + 1) _ (fun i hi => h i (by omega))
  intro i hi
  simp [truncate, show ¬ i.val ≤ r by omega]

lemma truncate_eq_self {m : ℕ} (r : ℕ) (z : EuclideanSpace ℝ (Fin m))
    (hz : ∀ i, r < i.val → z i = 0) : truncate r z = z := by
  ext i
  by_cases hi : i.val ≤ r
  · simp [truncate, hi]
  · simp [truncate, hi, hz i (by omega)]

lemma truncated_objective_eq {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (h0 : 0 < L₀) (h1 : 0 < L₁) (hε : 0 < ε)
    (hδ : φ.rOut ≤ 1 / (16 * L₁ * Real.sqrt m)) (r : Fin m)
    (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, r ≤ i → |x i| ≤ 1 / (16 * L₁ * Real.sqrt m)) :
    smoothObjective φ L₀ L₁ ε (truncate r.val x) = smoothObjective φ L₀ L₁ ε x := by
  symm
  apply smoothObjective_prefix_eq hm φ L₀ L₁ ε h0 h1 hε hδ r x (truncate r.val x)
  · intro i hi
    simp only [truncate, WithLp.ofLp_toLp, show i.val ≤ r.val from hi, ↓reduceIte]
  · exact (abs_le.mp (hx r le_rfl)).1
  · intro i hi
    exact (abs_le.mp (hx i hi.le)).2
  · intro i hi
    simp only [truncate, WithLp.ofLp_toLp, show ¬ i.val ≤ r.val from by omega, ↓reduceIte]
    positivity

lemma truncated_field_eq {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ)
    (h0 : 0 < L₀) (h1 : 0 < L₁) (hε : 0 < ε)
    (hδ : φ.rOut ≤ 1 / (16 * L₁ * Real.sqrt m)) (r : Fin m)
    (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, r ≤ i → |x i| ≤ 1 / (16 * L₁ * Real.sqrt m)) :
    truncate r.val (smoothField φ L₀ L₁ ε (truncate r.val x)) = smoothField φ L₀ L₁ ε x := by
  have he : smoothField φ L₀ L₁ ε x = smoothField φ L₀ L₁ ε (truncate r.val x) := by
    apply smoothField_prefix_eq hm φ L₀ L₁ ε h0 h1 hε hδ r x (truncate r.val x)
    · intro i hi
      simp only [truncate, WithLp.ofLp_toLp, show i.val ≤ r.val from hi, ↓reduceIte]
    · exact (abs_le.mp (hx r le_rfl)).1
    · intro i hi
      exact (abs_le.mp (hx i hi.le)).2
    · intro i hi
      simp only [truncate, WithLp.ofLp_toLp, show ¬ i.val ≤ r.val from by omega, ↓reduceIte]
      positivity
  rw [← he]
  apply truncate_eq_self
  intro i hi
  exact smoothField_tail_zero hm φ L₀ L₁ ε h0 h1 hε hδ r i hi x
    (abs_le.mp (hx r le_rfl)).1 (abs_le.mp (hx i (by omega))).2

end LongTails.Proofs.GeneralizedSmoothChainPrefix
