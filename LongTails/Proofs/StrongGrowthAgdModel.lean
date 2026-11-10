import LongTails.Proofs.StrongGrowthAgdLmi
import LongTails.Proofs.AdaptiveSilverSplit

namespace LongTails.Proofs.StrongGrowthAgdModel

open scoped RealInnerProductSpace
open LongTails.Proofs.StrongGrowthAgdLmi LongTails.Proofs.AdaptiveSilverSplit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

section Model

variable (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E) (x0 g0 : E) (f0 η θ : ℝ)

noncomputable def gmodel (x : E) : ℝ := f0 + ⟪g0, x - x0⟫ + ⟪H (x - x0), x - x0⟫ / 2

noncomputable def gradModel (x : E) : E := g0 + H (x - x0)

noncomputable def cj (j : ι) : ℝ := if η * eig j < -θ then 3 / 5 else 2 / 5

noncomputable def Phi (x d : E) : ℝ :=
  gmodel H x0 g0 f0 x + ∑ j, cj eig η θ j * ⟪b j, gradModel H x0 g0 x⟫ * ⟪b j, d⟫ + ‖d‖ ^ 2 / (2 * η)

noncomputable def Mvec (x d : E) : E :=
  ∑ j, (η * (1 + cj eig η θ j) * ((⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫) +
      eig j * ((1 - θ) * (1 - η * eig j) * ⟪b j, d⟫ - η * (⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫))) +
    (1 + cj eig η θ j * (η * eig j)) *
      ((1 - θ) * (1 - η * eig j) * ⟪b j, d⟫ - η * (⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫))) • b j

variable {b eig H}

lemma coord_sum_basis (M : ι → ℝ) (j : ι) : ⟪b j, ∑ i, M i • b i⟫ = M j := by
  classical
  rw [inner_sum]
  simp_rw [inner_smul_right, b.inner_eq_ite]
  simp

lemma gradModel_coord (hH : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫) (x : E) (j : ι) :
    ⟪b j, gradModel H x0 g0 x⟫ = ⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫ := by
  simp only [gradModel, inner_add_right, hH]

lemma gmodel_coords (hH : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫) (x : E) :
    gmodel H x0 g0 f0 x = f0 + ∑ j, (⟪b j, g0⟫ * ⟪b j, x - x0⟫ + eig j * ⟪b j, x - x0⟫ ^ 2 / 2) := by
  unfold gmodel
  rw [inner_coords b g0 (x - x0), inner_coords b (H (x - x0)) (x - x0)]
  have h2 : (∑ i, ⟪b i, H (x - x0)⟫ * ⟪b i, x - x0⟫) / 2 = ∑ i, eig i * ⟪b i, x - x0⟫ ^ 2 / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by rw [hH]; ring)
  rw [h2, add_assoc, ← Finset.sum_add_distrib]

lemma Phi_coords (hH : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫) (x d : E) :
    Phi b eig H x0 g0 f0 η θ x d =
      f0 + ∑ j, Q η (eig j) ⟪b j, g0⟫ (cj eig η θ j) ⟪b j, x - x0⟫ ⟪b j, d⟫ := by
  unfold Phi
  rw [gmodel_coords x0 g0 f0 hH, norm_sq_coords b d]
  have h2 : (∑ i, ⟪b i, d⟫ ^ 2) / (2 * η) = ∑ i, ⟪b i, d⟫ ^ 2 / (2 * η) := Finset.sum_div _ _ _
  rw [h2, add_assoc, add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [gradModel_coord x0 g0 hH]
  unfold Q
  ring

lemma Phi_start : Phi b eig H x0 g0 f0 η θ x0 0 = f0 := by
  simp [Phi, gmodel]

theorem Phi_step (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (hH : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (heig : ∀ j, -1 / 8 ≤ η * eig j ∧ η * eig j ≤ 1 / 8) (x d δ e : E) :
    let y := x + (1 - θ) • d
    let ghat := gradModel H x0 g0 y + δ + e
    let x' := y - η • ghat
    let d' := x' - x
    Phi b eig H x0 g0 f0 η θ x' d' ≤ Phi b eig H x0 g0 f0 η θ x d - θ / η / 16 * ‖d'‖ ^ 2 -
      9 / 50 * η * ‖ghat‖ ^ 2 - 1 / 25 * η * ‖gradModel H x0 g0 y‖ ^ 2 -
      ⟪Mvec b eig x0 g0 η θ x d, e⟫ + (58 / 25 * (η / θ) + 791 / 100 * η) * ‖δ‖ ^ 2 +
      279 / 100 * η * ‖e‖ ^ 2 := by
  intro y ghat x' d'
  rw [Phi_coords x0 g0 f0 η θ hH, Phi_coords x0 g0 f0 η θ hH, norm_sq_coords b d', norm_sq_coords b ghat,
    norm_sq_coords b (gradModel H x0 g0 y), norm_sq_coords b δ, norm_sq_coords b e,
    inner_coords b (Mvec b eig x0 g0 η θ x d) e]
  suffices key : ∀ j ∈ (Finset.univ : Finset ι),
      Q η (eig j) ⟪b j, g0⟫ (cj eig η θ j) ⟪b j, x' - x0⟫ ⟪b j, d'⟫ ≤
        Q η (eig j) ⟪b j, g0⟫ (cj eig η θ j) ⟪b j, x - x0⟫ ⟪b j, d⟫ - θ / η / 16 * ⟪b j, d'⟫ ^ 2 -
          9 / 50 * η * ⟪b j, ghat⟫ ^ 2 - 1 / 25 * η * ⟪b j, gradModel H x0 g0 y⟫ ^ 2 -
          ⟪b j, Mvec b eig x0 g0 η θ x d⟫ * ⟪b j, e⟫ +
          (58 / 25 * (η / θ) + 791 / 100 * η) * ⟪b j, δ⟫ ^ 2 + 279 / 100 * η * ⟪b j, e⟫ ^ 2 by
    have hs := Finset.sum_le_sum key
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    linarith
  intro j _
  have hd' : ⟪b j, d'⟫ = (1 - θ) * ⟪b j, d⟫ -
      η * ((⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫ + eig j * ((1 - θ) * ⟪b j, d⟫)) + ⟪b j, δ⟫ + ⟪b j, e⟫) := by
    have hy : ⟪b j, y - x0⟫ = ⟪b j, x - x0⟫ + (1 - θ) * ⟪b j, d⟫ := by
      simp only [y]
      rw [show x + (1 - θ) • d - x0 = (x - x0) + (1 - θ) • d by abel, inner_add_right,
        inner_smul_right]
    have hg : ⟪b j, ghat⟫ = (⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫ + eig j * ((1 - θ) * ⟪b j, d⟫)) +
        ⟪b j, δ⟫ + ⟪b j, e⟫ := by
      simp only [ghat, inner_add_right, gradModel_coord x0 g0 hH, hy]
      ring
    simp only [d', x', y]
    rw [show x + (1 - θ) • d - η • ghat - x = (1 - θ) • d - η • ghat by abel, inner_sub_right,
      inner_smul_right, inner_smul_right, hg]
  have hz' : ⟪b j, x' - x0⟫ = ⟪b j, x - x0⟫ + ⟪b j, d'⟫ := by
    simp only [d']
    rw [← inner_add_right]
    congr 1
    abel
  have hgy : ⟪b j, gradModel H x0 g0 y⟫ =
      ⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫ + eig j * ((1 - θ) * ⟪b j, d⟫) := by
    rw [gradModel_coord x0 g0 hH]
    simp only [y]
    rw [show x + (1 - θ) • d - x0 = (x - x0) + (1 - θ) • d by abel, inner_add_right,
      inner_smul_right]
    ring
  have hg : ⟪b j, ghat⟫ = ⟪b j, gradModel H x0 g0 y⟫ + ⟪b j, δ⟫ + ⟪b j, e⟫ := by
    simp only [ghat, inner_add_right]
  have hM : ⟪b j, Mvec b eig x0 g0 η θ x d⟫ = η * (1 + cj eig η θ j) *
      ((⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫) +
        eig j * ((1 - θ) * (1 - η * eig j) * ⟪b j, d⟫ - η * (⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫))) +
      (1 + cj eig η θ j * (η * eig j)) *
        ((1 - θ) * (1 - η * eig j) * ⟪b j, d⟫ - η * (⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫)) := by
    unfold Mvec
    exact coord_sum_basis _ j
  have hlmi : let G := ⟪b j, g0⟫ + eig j * ⟪b j, x - x0⟫
      let dd := (1 - θ) * (1 - η * eig j) * ⟪b j, d⟫ - η * G
      let G' := G + eig j * dd
      (G * dd + eig j / 2 * dd ^ 2) + cj eig η θ j * (G' * dd - G * ⟪b j, d⟫) +
        (dd ^ 2 - ⟪b j, d⟫ ^ 2) / (2 * η) ≤ -(θ / (4 * η)) * dd ^ 2 - η / 2 * G' ^ 2 := by
    unfold cj
    split_ifs with hc
    · exact lyapunov_step_concave hη hθ hθ1 (heig j).1 hc.le
    · exact lyapunov_step_convex hη hθ hθ1 (not_lt.mp hc) (heig j).2
  have hc0 : 0 ≤ cj eig η θ j := by unfold cj; split_ifs <;> norm_num
  have hc1 : cj eig η θ j ≤ 3 / 5 := by unfold cj; split_ifs <;> norm_num
  have key := coord_step_of_lmi (g0 := ⟪b j, g0⟫) (z := ⟪b j, x - x0⟫) (d := ⟪b j, d⟫)
    (δ := ⟪b j, δ⟫) (e := ⟪b j, e⟫) hη hθ hθ1 (heig j).1 (heig j).2 hc0 hc1 hlmi
  simp only at key
  rw [hgy] at hg
  rw [hz', hd', hgy, hg, hM]
  unfold Q at key ⊢
  linear_combination key

lemma gmodel_le_Phi (hη : 0 < η) (_hH : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫) (x d : E) :
    gmodel H x0 g0 f0 x ≤ Phi b eig H x0 g0 f0 η θ x d + 9 / 50 * η * ‖gradModel H x0 g0 x‖ ^ 2 := by
  unfold Phi
  rw [norm_sq_coords b d, norm_sq_coords b (gradModel H x0 g0 x)]
  have h2 : (∑ i, ⟪b i, d⟫ ^ 2) / (2 * η) = ∑ i, ⟪b i, d⟫ ^ 2 / (2 * η) := Finset.sum_div _ _ _
  rw [h2, Finset.mul_sum, add_assoc, add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have : 0 ≤ ∑ j, (cj eig η θ j * ⟪b j, gradModel H x0 g0 x⟫ * ⟪b j, d⟫ + (⟪b j, d⟫ ^ 2 / (2 * η) +
      9 / 50 * η * ⟪b j, gradModel H x0 g0 x⟫ ^ 2)) := by
    apply Finset.sum_nonneg
    intro j _
    have hc0 : 0 ≤ cj eig η θ j := by unfold cj; split_ifs <;> norm_num
    have hc1 : cj eig η θ j ≤ 3 / 5 := by unfold cj; split_ifs <;> norm_num
    set G := ⟪b j, gradModel H x0 g0 x⟫
    set dj := ⟪b j, d⟫
    have hy := young_coef (A := 1 / (2 * η)) (B := η / 2) (x := dj) (y := -(cj eig η θ j * G))
      (by positivity) (by field_simp; norm_num)
    have h2 : η / 2 * (-(cj eig η θ j * G)) ^ 2 ≤ 9 / 50 * η * G ^ 2 := by
      have : (cj eig η θ j) ^ 2 ≤ 9 / 25 := by nlinarith
      nlinarith [mul_nonneg hη.le (sq_nonneg G)]
    have h3 : dj ^ 2 / (2 * η) = 1 / (2 * η) * dj ^ 2 := by ring
    nlinarith
  linarith

end Model

end LongTails.Proofs.StrongGrowthAgdModel
