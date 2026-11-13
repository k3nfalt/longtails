import LongTails.Proofs.GeneralizedSmoothHardDualSegments
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothHardTransfer

open GeneralizedSmoothHardDual GeneralizedSmoothHardDualSegments CompactConjugate

lemma derivative_nonpositive_of_right_max (f : ℝ → ℝ) (d r : ℝ)
    (hr : 0 < r) (hd : HasDerivAt f d 0) (hmax : ∀ t ∈ Icc 0 r, f t ≤ f 0) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hr).filter_mono nhdsWithin_le_nhds] with t ht ht'
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt ht))
    (sub_nonpos.mpr (hmax t ⟨le_of_lt ht, le_of_lt ht'⟩))

noncomputable def transfer {m : ℕ} (G : Fin m → ℝ) (j l : Fin m) : EuclideanSpace ℝ (Fin m) :=
  EuclideanSpace.single j (G j) - EuclideanSpace.single l (G l)

lemma transfer_sum {m : ℕ} (G : Fin m → ℝ) (hG : ∀ i, 0 < G i) (j l : Fin m) :
    ∑ i, transfer G j l i / G i = 0 := by
  simp only [transfer, PiLp.sub_apply, sub_div, Finset.sum_sub_distrib]
  simp [PiLp.single_apply, ite_div, (hG j).ne', (hG l).ne']

lemma transfer_feasible {m : ℕ} (G : Fin m → ℝ) (hG : ∀ i, 0 < G i)
    (j l : Fin m) (hjl : j ≠ l) (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ feasible G)
    (t : ℝ) (ht : t ∈ Icc 0 (z l / G l)) : z + t • transfer G j l ∈ feasible G := by
  constructor
  · intro i
    by_cases hij : i = j
    · subst i
      simpa [transfer, PiLp.single_apply, hjl] using add_nonneg (hz.1 j) (mul_nonneg ht.1 (hG j).le)
    · by_cases hil : i = l
      · subst i
        have hh := (le_div_iff₀ (hG l)).mp ht.2
        simp only [transfer, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, PiLp.single_apply,
          hij, ↓reduceIte, zero_sub, smul_eq_mul]
        linarith
      · simpa [transfer, PiLp.single_apply, hij, hil] using hz.1 i
  · change ∑ i, (z i + t * transfer G j l i) / G i ≤ 1
    simpa only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      transfer_sum G hG j l, mul_zero, add_zero] using hz.2

lemma transfer_inner {m : ℕ} (G : Fin m → ℝ) (j l : Fin m) (a : EuclideanSpace ℝ (Fin m)) :
    ⟪a, transfer G j l⟫ = G j * a j - G l * a l := by
  simp [transfer, inner_sub_right, EuclideanSpace.inner_single_right]

lemma optimizer_transfer_inequality {m : ℕ} (hm : 0 < m) (L₀ L₁ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ) (hG : ∀ i, 0 < G i)
    (j l : Fin m) (hjl : j ≠ l) (a z : EuclideanSpace ℝ (Fin m))
    (hz : z ∈ feasible G) (hzl : 0 < z l)
    (hopt : IsMaxOn (fun v => ⟪a, v⟫ - dual L₀ L₁ v) (feasible G) z) :
    G j * a j - G l * a l ≤ dualSlope L₀ L₁ z (transfer G j l) := by
  let w := transfer G j l
  have hZ : 0 < ∑ i, z i := hzl.trans_le
    (Finset.single_le_sum (fun i _ => hz.1 i) (Finset.mem_univ l))
  have hc (i : Fin m) : HasDerivAt (fun t : ℝ => (z + t • w) i) (w i) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const (w i)).const_add (z i) using 1
    · ext t
      simp
    · simp
  have hd : HasDerivAt (fun t : ℝ => dual L₀ L₁ (z + t • w)) (dualSlope L₀ L₁ z w) 0 := by
    have hh := dual_hasDerivAt hm L₀ L₁ hL₀ hL₁ (fun t => z + t • w) w 0 hc
      (by simpa only [zero_smul, add_zero] using hz.1)
      (by simpa only [zero_smul, add_zero] using hZ)
    simpa only [zero_smul, add_zero] using hh
  have hi : HasDerivAt (fun t : ℝ => ⟪a, z + t • w⟫) ⟪a, w⟫ 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const ⟪a, w⟫).const_add ⟪a, z⟫ using 1
    · ext t
      simp only [inner_add_right, real_inner_smul_right, id_eq]
    · simp
  have hh := derivative_nonpositive_of_right_max _ _ (z l / G l) (div_pos hzl (hG l))
    (hi.sub hd) (fun t ht => by
      have hh := hopt (transfer_feasible G hG j l hjl z hz t ht)
      change ⟪a, z + t • w⟫ - dual L₀ L₁ (z + t • w) ≤ ⟪a, z⟫ - dual L₀ L₁ z at hh
      simpa only [Pi.sub_apply, zero_smul, add_zero] using hh)
  change ⟪a, transfer G j l⟫ - dualSlope L₀ L₁ z (transfer G j l) ≤ 0 at hh
  rw [transfer_inner] at hh
  linarith

noncomputable def slopeCoefficient {m : ℕ} (L₁ : ℝ) (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) : ℝ :=
  4 / L₁ * Real.log (1 + (z i / ∑ j, z j) / (1 / Real.sqrt m))

noncomputable def commonCoefficient {m : ℕ} (L₀ L₁ : ℝ) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  2 * (Real.log (1 + L₁ * (∑ i, z i) / L₀) / L₁) +
    (∑ i, entropy L₁ (1 / Real.sqrt m) (z i / ∑ j, z j)) -
    ∑ i, (z i / ∑ j, z j) * slopeCoefficient L₁ z i

lemma dualSlope_decomposition {m : ℕ} (L₀ L₁ : ℝ) (z w : EuclideanSpace ℝ (Fin m)) :
    dualSlope L₀ L₁ z w = (∑ i, w i) * commonCoefficient L₀ L₁ z +
      ∑ i, w i * slopeCoefficient L₁ z i := by
  unfold dualSlope commonCoefficient slopeCoefficient
  dsimp
  have he (i : Fin m) :
      (∑ j, w j) * entropy L₁ (1 / Real.sqrt m) (z i / ∑ j, z j) +
        (4 / L₁ * Real.log (1 + (z i / ∑ j, z j) / (1 / Real.sqrt m))) *
          (w i - (∑ j, w j) * (z i / ∑ j, z j)) =
      (∑ j, w j) * (entropy L₁ (1 / Real.sqrt m) (z i / ∑ j, z j) -
        (z i / ∑ j, z j) * (4 / L₁ * Real.log (1 + (z i / ∑ j, z j) / (1 / Real.sqrt m)))) +
      w i * (4 / L₁ * Real.log (1 + (z i / ∑ j, z j) / (1 / Real.sqrt m))) := by ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

lemma commonCoefficient_upper {m : ℕ} (hm : 0 < m) (L₀ L₁ B : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (z : EuclideanSpace ℝ (Fin m))
    (hz : ∀ i, 0 ≤ z i) (hZ : 0 < ∑ i, z i) (hB : (∑ i, z i) ≤ B) :
    commonCoefficient L₀ L₁ z ≤ 2 * (Real.log (1 + L₁ * B / L₀) / L₁) := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    entropy_upper L₁ (1 / Real.sqrt m) (z i / ∑ j, z j) hL₁ (by positivity)
      (div_nonneg (hz i) hZ.le))
  have hl : 2 * (Real.log (1 + L₁ * (∑ i, z i) / L₀) / L₁) ≤
      2 * (Real.log (1 + L₁ * B / L₀) / L₁) := by gcongr
  unfold commonCoefficient slopeCoefficient
  linarith

lemma slopeCoefficient_bounds {m : ℕ} (hm : 0 < m) (L₁ : ℝ) (hL₁ : 0 < L₁)
    (z : EuclideanSpace ℝ (Fin m)) (hz : ∀ i, 0 ≤ z i) (hZ : 0 < ∑ i, z i) (i : Fin m) :
    0 ≤ slopeCoefficient L₁ z i ∧
      slopeCoefficient L₁ z i ≤ 4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m)) := by
  have hp : 0 ≤ z i / ∑ j, z j := div_nonneg (hz i) hZ.le
  have hp' : z i / ∑ j, z j ≤ 1 := (div_le_one hZ).mpr
    (Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i))
  unfold slopeCoefficient
  constructor
  · apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    have hc : 0 ≤ (z i / ∑ j, z j) / (1 / Real.sqrt m) := by positivity
    linarith
  · gcongr

lemma feasible_sum_le {m : ℕ} (G : Fin m → ℝ) (B : ℝ)
    (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B)
    (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ feasible G) : (∑ i, z i) ≤ B := by
  have hh (i : Fin m) : z i ≤ B * (z i / G i) := by
    have hm := mul_le_mul_of_nonneg_right (hGB i) (div_nonneg (hz.1 i) (hG i).le)
    simpa only [mul_div_cancel₀ _ (hG i).ne'] using hm
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)
  rw [← Finset.mul_sum] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left hz.2 hB).trans_eq (mul_one B))

lemma dualSlope_transfer {m : ℕ} (L₀ L₁ : ℝ) (G : Fin m → ℝ) (j l : Fin m)
    (z : EuclideanSpace ℝ (Fin m)) :
    dualSlope L₀ L₁ z (transfer G j l) = (G j - G l) * commonCoefficient L₀ L₁ z +
      G j * slopeCoefficient L₁ z j - G l * slopeCoefficient L₁ z l := by
  rw [dualSlope_decomposition]
  simp [transfer, PiLp.sub_apply, Finset.sum_sub_distrib, sub_mul, PiLp.single_apply, ite_mul]
  ring

lemma dualSlope_transfer_upper {m : ℕ} (hm : 0 < m) (L₀ L₁ B : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ) (hG : ∀ i, 0 < G i)
    (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B) (j l : Fin m) (hjl : G l ≤ G j)
    (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ feasible G) (hZ : 0 < ∑ i, z i) :
    dualSlope L₀ L₁ z (transfer G j l) ≤
      (G j - G l) * (2 * (Real.log (1 + L₁ * B / L₀) / L₁)) +
        G j * (4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m))) := by
  have hc := mul_le_mul_of_nonneg_left
    (commonCoefficient_upper hm L₀ L₁ B hL₀ hL₁ z hz.1 hZ (feasible_sum_le G B hG hB hGB z hz))
    (sub_nonneg.mpr hjl)
  have hj := mul_le_mul_of_nonneg_left (slopeCoefficient_bounds hm L₁ hL₁ z hz.1 hZ j).2 (hG j).le
  have hl := mul_nonneg (hG l).le (slopeCoefficient_bounds hm L₁ hL₁ z hz.1 hZ l).1
  rw [dualSlope_transfer]
  linarith

lemma optimizer_coordinate_zero {m : ℕ} (hm : 0 < m) (L₀ L₁ B : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ) (hG : ∀ i, 0 < G i)
    (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B) (j l : Fin m) (hne : j ≠ l) (hjl : G l ≤ G j)
    (a z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ feasible G)
    (hopt : IsMaxOn (fun v => ⟪a, v⟫ - dual L₀ L₁ v) (feasible G) z)
    (hscore : (G j - G l) * (2 * (Real.log (1 + L₁ * B / L₀) / L₁)) +
      G j * (4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m))) < G j * a j - G l * a l) :
    z l = 0 := by
  apply le_antisymm _ (hz.1 l)
  by_contra hh
  have hzl : 0 < z l := lt_of_not_ge hh
  have hZ := hzl.trans_le (Finset.single_le_sum (fun i _ => hz.1 i) (Finset.mem_univ l))
  have hi := optimizer_transfer_inequality hm L₀ L₁ hL₀ hL₁ G hG j l hne a z hz hzl hopt
  have hu := dualSlope_transfer_upper hm L₀ L₁ B hL₀ hL₁ G hG hB hGB j l hjl z hz hZ
  linarith

noncomputable def tailSum {m : ℕ} (G : Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ i, if j ≤ i then G i else 0

lemma tailSum_gap {m : ℕ} (G : Fin m → ℝ) (hG : ∀ i, 0 ≤ G i)
    (j l : Fin m) (hjl : j < l) : G j + tailSum G l ≤ tailSum G j := by
  have hh (i : Fin m) : (if i = j then G j else 0) + (if l ≤ i then G i else 0) ≤
      if j ≤ i then G i else 0 := by
    by_cases hi : i = j
    · subst i
      simp [not_le.mpr hjl]
    · by_cases hl : l ≤ i
      · have hj : j ≤ i := (le_of_lt hjl).trans hl
        simp [hi, hl, hj]
      · simp only [hi, hl, ↓reduceIte, zero_add]
        split
        · exact hG i
        · exact le_rfl
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, tailSum] using hs

noncomputable def shiftCoordinate {m : ℕ} (L₀ L₁ B : ℝ) (G : Fin m → ℝ) (i : Fin m) : ℝ :=
  2 * (Real.log (1 + L₁ * B / L₀) / L₁) + 2 / L₁ +
    (4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m))) / G i * tailSum G i

lemma shifted_score {m : ℕ} (hm : 0 < m) (L₀ L₁ B τ : ℝ) (hL₁ : 0 < L₁)
    (G : Fin m → ℝ) (hG : ∀ i, 0 < G i) (j l : Fin m) (hjl : j < l)
    (yj yl : ℝ) (hyj : -τ ≤ yj) (hyl : yl ≤ τ)
    (hgap : τ * (G j + G l) < 2 * (G j - G l) / L₁) :
    (G j - G l) * (2 * (Real.log (1 + L₁ * B / L₀) / L₁)) +
      G j * (4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m))) <
      G j * (yj + shiftCoordinate L₀ L₁ B G j) - G l * (yl + shiftCoordinate L₀ L₁ B G l) := by
  let C := 4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m))
  have hC : 0 ≤ C := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    have hh : 0 ≤ 1 / (1 / Real.sqrt m) := by positivity
    linarith
  have ht := mul_le_mul_of_nonneg_left (tailSum_gap G (fun i => (hG i).le) j l hjl) hC
  have hyj' := mul_le_mul_of_nonneg_left hyj (hG j).le
  have hyl' := mul_le_mul_of_nonneg_left hyl (hG l).le
  have he (i : Fin m) : G i * shiftCoordinate L₀ L₁ B G i =
      G i * (2 * (Real.log (1 + L₁ * B / L₀) / L₁) + 2 / L₁) + C * tailSum G i := by
    unfold shiftCoordinate C
    field_simp [(hG i).ne']
  rw [mul_add, mul_add, he j, he l]
  dsimp [C] at ht ⊢
  simp only [div_eq_mul_inv] at ht hgap ⊢
  nlinarith only [ht, hyj', hyl', hgap]

noncomputable def shift {m : ℕ} (L₀ L₁ B : ℝ) (G : Fin m → ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (shiftCoordinate L₀ L₁ B G)

lemma shifted_optimizer_tail_zero {m : ℕ} (hm : 0 < m) (L₀ L₁ B τ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ) (hG : ∀ i, 0 < G i)
    (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B) (j l : Fin m) (hjl : j < l) (horder : G l ≤ G j)
    (y z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ feasible G)
    (hopt : IsMaxOn (fun v => ⟪y + shift L₀ L₁ B G, v⟫ - dual L₀ L₁ v) (feasible G) z)
    (hyj : -τ ≤ y j) (hyl : y l ≤ τ)
    (hgap : τ * (G j + G l) < 2 * (G j - G l) / L₁) : z l = 0 := by
  apply optimizer_coordinate_zero hm L₀ L₁ B hL₀ hL₁ G hG hB hGB j l (ne_of_lt hjl)
    horder (y + shift L₀ L₁ B G) z hz hopt
  simpa only [PiLp.add_apply, shift, WithLp.ofLp_toLp] using
    shifted_score hm L₀ L₁ B τ hL₁ G hG j l hjl (y j) (y l) hyj hyl hgap

end LongTails.Proofs.GeneralizedSmoothHardTransfer
