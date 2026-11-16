import LongTails.Proofs.QuasarHardChain
import LongTails.Proofs.FiniteSumNondualLowerSimulation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.QuasarHardInstance

open QuasarHardProfiles QuasarHardChain FiniteSumNondualLowerGeometry
open FiniteSumNondualLowerComponents FiniteSumNondualLowerSimulation

variable {d k : ℕ}

noncomputable def chainSeq (a : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) : ℕ → ℝ :=
  fun i => if h : i < k + 1 then z (π ⟨i, h⟩) / a else 0

lemma chainSeq_apply (a : ℝ) (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d))
    (i : Fin (k + 1)) : chainSeq a π z i = z (π i) / a := by
  simp [chainSeq, i.isLt]

noncomputable def bumpPart (μ a : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  μ * ∑ i : Fin (k + 1), bump (z (π i) / a)

noncomputable def bumpField (μ a : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ i : Fin (k + 1), (μ / a * bumpSlope (z (π i) / a)) • EuclideanSpace.single (π i) (1 : ℝ)

lemma bumpField_apply (μ a : ℝ) (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d))
    (i : Fin (k + 1)) : bumpField μ a π z (π i) = μ / a * bumpSlope (z (π i) / a) := by
  classical
  unfold bumpField
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [π.injective.ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma inner_bumpField (μ a : ℝ) (π : Fin (k + 1) ↪ Fin d) (z v : EuclideanSpace ℝ (Fin d)) :
    ⟪bumpField μ a π z, v⟫ = ∑ i : Fin (k + 1), μ / a * bumpSlope (z (π i) / a) * v (π i) := by
  unfold bumpField
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_left, EuclideanSpace.inner_single_left]
  simp

lemma bumpPart_hasGradientAt (μ a : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (bumpPart μ a π) (bumpField μ a π z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hproj (i : Fin (k + 1)) (v : EuclideanSpace ℝ (Fin d)) :
      (EuclideanSpace.proj (π i) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) v = v (π i) := rfl
  have hterm (i : Fin (k + 1)) : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => bump (w (π i) / a))
      ((bumpSlope (z (π i) / a) / a) • (EuclideanSpace.proj (π i) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) z := by
    have hp : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => w (π i) / a)
        ((1 / a) • (EuclideanSpace.proj (π i) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) z := by
      have := (EuclideanSpace.proj (π i) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt (x := z)
      convert this.const_smul (1 / a) using 1
      funext w
      simp only [Pi.smul_apply, hproj, smul_eq_mul]
      ring
    have hc := (bump_hasDerivAt (z (π i) / a)).comp_hasFDerivAt z hp
    refine hc.congr_fderiv ?_
    rw [smul_smul]
    congr 1
    ring
  have hs := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)
  have hm := hs.const_mul μ
  convert hm using 1
  · funext w
    simp only [bumpPart, Finset.sum_apply]
  · ext v
    rw [InnerProductSpace.toDual_apply_apply, inner_bumpField]
    simp only [smul_apply, sum_apply, smul_eq_mul, hproj]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma bumpField_lipschitz (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 < a) (π : Fin (k + 1) ↪ Fin d)
    (z w : EuclideanSpace ℝ (Fin d)) :
    ‖bumpField μ a π z - bumpField μ a π w‖ ≤ 600 * μ / a ^ 2 * ‖z - w‖ := by
  classical
  have hsq : ‖bumpField μ a π z - bumpField μ a π w‖ ^ 2 ≤
      (600 * μ / a ^ 2) ^ 2 * ‖z - w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have he : ⟪bumpField μ a π z - bumpField μ a π w, bumpField μ a π z - bumpField μ a π w⟫ =
        ∑ i : Fin (k + 1), (μ / a * (bumpSlope (z (π i) / a) - bumpSlope (w (π i) / a))) ^ 2 := by
      rw [inner_sub_left, inner_bumpField, inner_bumpField, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [PiLp.sub_apply, bumpField_apply]
      ring
    rw [he, EuclideanSpace.real_norm_sq_eq]
    calc _ ≤ ∑ i : Fin (k + 1), (600 * μ / a ^ 2) ^ 2 * (z (π i) - w (π i)) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hl := bumpSlope_lipschitz (z (π i) / a) (w (π i) / a)
          have hdiv : z (π i) / a - w (π i) / a = (z (π i) - w (π i)) / a := by ring
          rw [hdiv, abs_div, abs_of_pos ha] at hl
          have h1 : |μ / a * (bumpSlope (z (π i) / a) - bumpSlope (w (π i) / a))| ≤
              600 * μ / a ^ 2 * |z (π i) - w (π i)| := by
            rw [abs_mul, abs_of_nonneg (div_nonneg hμ ha.le)]
            calc _ ≤ μ / a * (600 * (|z (π i) - w (π i)| / a)) :=
                  mul_le_mul_of_nonneg_left hl (div_nonneg hμ ha.le)
              _ = _ := by field_simp
          have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          rw [sq_abs, mul_pow (600 * μ / a ^ 2) |z (π i) - w (π i)| 2, sq_abs] at h2
          exact h2
      _ = (600 * μ / a ^ 2) ^ 2 * ∑ i : Fin (k + 1), (z (π i) - w (π i)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (600 * μ / a ^ 2) ^ 2 * ∑ m : Fin d, (z - w) m ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          calc (∑ i : Fin (k + 1), (z (π i) - w (π i)) ^ 2) =
              ∑ m ∈ Finset.univ.map π, (z - w) m ^ 2 := by simp
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun _ _ _ => sq_nonneg _)
  have hc : 0 ≤ 600 * μ / a ^ 2 * ‖z - w‖ := by positivity
  nlinarith [norm_nonneg (bumpField μ a π z - bumpField μ a π w)]

lemma bumpPart_nonneg (μ a : ℝ) (hμ : 0 ≤ μ) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) : 0 ≤ bumpPart μ a π z :=
  mul_nonneg hμ (Finset.sum_nonneg (fun _ _ => bump_nonneg _))

lemma bumpPart_hiddenPoint (μ a : ℝ) (ha : a ≠ 0) (π : Fin (k + 1) ↪ Fin d) :
    bumpPart μ a π (hiddenPoint π a) = 0 := by
  simp [bumpPart, hiddenPoint_apply, div_self ha, bump_one]

lemma chainSeq_castSucc (a : ℝ) (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d))
    (j : Fin k) : chainSeq a π z (j : ℕ) = z (π j.castSucc) / a := by
  simpa using chainSeq_apply a π z j.castSucc

lemma chainSeq_succ (a : ℝ) (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d))
    (j : Fin k) : chainSeq a π z ((j : ℕ) + 1) = z (π j.succ) / a := by
  simpa using chainSeq_apply a π z j.succ

lemma chainSeq_zero (a : ℝ) (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    chainSeq a π z 0 = z (π 0) / a := by
  simpa using chainSeq_apply a π z 0

lemma bumpPart_eq (μ a : ℝ) (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    bumpPart μ a π z = μ * bumpSum (chainSeq a π z) k := by
  unfold bumpPart bumpSum
  rw [← Fin.sum_univ_eq_sum_range (fun i => bump (chainSeq a π z i)) (k + 1)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [chainSeq_apply]

lemma inner_bumpField_eq (μ a : ℝ) (ha : a ≠ 0) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) :
    ⟪bumpField μ a π z, z - hiddenPoint π a⟫ = μ * bumpPairing (chainSeq a π z) k := by
  rw [inner_bumpField]
  unfold bumpPairing
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => (chainSeq a π z i - 1) * bumpSlope (chainSeq a π z i)) (k + 1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [chainSeq_apply, PiLp.sub_apply, hiddenPoint_apply]
  field_simp

lemma max_scale (a u : ℝ) (ha : 0 < a) : max (a * u) 0 = a * max u 0 := by
  rcases le_total u 0 with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]; ring
  · rw [max_eq_left h, max_eq_left (by nlinarith)]

lemma deadZone_scale (a η t : ℝ) (ha : 0 < a) :
    deadZone (a * η) (a * t) = a * deadZone η t := by
  simp only [deadZone, abs_mul, abs_of_pos ha]
  rw [show a * |t| - a * η = a * (|t| - η) by ring, max_scale a _ ha]

lemma softThreshold_scale (a η t : ℝ) (ha : 0 < a) :
    softThreshold (a * η) (a * t) = a * softThreshold η t := by
  simp only [softThreshold]
  rw [show a * t - a * η = a * (t - η) by ring, show -(a * t) - a * η = a * (-t - η) by ring,
    max_scale a _ ha, max_scale a _ ha]
  ring

lemma chain_value_eq (L a η : ℝ) (ha : 0 < a) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) :
    hardComponent L (a * η) a π (fun _ => (0 : Fin 1)) 0 z =
      L * a ^ 2 / 2 * chainValue η (chainSeq a π z) k := by
  have hs := hardComponent_sum L (a * η) a π (fun _ => (0 : Fin 1)) z
  simp only [Fin.sum_univ_one] at hs
  rw [hs]
  unfold chainValue linkEnergy
  have hz : z (π 0) - a = a * (chainSeq a π z 0 - 1) := by
    rw [chainSeq_zero]
    field_simp
  have hl : (∑ j : Fin k, deadZone (a * η) (z (π j.castSucc) - z (π j.succ)) ^ 2) =
      a ^ 2 * ∑ j ∈ Finset.range k,
        deadZone η (chainSeq a π z j - chainSeq a π z (j + 1)) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => deadZone η (chainSeq a π z j - chainSeq a π z (j + 1)) ^ 2) k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [chainSeq_castSucc, chainSeq_succ]
    have he : z (π j.castSucc) - z (π j.succ) =
        a * (z (π j.castSucc) / a - z (π j.succ) / a) := by field_simp
    rw [he, deadZone_scale a η _ ha]
    ring
  rw [hz, hl]
  ring

lemma chain_pairing_eq (L a η : ℝ) (ha : 0 < a) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) :
    ⟪hardGradient L (a * η) a π (fun _ => (0 : Fin 1)) 0 z, z - hiddenPoint π a⟫ =
      L * a ^ 2 / 2 * chainPairing η (chainSeq a π z) k := by
  unfold hardGradient
  rw [inner_smul_left, ContinuousLinearMap.adjoint_inner_left, map_sub]
  simp only [RCLike.conj_to_real]
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [separableSlope, RCLike.inner_apply, conj_trivial, PiLp.sub_apply,
    selectedChain_apply_zero, selectedChain_apply_succ, hiddenPoint_apply, sub_self,
    sub_zero, decide_true, maskedSlope, ↓reduceIte, Fin.cases_zero, Fin.cases_succ]
  unfold chainPairing
  have hz : z (π 0) - a = a * (chainSeq a π z 0 - 1) := by
    rw [chainSeq_zero]
    field_simp
  have hsoft0 : softThreshold 0 (z (π 0) - a) = z (π 0) - a := by
    simp only [softThreshold, sub_zero]
    rcases le_total 0 (z (π 0) - a) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hl : (∑ j : Fin k, (z (π j.castSucc) - z (π j.succ)) *
      (2 * softThreshold (a * η) (z (π j.castSucc) - z (π j.succ)))) =
      2 * a ^ 2 * ∑ j ∈ Finset.range k,
        softThreshold η (chainSeq a π z j - chainSeq a π z (j + 1)) *
          (chainSeq a π z j - chainSeq a π z (j + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j =>
      softThreshold η (chainSeq a π z j - chainSeq a π z (j + 1)) *
        (chainSeq a π z j - chainSeq a π z (j + 1))) k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [chainSeq_castSucc, chainSeq_succ]
    have he : z (π j.castSucc) - z (π j.succ) =
        a * (z (π j.castSucc) / a - z (π j.succ) / a) := by field_simp
    rw [he, softThreshold_scale a η _ ha]
    ring
  rw [hsoft0, hl, hz]
  ring

noncomputable def hardObjective (L a η μ : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  hardComponent L (a * η) a π (fun _ => (0 : Fin 1)) 0 z + bumpPart μ a π z

noncomputable def hardField (L a η μ : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  hardGradient L (a * η) a π (fun _ => (0 : Fin 1)) 0 z + bumpField μ a π z

lemma hardObjective_gradient (L a η μ : ℝ) (ha : 0 < a) (hη : 0 ≤ η)
    (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (hardObjective L a η μ π) (hardField L a η μ π z) z := by
  have h1 := hardComponent_gradient L (a * η) a (mul_nonneg ha.le hη) π
    (fun _ => (0 : Fin 1)) 0 z
  have h2 := bumpPart_hasGradientAt μ a π z
  rw [hasGradientAt_iff_hasFDerivAt] at h1 h2 ⊢
  unfold hardField
  rw [map_add]
  exact h1.add h2

lemma hardField_lipschitz (L a η μ : ℝ) (hL : 0 ≤ L) (ha : 0 < a) (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (π : Fin (k + 1) ↪ Fin d) (z w : EuclideanSpace ℝ (Fin d)) :
    ‖hardField L a η μ π z - hardField L a η μ π w‖ ≤ (L + 600 * μ / a ^ 2) * ‖z - w‖ := by
  have h1 := hardGradient_lipschitz L (a * η) a hL (mul_nonneg ha.le hη) π
    (fun _ => (0 : Fin 1)) 0 z w
  have h2 := bumpField_lipschitz μ a hμ ha π z w
  unfold hardField
  calc _ = ‖(hardGradient L (a * η) a π (fun _ => (0 : Fin 1)) 0 z -
        hardGradient L (a * η) a π (fun _ => (0 : Fin 1)) 0 w) +
        (bumpField μ a π z - bumpField μ a π w)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by nlinarith

lemma hardObjective_nonneg (L a η μ : ℝ) (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    0 ≤ hardObjective L a η μ π z :=
  add_nonneg (hardComponent_nonneg L _ a hL π _ 0 z) (bumpPart_nonneg μ a hμ π z)

lemma hardObjective_hiddenPoint (L a η μ : ℝ) (ha : 0 < a) (hη : 0 ≤ η)
    (π : Fin (k + 1) ↪ Fin d) : hardObjective L a η μ π (hiddenPoint π a) = 0 := by
  unfold hardObjective
  rw [hardComponent_hiddenPoint L _ a (mul_nonneg ha.le hη) π _ 0,
    bumpPart_hiddenPoint μ a ha.ne' π, add_zero]

lemma hardObjective_eq (L a η μ : ℝ) (ha : 0 < a) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) :
    hardObjective L a η μ π z = L * a ^ 2 / 2 * chainValue η (chainSeq a π z) k +
      μ * bumpSum (chainSeq a π z) k := by
  unfold hardObjective
  rw [chain_value_eq L a η ha π z, bumpPart_eq]

lemma hardField_pairing (L a η μ : ℝ) (ha : 0 < a) (π : Fin (k + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) :
    ⟪hardField L a η μ π z, z - hiddenPoint π a⟫ =
      L * a ^ 2 / 2 * chainPairing η (chainSeq a π z) k +
        μ * bumpPairing (chainSeq a π z) k := by
  unfold hardField
  rw [inner_add_left, chain_pairing_eq L a η ha π z, inner_bumpField_eq μ a ha.ne' π z]

lemma hardObjective_quasar (L a η s γ : ℝ) (hL : 0 ≤ L) (ha : 0 < a) (hη : 0 ≤ η)
    (hηk : ((k : ℝ) + 1) * η ≤ 1 / 100) (hs : 0 < s) (hs1 : s ≤ 1 / 100)
    (hT : 1 ≤ ((k : ℝ) + 1) * s) (hγ : γ = 1 / (100 * (((k : ℝ) + 1) * s)))
    (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    γ * hardObjective L a η (s ^ 2 * (L * a ^ 2 / 2)) π z ≤
      ⟪hardField L a η (s ^ 2 * (L * a ^ 2 / 2)) π z, z - hiddenPoint π a⟫ := by
  rw [hardObjective_eq L a η _ ha π z, hardField_pairing L a η _ ha π z]
  have hq := quasar_normalized η s (chainSeq a π z) k hη hηk hs hs1 hT
  have hg : γ * (chainValue η (chainSeq a π z) k + s ^ 2 * bumpSum (chainSeq a π z) k) ≤
      chainPairing η (chainSeq a π z) k + s ^ 2 * bumpPairing (chainSeq a π z) k := by
    rw [hγ, one_div, inv_mul_eq_div]
    exact hq
  have hc : 0 ≤ L * a ^ 2 / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hg hc
  calc _ = L * a ^ 2 / 2 * (γ * (chainValue η (chainSeq a π z) k +
        s ^ 2 * bumpSum (chainSeq a π z) k)) := by ring
    _ ≤ L * a ^ 2 / 2 * (chainPairing η (chainSeq a π z) k +
        s ^ 2 * bumpPairing (chainSeq a π z) k) := this
    _ = _ := by ring

lemma hardObjective_convex_quasar (L a η γ : ℝ) (hL : 0 ≤ L) (ha : 0 < a) (hη : 0 ≤ η)
    (hγ1 : γ ≤ 1) (π : Fin (k + 1) ↪ Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    γ * hardObjective L a η 0 π z ≤ ⟪hardField L a η 0 π z, z - hiddenPoint π a⟫ := by
  rw [hardObjective_eq L a η _ ha π z, hardField_pairing L a η _ ha π z]
  have hq := convex_normalized η (chainSeq a π z) k hη
  have hv := chainValue_nonneg η (chainSeq a π z) k
  have hc : 0 ≤ L * a ^ 2 / 2 := by positivity
  simp only [zero_mul, add_zero]
  nlinarith [mul_le_mul_of_nonneg_left hq hc, mul_nonneg hc hv]

noncomputable def partialBumpField (μ a : ℝ) (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ i : Fin (k + 1), (if i.val ≤ r then μ / a * bumpSlope (z (π i) / a) else 0) •
    EuclideanSpace.single (π i) (1 : ℝ)

lemma partialBumpField_eq (μ a : ℝ) (ha : 0 < a) (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (z : EuclideanSpace ℝ (Fin d)) (h : ∀ i : Fin (k + 1), r < i.val → |z (π i)| ≤ a / 20) :
    partialBumpField μ a π r z = bumpField μ a π z := by
  unfold partialBumpField bumpField
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ≤ r
  · simp [hi]
  · have hb : |z (π i) / a| ≤ 1 / 20 := by
      rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
      linarith [h i (by omega)]
    simp [hi, bump_flat_slope hb]

lemma partialBumpField_prefix (μ a : ℝ) (π π' : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (hπ : ∀ j : Fin (k + 1), j.val ≤ r → π j = π' j) (z : EuclideanSpace ℝ (Fin d)) :
    partialBumpField μ a π r z = partialBumpField μ a π' r z := by
  unfold partialBumpField
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ≤ r
  · rw [hπ i hi]
  · simp [hi]

noncomputable def partialHardField (L a η μ : ℝ) (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  partialGradient L (a * η) a π (fun _ => (0 : Fin 1)) 0 r z + partialBumpField μ a π r z

lemma partialHardField_prefix (L a η μ : ℝ) (π π' : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (hπ : ∀ j : Fin (k + 1), j.val ≤ r → π j = π' j) (z : EuclideanSpace ℝ (Fin d)) :
    partialHardField L a η μ π r z = partialHardField L a η μ π' r z := by
  unfold partialHardField
  rw [partialGradient_prefix L (a * η) a π π' (fun _ => (0 : Fin 1)) (fun _ => (0 : Fin 1)) 0 r z
    hπ (fun _ _ => rfl), partialBumpField_prefix μ a π π' r hπ z]

lemma partialHardField_eq (L a η μ : ℝ) (ha : 0 < a) (hη : 0 ≤ η) (hη1 : η ≤ 1 / 5)
    (π : Fin (k + 1) ↪ Fin d) (r : ℕ) (z : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin (k + 1), r ≤ j.val → |z (π j)| ≤ a * η / 4) :
    partialHardField L a η μ π r z = hardField L a η μ π z := by
  unfold partialHardField hardField
  congr 1
  · apply partialGradient_eq
    intro j hj _
    have h₁ := h j.castSucc (by simp only [Fin.val_succ, Fin.val_castSucc] at *; omega)
    have h₂ := h j.succ hj.le
    have ht := abs_sub (z (π j.castSucc)) (z (π j.succ))
    have : 0 ≤ a * η := mul_nonneg ha.le hη
    linarith
  · apply partialBumpField_eq μ a ha π r z
    intro i hi
    have := h i hi.le
    nlinarith

end LongTails.Proofs.QuasarHardInstance
