import LongTails.Proofs.QuantileNoiseLaws
import LongTails.Proofs.QuantileOracleLowerBound

open MeasureTheory

namespace LongTails.Proofs.QuantileShellOracle

noncomputable def atomicMeasure {ι : Type*} [Fintype ι] (w x : ι → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i)

lemma integrable_atomic {ι : Type*} [Fintype ι] (w x : ι → ℝ) (f : ℝ → ℝ) :
    Integrable f (atomicMeasure w x) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma integral_atomic {ι : Type*} [Fintype ι] (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : ℝ → ℝ) : (∫ z, f z ∂atomicMeasure w x) = ∑ i, w i * f (x i) := by
  unfold atomicMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i)]
  rfl

lemma atomic_mass {ι : Type*} [Fintype ι] (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    atomicMeasure w x Set.univ = ENNReal.ofReal (∑ i, w i) := by
  simp only [atomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i)).symm

lemma atomic_probability {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : IsProbabilityMeasure (atomicMeasure w x) := by
  constructor
  rw [atomic_mass w x hw, hs]
  norm_num

open QuantileOracleLowerBound

noncomputable def shellWeights (w a : ℝ) (k : ℕ) (i : Fin 3 × Fin (k + 1)) : ℝ :=
  threeTagWeights w a i.1 / (k + 1)

noncomputable def shellPoints (k : ℕ) (h : ℝ) (i : Fin 3 × Fin (k + 1)) : ℝ :=
  ![0, ((k : ℝ) + i.2.val) * h, -(((k : ℝ) + i.2.val) * h)] i.1

noncomputable def shellLaw (w a : ℝ) (k : ℕ) (h : ℝ) : Measure ℝ :=
  atomicMeasure (shellWeights w a k) (shellPoints k h)

lemma shellWeights_sum (w a : ℝ) (k : ℕ) : ∑ i, shellWeights w a k i = 1 := by
  simp only [shellWeights, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_one]
  simp_rw [mul_div_cancel₀ _ hk]
  exact threeTagWeights_sum w a

lemma shellWeights_pos {w a : ℝ} (hw : 0 < w) (hw1 : w < 1) (ha : |a| ≤ w / 4)
    (k : ℕ) (i : Fin 3 × Fin (k + 1)) : 0 < shellWeights w a k i :=
  div_pos (threeTagWeights_pos hw hw1 ha i.1) (by positivity)

lemma shellLaw_probability {w a : ℝ} (hw : 0 < w) (hw1 : w < 1) (ha : |a| ≤ w / 4)
    (k : ℕ) (h : ℝ) : IsProbabilityMeasure (shellLaw w a k h) :=
  atomic_probability _ _ (fun i => (shellWeights_pos hw hw1 ha k i).le) (shellWeights_sum w a k)

lemma sum_cast_range (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (j : ℝ)) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma shell_grid_mean (k : ℕ) (h : ℝ) :
    (∑ j : Fin (k + 1), ((k : ℝ) + j.val) * h) = 3 * k * (k + 1) * h / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((k : ℝ) + j) * h)]
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.sum_mul, sum_cast_range]
  push_cast
  ring

lemma shellLaw_mean {w a : ℝ} (hw : 0 < w) (hw1 : w < 1) (ha : |a| ≤ w / 4)
    (k : ℕ) (h : ℝ) : (∫ z, z ∂shellLaw w a k h) = 3 * a * k * h := by
  rw [shellLaw, integral_atomic _ _ (fun i => (shellWeights_pos hw hw1 ha k i).le),
    Fintype.sum_prod_type, Finset.sum_comm]
  have htag (j : Fin (k + 1)) :
      (∑ i : Fin 3, shellWeights w a k (i, j) * shellPoints k h (i, j)) =
        (2 * a / ((k : ℝ) + 1)) * (((k : ℝ) + j.val) * h) := by
    simp [shellWeights, shellPoints, threeTagWeights, Fin.sum_univ_succ]
    ring
  simp_rw [htag, ← Finset.mul_sum, shell_grid_mean]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma shellWeights_chi {w a : ℝ} (hw : 0 < w) (hw1 : w < 1) (ha : |a| ≤ w / 4)
    (k : ℕ) :
    (∑ i, (shellWeights w a k i - shellWeights w (-a) k i) ^ 2 /
      shellWeights w (-a) k i) ≤ 32 * a ^ 2 / w := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have ha' : |-a| ≤ w / 4 := by simpa using ha
  have he (i : Fin 3 × Fin (k + 1)) :
      (shellWeights w a k i - shellWeights w (-a) k i) ^ 2 / shellWeights w (-a) k i =
      ((threeTagWeights w a i.1 - threeTagWeights w (-a) i.1) ^ 2 /
        threeTagWeights w (-a) i.1) / ((k : ℝ) + 1) := by
    have hq := (threeTagWeights_pos hw hw1 ha' i.1).ne'
    unfold shellWeights
    field_simp
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_div_cancel₀ _ hk]
  exact threeTagWeights_chi hw ha

lemma map_atomic {ι : Type*} [Fintype ι] (w x : ι → ℝ) {T : ℝ → ℝ} (hT : Measurable T) :
    (atomicMeasure w x).map T = atomicMeasure w (fun i => T (x i)) := by
  unfold atomicMeasure
  rw [← Measure.mapₗ_apply_of_measurable hT, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.mapₗ_apply_of_measurable hT, Measure.map_smul _ hT.aemeasurable,
    Measure.map_dirac' hT]

noncomputable def gridMeasure (n : ℕ) (b h : ℝ) : Measure ℝ :=
  ∑ j ∈ Finset.range n, Measure.dirac ((b + j) * h)

lemma gridMeasure_split (n m : ℕ) (b h : ℝ) :
    gridMeasure (n + m) b h = gridMeasure n b h + gridMeasure m (b + n) h := by
  unfold gridMeasure
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  push_cast
  ring

lemma gridMeasure_two (b h : ℝ) :
    gridMeasure 2 b h = Measure.dirac (b * h) + Measure.dirac ((b + 1) * h) := by
  simp [gridMeasure, Finset.sum_range_succ]

lemma gridMeasure_reflection (n : ℕ) (b h : ℝ) :
    (gridMeasure n b h).map (fun z : ℝ => -z) = gridMeasure n b (-h) := by
  unfold gridMeasure
  rw [← Measure.mapₗ_apply_of_measurable measurable_neg, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.mapₗ_apply_of_measurable measurable_neg, Measure.map_dirac' measurable_neg]
  congr 1
  ring

noncomputable def centralMeasure (w : ℝ) (k : ℕ) (h : ℝ) : Measure ℝ :=
  (k + 1) • (ENNReal.ofReal ((1 - w) / ((k : ℝ) + 1)) • Measure.dirac (-h))

lemma shifted_shell_grid (w a : ℝ) (k : ℕ) (h : ℝ) :
    (shellLaw w a k h).map (fun z => z - h) = centralMeasure w k h +
      ENNReal.ofReal ((w / 2 + a) / ((k : ℝ) + 1)) • gridMeasure (k + 1) (k - 1) h +
      ENNReal.ofReal ((w / 2 - a) / ((k : ℝ) + 1)) • gridMeasure (k + 1) (k + 1) (-h) := by
  have h3 (F : Fin 3 → Measure ℝ) : ∑ i, F i = F 0 + F 1 + F 2 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [shellLaw, map_atomic _ _ (by fun_prop)]
  unfold atomicMeasure
  rw [Fintype.sum_prod_type, h3]
  have hp (j : Fin (k + 1)) : ((k : ℝ) + j.val) * h - h = ((k : ℝ) - 1 + j.val) * h := by ring
  have hn (j : Fin (k + 1)) : -(((k : ℝ) + j.val) * h) - h = ((k : ℝ) + 1 + j.val) * (-h) := by ring
  simp only [shellWeights, shellPoints, threeTagWeights, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_sub, hp, hn]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.smul_sum, ← Finset.smul_sum]
  simp only [centralMeasure, gridMeasure,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => Measure.dirac (((k : ℝ) - 1 + j) * h)),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => Measure.dirac (((k : ℝ) + 1 + j) * (-h)))]

lemma shell_grid_left {k : ℕ} (hk : 1 ≤ k) (h : ℝ) :
    gridMeasure (k + 1) ((k : ℝ) - 1) h =
      gridMeasure (k - 1) ((k : ℝ) + 1) h +
        Measure.dirac (((k : ℝ) - 1) * h) + Measure.dirac ((k : ℝ) * h) := by
  have hn : k + 1 = 2 + (k - 1) := by omega
  rw [hn, gridMeasure_split, gridMeasure_two]
  norm_num only [Nat.cast_ofNat]
  rw [show (k : ℝ) - 1 + 2 = (k : ℝ) + 1 by ring,
    show (k : ℝ) - 1 + 1 = (k : ℝ) by ring]
  ac_rfl

lemma shell_grid_right {k : ℕ} (hk : 1 ≤ k) (h : ℝ) :
    gridMeasure (k + 1) ((k : ℝ) + 1) (-h) =
      gridMeasure (k - 1) ((k : ℝ) + 1) (-h) +
        Measure.dirac (-(2 * k * h)) + Measure.dirac (-((2 * k + 1) * h)) := by
  have hn : k + 1 = (k - 1) + 2 := by omega
  rw [hn, gridMeasure_split, gridMeasure_two, Nat.cast_sub hk, Nat.cast_one]
  rw [show ((k : ℝ) + 1 + ((k : ℝ) - 1)) * (-h) = -(2 * k * h) by ring,
    show ((k : ℝ) + 1 + ((k : ℝ) - 1) + 1) * (-h) = -((2 * k + 1) * h) by ring]
  rw [add_assoc]

noncomputable def shellSymmetric (w a : ℝ) (k : ℕ) (h : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((w / 2 - a) / ((k : ℝ) + 1)) •
    (gridMeasure (k - 1) ((k : ℝ) + 1) h + gridMeasure (k - 1) ((k : ℝ) + 1) (-h))

lemma shellSymmetric_reflection (w a : ℝ) (k : ℕ) (h : ℝ) :
    (shellSymmetric w a k h).map (fun z : ℝ => -z) = shellSymmetric w a k h := by
  unfold shellSymmetric
  rw [Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_add _ _ measurable_neg, gridMeasure_reflection, gridMeasure_reflection, neg_neg]
  congr 1
  exact add_comm _ _

noncomputable def shellRemainder (w a : ℝ) (k : ℕ) (h : ℝ) : Measure ℝ :=
  centralMeasure w k h +
    ENNReal.ofReal (2 * a / ((k : ℝ) + 1)) • gridMeasure (k + 1) ((k : ℝ) - 1) h +
    ENNReal.ofReal ((w / 2 - a) / ((k : ℝ) + 1)) •
      (Measure.dirac (((k : ℝ) - 1) * h) + Measure.dirac ((k : ℝ) * h) +
        Measure.dirac (-(2 * k * h)) + Measure.dirac (-((2 * k + 1) * h)))

lemma shifted_shell_decomposition {w a : ℝ} (ha : 0 ≤ a) (haw : a ≤ w / 2)
    {k : ℕ} (hk : 1 ≤ k) (h : ℝ) :
    (shellLaw w a k h).map (fun z => z - h) =
      shellSymmetric w a k h + shellRemainder w a k h := by
  have hc : 0 ≤ (w / 2 - a) / ((k : ℝ) + 1) := div_nonneg (sub_nonneg.mpr haw) (by positivity)
  have he : 0 ≤ 2 * a / ((k : ℝ) + 1) := by positivity
  have hw : ENNReal.ofReal ((w / 2 + a) / ((k : ℝ) + 1)) =
      ENNReal.ofReal ((w / 2 - a) / ((k : ℝ) + 1)) +
        ENNReal.ofReal (2 * a / ((k : ℝ) + 1)) := by
    rw [← ENNReal.ofReal_add hc he]
    congr 1
    ring
  rw [shifted_shell_grid, hw, add_smul]
  unfold shellSymmetric shellRemainder
  rw [shell_grid_left hk h, shell_grid_right hk h]
  simp only [smul_add]
  ac_rfl

lemma integrable_grid (n : ℕ) (b h : ℝ) (f : ℝ → ℝ) : Integrable f (gridMeasure n b h) := by
  apply integrable_finsetSum_measure.mpr
  exact fun _ _ => integrable_dirac (by simp)

lemma integrable_central (w : ℝ) (k : ℕ) (h : ℝ) (f : ℝ → ℝ) :
    Integrable f (centralMeasure w k h) := by
  have hi := integrable_atomic (fun _ : Fin (k + 1) => (1 - w) / ((k : ℝ) + 1))
    (fun _ => -h) f
  simpa [atomicMeasure, centralMeasure] using hi

lemma integrable_shellSymmetric (w a : ℝ) (k : ℕ) (h : ℝ) (f : ℝ → ℝ) :
    Integrable f (shellSymmetric w a k h) :=
  ((integrable_grid _ _ _ f).add_measure (integrable_grid _ _ _ f)).smul_measure
    ENNReal.ofReal_ne_top

lemma integrable_shellRemainder (w a : ℝ) (k : ℕ) (h : ℝ) (f : ℝ → ℝ) :
    Integrable f (shellRemainder w a k h) := by
  have hd (z : ℝ) : Integrable f (Measure.dirac z) := integrable_dirac (by simp)
  exact ((integrable_central w k h f).add_measure
    ((integrable_grid _ _ _ f).smul_measure ENNReal.ofReal_ne_top)).add_measure
    (((((hd _).add_measure (hd _)).add_measure (hd _)).add_measure (hd _)).smul_measure
      ENNReal.ofReal_ne_top)

lemma shellSymmetric_mean (w a : ℝ) (k : ℕ) (h : ℝ) :
    (∫ z, z ∂shellSymmetric w a k h) = 0 := by
  have he := integral_map (μ := shellSymmetric w a k h) measurable_neg.aemeasurable
    (f := fun z : ℝ => z) (by fun_prop)
  rw [shellSymmetric_reflection] at he
  change (∫ z, z ∂shellSymmetric w a k h) = ∫ z, -(fun z : ℝ => z) z ∂shellSymmetric w a k h at he
  rw [integral_neg] at he
  linarith

lemma shellRemainder_mean {w a : ℝ} (hw : 0 < w) (hw1 : w < 1) (ha : 0 ≤ a)
    (haw : |a| ≤ w / 4) {k : ℕ} (hk : 1 ≤ k) (hcenter : 3 * a * k = 1) (h : ℝ) :
    (∫ z, z ∂shellRemainder w a k h) = 0 := by
  let : IsProbabilityMeasure (shellLaw w a k h) := shellLaw_probability hw hw1 haw k h
  have hi : Integrable (fun z : ℝ => z) (shellLaw w a k h) := integrable_atomic _ _ _
  have hm : (∫ z, z ∂(shellLaw w a k h).map (fun z => z - h)) = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    rw [integral_sub hi (integrable_const h),
      shellLaw_mean hw hw1 haw k h]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hcenter, one_mul, sub_self]
  have haw' : a ≤ w / 2 := by have h := (abs_le.mp haw).2; linarith
  rw [shifted_shell_decomposition ha haw' hk h,
    integral_add_measure (integrable_shellSymmetric w a k h (fun z => z))
      (integrable_shellRemainder w a k h (fun z => z)), shellSymmetric_mean, zero_add] at hm
  exact hm

lemma integral_grid (n : ℕ) (b h : ℝ) (f : ℝ → ℝ) :
    (∫ z, f z ∂gridMeasure n b h) = ∑ j ∈ Finset.range n, f ((b + j) * h) := by
  rw [gridMeasure, integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp only [integral_dirac]

lemma integral_central {w : ℝ} (hw : w ≤ 1) (k : ℕ) (h : ℝ) (f : ℝ → ℝ) :
    (∫ z, f z ∂centralMeasure w k h) = (1 - w) * f (-h) := by
  have he : centralMeasure w k h =
      atomicMeasure (fun _ : Fin (k + 1) => (1 - w) / ((k : ℝ) + 1)) (fun _ => -h) := by
    simp [centralMeasure, atomicMeasure]
  rw [he, integral_atomic _ _ (fun _ => div_nonneg (sub_nonneg.mpr hw) (by positivity))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma shell_grid_square_bound {k : ℕ} (hk : 1 ≤ k) (h : ℝ) :
    (∫ z, z ^ 2 ∂gridMeasure (k + 1) ((k : ℝ) - 1) h) ≤
      ((k : ℝ) + 1) * (4 * k ^ 2 * h ^ 2) := by
  rw [integral_grid]
  calc
    _ ≤ ∑ _j ∈ Finset.range (k + 1), (4 : ℝ) * k ^ 2 * h ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : (j : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hj0 : (0 : ℝ) ≤ j := by positivity
      have hb : ((k : ℝ) - 1 + j) ^ 2 ≤ 4 * k ^ 2 := by
        calc
          _ ≤ (2 * (k : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
          _ = _ := by ring
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg h)
    _ = _ := by simp [Nat.cast_add, Nat.cast_one]

lemma shell_edge_square_bound {k : ℕ} (hk : 1 ≤ k) (h : ℝ) :
    (((k : ℝ) - 1) * h) ^ 2 + ((k : ℝ) * h) ^ 2 +
      (-(2 * (k : ℝ) * h)) ^ 2 + (-((2 * (k : ℝ) + 1) * h)) ^ 2 ≤
        36 * (k : ℝ) ^ 2 * h ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 10 * (k : ℝ) ^ 2 + 2 * k + 2 ≤ 36 * (k : ℝ) ^ 2 := by nlinarith
  convert mul_le_mul_of_nonneg_right hp (sq_nonneg h) using 1; ring

lemma shellRemainder_square_bound {w a : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (ha : 0 ≤ a) (haw : a ≤ w / 2) {k : ℕ} (hk : 1 ≤ k) (h : ℝ) :
    (∫ z, z ^ 2 ∂shellRemainder w a k h) ≤
      h ^ 2 + 8 * a * k ^ 2 * h ^ 2 + 18 * w * k * h ^ 2 := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkpos : (0 : ℝ) < k + 1 := by positivity
  have hc : 0 ≤ (w / 2 - a) / ((k : ℝ) + 1) := div_nonneg (sub_nonneg.mpr haw) hkpos.le
  have he : 0 ≤ 2 * a / ((k : ℝ) + 1) := by positivity
  have hd (z : ℝ) : Integrable (fun z : ℝ => z ^ 2) (Measure.dirac z) := integrable_dirac (by simp)
  have hg := (integrable_grid (k + 1) ((k : ℝ) - 1) h (fun z => z ^ 2)).smul_measure
    (c := ENNReal.ofReal (2 * a / ((k : ℝ) + 1))) ENNReal.ofReal_ne_top
  have hed := (((hd (((k : ℝ) - 1) * h)).add_measure (hd ((k : ℝ) * h))).add_measure
    (hd (-(2 * k * h)))).add_measure (hd (-((2 * k + 1) * h)))
  rw [shellRemainder, integral_add_measure ((integrable_central w k h (fun z => z ^ 2)).add_measure hg)
      (hed.smul_measure ENNReal.ofReal_ne_top),
    integral_add_measure (integrable_central w k h (fun z => z ^ 2)) hg,
    integral_central hw1, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal he, ENNReal.toReal_ofReal hc]
  rw [integral_add_measure (((hd _).add_measure (hd _)).add_measure (hd _)) (hd _),
    integral_add_measure ((hd _).add_measure (hd _)) (hd _), integral_add_measure (hd _) (hd _)]
  simp only [integral_dirac, smul_eq_mul, neg_sq]
  have hG : (2 * a / ((k : ℝ) + 1)) *
      (∫ z, z ^ 2 ∂gridMeasure (k + 1) ((k : ℝ) - 1) h) ≤ 8 * a * k ^ 2 * h ^ 2 := by
    calc
      _ ≤ (2 * a / ((k : ℝ) + 1)) * (((k : ℝ) + 1) * (4 * k ^ 2 * h ^ 2)) :=
        mul_le_mul_of_nonneg_left (shell_grid_square_bound hk h) he
      _ = _ := by field_simp; ring
  have hcoef : (w / 2 - a) / ((k : ℝ) + 1) * (36 * (k : ℝ) ^ 2) ≤ 18 * w * k := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hkpos).mpr
    nlinarith [mul_nonneg ha (sq_nonneg (k : ℝ)), mul_nonneg hw hk0]
  have hE := mul_le_mul_of_nonneg_left (shell_edge_square_bound hk h) hc
  have hE' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg h)
  have hC : (1 - w) * h ^ 2 ≤ h ^ 2 := by nlinarith [mul_nonneg hw (sq_nonneg h)]
  simp only [neg_sq] at hE
  nlinarith

lemma grid_mass (n : ℕ) (b h : ℝ) : gridMeasure n b h Set.univ = n := by
  simp [gridMeasure, Measure.finsetSum_apply]

lemma shifted_shell_quantile {w a h r : ℝ} (ha : |a| ≤ w / 2) (hh : |h| ≤ r)
    (k : ℕ) :
    ((shellLaw w a k h).map (fun z => z - h)) {z | r < |z|} ≤ ENNReal.ofReal w := by
  let B := {z : ℝ | r < |z|}
  have hB : MeasurableSet B := measurableSet_lt measurable_const continuous_abs.measurable
  have hnot : -h ∉ B := by simpa only [B, Set.mem_ofPred_eq, abs_neg, not_lt] using hh
  have hC : centralMeasure w k h B = 0 := by
    simp [centralMeasure, Measure.smul_apply, Measure.dirac_apply' _ hB, hnot]
  have hd : 0 ≤ (w / 2 + a) / ((k : ℝ) + 1) := by
    apply div_nonneg _ (by positivity)
    have hb := (abs_le.mp ha).1
    linarith
  have hc : 0 ≤ (w / 2 - a) / ((k : ℝ) + 1) :=
    div_nonneg (sub_nonneg.mpr (abs_le.mp ha).2) (by positivity)
  change ((shellLaw w a k h).map (fun z => z - h)) B ≤ _
  rw [shifted_shell_grid, Measure.add_apply, Measure.add_apply, hC, zero_add]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal ((w / 2 + a) / ((k : ℝ) + 1)) * (k + 1 : ℕ) +
        ENNReal.ofReal ((w / 2 - a) / ((k : ℝ) + 1)) * (k + 1 : ℕ) := by
      apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ zero_le
      · rw [← grid_mass (k + 1) ((k : ℝ) - 1) h]
        exact measure_mono (Set.subset_univ B)
      · rw [← grid_mass (k + 1) ((k : ℝ) + 1) (-h)]
        exact measure_mono (Set.subset_univ B)
    _ = ENNReal.ofReal w := by
      rw [← add_mul, ← ENNReal.ofReal_add hd hc]
      rw [show (w / 2 + a) / ((k : ℝ) + 1) + (w / 2 - a) / ((k : ℝ) + 1) =
        w / ((k : ℝ) + 1) by ring]
      have hn : ENNReal.ofReal ((k : ℝ) + 1) = (k + 1 : ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using ENNReal.ofReal_natCast (k + 1)
      have hw : 0 ≤ w := by have hb := abs_nonneg a; linarith
      rw [← hn, ← ENNReal.ofReal_mul (div_nonneg hw (by positivity))]
      congr 1
      field_simp

lemma fixed_shell_conditions {k : ℕ} (hk : 128 ≤ k) :
    0 ≤ 1 / (3 * (k : ℝ)) ∧ |1 / (3 * (k : ℝ))| ≤ (1 / 64 : ℝ) / 4 ∧
      3 * (1 / (3 * (k : ℝ))) * k = 1 := by
  have hk128 : (128 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [abs_of_pos (by positivity)]
    apply (div_le_iff₀ (by positivity : 0 < 3 * (k : ℝ))).mpr
    linarith
  · field_simp

lemma fixed_shell_remainder_square {k : ℕ} (hk : 128 ≤ k) (h : ℝ) :
    (∫ z, z ^ 2 ∂shellRemainder (1 / 64) (1 / (3 * k)) k h) ≤ 3 * k * h ^ 2 := by
  have hk128 : (128 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨ha, haw, _⟩ := fixed_shell_conditions hk
  have hb := shellRemainder_square_bound (by norm_num : (0 : ℝ) ≤ 1 / 64)
    (by norm_num : (1 / 64 : ℝ) ≤ 1) ha
    (show 1 / (3 * (k : ℝ)) ≤ (1 / 64 : ℝ) / 2 by have h := (abs_le.mp haw).2; linarith)
    (show 1 ≤ k by omega) h
  have he : h ^ 2 + 8 * (1 / (3 * (k : ℝ))) * k ^ 2 * h ^ 2 +
      18 * (1 / 64 : ℝ) * k * h ^ 2 = (1 + 283 / 96 * (k : ℝ)) * h ^ 2 := by
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    field_simp
    all_goals ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg h))

lemma fixed_shell_noise {k : ℕ} (hk : 128 ≤ k) {h r M : ℝ} (hh : |h| ≤ r)
    (hM : 3 * (k : ℝ) * h ^ 2 ≤ M) :
    LongTails.Setups.QuantileSymmetricRemainderConvex.NoiseCondition
      ((shellLaw (1 / 64) (1 / (3 * k)) k h).map (fun z => z - h)) r M := by
  obtain ⟨ha, haw, hcenter⟩ := fixed_shell_conditions hk
  have haw' : 1 / (3 * (k : ℝ)) ≤ (1 / 64 : ℝ) / 2 := by
    have hb := (abs_le.mp haw).2
    linarith
  refine ⟨⟨shellSymmetric (1 / 64) (1 / (3 * k)) k h,
    shellRemainder (1 / 64) (1 / (3 * k)) k h,
    shifted_shell_decomposition ha haw' (by omega) h,
    shellSymmetric_reflection _ _ _ _, integrable_shellRemainder _ _ _ _ _,
    shellRemainder_mean (by norm_num) (by norm_num) ha haw (by omega) hcenter h,
    integrable_shellRemainder _ _ _ _ _, (fixed_shell_remainder_square hk h).trans hM⟩, ?_⟩
  have hb := shifted_shell_quantile (show |1 / (3 * (k : ℝ))| ≤ (1 / 64 : ℝ) / 2 by linarith)
    hh k
  have he : ENNReal.ofReal (1 / 64 : ℝ) = (1 / 64 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [he] at hb
  exact hb

lemma shell_count_bounds {h M : ℝ} (hh : 0 < h) (hM : h ^ 2 ≤ M / 512) :
    128 ≤ ⌈M / (4 * h ^ 2)⌉₊ ∧
      3 * (⌈M / (4 * h ^ 2)⌉₊ : ℝ) * h ^ 2 ≤ M := by
  have hMpos : 0 < M := by nlinarith [sq_pos_of_pos hh]
  have hden : 0 < 4 * h ^ 2 := by positivity
  have hratio : (128 : ℝ) ≤ M / (4 * h ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  constructor
  · have hb := hratio.trans (Nat.le_ceil _)
    exact_mod_cast hb
  · have hc := (Nat.ceil_lt_add_one (show 0 ≤ M / (4 * h ^ 2) by positivity)).le
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg h)
    have he : (M / (4 * h ^ 2) + 1) * h ^ 2 = M / 4 + h ^ 2 := by
      field_simp
    rw [he] at hm
    nlinarith

lemma shellLaw_reflection (w a : ℝ) (k : ℕ) (h : ℝ) :
    (shellLaw w a k h).map (fun z : ℝ => -z) = shellLaw w (-a) k h := by
  rw [shellLaw, map_atomic _ _ measurable_neg, shellLaw]
  unfold atomicMeasure
  simp only [Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [shellWeights, shellPoints, threeTagWeights, Fin.sum_univ_succ,
    sub_eq_add_neg, add_comm]

lemma fixed_shell_negative_noise {k : ℕ} (hk : 128 ≤ k) {h r M : ℝ} (hh : |h| ≤ r)
    (hM : 3 * (k : ℝ) * h ^ 2 ≤ M) :
    LongTails.Setups.QuantileSymmetricRemainderConvex.NoiseCondition
      ((shellLaw (1 / 64) (-(1 / (3 * k))) k h).map (fun z => z + h)) r M := by
  have hn := QuantileNoiseLaws.noise_reflection (fixed_shell_noise hk hh hM)
  rw [← shellLaw_reflection, Measure.map_map (by fun_prop) measurable_neg]
  rw [Measure.map_map measurable_neg (by fun_prop)] at hn
  convert hn using 1
  congr 1
  funext z
  simp only [Function.comp_apply]
  ring

lemma chosen_shell_chi {h M : ℝ} (hh : 0 < h) (hM : h ^ 2 ≤ M / 512) :
    let k := ⌈M / (4 * h ^ 2)⌉₊
    (∑ i, (shellWeights (1 / 64) (1 / (3 * k)) k i -
      shellWeights (1 / 64) (-(1 / (3 * k))) k i) ^ 2 /
        shellWeights (1 / 64) (-(1 / (3 * k))) k i) ≤ 4096 * h ^ 4 / M ^ 2 := by
  intro k
  have hk128 : 128 ≤ k := (shell_count_bounds hh hM).1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨_, ha, _⟩ := fixed_shell_conditions hk128
  have hχ := shellWeights_chi (by norm_num : (0 : ℝ) < 1 / 64)
    (by norm_num : (1 / 64 : ℝ) < 1) ha k
  have hMpos : 0 < M := by nlinarith [sq_pos_of_pos hh]
  have hceil : M / (4 * h ^ 2) ≤ (k : ℝ) := Nat.le_ceil _
  have hmk : M ≤ 4 * (k : ℝ) * h ^ 2 := by
    have hb := (div_le_iff₀ (by positivity : 0 < 4 * h ^ 2)).mp hceil
    nlinarith
  have hsq := pow_le_pow_left₀ hMpos.le hmk 2
  have he : 32 * (1 / (3 * (k : ℝ))) ^ 2 / (1 / 64) = 2048 / (9 * (k : ℝ) ^ 2) := by
    field_simp
    norm_num
  rw [he] at hχ
  apply hχ.trans
  apply (div_le_div_iff₀ (by positivity : 0 < 9 * (k : ℝ) ^ 2)
    (sq_pos_of_pos hMpos)).mpr
  nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (pow_nonneg hh.le 4)]

end LongTails.Proofs.QuantileShellOracle
