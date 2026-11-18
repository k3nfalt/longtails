import LongTails.Algorithms.DashaQuantization
import LongTails.Proofs.DistributedQuantization
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace LongTails.Proofs.DashaQuantization

open LongTails.Algorithms.DashaQuantization
open MeasureTheory

lemma uniform_threshold_integrable (t : ℝ) :
    Integrable (fun u : ℝ => if u < t then (1 : ℝ) else 0) (unitLaw : Measure ℝ) :=
  (integrable_const (1 : ℝ)).indicator measurableSet_Iio

lemma uniform_threshold_mean (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ u : ℝ, (if u < t then (1 : ℝ) else 0) ∂(unitLaw : Measure ℝ)) = t := by
  change (∫ u, (Set.Iio t).indicator (fun _ => (1 : ℝ)) u ∂(unitLaw : Measure ℝ)) = t
  rw [integral_indicator_const _ measurableSet_Iio]
  simp only [smul_eq_mul, mul_one]
  change (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iio t) = t
  have hset : Set.Iio t ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 t := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨hu, hl, _⟩
      exact ⟨hl, hu⟩
    · rintro ⟨hl, hu⟩
      exact ⟨hu, hl, hu.le.trans ht1⟩
  rw [measureReal_def, Measure.restrict_apply measurableSet_Iio, hset,
    Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal ht]

lemma rounded_magnitude_mean (s : ℕ) (hs : 0 < s) (r : ℝ) (hr : 0 ≤ r) :
    (∫ u : ℝ, (((⌊r / s⌋₊ + if u < r / s - ⌊r / s⌋₊ then 1 else 0) * s : ℕ) : ℝ)
      ∂(unitLaw : Measure ℝ)) = r := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hlo := Nat.floor_le (div_nonneg hr hsr.le)
  have hhi := Nat.lt_floor_add_one (r / s)
  have ht : 0 ≤ r / s - (⌊r / s⌋₊ : ℝ) := by linarith
  have ht1 : r / s - (⌊r / s⌋₊ : ℝ) ≤ 1 := by linarith
  simp_rw [Nat.cast_mul, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [integral_mul_const, integral_add (integrable_const _) (uniform_threshold_integrable _),
    integral_const, uniform_threshold_mean _ ht ht1]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  convert div_mul_cancel₀ r hsr.ne' using 1; ring

lemma stride_pos (coarse : Bool) (x : ℝ) : 0 < stride coarse x := by
  cases coarse <;> simp [stride]

lemma stride_bound (coarse : Bool) (x : ℝ) :
    (stride coarse x : ℝ) ≤ 1 + |x| / 4 := by
  cases coarse with
  | false =>
    simp only [stride, Bool.false_eq_true, ↓reduceIte, Nat.cast_one]
    linarith [abs_nonneg x]
  | true =>
    by_cases hlog : Nat.log2 ⌊|x|⌋₊ ≤ 2
    · simp only [stride, ↓reduceIte, Nat.sub_eq_zero_of_le hlog, pow_zero, Nat.cast_one]
      linarith [abs_nonneg x]
    · have hn : ⌊|x|⌋₊ ≠ 0 := by
        intro hz
        simp [hz] at hlog
      have hp : 4 * 2 ^ (Nat.log2 ⌊|x|⌋₊ - 2) ≤ ⌊|x|⌋₊ := by
        calc
          _ = 2 ^ Nat.log2 ⌊|x|⌋₊ := by
            rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
            congr 1
            omega
          _ ≤ _ := Nat.log2_self_le hn
      have hpr : (4 : ℝ) * (2 ^ (Nat.log2 ⌊|x|⌋₊ - 2) : ℕ) ≤ (⌊|x|⌋₊ : ℝ) := by
        exact_mod_cast hp
      have hf := Nat.floor_le (abs_nonneg x)
      simp only [stride, ↓reduceIte]
      nlinarith

lemma magnitude_error (s : ℕ) (hs : 0 < s) (x u : ℝ) :
    abs ((((⌊|x| / s⌋₊ + if u < |x| / s - ⌊|x| / s⌋₊ then 1 else 0) * s : ℕ) : ℝ) - |x|) ≤ s := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hlo := Nat.floor_le (div_nonneg (abs_nonneg x) hsr.le)
  have hhi := Nat.lt_floor_add_one (|x| / s)
  have he : |x| / s * s = |x| := div_mul_cancel₀ _ hsr.ne'
  split_ifs <;> push_cast <;> apply abs_le.mpr <;> constructor <;> nlinarith

lemma scalar_error (coarse : Bool) (x u : ℝ) :
    |(scalarIndex coarse x u : ℝ) - x| ≤ stride coarse x := by
  have hm := magnitude_error (stride coarse x) (stride_pos coarse x) x u
  unfold scalarIndex
  dsimp only
  by_cases hx : x < 0
  · simp only [ite_eq_left hx, Int.cast_neg, Int.cast_natCast]
    simp only [abs_of_neg hx] at hm ⊢
    have hab := abs_le.mp hm
    apply abs_le.mpr
    constructor <;> linarith
  · simp only [ite_eq_right hx, Int.cast_natCast]
    simpa only [abs_of_nonneg (le_of_not_gt hx)] using hm

lemma scalar_relative_error (coarse : Bool) (x u : ℝ) :
    |(scalarIndex coarse x u : ℝ) - x| ≤ |x| / 4 + 1 := by
  have hs := stride_bound coarse x
  linarith [scalar_error coarse x u]

lemma scalar_initial_error (x u : ℝ) : |(scalarIndex false x u : ℝ) - x| ≤ 1 := by
  simpa only [stride, Bool.false_eq_true, ↓reduceIte, Nat.cast_one] using scalar_error false x u

lemma coordinate_error (d : ℕ) (coarse : Bool) (spacing : ℝ) (hs : 0 < spacing)
    (x : Vector d) (u : Fin d → ℝ) (i : Fin d) :
    |rounded d coarse spacing x u i - x i| ≤ |x i| / 4 + spacing := by
  have he : rounded d coarse spacing x u i - x i =
      spacing * ((scalarIndex coarse (x i / spacing) (u i) : ℝ) - x i / spacing) := by
    change spacing * (scalarIndex coarse (x i / spacing) (u i) : ℝ) - x i = _
    rw [mul_sub, mul_div_cancel₀ _ hs.ne']
  rw [he, abs_mul, abs_of_pos hs]
  calc
    _ ≤ spacing * (|x i / spacing| / 4 + 1) :=
      mul_le_mul_of_nonneg_left (scalar_relative_error coarse _ _) hs.le
    _ = _ := by
      rw [abs_div, abs_of_pos hs]
      field_simp

lemma coordinate_initial_error (d : ℕ) (spacing : ℝ) (hs : 0 < spacing)
    (x : Vector d) (u : Fin d → ℝ) (i : Fin d) :
    |rounded d false spacing x u i - x i| ≤ spacing := by
  have he : rounded d false spacing x u i - x i =
      spacing * ((scalarIndex false (x i / spacing) (u i) : ℝ) - x i / spacing) := by
    change spacing * (scalarIndex false (x i / spacing) (u i) : ℝ) - x i = _
    rw [mul_sub, mul_div_cancel₀ _ hs.ne']
  rw [he, abs_mul, abs_of_pos hs]
  simpa using mul_le_mul_of_nonneg_left (scalar_initial_error (x i / spacing) (u i)) hs.le

lemma norm_le_of_coordinates {d : ℕ} (x y : Vector d)
    (h : ∀ i, |x i| ≤ |y i|) : ‖x‖ ≤ ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  have hi := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (h i)
  simpa only [sq_abs] using hi

lemma norm_const_le (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ‖(WithLp.toLp 2 (fun _ : Fin d => r) : Vector d)‖ ≤ d * r := by
  have he : ‖(WithLp.toLp 2 (fun _ : Fin d => r) : Vector d)‖ ^ 2 = d * r ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    simpa only [pow_two] using (show (d : ℝ) ≤ d * d by exact_mod_cast Nat.le_mul_self d)
  have hm := mul_le_mul_of_nonneg_right hd (sq_nonneg r)
  have hpos : (0 : ℝ) ≤ d * r := by positivity
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun _ : Fin d => r) : Vector d)]

lemma vector_error (d : ℕ) (coarse : Bool) (spacing : ℝ) (hs : 0 < spacing)
    (x : Vector d) (u : Fin d → ℝ) :
    ‖rounded d coarse spacing x u - x‖ ≤ ‖x‖ / 4 + d * spacing := by
  let v : Vector d := WithLp.toLp 2 (fun i => |x i|)
  let c : Vector d := WithLp.toLp 2 (fun _ => spacing)
  have hv : ‖v‖ = ‖x‖ := by
    have he : ‖v‖ ^ 2 = ‖x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, v]
    nlinarith [norm_nonneg v, norm_nonneg x]
  have he := norm_le_of_coordinates (rounded d coarse spacing x u - x) ((1 / 4 : ℝ) • v + c) (by
    intro i
    have hnonneg : 0 ≤ (1 / 4 : ℝ) * |x i| + spacing := by positivity
    change |rounded d coarse spacing x u i - x i| ≤ |(1 / 4 : ℝ) * |x i| + spacing|
    rw [abs_of_nonneg hnonneg]
    simpa only [one_div_mul_eq_div] using coordinate_error d coarse spacing hs x u i)
  have ht := norm_add_le ((1 / 4 : ℝ) • v) c
  norm_num [norm_smul, hv] at ht
  have hc := norm_const_le d spacing hs.le
  change ‖c‖ ≤ d * spacing at hc
  linarith

lemma vector_initial_error (d : ℕ) (spacing : ℝ) (hs : 0 < spacing)
    (x : Vector d) (u : Fin d → ℝ) :
    ‖rounded d false spacing x u - x‖ ≤ d * spacing := by
  apply (norm_le_of_coordinates _ (WithLp.toLp 2 (fun _ : Fin d => spacing)) ?_).trans
    (norm_const_le d spacing hs.le)
  intro i
  change |rounded d false spacing x u i - x i| ≤ |spacing|
  rw [abs_of_pos hs]
  exact coordinate_initial_error d spacing hs x u i

lemma encode_length (d width : ℕ) (z : Fin d → ℤ) :
    (encode d width z).length = d * width :=
  LongTails.Proofs.DistributedQuantization.encode_length _

lemma unpack_pack (width : ℕ) (z : ℤ)
    (hlo : -(center width : ℤ) ≤ z)
    (hhi : z + center width < (2 ^ width : ℕ)) :
    unpackScalar (packScalar width z) = z := by
  have hz : 0 ≤ z + center width := by omega
  have hb : (z + center width).toNat ≤ 2 ^ width - 1 := by omega
  simp only [packScalar, unpackScalar, min_eq_left hb]
  rw [Int.toNat_of_nonneg hz]
  omega

lemma decode_encode (d width : ℕ) (z : Fin d → ℤ)
    (hlo : ∀ i, -(center width : ℤ) ≤ z i)
    (hhi : ∀ i, z i + center width < (2 ^ width : ℕ)) :
    decode d width (encode d width z) = z := by
  have hlen := encode_length d width z
  funext i
  simp only [decode, ← hlen, List.take_length, encode,
    LongTails.Proofs.DistributedQuantization.decode_encode]
  exact unpack_pack width (z i) (hlo i) (hhi i)

lemma measurable_stride (coarse : Bool) : Measurable (stride coarse) := by
  cases coarse with
  | false =>
    change Measurable (fun _ : ℝ => (1 : ℕ))
    exact measurable_const
  | true =>
    exact (measurable_of_countable (fun k : ℕ => 2 ^ (Nat.log2 k - 2))).comp
      (Nat.measurable_floor.comp continuous_abs.measurable)

lemma measurable_scalarIndex (coarse : Bool) :
    Measurable (fun z : ℝ × ℝ => scalarIndex coarse z.1 z.2) := by
  have hs : Measurable (fun z : ℝ × ℝ => stride coarse z.1) :=
    (measurable_stride coarse).comp measurable_fst
  have hsR : Measurable (fun z : ℝ × ℝ => (stride coarse z.1 : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hs
  have habs : Measurable (fun z : ℝ × ℝ => |z.1|) :=
    continuous_abs.measurable.comp measurable_fst
  have hy := habs.div hsR
  have hk := Nat.measurable_floor.comp hy
  have hkR := (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hk
  have hb : Measurable (fun z : ℝ × ℝ =>
      if z.2 < |z.1| / (stride coarse z.1 : ℝ) - (⌊|z.1| / (stride coarse z.1 : ℝ)⌋₊ : ℝ)
      then (1 : ℕ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_snd (hy.sub hkR)) measurable_const measurable_const
  have hm := (hk.add hb).mul hs
  have hmZ := (measurable_of_countable (fun k : ℕ => (k : ℤ))).comp hm
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_const) hmZ.neg hmZ

lemma measurable_indices (d : ℕ) (coarse : Bool) (spacing : ℝ) :
    Measurable (fun z : Vector d × (Fin d → ℝ) => indices d coarse spacing z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  have hx : Measurable (fun z : Vector d × (Fin d → ℝ) => z.1 i / spacing) :=
    ((measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 (Fin d → ℝ)).comp measurable_fst)).div_const spacing
  have hu : Measurable (fun z : Vector d × (Fin d → ℝ) => z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact (measurable_scalarIndex coarse).comp (hx.prodMk hu)

lemma measurable_reconstruct (d : ℕ) (spacing : ℝ) :
    Measurable (reconstruct (d := d) spacing) := measurable_of_countable _

lemma scalarIndex_mean (coarse : Bool) (x : ℝ) :
    (∫ u : ℝ, (scalarIndex coarse x u : ℝ) ∂(unitLaw : Measure ℝ)) = x := by
  by_cases hx : x < 0
  · simp only [scalarIndex, hx, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
    rw [integral_neg, rounded_magnitude_mean _ (stride_pos coarse x) _ (abs_nonneg x), abs_of_neg hx]
    ring
  · simp only [scalarIndex, hx, ↓reduceIte, Int.cast_natCast]
    rw [rounded_magnitude_mean _ (stride_pos coarse x) _ (abs_nonneg x), abs_of_nonneg (le_of_not_gt hx)]

end LongTails.Proofs.DashaQuantization
