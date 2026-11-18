import LongTails.Algorithms.DistributedRandomRounding
import LongTails.Proofs.DistributedQuantization
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory

namespace LongTails.Proofs.DistributedRandomRounding

open LongTails.Algorithms.DistributedRandomRounding

lemma scalar_grid_mean {spacing : ℝ} (hs : spacing ≠ 0) (x : ℝ) :
    lower spacing x + spacing * threshold spacing x = x := by
  have h := Int.floor_add_fract (x / spacing)
  calc
    _ = spacing * ((⌊x / spacing⌋ : ℝ) + Int.fract (x / spacing)) := by
      simp only [lower, threshold]; ring
    _ = spacing * (x / spacing) := by rw [h]
    _ = x := by field_simp

lemma scalar_weighted_mean {spacing : ℝ} (hs : spacing ≠ 0) (x : ℝ) :
    (1 - threshold spacing x) * lower spacing x +
      threshold spacing x * upper spacing x = x := by
  calc
    _ = lower spacing x + spacing * threshold spacing x := by unfold upper; ring
    _ = x := scalar_grid_mean hs x

lemma scalar_weighted_variance {spacing : ℝ} (hs : spacing ≠ 0) (x : ℝ) :
    (1 - threshold spacing x) * (lower spacing x - x) ^ 2 +
      threshold spacing x * (upper spacing x - x) ^ 2 =
        spacing ^ 2 * threshold spacing x * (1 - threshold spacing x) := by
  set a := lower spacing x
  set p := threshold spacing x
  have hx : a + spacing * p = x := scalar_grid_mean hs x
  change (1 - p) * (a - x) ^ 2 + p * (a + spacing - x) ^ 2 = spacing ^ 2 * p * (1 - p)
  rw [← hx]
  ring

lemma scalar_weighted_variance_le {spacing : ℝ} (hs : spacing ≠ 0) (x : ℝ) :
    (1 - threshold spacing x) * (lower spacing x - x) ^ 2 +
      threshold spacing x * (upper spacing x - x) ^ 2 ≤ spacing ^ 2 / 4 := by
  rw [scalar_weighted_variance hs x]
  have h : threshold spacing x * (1 - threshold spacing x) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (threshold spacing x - 1 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg spacing)]

lemma scalar_error {spacing : ℝ} (hs : 0 < spacing) (x u : ℝ) :
    |scalar spacing x u - x| ≤ spacing := by
  have hx := scalar_grid_mean hs.ne' x
  have hp0 : 0 ≤ threshold spacing x := Int.fract_nonneg _
  have hp1 : threshold spacing x ≤ 1 := (Int.fract_lt_one _).le
  unfold scalar
  split_ifs
  · unfold upper
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hs.le hp0, mul_le_mul_of_nonneg_left hp1 hs.le]
  · rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hs.le hp0, mul_le_mul_of_nonneg_left hp1 hs.le]

lemma message_length (d width : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (u : Fin d → ℝ) :
    (message d width spacing x u).length = d * width := by
  exact LongTails.Proofs.DistributedQuantization.encode_length _

lemma uniform_Iio {p : ℝ} (hp1 : p ≤ 1) :
    (uniform : Measure ℝ) (Set.Iio p) = ENNReal.ofReal p := by
  change volume.restrict (Set.Ico 0 1) (Set.Iio p) = _
  rw [Measure.restrict_apply measurableSet_Iio]
  have he : Set.Iio p ∩ Set.Ico 0 1 = Set.Ico 0 p := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
    constructor
    · intro h; exact ⟨h.2.1, h.1⟩
    · intro h; exact ⟨h.2, h.1, lt_of_lt_of_le h.2 hp1⟩
  rw [he, Real.volume_Ico, sub_zero]

lemma uniform_two_point_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : ℝ) :
    Integrable (fun u : ℝ => if u < p then a else b) (uniform : Measure ℝ) ∧
      (∫ u : ℝ, (if u < p then a else b) ∂(uniform : Measure ℝ)) = p * a + (1 - p) * b := by
  classical
  have ha : Integrable (fun _ : ℝ => a) (uniform : Measure ℝ) := integrable_const a
  have hb : Integrable (fun _ : ℝ => b) (uniform : Measure ℝ) := integrable_const b
  have hi : Integrable (fun u : ℝ => if u < p then a else b) (uniform : Measure ℝ) :=
    Integrable.piecewise measurableSet_Iio ha.integrableOn hb.integrableOn
  refine ⟨hi, ?_⟩
  change (∫ u : ℝ, (Set.Iio p).piecewise (fun _ => a) (fun _ => b) u
    ∂(uniform : Measure ℝ)) = _
  rw [integral_piecewise measurableSet_Iio ha.integrableOn hb.integrableOn,
    setIntegral_const, setIntegral_const, measureReal_compl measurableSet_Iio]
  have hm : (uniform : Measure ℝ).real (Set.Iio p) = p := by
    rw [Measure.real, uniform_Iio hp1, ENNReal.toReal_ofReal hp0]
  rw [hm, probReal_univ]
  rfl

lemma scalar_integral {spacing : ℝ} (hs : spacing ≠ 0) (x : ℝ) :
    Integrable (scalar spacing x) (uniform : Measure ℝ) ∧
      (∫ u, scalar spacing x u ∂(uniform : Measure ℝ)) = x := by
  have hp0 : 0 ≤ threshold spacing x := Int.fract_nonneg _
  have hp1 : threshold spacing x ≤ 1 := (Int.fract_lt_one _).le
  obtain ⟨hi, hm⟩ := uniform_two_point_integral hp0 hp1 (upper spacing x) (lower spacing x)
  refine ⟨hi, ?_⟩
  change (∫ u : ℝ, (if u < threshold spacing x then upper spacing x else lower spacing x)
    ∂(uniform : Measure ℝ)) = _
  rw [hm, add_comm]
  exact scalar_weighted_mean hs x

lemma scalar_integral_variance {spacing : ℝ} (hs : spacing ≠ 0) (x : ℝ) :
    Integrable (fun u => (scalar spacing x u - x) ^ 2) (uniform : Measure ℝ) ∧
      (∫ u, (scalar spacing x u - x) ^ 2 ∂(uniform : Measure ℝ)) ≤ spacing ^ 2 / 4 := by
  have hp0 : 0 ≤ threshold spacing x := Int.fract_nonneg _
  have hp1 : threshold spacing x ≤ 1 := (Int.fract_lt_one _).le
  obtain ⟨hi, hm⟩ := uniform_two_point_integral hp0 hp1 ((upper spacing x - x) ^ 2) ((lower spacing x - x) ^ 2)
  have he : (fun u => (scalar spacing x u - x) ^ 2) =
      (fun u => if u < threshold spacing x then (upper spacing x - x) ^ 2
        else (lower spacing x - x) ^ 2) := by
    funext u
    unfold scalar
    split_ifs <;> rfl
  rw [he]
  refine ⟨hi, ?_⟩
  rw [hm, add_comm]
  exact scalar_weighted_variance_le hs x

lemma gridIndex_unclamped (width : ℕ) (spacing x u : ℝ)
    (hcap : ⌊x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2⌋₊ + 1 ≤ 2 ^ width - 1) :
    (gridIndex width spacing x u).val =
      ⌊x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2⌋₊ +
        if u < Int.fract (x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2) then 1 else 0 := by
  dsimp only [gridIndex]
  apply min_eq_left
  split_ifs <;> omega

lemma gridIndex_reconstruction (width : ℕ) {spacing : ℝ} (hs : spacing ≠ 0) (x u : ℝ)
    (h0 : 0 ≤ x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2)
    (hcap : ⌊x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2⌋₊ + 1 ≤ 2 ^ width - 1) :
    spacing * (((gridIndex width spacing x u).val : ℝ) - ((2 ^ width - 1 : ℕ) : ℝ) / 2) =
      scalar spacing (x + spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2)) u -
        spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2) := by
  let c : ℝ := ((2 ^ width - 1 : ℕ) : ℝ) / 2
  have h0' : 0 ≤ x / spacing + c := h0
  have ht : (x + spacing * c) / spacing = x / spacing + c := by
    field_simp
  have hth : threshold spacing (x + spacing * c) = Int.fract (x / spacing + c) := by
    unfold threshold
    rw [ht]
  rw [gridIndex_unclamped width spacing x u hcap, Nat.cast_add]
  change spacing * ((⌊x / spacing + c⌋₊ : ℝ) +
    ((if u < Int.fract (x / spacing + c) then 1 else 0 : ℕ) : ℝ) - c) =
      scalar spacing (x + spacing * c) u - spacing * c
  by_cases hu : u < Int.fract (x / spacing + c)
  · have hu' : u < threshold spacing (x + spacing * c) := by rw [hth]; exact hu
    rw [ite_eq_left hu, scalar, ite_eq_left hu']
    unfold upper lower
    rw [ht, natCast_floor_eq_intCast_floor h0']
    simp only [Nat.cast_one]
    ring
  · have hu' : ¬u < threshold spacing (x + spacing * c) := by rw [hth]; exact hu
    rw [ite_eq_right hu, scalar, ite_eq_right hu']
    unfold lower
    rw [ht, natCast_floor_eq_intCast_floor h0']
    simp only [Nat.cast_zero]
    ring

lemma grid_capacity_of_abs (width : ℕ) {spacing : ℝ} (hs : 0 < spacing) (x : ℝ)
    (hx : |x| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    0 ≤ x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2 ∧
      ⌊x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2⌋₊ + 1 ≤ 2 ^ width - 1 := by
  have hxhi : x / spacing ≤ ((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [(abs_le.mp hx).2]
  have hxlo : -(((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1) ≤ x / spacing := by
    apply (le_div_iff₀ hs).mpr
    nlinarith [(abs_le.mp hx).1]
  have h0 : 0 ≤ x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2 := by linarith
  refine ⟨h0, ?_⟩
  have hf := Nat.floor_le h0
  have hb : ((⌊x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) ≤
      ((2 ^ width - 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hb

lemma encoded_scalar_integral (width : ℕ) {spacing : ℝ} (hs : 0 < spacing) (x : ℝ)
    (hx : |x| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    Integrable (fun u => spacing * (((gridIndex width spacing x u).val : ℝ) -
      ((2 ^ width - 1 : ℕ) : ℝ) / 2)) (uniform : Measure ℝ) ∧
    (∫ u, spacing * (((gridIndex width spacing x u).val : ℝ) -
      ((2 ^ width - 1 : ℕ) : ℝ) / 2) ∂(uniform : Measure ℝ)) = x := by
  obtain ⟨h0, hcap⟩ := grid_capacity_of_abs width hs x hx
  let c : ℝ := ((2 ^ width - 1 : ℕ) : ℝ) / 2
  have he (u : ℝ) : spacing * (((gridIndex width spacing x u).val : ℝ) - c) =
      scalar spacing (x + spacing * c) u - spacing * c :=
    gridIndex_reconstruction width hs.ne' x u h0 hcap
  change Integrable (fun u => spacing * (((gridIndex width spacing x u).val : ℝ) - c))
    (uniform : Measure ℝ) ∧
    (∫ u, spacing * (((gridIndex width spacing x u).val : ℝ) - c) ∂(uniform : Measure ℝ)) = x
  simp_rw [he]
  obtain ⟨hi, hm⟩ := scalar_integral hs.ne' (x + spacing * c)
  have hc : Integrable (fun _ : ℝ => spacing * c) (uniform : Measure ℝ) := integrable_const _
  refine ⟨hi.sub hc, ?_⟩
  rw [integral_sub hi hc, hm]
  simp only [integral_const, probReal_univ, one_smul, add_sub_cancel_right]

lemma encoded_scalar_variance (width : ℕ) {spacing : ℝ} (hs : 0 < spacing) (x : ℝ)
    (hx : |x| ≤ spacing * (((2 ^ width - 1 : ℕ) : ℝ) / 2 - 1)) :
    Integrable (fun u => (spacing * (((gridIndex width spacing x u).val : ℝ) -
      ((2 ^ width - 1 : ℕ) : ℝ) / 2) - x) ^ 2) (uniform : Measure ℝ) ∧
    (∫ u, (spacing * (((gridIndex width spacing x u).val : ℝ) -
      ((2 ^ width - 1 : ℕ) : ℝ) / 2) - x) ^ 2 ∂(uniform : Measure ℝ)) ≤ spacing ^ 2 / 4 := by
  obtain ⟨h0, hcap⟩ := grid_capacity_of_abs width hs x hx
  let c : ℝ := ((2 ^ width - 1 : ℕ) : ℝ) / 2
  have he (u : ℝ) : (spacing * (((gridIndex width spacing x u).val : ℝ) - c) - x) ^ 2 =
      (scalar spacing (x + spacing * c) u - (x + spacing * c)) ^ 2 := by
    rw [gridIndex_reconstruction width hs.ne' x u h0 hcap]
    congr 1
    ring
  change Integrable (fun u => (spacing * (((gridIndex width spacing x u).val : ℝ) - c) - x) ^ 2)
    (uniform : Measure ℝ) ∧
    (∫ u, (spacing * (((gridIndex width spacing x u).val : ℝ) - c) - x) ^ 2
      ∂(uniform : Measure ℝ)) ≤ spacing ^ 2 / 4
  simp_rw [he]
  exact scalar_integral_variance hs.ne' (x + spacing * c)

lemma measurable_scalar (spacing : ℝ) :
    Measurable (fun z : ℝ × ℝ => scalar spacing z.1 z.2) := by
  unfold scalar threshold upper lower
  apply Measurable.ite (measurableSet_lt measurable_snd (measurable_fst.div_const spacing).fract)
  · fun_prop
  · fun_prop

lemma measurable_gridIndex (width : ℕ) (spacing : ℝ) :
    Measurable (fun z : ℝ × ℝ => gridIndex width spacing z.1 z.2) := by
  have he : MeasurableEmbedding (Fin.val : Fin (2 ^ width) → ℕ) :=
    ⟨Fin.val_injective, measurable_of_countable _, fun _ _ => (Set.to_countable _).measurableSet⟩
  apply he.measurable_comp_iff.mp
  change Measurable (fun z : ℝ × ℝ =>
    min (⌊z.1 / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2⌋₊ +
      if z.2 < Int.fract (z.1 / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2) then 1 else 0)
      (2 ^ width - 1))
  have ht : Measurable (fun z : ℝ × ℝ => z.1 / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2) := by
    fun_prop
  exact (ht.nat_floor.add (Measurable.ite (measurableSet_lt measurable_snd ht.fract)
    measurable_const measurable_const)).min measurable_const

end LongTails.Proofs.DistributedRandomRounding
