import LongTails.Algorithms.DashaFloat
import LongTails.Proofs.DashaQuantization
import LongTails.Proofs.AdaptiveReplicaMoments
import Mathlib.Data.Nat.Size

namespace LongTails.Proofs.DashaFloat

open MeasureTheory
open LongTails.Algorithms.DashaFloat

lemma stride_pos (precision : ℕ) (x : ℝ) : 0 < stride precision x := by
  unfold stride
  positivity

lemma stride_bound (precision : ℕ) (x : ℝ) :
    (stride precision x : ℝ) ≤ 1 + |x| / (2 : ℝ) ^ precision := by
  by_cases hlog : Nat.log2 ⌊|x|⌋₊ ≤ precision
  · simp only [stride, exponent, Nat.sub_eq_zero_of_le hlog, pow_zero, Nat.cast_one]
    exact le_add_of_nonneg_right (div_nonneg (abs_nonneg x) (by positivity))
  · have hn : ⌊|x|⌋₊ ≠ 0 := by
      intro hz
      simp [hz] at hlog
    have hp : 2 ^ precision * 2 ^ (Nat.log2 ⌊|x|⌋₊ - precision) ≤ ⌊|x|⌋₊ := by
      calc
        _ = 2 ^ Nat.log2 ⌊|x|⌋₊ := by rw [← pow_add]; congr 1; omega
        _ ≤ _ := Nat.log2_self_le hn
    have hpr : (2 : ℝ) ^ precision * (stride precision x : ℝ) ≤ (⌊|x|⌋₊ : ℝ) := by
      exact_mod_cast hp
    have hf := Nat.floor_le (abs_nonneg x)
    have he : (stride precision x : ℝ) ≤ |x| / (2 : ℝ) ^ precision := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith

lemma scalar_error (precision : ℕ) (x u : ℝ) :
    |(scalarIndex precision x u : ℝ) - x| ≤ stride precision x := by
  have hm := DashaQuantization.magnitude_error (stride precision x) (stride_pos precision x) x u
  unfold scalarIndex mantissa
  dsimp only
  by_cases hx : x < 0
  · simp only [ite_eq_left hx, Int.cast_neg, Int.cast_natCast]
    simp only [abs_of_neg hx] at hm ⊢
    have hab := abs_le.mp hm
    apply abs_le.mpr
    constructor <;> linarith
  · simp only [ite_eq_right hx, Int.cast_natCast]
    simpa only [abs_of_nonneg (le_of_not_gt hx)] using hm

lemma scalar_squared_error (precision : ℕ) (x u : ℝ) :
    ((scalarIndex precision x u : ℝ) - x) ^ 2 ≤
      2 / (4 : ℝ) ^ precision * x ^ 2 + 2 := by
  have he := (scalar_error precision x u).trans (stride_bound precision x)
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr he
  have hp : ((2 : ℝ) ^ precision) ^ 2 = (4 : ℝ) ^ precision := by
    rw [← pow_mul, mul_comm precision 2, pow_mul]
    norm_num
  have haux := sq_nonneg (1 - |x| / (2 : ℝ) ^ precision)
  rw [sq_abs] at hs
  have hpow : (|x| / (2 : ℝ) ^ precision) ^ 2 = x ^ 2 / (4 : ℝ) ^ precision := by
    rw [div_pow, sq_abs, hp]
  calc
    _ ≤ 2 * (|x| / (2 : ℝ) ^ precision) ^ 2 + 2 := by nlinarith only [hs, haux]
    _ = _ := by rw [hpow]; ring

lemma scalar_mean (precision : ℕ) (x : ℝ) :
    (∫ u : ℝ, (scalarIndex precision x u : ℝ)
      ∂(LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ)) = x := by
  by_cases hx : x < 0
  · simp only [scalarIndex, mantissa, hx, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
    rw [integral_neg, DashaQuantization.rounded_magnitude_mean _ (stride_pos precision x) _ (abs_nonneg x),
      abs_of_neg hx]
    ring
  · simp only [scalarIndex, mantissa, hx, ↓reduceIte, Int.cast_natCast]
    rw [DashaQuantization.rounded_magnitude_mean _ (stride_pos precision x) _ (abs_nonneg x),
      abs_of_nonneg (le_of_not_gt hx)]

lemma magnitude_lt_power (x : ℝ) : |x| < (2 : ℝ) ^ (Nat.log2 ⌊|x|⌋₊ + 1) := by
  have hn := Nat.lt_log2_self (n := ⌊|x|⌋₊)
  have hs : (⌊|x|⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log2 ⌊|x|⌋₊ + 1) := by
    exact_mod_cast (show ⌊|x|⌋₊ + 1 ≤ 2 ^ (Nat.log2 ⌊|x|⌋₊ + 1) by omega)
  exact (Nat.lt_floor_add_one |x|).trans_le hs

lemma mantissa_bound (precision : ℕ) (x u : ℝ) : mantissa precision x u ≤ 2 ^ (precision + 1) := by
  have hs : (0 : ℝ) < stride precision x := by exact_mod_cast stride_pos precision x
  have hx : |x| < (2 : ℝ) ^ (precision + 1) * (stride precision x : ℝ) := by
    by_cases hlog : Nat.log2 ⌊|x|⌋₊ ≤ precision
    · have hp : (2 : ℝ) ^ (Nat.log2 ⌊|x|⌋₊ + 1) ≤ (2 : ℝ) ^ (precision + 1) := by gcongr; norm_num
      simp only [stride, exponent, Nat.sub_eq_zero_of_le hlog, pow_zero, Nat.cast_one, mul_one]
      exact (magnitude_lt_power x).trans_le hp
    · have he : (2 : ℝ) ^ (precision + 1) * (stride precision x : ℝ) =
          (2 : ℝ) ^ (Nat.log2 ⌊|x|⌋₊ + 1) := by
        unfold stride exponent
        push_cast
        rw [← pow_add]
        congr 1
        omega
      rw [he]
      exact magnitude_lt_power x
  have hy : |x| / (stride precision x : ℝ) < (2 : ℝ) ^ (precision + 1) :=
    (div_lt_iff₀ hs).mpr hx
  have hf : ⌊|x| / (stride precision x : ℝ)⌋₊ < 2 ^ (precision + 1) :=
    (Nat.floor_lt (div_nonneg (abs_nonneg x) hs.le)).mpr (by exact_mod_cast hy)
  unfold mantissa
  dsimp only
  split_ifs <;> omega

lemma measurable_stride (precision : ℕ) : Measurable (stride precision) :=
  (measurable_of_countable (fun k : ℕ => 2 ^ (Nat.log2 k - precision))).comp
    (Nat.measurable_floor.comp continuous_abs.measurable)

lemma measurable_scalarIndex (precision : ℕ) :
    Measurable (fun z : ℝ × ℝ => scalarIndex precision z.1 z.2) := by
  have hs : Measurable (fun z : ℝ × ℝ => stride precision z.1) :=
    (measurable_stride precision).comp measurable_fst
  have hsR : Measurable (fun z : ℝ × ℝ => (stride precision z.1 : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hs
  have habs : Measurable (fun z : ℝ × ℝ => |z.1|) :=
    continuous_abs.measurable.comp measurable_fst
  have hy := habs.div hsR
  have hk := Nat.measurable_floor.comp hy
  have hkR := (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hk
  have hb : Measurable (fun z : ℝ × ℝ =>
      if z.2 < |z.1| / (stride precision z.1 : ℝ) - (⌊|z.1| / (stride precision z.1 : ℝ)⌋₊ : ℝ)
      then (1 : ℕ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_snd (hy.sub hkR)) measurable_const measurable_const
  have hm := (hk.add hb).mul hs
  have hmZ := (measurable_of_countable (fun k : ℕ => (k : ℤ))).comp hm
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_const) hmZ.neg hmZ

lemma scalar_integrable (precision : ℕ) (x : ℝ) :
    Integrable (fun u : ℝ => (scalarIndex precision x u : ℝ))
      (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) := by
  have hm : Integrable (fun u : ℝ =>
      (((mantissa precision x u * stride precision x : ℕ) : ℝ)))
      (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) := by
    unfold mantissa
    dsimp only
    simp_rw [Nat.cast_mul, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact ((integrable_const _).add (DashaQuantization.uniform_threshold_integrable _)).mul_const _
  by_cases hx : x < 0
  · have hn := hm.neg
    change Integrable (fun u : ℝ => -(((mantissa precision x u * stride precision x : ℕ) : ℝ)))
      (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) at hn
    simpa only [scalarIndex, hx, ↓reduceIte, Int.cast_neg, Int.cast_natCast] using hn
  · simpa only [scalarIndex, hx, ↓reduceIte, Int.cast_natCast] using hm

lemma scalar_variance (precision : ℕ) (x : ℝ) :
    Integrable (fun u : ℝ => ((scalarIndex precision x u : ℝ) - x) ^ 2)
        (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) ∧
      (∫ u : ℝ, ((scalarIndex precision x u : ℝ) - x) ^ 2
        ∂(LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ)) ≤
        2 / (4 : ℝ) ^ precision * x ^ 2 + 2 := by
  have hm : Measurable (fun u : ℝ => (scalarIndex precision x u : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      ((measurable_scalarIndex precision).comp (measurable_const.prodMk measurable_id))
  have hi : Integrable (fun u : ℝ => ((scalarIndex precision x u : ℝ) - x) ^ 2)
      (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) := by
    apply Integrable.of_bound ((hm.sub_const x).pow_const 2).aestronglyMeasurable
      (2 / (4 : ℝ) ^ precision * x ^ 2 + 2)
    exact Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((scalarIndex precision x u : ℝ) - x))]
      exact scalar_squared_error precision x u)
  refine ⟨hi, ?_⟩
  have h := integral_mono hi (integrable_const (2 / (4 : ℝ) ^ precision * x ^ 2 + 2))
    (scalar_squared_error precision x)
  simpa using h

lemma rounded_mean (precision : ℕ) (spacing x : ℝ) (hs : spacing ≠ 0) :
    (∫ u : ℝ, rounded precision spacing x u
      ∂(LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ)) = x := by
  unfold rounded
  rw [integral_const_mul, scalar_mean, mul_div_cancel₀ _ hs]

lemma rounded_squared_error (precision : ℕ) (spacing x u : ℝ) (hs : spacing ≠ 0) :
    (rounded precision spacing x u - x) ^ 2 ≤
      2 / (4 : ℝ) ^ precision * x ^ 2 + 2 * spacing ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (scalar_squared_error precision (x / spacing) u)
    (sq_nonneg spacing)
  have he : rounded precision spacing x u - x =
      spacing * ((scalarIndex precision (x / spacing) u : ℝ) - x / spacing) := by
    unfold rounded
    rw [mul_sub, mul_div_cancel₀ _ hs]
  rw [he, mul_pow]
  have heq : spacing ^ 2 * (2 / (4 : ℝ) ^ precision * (x / spacing) ^ 2 + 2) =
      2 / (4 : ℝ) ^ precision * x ^ 2 + 2 * spacing ^ 2 := by
    field_simp [hs]
  exact h.trans_eq heq

lemma encode_length {precision exponentWidth : ℕ} (p : Packet precision exponentWidth) :
    (encode p).length = precision + exponentWidth + 3 := by
  simp [encode]

lemma decode_encode {precision exponentWidth : ℕ} (p : Packet precision exponentWidth) :
    decode precision exponentWidth (encode p) = p := by
  unfold decode
  rw [dite_eq_left (encode_length p)]
  have h : (fun i : Fin (precision + exponentWidth + 3) =>
      (encode p).get ⟨i.val, (encode_length p).symm ▸ i.isLt⟩) = bitEquiv precision exponentWidth p := by
    funext i
    simp only [encode, List.get_eq_getElem, List.getElem_ofFn]
  rw [h]
  exact (bitEquiv precision exponentWidth).symm_apply_apply p

lemma value_packet (precision exponentWidth : ℕ) (x u : ℝ)
    (he : exponent precision x < 2 ^ exponentWidth) :
    value (packet precision exponentWidth x u) = scalarIndex precision x u := by
  have hm : mantissa precision x u < 2 ^ (precision + 2) := by
    have hb := mantissa_bound precision x u
    have hp : 2 ^ (precision + 1) < 2 ^ (precision + 2) := by
      apply Nat.pow_lt_pow_right (by omega)
      omega
    exact hb.trans_lt hp
  simp only [value, packet, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt he, decide_eq_true_eq,
    scalarIndex, stride]

lemma receive_encode_packet (precision exponentWidth : ℕ) (x u : ℝ)
    (he : exponent precision x < 2 ^ exponentWidth) :
    value (decode precision exponentWidth (encode (packet precision exponentWidth x u))) =
      scalarIndex precision x u := by
  rw [decode_encode, value_packet precision exponentWidth x u he]

lemma exponent_le_of_magnitude (precision B : ℕ) (x : ℝ)
    (hx : |x| < (2 : ℝ) ^ (B + 1)) : exponent precision x ≤ B := by
  have hl : Nat.log2 ⌊|x|⌋₊ ≤ B := by
    by_cases hz : ⌊|x|⌋₊ = 0
    · simp [hz]
    · by_contra h
      have hb : B + 1 ≤ Nat.log2 ⌊|x|⌋₊ := by omega
      have hp : 2 ^ (B + 1) ≤ ⌊|x|⌋₊ := (Nat.le_log2 hz).mp hb
      have hpr : (2 : ℝ) ^ (B + 1) ≤ (⌊|x|⌋₊ : ℝ) := by exact_mod_cast hp
      have hf := Nat.floor_le (abs_nonneg x)
      linarith
  exact (Nat.sub_le _ _).trans hl

lemma rounded_variance (precision : ℕ) (spacing x : ℝ) (hs : spacing ≠ 0) :
    Integrable (fun u : ℝ => (rounded precision spacing x u - x) ^ 2)
        (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) ∧
      (∫ u : ℝ, (rounded precision spacing x u - x) ^ 2
        ∂(LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ)) ≤
        2 / (4 : ℝ) ^ precision * x ^ 2 + 2 * spacing ^ 2 := by
  have hm : Measurable (fun u : ℝ => rounded precision spacing x u) :=
    measurable_const.mul ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      ((measurable_scalarIndex precision).comp (measurable_const.prodMk measurable_id)))
  have hi : Integrable (fun u : ℝ => (rounded precision spacing x u - x) ^ 2)
      (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) := by
    apply Integrable.of_bound ((hm.sub_const x).pow_const 2).aestronglyMeasurable
      (2 / (4 : ℝ) ^ precision * x ^ 2 + 2 * spacing ^ 2)
    exact Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (rounded precision spacing x u - x))]
      exact rounded_squared_error precision spacing x u hs)
  refine ⟨hi, ?_⟩
  have h := integral_mono hi (integrable_const (2 / (4 : ℝ) ^ precision * x ^ 2 + 2 * spacing ^ 2))
    (fun u => rounded_squared_error precision spacing x u hs)
  simpa using h

lemma exponent_geometric_bound (precision A C K : ℕ) (x : ℝ)
    (hx : |x| ≤ (A : ℝ) * (C : ℝ) ^ K) :
    exponent precision x < 2 ^ (Nat.size (Nat.size A + K * Nat.size C)) := by
  have hA : (A : ℝ) ≤ (2 : ℝ) ^ Nat.size A := by
    exact_mod_cast (Nat.lt_size_self A).le
  have hC : (C : ℝ) ≤ (2 : ℝ) ^ Nat.size C := by
    exact_mod_cast (Nat.lt_size_self C).le
  have hp : |x| ≤ (2 : ℝ) ^ (Nat.size A + K * Nat.size C) := by
    calc
      _ ≤ (A : ℝ) * (C : ℝ) ^ K := hx
      _ ≤ (2 : ℝ) ^ Nat.size A * ((2 : ℝ) ^ Nat.size C) ^ K :=
        mul_le_mul hA (pow_le_pow_left₀ (by positivity) hC K) (by positivity) (by positivity)
      _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm (Nat.size C) K]
  have ht : |x| < (2 : ℝ) ^ (Nat.size A + K * Nat.size C + 1) := by
    have hpos : 0 < (2 : ℝ) ^ (Nat.size A + K * Nat.size C) := by positivity
    rw [pow_succ]
    linarith
  exact (exponent_le_of_magnitude precision _ x ht).trans_lt (Nat.lt_size_self _)

lemma rounded_integrable (precision : ℕ) (spacing x : ℝ) :
    Integrable (fun u : ℝ => rounded precision spacing x u)
      (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) :=
  (scalar_integrable precision (x / spacing)).const_mul spacing

lemma rounded_shifted_variance (precision : ℕ) (spacing y x : ℝ) (hs : spacing ≠ 0) :
    Integrable (fun u : ℝ => (rounded precision spacing y u - x) ^ 2)
        (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) ∧
      (∫ u : ℝ, (rounded precision spacing y u - x) ^ 2
        ∂(LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ)) ≤
        (y - x) ^ 2 + 2 / (4 : ℝ) ^ precision * y ^ 2 + 2 * spacing ^ 2 := by
  have hi := (rounded_integrable precision spacing y).sub (integrable_const y)
  change Integrable (fun u : ℝ => rounded precision spacing y u - y)
    (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) at hi
  have hv := rounded_variance precision spacing y hs
  have hzero : (∫ u : ℝ, rounded precision spacing y u - y
      ∂(LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ)) = 0 := by
    rw [integral_sub (rounded_integrable precision spacing y) (integrable_const y),
      rounded_mean precision spacing y hs]
    simp
  have hi2 : Integrable (fun u : ℝ => ‖rounded precision spacing y u - y‖ ^ 2)
      (LongTails.Algorithms.DashaQuantization.unitLaw : Measure ℝ) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hv.1
  have hI := AdaptiveReplicaMoments.shifted_second_moment_integrable (y - x) hi hi2
  have hE := AdaptiveReplicaMoments.shifted_second_moment (y - x) hi hi2 hzero
  have he (u : ℝ) : y - x + (rounded precision spacing y u - y) =
      rounded precision spacing y u - x := by ring
  simp only [he, Real.norm_eq_abs, sq_abs] at hI hE
  refine ⟨hI, ?_⟩
  rw [hE]
  linarith [hv.2]

lemma scalar_abs_bound (precision : ℕ) (x u : ℝ) :
    |(scalarIndex precision x u : ℝ)| ≤ 1 + 2 * |x| := by
  have h := (scalar_error precision x u).trans (stride_bound precision x)
  have hp : (1 : ℝ) ≤ 2 ^ precision := one_le_pow₀ (by norm_num)
  have hd := div_le_self (abs_nonneg x) hp
  have ht : |(scalarIndex precision x u : ℝ)| ≤
      |(scalarIndex precision x u : ℝ) - x| + |x| := by
    simpa using abs_add_le ((scalarIndex precision x u : ℝ) - x) x
  linarith

lemma rounded_abs_bound (precision : ℕ) (ρ x u : ℝ) (hρ : 0 < ρ) :
    |rounded precision ρ x u| ≤ ρ + 2 * |x| := by
  unfold rounded
  rw [abs_mul, abs_of_pos hρ]
  have h := mul_le_mul_of_nonneg_left (scalar_abs_bound precision (x / ρ) u) hρ.le
  rw [abs_div, abs_of_pos hρ] at h
  calc
    _ ≤ ρ * (1 + 2 * (|x| / ρ)) := h
    _ = _ := by field_simp

lemma exponent_real_geometric_bound (precision k K : ℕ) (x A C : ℝ)
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hk : k ≤ K) (hx : |x| ≤ A * C ^ k) :
    exponent precision x < 2 ^ (Nat.size (Nat.size ⌈A⌉₊ + K * Nat.size ⌈C⌉₊)) := by
  apply exponent_geometric_bound
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  calc
    _ ≤ A * C ^ k := hx
    _ ≤ A * C ^ K := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hk) hA
    _ ≤ (⌈A⌉₊ : ℝ) * (⌈C⌉₊ : ℝ) ^ K :=
      mul_le_mul (Nat.le_ceil A) (pow_le_pow_left₀ hC0 (Nat.le_ceil C) K)
        (by positivity) (by positivity)

end LongTails.Proofs.DashaFloat
