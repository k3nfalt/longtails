import LongTails.TemplateDistributed
import LongTails.Algorithms.LocalExtragradientQuantization
import LongTails.Proofs.DistributedQuantization

namespace LongTails.Proofs.LocalExtragradientQuantization

open LongTails.Algorithms.DistributedQuantization
open LongTails.Algorithms.LocalExtragradientQuantization

lemma aggregateCodes_bound {n d width : ℕ} (codes : Fin n → Grid d width) (j : Fin d) :
    aggregateCodes codes j ≤ n * (2 ^ width - 1) := by
  calc
    _ ≤ ∑ _ : Fin n, (2 ^ width - 1) :=
      Finset.sum_le_sum fun i _ => Nat.le_sub_one_of_lt (codes i j).isLt
    _ = _ := by simp

lemma decodeAverage_eq {n d width : ℕ} (spacing : ℝ) (codes : Fin n → Grid d width) :
    decodeAverage n width spacing (aggregateCodes codes) =
      (1 / (n : ℝ)) • ∑ i, reconstruct spacing (codes i) := by
  ext j
  simp only [decodeAverage, aggregateCodes, reconstruct, WithLp.ofLp_toLp,
    PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, Nat.cast_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma quantizedAverage_eq (n d width : ℕ) (spacing : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    quantizedAverage n d width spacing x = (1 / (n : ℝ)) •
      ∑ i, reconstruct spacing (quantize d width spacing (x i)) :=
  decodeAverage_eq spacing _

lemma average_norm_bound {n d : ℕ} (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) {a : ℝ}
    (hx : ∀ i, ‖x i‖ ≤ a) :
    ‖(1 / (n : ℝ)) • ∑ i, x i‖ ≤ a := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))]
  calc
    _ ≤ (1 / (n : ℝ)) * ∑ i, ‖x i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (1 / (n : ℝ)) * ∑ _ : Fin n, a :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hx i) (by positivity)
    _ = a := by simp [hn'.ne']

lemma quantizedAverage_error (n d width : ℕ) (hn : 0 < n)
    (spacing : ℝ) (hspacing : 0 < spacing)
    (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i j, |x i j| ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2) :
    ‖quantizedAverage n d width spacing x - (1 / (n : ℝ)) • ∑ i, x i‖ ≤
      Real.sqrt d * spacing := by
  rw [quantizedAverage_eq, ← smul_sub, ← Finset.sum_sub_distrib]
  apply average_norm_bound hn _
  intro i
  have hb := DistributedQuantization.reconstruction_error d width spacing hspacing (x i) (hx i)
  have hs : (Real.sqrt (d : ℝ) * spacing) ^ 2 = (d : ℝ) * spacing ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hs]
  exact hb

lemma aggregateCodes_lt {n d width : ℕ} (hn : 0 < n)
    (codes : Fin n → Grid d width) (extra : ℕ) (hnextra : n ≤ 2 ^ extra) (j : Fin d) :
    aggregateCodes codes j < 2 ^ (width + extra) := by
  calc
    _ ≤ n * (2 ^ width - 1) := aggregateCodes_bound codes j
    _ < n * 2 ^ width := Nat.mul_lt_mul_of_pos_left (Nat.sub_lt (by positivity) (by decide)) hn
    _ ≤ 2 ^ extra * 2 ^ width := Nat.mul_le_mul_right _ hnextra
    _ = _ := by rw [pow_add, Nat.mul_comm]

lemma packAggregate_exact {n d width : ℕ} (hn : 0 < n)
    (codes : Fin n → Grid d width) (extra : ℕ) (hnextra : n ≤ 2 ^ extra) (j : Fin d) :
    (packAggregate extra codes j).val = aggregateCodes codes j :=
  Nat.mod_eq_of_lt (aggregateCodes_lt hn codes extra hnextra j)

lemma aggregateMessage_length {n d width : ℕ} (extra : ℕ) (codes : Fin n → Grid d width) :
    (aggregateMessage extra codes).length = d * (width + extra) :=
  DistributedQuantization.encode_length _

lemma receiveAggregate_message {n d width : ℕ} (hn : 0 < n)
    (codes : Fin n → Grid d width) (extra : ℕ) (hnextra : n ≤ 2 ^ extra)
    (padding : List Bool) :
    receiveAggregate d width extra (aggregateMessage extra codes ++ padding) = aggregateCodes codes := by
  funext j
  have ht : (aggregateMessage extra codes ++ padding).take (d * (width + extra)) =
      aggregateMessage extra codes := by
    rw [← aggregateMessage_length extra codes]
    simp
  change (decode d (width + extra)
    ((aggregateMessage extra codes ++ padding).take (d * (width + extra))) j).val = _
  rw [ht]
  simp only [aggregateMessage, DistributedQuantization.decode_encode]
  exact packAggregate_exact hn codes extra hnextra j

lemma measurable_quantizedAverage (n d width : ℕ) (spacing : ℝ) :
    Measurable (quantizedAverage n d width spacing) := by
  have hm (i : Fin n) : Measurable (fun x : Fin n → EuclideanSpace ℝ (Fin d) =>
      reconstruct spacing (quantize d width spacing (x i))) :=
    (DistributedQuantization.measurable_reconstruction d width spacing).comp (measurable_pi_apply i)
  have hh := (Finset.measurable_sum Finset.univ (fun i _ => hm i)).const_smul (1 / (n : ℝ))
  change Measurable (fun x : Fin n → EuclideanSpace ℝ (Fin d) => (1 / (n : ℝ)) •
    ∑ i, reconstruct spacing (quantize d width spacing (x i))) at hh
  simpa only [← quantizedAverage_eq] using hh

lemma quantizedAverage_error_of_norm (n d width : ℕ) (hn : 0 < n)
    (spacing : ℝ) (hspacing : 0 < spacing)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (H : ℝ)
    (hx : ∀ i, ‖x i‖ ≤ H) (hrange : H ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2) :
    ‖quantizedAverage n d width spacing x - (1 / (n : ℝ)) • ∑ i, x i‖ ≤
      Real.sqrt d * spacing := by
  apply quantizedAverage_error n d width hn spacing hspacing x
  intro i j
  simpa only [Real.norm_eq_abs] using ((PiLp.norm_apply_le (x i) j).trans (hx i)).trans hrange

lemma naturalMessage_length {d : ℕ} (width : ℕ) (values : Fin d → ℕ) :
    (naturalMessage width values).length = d * width :=
  DistributedQuantization.encode_length _

lemma receiveNaturals_message {d : ℕ} (width : ℕ) (values : Fin d → ℕ)
    (hvalues : ∀ j, values j < 2 ^ width) (padding : List Bool) :
    receiveNaturals d width (naturalMessage width values ++ padding) = values := by
  funext j
  have ht : (naturalMessage width values ++ padding).take (d * width) = naturalMessage width values := by
    rw [← naturalMessage_length width values]
    simp
  change (decode d width ((naturalMessage width values ++ padding).take (d * width)) j).val = _
  rw [ht]
  simp only [naturalMessage, DistributedQuantization.decode_encode, packNaturals]
  exact Nat.mod_eq_of_lt (hvalues j)

lemma naturalMessage_packet_length {d : ℕ} (width : ℕ) (values : Fin d → ℕ) :
    (naturalMessage width values ++ List.replicate DistributedTemplate.clockBits false).length =
      d * width + 64 := by
  rw [List.length_append, naturalMessage_length, List.length_replicate]
  rfl

end LongTails.Proofs.LocalExtragradientQuantization
