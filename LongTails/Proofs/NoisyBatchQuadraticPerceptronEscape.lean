import LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift
import LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronEscape
open Classical MeasureTheory ProbabilityTheory
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
open scoped RealInnerProductSpace
open LongTails.Setups.NoisyBatchQuadraticPerceptron
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma shifted_imbalance_identity (c a z : E) (v η : ℝ) :
    (v + η * ⟪a, c⟫) ^ 2 - ‖c + (η * v) • a - z‖ ^ 2 =
      v ^ 2 - ‖c - z‖ ^ 2 + 2 * η * v * ⟪a, z⟫ +
        η ^ 2 * (⟪a, c⟫ ^ 2 - v ^ 2 * ‖a‖ ^ 2) := by
  have hi : ⟪c - z, a⟫ = ⟪a, c⟫ - ⟪a, z⟫ := by
    rw [real_inner_comm, inner_sub_right]
  rw [show c + (η * v) • a - z = (c - z) + (η * v) • a by abel,
    norm_add_sq_real, norm_smul, real_inner_smul_right, hi,
    mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma shifted_imbalance_step_le (c a z : E) (v η : ℝ)
    (hη : 0 ≤ η) (hv : 0 ≤ v)
    (htarget : η * v * ‖a‖ ^ 2 ≤ 2 * ⟪a, z⟫) :
    v ^ 2 - ‖c - z‖ ^ 2 ≤
      (v + η * ⟪a, c⟫) ^ 2 - ‖c + (η * v) • a - z‖ ^ 2 := by
  rw [shifted_imbalance_identity]
  have h := mul_le_mul_of_nonneg_left htarget (show 0 ≤ η * v by positivity)
  nlinarith [sq_nonneg (η * ⟪a, c⟫)]

noncomputable def selectedSet {P : Public} (data : Data P) (c : Features P.dimension) (v : ℝ) :=
  Finset.univ.filter (fun i => v * ⟪data i, c⟫ ≤ 0)
noncomputable def selectedFraction {P : Public} (data : Data P) (c : Features P.dimension) (v : ℝ) : ℝ :=
  ((selectedSet data c v).card : ℝ) / P.count
lemma selected_eq_sum (P : Public) (data : Data P) (c : Features P.dimension) (v : ℝ) :
    selected data c v = (P.count : ℝ)⁻¹ • ∑ i ∈ selectedSet data c v, data i := by
  simp [selected, selectedSet, Finset.sum_filter]
lemma selectedFraction_bounds (P : Public) (data : Data P) (c : Features P.dimension) (v : ℝ) :
    0 ≤ selectedFraction data c v ∧ selectedFraction data c v ≤ 1 := by
  have hn : (0 : ℝ) < P.count := by positivity
  constructor
  · unfold selectedFraction; positivity
  · rw [selectedFraction, div_le_one hn]
    have hc := Finset.card_le_card (Finset.filter_subset (fun i => v * ⟪data i, c⟫ ≤ 0)
      (Finset.univ : Finset (Fin P.count)))
    simpa only [selectedSet, Finset.card_univ, Fintype.card_fin, Nat.cast_le] using hc
lemma selected_norm_fraction (P : Public) (data : Data P) (c : Features P.dimension) (v : ℝ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    ‖selected data c v‖ ≤ selectedFraction data c v * P.radius := by
  rw [selected_eq_sum, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : ‖∑ i ∈ selectedSet data c v, data i‖ ≤ (selectedSet data c v).card * P.radius := by
    calc
      _ ≤ ∑ i ∈ selectedSet data c v, ‖data i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ selectedSet data c v, P.radius := Finset.sum_le_sum fun i _ => hR i
      _ = _ := by simp
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ (P.count : ℝ)⁻¹ by positivity)
  simpa only [selectedFraction, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hb
lemma selected_inner_fraction (P : Public) (data : Data P) (c z : Features P.dimension)
    (v a : ℝ) (ha : ∀ i, a ≤ ⟪data i, z⟫) :
    selectedFraction data c v * a ≤ ⟪selected data c v, z⟫ := by
  rw [selected_eq_sum, real_inner_smul_left, sum_inner]
  have hs : (selectedSet data c v).card * a ≤ ∑ i ∈ selectedSet data c v, ⟪data i, z⟫ := by
    calc
      _ = ∑ _i ∈ selectedSet data c v, a := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => ha i
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ (P.count : ℝ)⁻¹ by positivity)
  simpa only [selectedFraction, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hb
lemma selectedFraction_lower (P : Public) (data : Data P) (c : Features P.dimension) (v : ℝ)
    (hwrong : ∃ i, v * ⟪data i, c⟫ ≤ 0) :
    (P.count : ℝ)⁻¹ ≤ selectedFraction data c v := by
  obtain ⟨i, hi⟩ := hwrong
  have hc : 1 ≤ (selectedSet data c v).card := Finset.card_pos.mpr
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hcr : (1 : ℝ) ≤ (selectedSet data c v).card := by exact_mod_cast hc
  unfold selectedFraction
  simpa only [one_div] using div_le_div_of_nonneg_right hcr (show 0 ≤ (P.count : ℝ) by positivity)
lemma shifted_separator_inner (P : Public) (data : Data P) (c u : Features P.dimension)
    (δ a : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) (hu : ∀ i, δ ≤ ⟪data i, u⟫) (i : Fin P.count) :
    a ≤ ⟪data i, c + (((P.count : ℝ) * negative data c + a) / δ) • u⟫ := by
  have hq := negative_nonneg P data c
  have ht : 0 ≤ ((P.count : ℝ) * negative data c + a) / δ := by positivity
  have hb := mul_le_mul_of_nonneg_left (hu i) ht
  have he : (((P.count : ℝ) * negative data c + a) / δ) * δ =
      (P.count : ℝ) * negative data c + a := div_mul_cancel₀ _ hδ.ne'
  have hc := negative_component P data c i
  rw [inner_add_right, inner_smul_right]
  nlinarith
lemma selected_shifted_imbalance (P : Public) (data : Data P) (c z : Features P.dimension)
    (v V η : ℝ) (hv : 0 ≤ v) (hV : v ≤ 2 * V) (hη : 0 ≤ η)
    (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hz : ∀ i, η * V * P.radius ^ 2 ≤ ⟪data i, z⟫) :
    v ^ 2 - ‖c - z‖ ^ 2 ≤
      (v + η * ⟪selected data c v, c⟫) ^ 2 -
        ‖c + (η * v) • selected data c v - z‖ ^ 2 := by
  apply shifted_imbalance_step_le c (selected data c v) z v η hη hv
  have hf := selectedFraction_bounds P data c v
  have hr : 0 ≤ P.radius := (norm_nonneg (data 0)).trans (hR 0)
  have hg := selected_norm_fraction P data c v hR
  have hg2 : ‖selected data c v‖ ^ 2 ≤ selectedFraction data c v * P.radius ^ 2 := by
    have hs : ‖selected data c v‖ ^ 2 ≤ (selectedFraction data c v * P.radius) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (mul_nonneg hf.1 hr) |>.mpr hg
    have hf2 : (selectedFraction data c v) ^ 2 ≤ selectedFraction data c v := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hf2 (sq_nonneg P.radius)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hg2 (mul_nonneg hη hv)
  have h2 := mul_le_mul_of_nonneg_left hV
    (mul_nonneg (mul_nonneg hη hf.1) (sq_nonneg P.radius))
  have h3 := selected_inner_fraction P data c z v (η * V * P.radius ^ 2) hz
  nlinarith
lemma escape_shift_bound (P : Public) (data : Data P) (c : Features P.dimension)
    (V η δ : ℝ) (hV : 0 < V) (hη : 0 ≤ η) (hδ : 0 < δ)
    (hq : negative data c ≤ 4 * η * P.radius ^ 2 * V)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ) :
    0 ≤ ((P.count : ℝ) * negative data c + η * V * P.radius ^ 2) / δ ∧
      ((P.count : ℝ) * negative data c + η * V * P.radius ^ 2) / δ < V / 2 := by
  have hn : (0 : ℝ) ≤ P.count := by positivity
  have hq0 := negative_nonneg P data c
  constructor
  · positivity
  · rw [div_lt_iff₀ hδ]
    have h1 := mul_le_mul_of_nonneg_left hq hn
    have h2 := mul_lt_mul_of_pos_right ht hV
    nlinarith
lemma escape_tuning_bound (n : ℕ+) (R δ : ℝ) (hδ : 0 < δ) (hR : δ ≤ R) :
    2 * (δ / (8 * ((n : ℝ) + 1) * R ^ 2)) * R ^ 2 * (4 * (n : ℝ) + 1) < δ := by
  have hr : 0 < R := hδ.trans_le hR
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have he : 2 * (δ / (8 * ((n : ℝ) + 1) * R ^ 2)) * R ^ 2 * (4 * (n : ℝ) + 1) =
      δ * (4 * (n : ℝ) + 1) / (4 * ((n : ℝ) + 1)) := by field_simp; ring
  rw [he, div_lt_iff₀ (by positivity)]
  nlinarith
lemma selected_forward_bounds (P : Public) (data : Data P) (c z : Features P.dimension)
    (v η : ℝ) (hv : 0 < v) (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hz : ∀ i, 0 ≤ ⟪data i, z⟫)
    (hd : ‖c - z‖ ≤ v) :
    (15 / 16 : ℝ) * v ≤ v + η * ⟪selected data c v, c⟫ ∧
      v + η * ⟪selected data c v, c⟫ ≤ v ∧
      ‖c + (η * v) • selected data c v - z‖ ≤ (17 / 16 : ℝ) * v := by
  have hr : 0 ≤ P.radius := (norm_nonneg (data 0)).trans (hR 0)
  have hg := norm_selected_le P data c v hR
  have hgz := selected_inner_fraction P data c z v 0 hz
  simp only [mul_zero] at hgz
  have hgc := neg_le_of_abs_le (abs_real_inner_le_norm (selected data c v) (c - z))
  rw [inner_sub_right] at hgc
  have hnv := mul_le_mul hg hd (norm_nonneg _) hr
  have hl : -P.radius * v ≤ ⟪selected data c v, c⟫ := by linarith
  have hlη := mul_le_mul_of_nonneg_left hl hη
  have hsm := mul_le_mul_of_nonneg_right hsmall hv.le
  have hn := negative_nonneg P data c
  constructor
  · nlinarith
  constructor
  · rw [selected_inner_pos P data c v hv]
    nlinarith
  · calc
      _ = ‖(c - z) + (η * v) • selected data c v‖ := by congr 1; abel
      _ ≤ ‖c - z‖ + ‖(η * v) • selected data c v‖ := norm_add_le _ _
      _ ≤ v + η * v * P.radius := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hη hv.le)]
        exact add_le_add hd (mul_le_mul_of_nonneg_left hg (mul_nonneg hη hv.le))
      _ ≤ _ := by nlinarith
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma shifted_noise_loss (x z e : E) (v r V ε : ℝ)
    (hV : 0 ≤ V) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 64)
    (hv : |v| ≤ 2 * V) (hx : ‖x - z‖ ≤ (17 / 8 : ℝ) * V)
    (he : ‖e‖ ≤ ε * V) (hr : |r| ≤ ε * V) :
    v ^ 2 - ‖x - z‖ ^ 2 - 9 * ε * V ^ 2 ≤
      (v + r) ^ 2 - ‖x + e - z‖ ^ 2 := by
  have hvr := mul_le_mul hv hr (abs_nonneg r) (by positivity : 0 ≤ 2 * V)
  have hvrlow := neg_abs_le (v * r)
  rw [abs_mul] at hvrlow
  have hxe := (real_inner_le_norm (x - z) e).trans
    (mul_le_mul hx he (norm_nonneg e) (by positivity : 0 ≤ (17 / 8 : ℝ) * V))
  have he2 : ‖e‖ ^ 2 ≤ ε ^ 2 * V ^ 2 := by
    have hh := (sq_le_sq₀ (norm_nonneg e) (mul_nonneg hε hV)).mpr he
    nlinarith
  have hε2 : ε ^ 2 ≤ ε / 64 := by nlinarith
  have hsmall := mul_le_mul_of_nonneg_right hε2 (sq_nonneg V)
  rw [show x + e - z = (x - z) + e by abel, norm_add_sq_real]
  nlinarith [sq_nonneg r, mul_nonneg hε (sq_nonneg V)]
lemma escape_perturbed_step (P : Public) (data : Data P) (c z e : Features P.dimension)
    (v V η ε r : ℝ) (hV : 0 < V) (hvlow : V / 2 ≤ v) (hvhigh : v ≤ 2 * V)
    (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 64)
    (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hz : ∀ i, η * V * P.radius ^ 2 ≤ ⟪data i, z⟫)
    (hd : ‖c - z‖ ≤ v) (he : ‖e‖ ≤ ε * V) (hr : |r| ≤ ε * V) :
    0 < v + η * ⟪selected data c v, c⟫ + r ∧
      v + η * ⟪selected data c v, c⟫ + r ≤ v + ε * V ∧
      v ^ 2 - ‖c - z‖ ^ 2 - 9 * ε * V ^ 2 ≤
        (v + η * ⟪selected data c v, c⟫ + r) ^ 2 -
          ‖c + (η * v) • selected data c v + e - z‖ ^ 2 := by
  have hv : 0 < v := by linarith
  have hz0 (i : Fin P.count) : 0 ≤ ⟪data i, z⟫ := le_trans (by positivity) (hz i)
  have hb := selected_forward_bounds P data c z v η hv hη hsmall hR hz0 hd
  have hrb := abs_le.mp hr
  have hs := mul_le_mul_of_nonneg_right hεsmall hV.le
  have hvd : 0 ≤ v + η * ⟪selected data c v, c⟫ := by linarith [hb.1]
  refine ⟨by linarith [hb.1], by linarith [hb.2.1], ?_⟩
  have hn := shifted_noise_loss (c + (η * v) • selected data c v) z e
    (v + η * ⟪selected data c v, c⟫) r V ε hV.le hε hεsmall
    (by rw [abs_of_nonneg hvd]; exact hb.2.1.trans hvhigh)
    (by nlinarith [hb.2.2]) he hr
  have hm := selected_shifted_imbalance P data c z v V η hv.le hvhigh hη hR hz
  linarith
lemma escape_initial (c z e : E) (V ε r : ℝ) (hV : 0 < V)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 64) (hd : ‖c - z‖ ≤ V / 2)
    (he : ‖e‖ ≤ ε * V) (hr : |r| ≤ ε * V) :
    0 < V + r ∧ V + r ≤ V + ε * V ∧
      (3 / 4 - 11 * ε) * V ^ 2 ≤ (V + r) ^ 2 - ‖c + e - z‖ ^ 2 := by
  have hrb := abs_le.mp hr
  have hs := mul_le_mul_of_nonneg_right hεsmall hV.le
  have hd2 := (sq_le_sq₀ (norm_nonneg (c - z)) (by positivity : 0 ≤ V / 2)).mpr hd
  have hn := shifted_noise_loss c z e V r V ε hV.le hε hεsmall
    (by rw [abs_of_pos hV]; linarith) (by linarith) he hr
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [mul_nonneg hε (sq_nonneg V)]
omit [InnerProductSpace ℝ E] in
lemma escape_invariant_bounds (c z : E) (v V a : ℝ) (hV : 0 < V) (hv : 0 < v)
    (ha : a ≤ 1 / 64) (hvhigh : v ≤ V + a * V)
    (hJ : (3 / 4 - 11 * a) * V ^ 2 ≤ v ^ 2 - ‖c - z‖ ^ 2) :
    V / 2 ≤ v ∧ v ≤ 2 * V ∧ ‖c - z‖ ≤ v := by
  have h1 := mul_le_mul_of_nonneg_right ha hV.le
  have h2 := mul_le_mul_of_nonneg_right ha (sq_nonneg V)
  have hJ0 : V ^ 2 / 4 ≤ v ^ 2 - ‖c - z‖ ^ 2 := by nlinarith [sq_nonneg V]
  constructor
  · nlinarith [sq_nonneg ‖c - z‖]
  constructor
  · linarith
  · nlinarith [norm_nonneg (c - z)]
lemma escape_path_invariant (P : Public) (data : Data P) (z : Features P.dimension)
    (c e : ℕ → Features P.dimension) (v r : ℕ → ℝ) (V η ε : ℝ) (K : ℕ)
    (hV : 0 < V) (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hz : ∀ i, η * V * P.radius ^ 2 ≤ ⟪data i, z⟫)
    (hinit : 0 < v 0 ∧ v 0 ≤ V + ε * V ∧
      (3 / 4 - 11 * ε) * V ^ 2 ≤ (v 0) ^ 2 - ‖c 0 - z‖ ^ 2)
    (hc : ∀ j < K, c (j + 1) = c j + (η * v j) • selected data (c j) (v j) + e j)
    (hv : ∀ j < K, v (j + 1) = v j + η * ⟪selected data (c j) (v j), c j⟫ + r j)
    (he : ∀ j < K, ‖e j‖ ≤ ε * V) (hr : ∀ j < K, |r j| ≤ ε * V) :
    ∀ t ≤ K, 0 < v t ∧ v t ≤ V + ((t + 1 : ℕ) : ℝ) * ε * V ∧
      (3 / 4 - 11 * ((t + 1 : ℕ) : ℝ) * ε) * V ^ 2 ≤ (v t) ^ 2 - ‖c t - z‖ ^ 2 := by
  have hεsmall : ε ≤ 1 / 64 := by
    have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (K + 1 : ℕ) by exact_mod_cast Nat.succ_pos K) hε
    nlinarith
  intro t ht
  induction t with
  | zero => simpa using hinit
  | succ t ih =>
    have htk : t < K := by omega
    have hh := ih htk.le
    have hta : ((t + 1 : ℕ) : ℝ) * ε ≤ 1 / 64 := by
      have hcast : ((t + 1 : ℕ) : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right htk.le 1
      exact (mul_le_mul_of_nonneg_right hcast hε).trans hεtotal
    have hb := escape_invariant_bounds (c t) z (v t) V (((t + 1 : ℕ) : ℝ) * ε) hV hh.1 hta
      hh.2.1 (by nlinarith [hh.2.2])
    have hs := escape_perturbed_step P data (c t) z (e t) (v t) V η ε (r t) hV
      hb.1 hb.2.1 hη hsmall hε hεsmall hR hz hb.2.2 (he t htk) (hr t htk)
    rw [← hc t htk, ← hv t htk] at hs
    refine ⟨hs.1, ?_, ?_⟩
    · simp only [Nat.cast_add, Nat.cast_one] at hh hs ⊢
      nlinarith [hh.2.1, hs.2.1]
    · simp only [Nat.cast_add, Nat.cast_one] at hh hs ⊢
      nlinarith [hh.2.2, hs.2.2, mul_nonneg hε (sq_nonneg V)]
lemma escape_wrong_progress (P : Public) (data : Data P) (c u e : Features P.dimension)
    (v V η δ ε : ℝ) (hV : 0 ≤ V) (hv : V / 2 ≤ v) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hu : ‖u‖ = 1) (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (hwrong : ∃ i, v * ⟪data i, c⟫ ≤ 0) (he : ‖e‖ ≤ ε * V)
    (hε : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4) :
    η * V * δ * (P.count : ℝ)⁻¹ / 4 ≤
      ⟪u, c + (η * v) • selected data c v + e - c⟫ := by
  have hv0 : 0 ≤ v := by linarith
  have hn : 0 ≤ (P.count : ℝ)⁻¹ := by positivity
  have hf := selectedFraction_lower P data c v hwrong
  have hg := selected_inner_fraction P data c u v δ hmargin
  have hfd := mul_le_mul_of_nonneg_right hf hδ
  have hgl : δ * (P.count : ℝ)⁻¹ ≤ ⟪selected data c v, u⟫ := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hgl (mul_nonneg hη hv0)
  have h2 := mul_le_mul_of_nonneg_left hv (mul_nonneg (mul_nonneg hη hδ) hn)
  have hnoise := neg_le_of_abs_le (abs_real_inner_le_norm u e)
  rw [hu, one_mul] at hnoise
  have h3 := mul_le_mul_of_nonneg_right hε hV
  rw [show c + (η * v) • selected data c v + e - c =
      (η * v) • selected data c v + e by abel,
    inner_add_right, real_inner_smul_right, real_inner_comm (selected data c v) u]
  nlinarith
lemma escape_path_not_all_wrong (P : Public) (data : Data P) (z u : Features P.dimension)
    (c e : ℕ → Features P.dimension) (v r : ℕ → ℝ) (V η δ ε : ℝ) (K : ℕ)
    (hV : 0 < V) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (hz : ∀ i, η * V * P.radius ^ 2 ≤ ⟪data i, z⟫)
    (hd0 : ‖c 0 - z‖ ≤ V)
    (hinit : 0 < v 0 ∧ v 0 ≤ V + ε * V ∧
      (3 / 4 - 11 * ε) * V ^ 2 ≤ (v 0) ^ 2 - ‖c 0 - z‖ ^ 2)
    (hc : ∀ j < K, c (j + 1) = c j + (η * v j) • selected data (c j) (v j) + e j)
    (hv : ∀ j < K, v (j + 1) = v j + η * ⟪selected data (c j) (v j), c j⟫ + r j)
    (he : ∀ j < K, ‖e j‖ ≤ ε * V) (hr : ∀ j < K, |r j| ≤ ε * V) :
    ¬∀ j < K, ∃ i, v j * ⟪data i, c j⟫ ≤ 0 := by
  intro hwrong
  have hinv := escape_path_invariant P data z c e v r V η ε K hV hη hsmall hε hεtotal
    hR hz hinit hc hv he hr
  have hb (t : ℕ) (ht : t ≤ K) : V / 2 ≤ v t ∧ v t ≤ 2 * V ∧ ‖c t - z‖ ≤ v t := by
    have hh := hinv t ht
    have hta : ((t + 1 : ℕ) : ℝ) * ε ≤ 1 / 64 := by
      have hcast : ((t + 1 : ℕ) : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right ht 1
      exact (mul_le_mul_of_nonneg_right hcast hε).trans hεtotal
    exact escape_invariant_bounds (c t) z (v t) V (((t + 1 : ℕ) : ℝ) * ε) hV hh.1 hta
      hh.2.1 (by nlinarith [hh.2.2])
  have hstep (j : ℕ) (hj : j < K) : η * V * δ * (P.count : ℝ)⁻¹ / 4 ≤
      ⟪u, c (j + 1) - c j⟫ := by
    rw [hc j hj]
    exact escape_wrong_progress P data (c j) u (e j) (v j) V η δ ε hV.le
      (hb j hj.le).1 hη hδ hu hmargin (hwrong j hj) (he j hj) hεprogress
  have hprog : ∀ t ≤ K, (t : ℝ) * (η * V * δ * (P.count : ℝ)⁻¹ / 4) ≤ ⟪u, c t - c 0⟫ := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have htK : t < K := by omega
      have hh := ih htK.le
      have hs := hstep t htK
      simp only [inner_sub_right, Nat.cast_add, Nat.cast_one] at hh hs ⊢
      nlinarith
  have hfinal := hb K le_rfl
  have hnorm : ‖c K - c 0‖ ≤ 3 * V := by
    calc
      _ = ‖(c K - z) + (z - c 0)‖ := by congr 1; abel
      _ ≤ ‖c K - z‖ + ‖z - c 0‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_sub_rev z (c 0)]; linarith [hfinal.2.1, hfinal.2.2]
  have hupper := real_inner_le_norm u (c K - c 0)
  rw [hu, one_mul] at hupper
  have hn : (P.count : ℝ) ≠ 0 := by positivity
  have hKi := mul_le_mul_of_nonneg_right hK (show 0 ≤ (P.count : ℝ)⁻¹ by positivity)
  have hKe : 16 * (P.count : ℝ) * (P.count : ℝ)⁻¹ = 16 := by field_simp
  rw [hKe] at hKi
  have hlarge := mul_le_mul_of_nonneg_right hKi (show 0 ≤ V / 4 by positivity)
  have hp := hprog K le_rfl
  nlinarith

lemma separates_of_frozen_path (P : Public) (data : Data P) (w : ℕ → Weights P.dimension)
    (K : ℕ) (hfreeze : ∀ j < K, Separates data (w j) → w (j + 1) = w j)
    (t s : ℕ) (hts : t ≤ s) (hsK : s ≤ K) (ht : Separates data (w t)) :
    Separates data (w s) := by
  have hh : ∀ s, t ≤ s → s ≤ K → Separates data (w s) := by
    apply Nat.le_induction
    · exact fun _ => ht
    · intro j _ ih hjK
      have hprev := ih (by omega)
      rw [hfreeze j (by omega) hprev]
      exact hprev
  exact hh s hts hsK
lemma frozen_escape_path_separates (P : Public) (data : Data P) (z u : Features P.dimension)
    (w e : ℕ → Weights P.dimension) (V η δ ε : ℝ) (K : ℕ)
    (hV : 0 < V) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (hz : ∀ i, η * V * P.radius ^ 2 ≤ ⟪data i, z⟫)
    (hd0 : ‖(w 0).ofLp.1 - z‖ ≤ V)
    (hinit : 0 < (w 0).ofLp.2 ∧ (w 0).ofLp.2 ≤ V + ε * V ∧
      (3 / 4 - 11 * ε) * V ^ 2 ≤ ((w 0).ofLp.2) ^ 2 - ‖(w 0).ofLp.1 - z‖ ^ 2)
    (hstep : ∀ j < K, w (j + 1) = if Separates data (w j) then w j else
      WithLp.toLp 2 ((w j).ofLp.1 + (η * (w j).ofLp.2) • selected data (w j).ofLp.1 (w j).ofLp.2,
        (w j).ofLp.2 + η * ⟪selected data (w j).ofLp.1 (w j).ofLp.2, (w j).ofLp.1⟫) + e j)
    (he : ∀ j < K, ‖e j‖ ≤ ε * V) : Separates data (w K) := by
  by_contra hn
  have hf (j : ℕ) (hj : j < K) (hs : Separates data (w j)) : w (j + 1) = w j := by
    rw [hstep j hj, ite_eq_left hs]
  have hwrong (j : ℕ) (hj : j ≤ K) : ¬Separates data (w j) := by
    intro hs
    exact hn (separates_of_frozen_path P data w K hf j K hj le_rfl hs)
  let c := fun j => (w j).ofLp.1
  let v := fun j => (w j).ofLp.2
  let ec := fun j => (e j).ofLp.1
  let rv := fun j => (e j).ofLp.2
  have hc (j : ℕ) (hj : j < K) : c (j + 1) = c j + (η * v j) • selected data (c j) (v j) + ec j := by
    dsimp only [c, v, ec]
    rw [hstep j hj, ite_eq_right (hwrong j hj.le)]
    simp [WithLp.ofLp_add]
  have hv (j : ℕ) (hj : j < K) : v (j + 1) = v j + η * ⟪selected data (c j) (v j), c j⟫ + rv j := by
    dsimp only [c, v, rv]
    rw [hstep j hj, ite_eq_right (hwrong j hj.le)]
    simp [WithLp.ofLp_add]
  have hec (j : ℕ) (hj : j < K) : ‖ec j‖ ≤ ε * V := (WithLp.norm_fst_le _ (e j)).trans (he j hj)
  have hrv (j : ℕ) (hj : j < K) : |rv j| ≤ ε * V := by
    exact (WithLp.norm_snd_le _ (e j)).trans (he j hj)
  apply escape_path_not_all_wrong P data z u c ec v rv V η δ ε K hV hη hδ hsmall hε
    hεtotal hεprogress hK hR hu hmargin hz hd0 hinit hc hv hec hrv
  intro j hj
  have hh := hwrong j hj.le
  simpa only [Separates, not_forall, not_lt] using hh
lemma actual_batch_frozen_recurrence (P : Public) (data : Data P) (η : ℝ)
    (ω : P.noise.Ω) (t j : ℕ) :
    let w := (LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution.trajectory P data η ω
      ((P.count : ℕ) * (t + j))).point
    (LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution.trajectory P data η ω
      ((P.count : ℕ) * (t + (j + 1)))).point =
      if Separates data w then w else
        WithLp.toLp 2 (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
          w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) +
          P.noiseScale • P.noise.sample (t + j) ω := by
  dsimp only
  rw [← Nat.add_assoc, LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution.batch_recurrence]
  split_ifs with hs
  · rfl
  · rw [LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.deterministic_proposal]
lemma frozen_escape_from_base (P : Public) (data : Data P) (c u : Features P.dimension)
    (w e : ℕ → Weights P.dimension) (e0 : Weights P.dimension) (V η δ ε : ℝ) (K : ℕ)
    (hV : 0 < V) (hη : 0 ≤ η) (hδ : 0 < δ)
    (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (hq : negative data c ≤ 4 * η * P.radius ^ 2 * V)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hw0 : w 0 = WithLp.toLp 2 (c, V) + e0) (he0 : ‖e0‖ ≤ ε * V)
    (hstep : ∀ j < K, w (j + 1) = if Separates data (w j) then w j else
      WithLp.toLp 2 ((w j).ofLp.1 + (η * (w j).ofLp.2) • selected data (w j).ofLp.1 (w j).ofLp.2,
        (w j).ofLp.2 + η * ⟪selected data (w j).ofLp.1 (w j).ofLp.2, (w j).ofLp.1⟫) + e j)
    (he : ∀ j < K, ‖e j‖ ≤ ε * V) : Separates data (w K) := by
  let a := ((P.count : ℝ) * negative data c + η * V * P.radius ^ 2) / δ
  let z := c + a • u
  have ha : 0 ≤ a ∧ a < V / 2 := escape_shift_bound P data c V η δ hV hη hδ hq ht
  have hdist : ‖c - z‖ = a := by
    rw [show c - z = -(a • u) by dsimp [z]; abel, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha.1, hu, mul_one]
  have hz (i : Fin P.count) : η * V * P.radius ^ 2 ≤ ⟪data i, z⟫ :=
    shifted_separator_inner P data c u δ (η * V * P.radius ^ 2) hδ (by positivity) hmargin i
  have hεsmall : ε ≤ 1 / 64 := by
    have hh := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ (K + 1 : ℕ) by exact_mod_cast Nat.succ_pos K) hε
    nlinarith
  have hec : ‖e0.ofLp.1‖ ≤ ε * V := (WithLp.norm_fst_le _ e0).trans he0
  have her : |e0.ofLp.2| ≤ ε * V := (WithLp.norm_snd_le _ e0).trans he0
  have hi := escape_initial c z e0.ofLp.1 V ε e0.ofLp.2 hV hε hεsmall
    (hdist.trans_le ha.2.le) hec her
  have hcoords : (w 0).ofLp = (c + e0.ofLp.1, V + e0.ofLp.2) := by
    rw [hw0, WithLp.ofLp_add]
    rfl
  have hd0 : ‖(w 0).ofLp.1 - z‖ ≤ V := by
    rw [hcoords]
    change ‖c + e0.ofLp.1 - z‖ ≤ V
    have hnorm : ‖c + e0.ofLp.1 - z‖ ≤ ‖c - z‖ + ‖e0.ofLp.1‖ := by
      rw [show c + e0.ofLp.1 - z = (c - z) + e0.ofLp.1 by abel]
      exact norm_add_le _ _
    have hsm := mul_le_mul_of_nonneg_right hεsmall hV.le
    rw [hdist] at hnorm
    linarith [ha.2]
  apply frozen_escape_path_separates P data z u w e V η δ ε K hV hη hδ.le hsmall hε
    hεtotal hεprogress hK hR hu hmargin hz hd0 _ hstep he
  simpa only [hcoords] using hi
lemma escape_trial_tuning (n : ℕ+) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    let K : ℕ := ⌈16 * (n : ℝ) / (η * δ)⌉₊
    let ε : ℝ := 1 / (64 * ((K : ℝ) + 1))
    0 ≤ ε ∧ ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64 ∧
      ε ≤ η * δ * (n : ℝ)⁻¹ / 4 ∧ 16 * (n : ℝ) ≤ (K : ℝ) * η * δ := by
  dsimp only
  let K : ℕ := ⌈16 * (n : ℝ) / (η * δ)⌉₊
  have hn : (0 : ℝ) < n := by positivity
  have hp : 0 < η * δ := mul_pos hη hδ
  have hK : 16 * (n : ℝ) ≤ (K : ℝ) * η * δ := by
    have hh := (div_le_iff₀ hp).mp (Nat.le_ceil (16 * (n : ℝ) / (η * δ)))
    nlinarith
  have hden : 0 < 64 * ((K : ℝ) + 1) := by positivity
  have he : ((K + 1 : ℕ) : ℝ) * (1 / (64 * ((K : ℝ) + 1))) = 1 / 64 := by
    push_cast
    field_simp
  refine ⟨by positivity, he.le, ?_, hK⟩
  rw [div_le_iff₀ hden]
  have hi := mul_le_mul_of_nonneg_right hK (inv_nonneg.mpr hn.le)
  have hei : 16 * (n : ℝ) * (n : ℝ)⁻¹ = 16 := by field_simp
  rw [hei] at hi
  have hpi : 0 ≤ η * δ * (n : ℝ)⁻¹ := by positivity
  nlinarith

lemma separates_neg_iff (P : Public) (data : Data P) (w : Weights P.dimension) :
    Separates data (-w) ↔ Separates data w := by
  simp [Separates, WithLp.ofLp_neg]
lemma proposal_neg (P : Public) (data : Data P) (η : ℝ) (w : Weights P.dimension) :
    WithLp.toLp 2 ((-w).ofLp.1 + (η * (-w).ofLp.2) • selected data (-w).ofLp.1 (-w).ofLp.2,
      (-w).ofLp.2 + η * ⟪selected data (-w).ofLp.1 (-w).ofLp.2, (-w).ofLp.1⟫) =
    -(WithLp.toLp 2 (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
      w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) : Weights P.dimension) := by
  apply WithLp.ofLp_injective
  simp [WithLp.ofLp_neg, LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.selected_reflect,
    neg_smul, add_comm]
lemma reflected_frozen_recurrence (P : Public) (data : Data P) (η : ℝ)
    (w e : ℕ → Weights P.dimension) (K : ℕ)
    (hstep : ∀ j < K, w (j + 1) = if Separates data (w j) then w j else
      WithLp.toLp 2 ((w j).ofLp.1 + (η * (w j).ofLp.2) • selected data (w j).ofLp.1 (w j).ofLp.2,
        (w j).ofLp.2 + η * ⟪selected data (w j).ofLp.1 (w j).ofLp.2, (w j).ofLp.1⟫) + e j) :
    ∀ j < K, -w (j + 1) = if Separates data (-w j) then -w j else
      WithLp.toLp 2 ((-w j).ofLp.1 + (η * (-w j).ofLp.2) • selected data (-w j).ofLp.1 (-w j).ofLp.2,
        (-w j).ofLp.2 + η * ⟪selected data (-w j).ofLp.1 (-w j).ofLp.2, (-w j).ofLp.1⟫) + -e j := by
  intro j hj
  rw [hstep j hj, separates_neg_iff]
  split_ifs with hs
  · rfl
  · rw [proposal_neg, neg_add]
lemma frozen_escape (P : Public) (data : Data P) (u : Features P.dimension)
    (w e : ℕ → Weights P.dimension) (b e0 : Weights P.dimension) (η δ ε : ℝ) (K : ℕ)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hescape : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η b.ofLp.1 b.ofLp.2)
    (hw0 : w 0 = b + e0) (he0 : ‖e0‖ ≤ ε * |b.ofLp.2|)
    (hstep : ∀ j < K, w (j + 1) = if Separates data (w j) then w j else
      WithLp.toLp 2 ((w j).ofLp.1 + (η * (w j).ofLp.2) • selected data (w j).ofLp.1 (w j).ofLp.2,
        (w j).ofLp.2 + η * ⟪selected data (w j).ofLp.1 (w j).ofLp.2, (w j).ofLp.1⟫) + e j)
    (he : ∀ j < K, ‖e j‖ ≤ ε * |b.ofLp.2|) : Separates data (w K) := by
  rcases hescape with ⟨hb, hq⟩ | ⟨hb, hp⟩
  · have hbase : WithLp.toLp 2 (b.ofLp.1, b.ofLp.2) = b := by
      apply WithLp.ofLp_injective
      rfl
    apply frozen_escape_from_base P data b.ofLp.1 u w e e0 b.ofLp.2 η δ ε K hb hη hδ
      hsmall hε hεtotal hεprogress hK hR hu hmargin hq ht
    · rw [hbase]; exact hw0
    · simpa only [abs_of_pos hb] using he0
    · exact hstep
    · simpa only [abs_of_pos hb] using he
  · have hbase : WithLp.toLp 2 (-b.ofLp.1, -b.ofLp.2) = -b := by
      apply WithLp.ofLp_injective
      rfl
    have hw : -w 0 = WithLp.toLp 2 (-b.ofLp.1, -b.ofLp.2) + -e0 := by
      rw [hw0, hbase]
      abel
    have hq : negative data (-b.ofLp.1) ≤ 4 * η * P.radius ^ 2 * (-b.ofLp.2) := by
      rw [negative_neg]
      exact hp
    have hs := frozen_escape_from_base P data (-b.ofLp.1) u (fun j => -w j) (fun j => -e j)
      (-e0) (-b.ofLp.2) η δ ε K (neg_pos.mpr hb) hη hδ hsmall hε hεtotal hεprogress
      hK hR hu hmargin hq ht hw
      (by simpa only [norm_neg, abs_of_neg hb] using he0)
      (reflected_frozen_recurrence P data η w e K hstep)
      (by simpa only [norm_neg, abs_of_neg hb] using he)
    exact (separates_neg_iff P data (w K)).mp hs

open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
lemma batch_current_escape (P : Public) (data : Data P) (u : Features P.dimension)
    (η δ ε : ℝ) (K t : ℕ) (ω : P.noise.Ω)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hσ : 0 ≤ P.noiseScale)
    (hescape : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2)
    (hv : P.noiseScale ≤ |(trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2|)
    (hnoise : ∀ j < K, ‖P.noise.sample (t + j) ω‖ ≤ ε) :
    Separates data (trajectory P data η ω ((P.count : ℕ) * (t + K))).point := by
  apply frozen_escape P data u
    (fun j => (trajectory P data η ω ((P.count : ℕ) * (t + j))).point)
    (fun j => P.noiseScale • P.noise.sample (t + j) ω)
    (trajectory P data η ω ((P.count : ℕ) * t)).point 0 η δ ε K
    hη hδ hsmall hε hεtotal hεprogress hK hR hu hmargin ht hescape
  · simp
  · simp only [norm_zero]
    positivity
  · intro j hj
    simpa only [Nat.add_assoc] using actual_batch_frozen_recurrence P data η ω t j
  · intro j hj
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    calc
      _ ≤ P.noiseScale * ε := mul_le_mul_of_nonneg_left (hnoise j hj) hσ
      _ ≤ ε * |(trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2| := by nlinarith
lemma batch_proposal_escape (P : Public) (data : Data P) (u : Features P.dimension)
    (η δ ε : ℝ) (K t : ℕ) (ω : P.noise.Ω) (b : Weights P.dimension)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hσ : 0 ≤ P.noiseScale)
    (hbase : b = WithLp.toLp 2
      ((trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1 +
        (η * (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2) •
          LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry.selected data
            (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1
            (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2,
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2 + η *
        ⟪LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry.selected data
          (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1
          (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2,
        (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1⟫))
    (hwrong : ¬Separates data (trajectory P data η ω ((P.count : ℕ) * t)).point)
    (hescape : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η b.ofLp.1 b.ofLp.2)
    (hv : P.noiseScale ≤ |b.ofLp.2|)
    (hnoise : ∀ j < K + 1, ‖P.noise.sample (t + j) ω‖ ≤ ε) :
    Separates data (trajectory P data η ω ((P.count : ℕ) * (t + 1 + K))).point := by
  have hn (j : ℕ) (hj : j < K + 1) : ‖P.noiseScale • P.noise.sample (t + j) ω‖ ≤ ε * |b.ofLp.2| := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    have hh := mul_le_mul_of_nonneg_left (hnoise j hj) hσ
    nlinarith
  apply frozen_escape P data u
    (fun j => (trajectory P data η ω ((P.count : ℕ) * (t + 1 + j))).point)
    (fun j => P.noiseScale • P.noise.sample (t + 1 + j) ω)
    b (P.noiseScale • P.noise.sample t ω) η δ ε K
    hη hδ hsmall hε hεtotal hεprogress hK hR hu hmargin ht hescape
  · have hh := actual_batch_frozen_recurrence P data η ω t 0
    simpa only [Nat.add_zero, ite_eq_right hwrong, ← hbase] using hh
  · simpa only [Nat.add_zero] using hn 0 (by omega)
  · intro j hj
    exact actual_batch_frozen_recurrence P data η ω (t + 1) j
  · intro j hj
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hn (j + 1) (by omega)

end LongTails.Proofs.NoisyBatchQuadraticPerceptronEscape
