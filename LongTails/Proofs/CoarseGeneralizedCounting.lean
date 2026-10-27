import LongTails.Proofs.GeneralizedMixedRate
import LongTails.Proofs.GeneralizedComparison

open Finset

namespace OracleTemplate.CoarseGeneralized

lemma inverse_weight_card_cube {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) :
    (s.card : ℝ) ^ 3 ≤ (∑ i ∈ s, b i ^ 2) * (∑ i ∈ s, 1 / b i) ^ 2 := by
  have hh := GeneralizedAccelerated.weighted_holder_cube s
    (fun i => b i ^ 2) (fun i => 1 / b i) (fun _ => (1 : ℝ))
    (fun i _ => sq_nonneg (b i)) (fun i hi => div_pos zero_lt_one (hb i hi))
    (fun _ _ => zero_le_one) (by
      intro i hi
      have hn := (hb i hi).ne'
      field_simp
      norm_num)
  simpa using hh

lemma large_weight_card {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    {H : ℝ} (hH : 0 < H) (hb : ∀ i ∈ s, Real.sqrt H ≤ b i)
    (he : (∑ i ∈ s, b i ^ 2) ≤ H ^ 2) : (s.card : ℝ) ≤ H := by
  have hh : (s.card : ℝ) * H ≤ ∑ i ∈ s, b i ^ 2 := by
    calc
      _ = ∑ _i ∈ s, H := by simp
      _ ≤ _ := sum_le_sum fun i hi => by
        have hs := Real.sq_sqrt hH.le
        have hp := sq_le_sq₀ (Real.sqrt_nonneg H)
          ((Real.sqrt_nonneg H).trans (hb i hi))
        exact hs ▸ hp.mpr (hb i hi)
  nlinarith

lemma small_weight_card {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    {H C : ℝ} (hH : 0 ≤ H) (hb : ∀ i ∈ s, 0 < b i)
    (he : (∑ i ∈ s, b i ^ 2) ≤ H ^ 2)
    (hi : (∑ i ∈ s, 1 / b i) ≤ C * Real.sqrt H) :
    (s.card : ℝ) ^ 3 ≤ C ^ 2 * H ^ 3 := by
  have hn : 0 ≤ ∑ i ∈ s, 1 / b i := sum_nonneg fun i hi => (div_pos zero_lt_one (hb i hi)).le
  have hsq := pow_le_pow_left₀ hn hi 2
  have hm := mul_le_mul he hsq (sq_nonneg _) (sq_nonneg H)
  have hh := (inverse_weight_card_cube s b hb).trans hm
  rw [mul_pow, Real.sq_sqrt hH] at hh
  nlinarith only [hh]

lemma relative_increment_le_log {A a : ℝ} (hA : 0 < A) (ha : 0 ≤ a) :
    a / (A + a) ≤ Real.log (A + a) - Real.log A := by
  have hp : 0 < A + a := by positivity
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hp hA)
  rw [Real.log_div hp.ne' hA.ne'] at hh
  have he : 1 - ((A + a) / A)⁻¹ = a / (A + a) := by
    field_simp
    ring
  rwa [he] at hh

lemma sum_relative_increment_le_log (A : ℕ → ℝ) {j K : ℕ} (hjK : j ≤ K)
    (hpos : ∀ i ∈ Ico j K, 0 < A i)
    (hmono : ∀ i ∈ Ico j K, A i ≤ A (i + 1)) :
    (∑ i ∈ Ico j K, (A (i + 1) - A i) / A (i + 1)) ≤
      Real.log (A K) - Real.log (A j) := by
  calc
    _ ≤ ∑ i ∈ Ico j K, (Real.log (A (i + 1)) - Real.log (A i)) := by
      apply sum_le_sum
      intro i hi
      have hh := relative_increment_le_log (hpos i hi) (sub_nonneg.mpr (hmono i hi))
      simpa only [add_sub_cancel] using hh
    _ = _ := by
      rw [sum_Ico_eq_sub _ hjK, sum_range_sub (fun i => Real.log (A i)),
        sum_range_sub (fun i => Real.log (A i))]
      ring

lemma weight_relative_growth {b u w : ℝ} (hb : 0 < b) (hu : 1 ≤ u)
    (hw : 0 < w) (he : w * u ^ 2 / (128 * (1 + u)) ≤ b ^ 2) :
    1 / (256 * b) ≤ b / (u * w) := by
  have hup : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hd : 0 < 128 * (1 + u) := by positivity
  have hh := (div_le_iff₀ hd).mp he
  have hm : w * u ≤ 256 * b ^ 2 := by
    have hc : 128 * (1 + u) ≤ 256 * u := by linarith
    have he' := mul_le_mul_of_nonneg_left hc (sq_nonneg b)
    have hh' : u * (w * u) ≤ u * (256 * b ^ 2) := by nlinarith only [hh, he']
    exact (mul_le_mul_iff_right₀ hup).mp hh'
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hm]

lemma weight_initial_floor {b u w : ℝ} (hb : 0 < b) (hu : 0 < u)
    (hnew : b / u ≤ w) (he : w * u ^ 2 / (128 * (1 + u)) ≤ b ^ 2) :
    1 / (128 * (1 + u)) ≤ w := by
  have hd : 0 < 128 * (1 + u) := by positivity
  have hh := (div_le_iff₀ hd).mp he
  have hn := (div_le_iff₀ hu).mp hnew
  have hnm := mul_le_mul_of_nonneg_right hn hu.le
  have hbw : u ≤ b * (128 * (1 + u)) := by
    have hh' : b * u ≤ b * (b * (128 * (1 + u))) := by nlinarith only [hh, hnm]
    exact (mul_le_mul_iff_right₀ hb).mp hh'
  have hwm := mul_le_mul_of_nonneg_right hn hd.le
  apply (div_le_iff₀ hd).mpr
  have hh' : u * 1 ≤ u * (w * (128 * (1 + u))) := by nlinarith only [hbw, hwm]
  exact (mul_le_mul_iff_right₀ hu).mp hh'

lemma small_weight_card_linear {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    {H : ℝ} (hH : 0 ≤ H) (hb : ∀ i ∈ s, 0 < b i)
    (he : (∑ i ∈ s, b i ^ 2) ≤ H ^ 2)
    (hi : (∑ i ∈ s, 1 / b i) ≤ 36352 * Real.sqrt H) :
    (s.card : ℝ) ≤ 2048 * H := by
  have hh := small_weight_card s b hH hb he hi
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg s.card) (by positivity) (by decide : 3 ≠ 0)).mp
  have hp : 0 ≤ H ^ 3 := pow_nonneg hH 3
  calc
    (s.card : ℝ) ^ 3 ≤ 36352 ^ 2 * H ^ 3 := hh
    _ ≤ (2048 * H) ^ 3 := by nlinarith only [hp]

lemma weight_log_window {H u w W : ℝ} (hH : 1 ≤ H) (hu : 1 ≤ u)
    (hw : 1 / (128 * (1 + u)) ≤ w) (hW : 0 < W) (hWupper : W ≤ H ^ 2)
    (hlog : Real.log (u / 2) ≤ 128 * Real.sqrt H) :
    Real.log W - Real.log w ≤ 142 * Real.sqrt H := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hup : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hden : 0 < 128 * (1 + u) := by positivity
  have hlarge := Real.log_le_log hW hWupper
  rw [Real.log_pow] at hlarge
  norm_num at hlarge
  have hsmall := Real.log_le_log (div_pos zero_lt_one hden) hw
  rw [Real.log_div one_ne_zero hden.ne', Real.log_one, zero_sub] at hsmall
  have hbound : Real.log (128 * (1 + u)) ≤ Real.log 512 + Real.log (u / 2) := by
    rw [← Real.log_mul (by norm_num : (512 : ℝ) ≠ 0) (by positivity : u / 2 ≠ 0)]
    exact Real.log_le_log hden (by linarith)
  have h512 : Real.log (512 : ℝ) ≤ 9 := by
    have he : (512 : ℝ) = 2 ^ (9 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hroot : 1 ≤ Real.sqrt H := by
    simpa using Real.sqrt_le_sqrt hH
  have hlogH := GeneralizedAccelerated.log_le_twice_sqrt hHp
  nlinarith only [hlarge, hsmall, hbound, h512, hlog, hlogH, hroot]

lemma inverse_weight_tail (s : Finset ℕ) (b A : ℕ → ℝ) {j K : ℕ}
    (hjK : j ≤ K) (hsub : s ⊆ Ico j K)
    (hpos : ∀ i ∈ Ico j K, 0 < A i)
    (hmono : ∀ i ∈ Ico j K, A i ≤ A (i + 1))
    (hrel : ∀ i ∈ s, 1 / b i ≤ 256 * ((A (i + 1) - A i) / A (i + 1))) :
    (∑ i ∈ s, 1 / b i) ≤ 256 * (Real.log (A K) - Real.log (A j)) := by
  have hn : ∀ i ∈ Ico j K, 0 ≤ (A (i + 1) - A i) / A (i + 1) := by
    intro i hi
    exact div_nonneg (sub_nonneg.mpr (hmono i hi)) ((hpos i hi).le.trans (hmono i hi))
  calc
    _ ≤ ∑ i ∈ s, 256 * ((A (i + 1) - A i) / A (i + 1)) := sum_le_sum hrel
    _ = 256 * ∑ i ∈ s, (A (i + 1) - A i) / A (i + 1) := by rw [mul_sum]
    _ ≤ 256 * ∑ i ∈ Ico j K, (A (i + 1) - A i) / A (i + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum_of_subset_of_nonneg hsub fun i hi _ => hn i hi
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_relative_increment_le_log A hjK hpos hmono)
      (by norm_num)

lemma first_small_card_bound (b : ℕ → ℝ) {H : ℝ} {j K : ℕ}
    (hH : 1 ≤ H)
    (hfirst : ∀ i < j, Real.sqrt H ≤ b i)
    (he : (∑ i ∈ range K, b i ^ 2) ≤ H ^ 2)
    (htail : ((range K).filter (fun i => j < i ∧ b i < Real.sqrt H)).card ≤ 2048 * H) :
    (K : ℝ) ≤ 2050 * H := by
  classical
  let large := (range K).filter (fun i => Real.sqrt H ≤ b i)
  let tail := (range K).filter (fun i => j < i ∧ b i < Real.sqrt H)
  have hlarge : (large.card : ℝ) ≤ H := by
    apply large_weight_card large b (by linarith)
    · intro i hi
      exact (mem_filter.mp hi).2
    · exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => sq_nonneg (b i))).trans he
  have hcover : range K ⊆ large ∪ insert j tail := by
    intro i hi
    by_cases hb : Real.sqrt H ≤ b i
    · exact mem_union_left _ (mem_filter.mpr ⟨hi, hb⟩)
    · apply mem_union_right
      by_cases hij : i = j
      · exact mem_insert.mpr (Or.inl hij)
      · apply mem_insert.mpr
        right
        apply mem_filter.mpr
        refine ⟨hi, ?_, lt_of_not_ge hb⟩
        by_contra h
        have hlt : i < j := by omega
        exact hb (hfirst i hlt)
  have hcard := card_le_card hcover
  have hc := card_union_le large (insert j tail)
  have hi := card_insert_le j tail
  have hh : K ≤ large.card + 1 + tail.card := by simp only [card_range] at hcard; omega
  have hh' : (K : ℝ) ≤ (large.card : ℝ) + 1 + tail.card := by exact_mod_cast hh
  change (tail.card : ℝ) ≤ 2048 * H at htail
  linarith

lemma tail_count_from_weights (b u w : ℕ → ℝ) {H : ℝ} {j K : ℕ}
    (hH : 1 ≤ H) (hj : j < K)
    (hb : ∀ i < K, 0 < b i) (hu : ∀ i < K, 1 ≤ u i)
    (hw : ∀ i ≤ K, 0 ≤ w i)
    (hstep : ∀ i < K, w (i + 1) = w i + b i / u i)
    (hweight : ∀ i < K, w (i + 1) * (u i) ^ 2 / (128 * (1 + u i)) ≤ (b i) ^ 2)
    (hsurplus : Real.log (u j / 2) ≤ 128 * b j) (hsmall : b j ≤ Real.sqrt H)
    (hfinal : w K ≤ H ^ 2) (he : (∑ i ∈ range K, b i ^ 2) ≤ H ^ 2) :
    (((range K).filter (fun i => j < i ∧ b i < Real.sqrt H)).card : ℝ) ≤ 2048 * H := by
  classical
  let s := (range K).filter (fun i => j < i ∧ b i < Real.sqrt H)
  have hup : ∀ i < K, 0 < u i := fun i hi => lt_of_lt_of_le zero_lt_one (hu i hi)
  have hwp : ∀ i, 0 < i → i ≤ K → 0 < w i := by
    intro i hi hiK
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    have hk : k < K := by omega
    rw [show k.succ = k + 1 by omega, hstep k hk]
    exact add_pos_of_nonneg_of_pos (hw k (by omega)) (div_pos (hb k hk) (hup k hk))
  have hfloor : 1 / (128 * (1 + u j)) ≤ w (j + 1) := by
    apply weight_initial_floor (hb j hj) (hup j hj) _ (hweight j hj)
    rw [hstep j hj]
    linarith [hw j hj.le]
  have hwindow := weight_log_window hH (hu j hj) hfloor (hwp K (by omega) le_rfl)
    hfinal (hsurplus.trans (mul_le_mul_of_nonneg_left hsmall (by norm_num)))
  apply small_weight_card_linear s b (by linarith)
  · intro i hi
    exact hb i (mem_range.mp (mem_filter.mp hi).1)
  · exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => sq_nonneg (b i))).trans he
  · have hs : s ⊆ Ico (j + 1) K := by
      intro i hi
      rcases mem_filter.mp hi with ⟨hiK, hji, _⟩
      exact mem_Ico.mpr ⟨by omega, mem_range.mp hiK⟩
    have hm : ∀ i ∈ Ico (j + 1) K, w i ≤ w (i + 1) := by
      intro i hi
      have hiK := (mem_Ico.mp hi).2
      rw [hstep i hiK]
      exact le_add_of_nonneg_right (div_pos (hb i hiK) (hup i hiK)).le
    have hr : ∀ i ∈ s, 1 / b i ≤ 256 * ((w (i + 1) - w i) / w (i + 1)) := by
      intro i hi
      have hiK := mem_range.mp (mem_filter.mp hi).1
      have hg := weight_relative_growth (hb i hiK) (hu i hiK)
        (hwp (i + 1) (by omega) (by omega)) (hweight i hiK)
      have heq : (w (i + 1) - w i) / w (i + 1) = b i / (u i * w (i + 1)) := by
        have hd : w (i + 1) - w i = b i / u i := by rw [hstep i hiK]; ring
        rw [hd, div_div]
      rw [heq]
      have hh := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 256)
      have heq' : 256 * (1 / (256 * b i)) = 1 / b i := by ring
      rwa [heq'] at hh
    have ht := inverse_weight_tail s b w (by omega) hs
      (fun i hi => hwp i (by have := (mem_Ico.mp hi).1; omega) (mem_Ico.mp hi).2.le) hm hr
    have hh := mul_le_mul_of_nonneg_left hwindow (by norm_num : (0 : ℝ) ≤ 256)
    nlinarith only [ht, hh]

lemma trajectory_count (b u w : ℕ → ℝ) {H : ℝ} {K : ℕ}
    (hH : 1 ≤ H) (hb : ∀ i < K, 0 < b i) (hu : ∀ i < K, 1 ≤ u i)
    (hw : ∀ i ≤ K, 0 ≤ w i)
    (hstep : ∀ i < K, w (i + 1) = w i + b i / u i)
    (hweight : ∀ i < K, w (i + 1) * (u i) ^ 2 / (128 * (1 + u i)) ≤ (b i) ^ 2)
    (hsurplus : ∀ i < K, Real.log (u i / 2) ≤ 128 * b i)
    (hfinal : w K ≤ H ^ 2) (he : (∑ i ∈ range K, b i ^ 2) ≤ H ^ 2) :
    (K : ℝ) ≤ 2050 * H := by
  classical
  by_cases hall : ∀ i < K, Real.sqrt H ≤ b i
  · have hh := large_weight_card (range K) b (by linarith : 0 < H)
      (fun i hi => hall i (mem_range.mp hi)) he
    simp only [card_range] at hh
    linarith
  · have hex : ∃ j, j < K ∧ b j < Real.sqrt H := by
      push Not at hall
      exact hall
    let j := Nat.find hex
    have hj : j < K := (Nat.find_spec hex).1
    have hsmall : b j < Real.sqrt H := (Nat.find_spec hex).2
    have hfirst : ∀ i < j, Real.sqrt H ≤ b i := by
      intro i hi
      by_contra h
      have hh : i < K ∧ b i < Real.sqrt H := ⟨by omega, lt_of_not_ge h⟩
      exact Nat.find_min hex hi hh
    apply first_small_card_bound b hH hfirst he
    exact tail_count_from_weights b u w hH hj hb hu hw hstep hweight
      (hsurplus j hj) hsmall.le hfinal he

lemma normalized_weight_bounds {b u w : ℝ} (hb : 0 < b) (hu : 2 ≤ u)
    (hw : 0 ≤ w)
    (he : b ^ 2 = w * u ^ 2 / (128 * (1 + u)) + b * Real.log (u / 2) / 128) :
    w * u ^ 2 / (128 * (1 + u)) ≤ b ^ 2 ∧ Real.log (u / 2) ≤ 128 * b := by
  have hl : 0 ≤ Real.log (u / 2) := Real.log_nonneg (by linarith)
  have ht : 0 ≤ w * u ^ 2 / (128 * (1 + u)) := by positivity
  have hp : 0 ≤ b * Real.log (u / 2) := mul_nonneg hb.le hl
  constructor
  · linarith
  · have hh : b * Real.log (u / 2) ≤ b * (128 * b) := by nlinarith only [he, ht]
    exact (mul_le_mul_iff_right₀ hb).mp hh

lemma energy_sum_bound (energy loss : ℕ → ℝ) {K : ℕ}
    (hstep : ∀ i < K, energy (i + 1) + loss i / 2 ≤ energy i) :
    energy K + (∑ i ∈ range K, loss i) / 2 ≤ energy 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hh := ih (fun i hi => hstep i (by omega))
      have hs := hstep K (by omega)
      rw [sum_range_succ]
      linarith

end OracleTemplate.CoarseGeneralized
