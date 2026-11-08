import LongTails.Proofs.BirchCausalEncoding

namespace LongTails.Proofs.BirchCausalCertificate

open Finset
open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchCausalEncoding
open LongTails.Proofs.BirchCausalCoefficients
open LongTails.Proofs.BirchCausalTransport
open LongTails.Proofs.BirchNonEuclideanDelta (linearValue_snd_smul linearValue_snd_sum)

noncomputable def labelIndex (N : ℕ) (label : ℕ → ℕ) (e : ℕ) : ℕ :=
  if h : ∃ i, i < N ∧ label i = e then Classical.choose h else 0

lemma labelIndex_eq (N : ℕ) (label : ℕ → ℕ) (hinj : Set.InjOn label (Set.Iio N))
    (i : ℕ) (hi : i < N) : labelIndex N label (label i) = i := by
  have he : ∃ j, j < N ∧ label j = label i := ⟨i, hi, rfl⟩
  rw [labelIndex, dite_eq_left he]
  exact hinj (Classical.choose_spec he).1 hi (Classical.choose_spec he).2

structure Encoding (a : Program) (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (H K B : ℕ) (η : ℝ)
    (main raw sharp : ℕ → ℕ) : Prop where
  raw_injective : Set.InjOn raw (Set.Iio (K * H))
  sharp_injective : Set.InjOn sharp (Set.Iio (K * H))
  separation : ∀ q, q < K * H → raw q ∉ (range B).image (fun j => 1 + j)
  queries : a.symbolic.queries = (range B).image (fun j => 1 + j) ∪ (range (K * H)).image raw
  sharps : a.symbolic.sharps = (range (K * H)).image sharp
  units : a.symbolic.units = ∅
  input : ∀ n, n < K * H → a.symbolic.sharpInputs (sharp n) = estimator history hpast B raw n
  batch_points : ∀ j, j < B → a.symbolic.queryPoints (1 + j) = 0
  raw_points : ∀ q, q < K * H → a.symbolic.queryPoints (raw q) = path (1 / (H : ℝ) * η) sharp (history q)
  main_points : ∀ k, k ≤ K → a.symbolic.points (main k) = path (1 / (H : ℝ) * η) sharp (range (k * H))
  main_zero : main 0 = 0
  output_count : a.outputCount + 1 = K
  output_indices : ∀ j, a.outputPoint j = main j.val

lemma displacement_path (history : ℕ → Finset ℕ) (hpast : ∀ q, history q ⊆ range q)
    (H N start q t : ℕ) (η : ℝ) (sharp : ℕ → ℕ) (hH : 0 < H) (hη : η ≠ 0)
    (hq : q < N) (ht : t < N) (hstart : start ≤ N) (hinj : Set.InjOn sharp (Set.Iio N)) :
    |((path (1 / (H : ℝ) * η) sharp (history q)).2 (sharp t) -
      (path (1 / (H : ℝ) * η) sharp (range start)).2 (sharp t)) / η| =
      displacement history start q t / H := by
  rw [path_sharp _ _ _ N t ht ((hpast q).trans (range_mono hq.le)) hinj,
    path_sharp _ _ _ N t ht (range_mono hstart) hinj]
  simp only [mem_range]
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hH)
  have he (a b : ℝ) : ((1 / (H : ℝ) * η) * a - (1 / (H : ℝ) * η) * b) / η = (a - b) / H := by
    field_simp
  rw [he, abs_div, abs_of_pos (show (0 : ℝ) < H by exact_mod_cast hH), ← displacement_eq_abs]

lemma initial_displacement (H N start t : ℕ) (η : ℝ) (sharp : ℕ → ℕ)
    (hH : 0 < H) (hη : η ≠ 0) (ht : t < N) (hstart : start ≤ N)
    (hinj : Set.InjOn sharp (Set.Iio N)) :
    |(0 - (path (1 / (H : ℝ) * η) sharp (range start)).2 (sharp t)) / η| =
      (if t < start then 1 else 0) / (H : ℝ) := by
  rw [path_sharp _ _ _ N t ht (range_mono hstart) hinj]
  simp only [mem_range]
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hH)
  have he (a : ℝ) : (0 - (1 / (H : ℝ) * η) * a) / η = -a / H := by field_simp; ring
  rw [he, abs_div, abs_of_pos (show (0 : ℝ) < H by exact_mod_cast hH)]
  split_ifs <;> norm_num

lemma Encoding.transport (a : Program) (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (H K B r : ℕ) (η : ℝ) (main raw sharp : ℕ → ℕ)
    (h : Encoding a history hpast H K B η main raw sharp)
    (hH : 0 < H) (hη : η ≠ 0) (hB : 2 ≤ B) (hr : 4 * r ≤ B)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n)
    (n t : ℕ) (hn : n < K * H) (ht : t < K * H) :
    transportCoefficient a main (fun e => labelIndex (K * H) sharp e / H) η (sharp n) (sharp t) =
      causalTransport history hpast B H n t := by
  have hb := weight_bounds history hpast B r hB hr hrecent hclosed
  have ho : n / H < K := (Nat.div_lt_iff_lt_mul hH).2 hn
  have hs : n / H * H ≤ K * H := Nat.mul_le_mul_right H ho.le
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hH)
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  rw [transportCoefficient, h.queries, h.input n hn, labelIndex_eq _ _ h.sharp_injective n hn,
    h.main_points _ ho.le, query_sum B (K * H) raw _ h.raw_injective h.separation]
  have hbatch (j : ℕ) (hj : j ∈ range B) :
      |(estimator history hpast B raw n).1 (1 + j)| *
        |((a.symbolic.queryPoints (1 + j)).2 (sharp t) -
          (path (1 / (H : ℝ) * η) sharp (range (n / H * H))).2 (sharp t)) / η| =
      (initialWeight history hpast B n / B) * (if t < n / H * H then 1 else 0) / H := by
    rw [estimator_raw_batch history hpast B raw n j (mem_range.mp hj) (fun q hq he =>
      h.separation q (hq.trans_lt hn) (mem_image.mpr ⟨j, hj, he⟩)),
      h.batch_points j (mem_range.mp hj)]
    change |initialWeight history hpast B n / B| *
      |(0 - (path (1 / (H : ℝ) * η) sharp (range (n / H * H))).2 (sharp t)) / η| = _
    rw [abs_of_nonneg (div_nonneg (hb.1 n).1 (by positivity)),
      initial_displacement H (K * H) _ t η sharp hH hη ht hs h.sharp_injective]
    ring
  have hraw (q : ℕ) (hq : q ∈ range (K * H)) :
      |(estimator history hpast B raw n).1 (raw q)| *
        |((a.symbolic.queryPoints (raw q)).2 (sharp t) -
          (path (1 / (H : ℝ) * η) sharp (range (n / H * H))).2 (sharp t)) / η| =
      sourceWeight history hpast B n q * displacement history (n / H * H) q t / H := by
    rw [estimator_raw_source history hpast B (K * H) raw n q hn (mem_range.mp hq)
      h.raw_injective (h.separation q (mem_range.mp hq)), h.raw_points q (mem_range.mp hq),
      abs_of_nonneg (hb.2.1 n q).1,
      displacement_path history hpast H (K * H) _ q t η sharp hH hη (mem_range.mp hq) ht hs h.sharp_injective]
    ring
  rw [sum_congr rfl hbatch, sum_congr rfl hraw, sum_const, card_range, nsmul_eq_mul]
  have hsum : (∑ q ∈ range (K * H), sourceWeight history hpast B n q * displacement history (n / H * H) q t) =
      ∑ q ∈ range (n + 1), sourceWeight history hpast B n q * displacement history (n / H * H) q t := by
    symm
    apply sum_subset (range_mono (show n + 1 ≤ K * H by omega))
    intro q hq hqn
    have hqn' : n < q := by have := mem_range.not.mp hqn; omega
    rw [sourceWeight_later history hpast hclosed B n q hqn', zero_mul]
  rw [← sum_div, hsum, causalTransport, transportMass]
  field_simp

lemma group_filter (H K k : ℕ) (hH : 0 < H) (hk : k < K) :
    (range (K * H)).filter (fun n => n / H = k) = Ico (k * H) ((k + 1) * H) := by
  ext n
  simp only [mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨hn, hd⟩
    constructor
    · rw [← hd]; exact Nat.div_mul_le_self n H
    · apply (Nat.div_lt_iff_lt_mul hH).1
      omega
  · rintro ⟨hl, hu⟩
    have hlow : k ≤ n / H := (Nat.le_div_iff_mul_le hH).2 hl
    have hupp : n / H < k + 1 := (Nat.div_lt_iff_lt_mul hH).2 hu
    exact ⟨hu.trans_le (Nat.mul_le_mul_right H hk), by omega⟩

lemma sharp_sum_filter {E : Type*} [AddCommMonoid E] (H K k : ℕ) (sharp : ℕ → ℕ)
    (hH : 0 < H) (hk : k < K) (hinj : Set.InjOn sharp (Set.Iio (K * H))) (f : ℕ → E) :
    (∑ e ∈ ((range (K * H)).image sharp).filter
      (fun e => labelIndex (K * H) sharp e / H = k), f e) =
      ∑ n ∈ Ico (k * H) ((k + 1) * H), f (sharp n) := by
  rw [sum_filter, sum_image (fun a ha b hb he => hinj (mem_range.mp ha) (mem_range.mp hb) he)]
  calc
    _ = ∑ n ∈ range (K * H), if n / H = k then f (sharp n) else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [labelIndex_eq _ _ hinj n (mem_range.mp hn)]
    _ = _ := by rw [← sum_filter, group_filter H K k hH hk]

lemma Encoding.partition (a : Program) (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (H K B : ℕ) (η : ℝ) (main raw sharp : ℕ → ℕ)
    (h : Encoding a history hpast H K B η main raw sharp) (hH : 0 < H) (k : ℕ) (hk : k < K) :
    (∑ _e ∈ a.symbolic.sharps.filter (fun e => labelIndex (K * H) sharp e / H = k),
      1 / (H : ℝ)) = 1 := by
  rw [h.sharps, sharp_sum_filter H K k sharp hH hk h.sharp_injective]
  simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hc : (k + 1) * H - k * H = H := by rw [add_mul, one_mul, Nat.add_sub_cancel_left]
  rw [hc]
  exact mul_one_div_cancel (by exact_mod_cast (Nat.ne_zero_of_lt hH))

lemma Encoding.chain (a : Program) (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (H K B : ℕ) (η : ℝ) (main raw sharp : ℕ → ℕ)
    (h : Encoding a history hpast H K B η main raw sharp) (hH : 0 < H) (k : ℕ) (hk : k < K) :
    (a.symbolic.points (main (k + 1))).2 = (a.symbolic.points (main k)).2 +
      η • ∑ e ∈ a.symbolic.sharps.filter (fun e => labelIndex (K * H) sharp e / H = k),
        (1 / (H : ℝ)) • Finsupp.single e 1 := by
  rw [h.main_points (k + 1) hk, h.main_points k hk.le, h.sharps,
    sharp_sum_filter H K k sharp hH hk h.sharp_injective]
  simp only [path, linearValue_snd_smul, linearValue_snd_sum, sharpBasis]
  rw [← sum_range_add_sum_Ico (f := fun j => Finsupp.single (sharp j) (1 : ℝ))
    (Nat.mul_le_mul_right H (Nat.le_succ k)), smul_add, ← smul_sum, smul_smul]
  congr 1
  rw [mul_comm η]

lemma Encoding.noise (a : Program) (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (H K B r : ℕ) (η : ℝ) (main raw sharp : ℕ → ℕ)
    (h : Encoding a history hpast H K B η main raw sharp)
    (hH : 0 < H) (hB : 2 ≤ B) (hr : 4 * r ≤ B)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n) :
    (∑ e ∈ a.symbolic.sharps, (1 / (H : ℝ)) *
      ∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q ^ 2) ≤ (K : ℝ) * (1 / (B : ℝ)) := by
  rw [h.sharps, sum_image (fun a ha b hb he => h.sharp_injective (mem_range.mp ha) (mem_range.mp hb) he)]
  calc
    _ ≤ ∑ n ∈ range (K * H), (1 / (H : ℝ)) * (1 / (B : ℝ)) := by
      apply sum_le_sum
      intro n hn
      rw [h.input n (mem_range.mp hn), h.queries, estimator_noise_encoded history hpast B (K * H) raw n
        (by omega) (mem_range.mp hn) h.raw_injective h.separation]
      exact mul_le_mul_of_nonneg_left
        (weight_square_mass history hpast B r hB hr hrecent hclosed n (K * H) (mem_range.mp hn)) (by positivity)
    _ = _ := by
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_mul]
      have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hH)
      field_simp

noncomputable def Encoding.certificate (a : Program) (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (H K B r : ℕ) (η : ℝ) (main raw sharp : ℕ → ℕ)
    (h : Encoding a history hpast H K B η main raw sharp)
    (hH : 0 < H) (hK : 0 < K) (hη : η ≠ 0) (hB : 2 ≤ B) (hr : 4 * r ≤ B)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n) :
    ProgramCertificate a K η ((((max (H - 1) (2 * r + 1) : ℕ) : ℝ) + B) / H) (1 / (B : ℝ)) := by
  have hb := weight_bounds history hpast B r hB hr hrecent hclosed
  refine {
    main := main
    owner := fun e => labelIndex (K * H) sharp e / H
    weight := fun _ => 1 / (H : ℝ)
    positive_horizon := hK
    sharp_only := h.units
    estimator_linear := ?_
    estimator_mass := ?_
    query_linear := ?_
    main_initial := h.main_zero
    main_linear := ?_
    weight_nonneg := fun _ _ => by positivity
    owner_lt := ?_
    partition := h.partition _ _ _ _ _ _ _ _ _ _ hH
    chain := h.chain _ _ _ _ _ _ _ _ _ _ hH
    output_count := h.output_count
    output_indices := h.output_indices
    transport := ?_
    noise := h.noise _ _ _ _ _ _ r _ _ _ _ hH hB hr hrecent hclosed }
  · intro e he
    rw [h.sharps] at he
    obtain ⟨n, hn, rfl⟩ := mem_image.mp he
    rw [h.input n (mem_range.mp hn)]
    exact estimator_sharp history hpast B raw n
  · intro e he
    rw [h.sharps] at he
    obtain ⟨n, hn, rfl⟩ := mem_image.mp he
    rw [h.input n (mem_range.mp hn), h.queries]
    exact estimator_mass_encoded history hpast B (K * H) raw n (by omega) (mem_range.mp hn)
      h.raw_injective h.separation (hb.2.2.1 n (K * H) (mem_range.mp hn))
  · intro q hq
    rw [h.queries] at hq
    rcases mem_union.mp hq with hq | hq
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
      rw [h.batch_points j (mem_range.mp hj)]
      rfl
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
      rw [h.raw_points j (mem_range.mp hj)]
      exact path_raw _ _ _
  · intro k hk
    rw [h.main_points k hk]
    exact path_raw _ _ _
  · intro e he
    rw [h.sharps] at he
    obtain ⟨n, hn, rfl⟩ := mem_image.mp he
    rw [labelIndex_eq _ _ h.sharp_injective n (mem_range.mp hn)]
    exact (Nat.div_lt_iff_lt_mul hH).2 (mem_range.mp hn)
  · intro t ht
    rw [h.sharps] at ht
    obtain ⟨t, htr, rfl⟩ := mem_image.mp ht
    have hinj : Set.InjOn sharp (range (K * H)) := fun a ha b hb he =>
      h.sharp_injective (mem_range.mp ha) (mem_range.mp hb) he
    rw [h.sharps, sum_image hinj]
    have heq (n : ℕ) (hn : n ∈ range (K * H)) :
        (∑ j ∈ (range (K * H)).image sharp,
          transportCoefficient a main (fun e => labelIndex (K * H) sharp e / H) η (sharp n) j) =
        ∑ j ∈ range (K * H), causalTransport history hpast B H n j := by
      rw [sum_image hinj]
      exact sum_congr rfl (fun j hj => h.transport _ _ _ _ _ _ r _ _ _ _ hH hη hB hr hrecent hclosed n j
        (mem_range.mp hn) (mem_range.mp hj))
    have hs := causalTransport_certificate history hpast B H r (K * H) hB hH hr hrecent hclosed t htr
    calc
      _ = ∑ n ∈ range (K * H), (1 / (H : ℝ)) *
          (∑ j ∈ range (K * H), causalTransport history hpast B H n j) * causalTransport history hpast B H n t := by
        apply sum_congr rfl
        intro n hn
        rw [heq n hn, h.transport _ _ _ _ _ _ r _ _ _ _ hH hη hB hr hrecent hclosed n t
          (mem_range.mp hn) (mem_range.mp htr)]
      _ ≤ _ := hs.trans_eq (by field_simp)

end LongTails.Proofs.BirchCausalCertificate
