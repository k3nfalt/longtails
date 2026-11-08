import LongTails.Proofs.BirchCausalStates
import LongTails.Proofs.BirchCausalTransport
import LongTails.Proofs.BirchNonEuclideanDelta

namespace LongTails.Proofs.BirchCausalEncoding

open Finset
open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchCausalStates
open LongTails.Proofs.BirchCausalCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta (linearValue_fst_smul linearValue_snd_smul
  linearValue_fst_sum linearValue_snd_sum)

noncomputable def rawBasis (q : ℕ) : LinearValue := (Finsupp.single q 1, 0)
noncomputable def sharpBasis (q : ℕ) : LinearValue := (0, Finsupp.single q 1)
noncomputable def batchMomentum (B : ℕ) : LinearValue :=
  (1 / (B : ℝ)) • ∑ j ∈ range B, rawBasis (1 + j)

noncomputable def rawEval (q : ℕ) : LinearValue →ₗ[ℝ] ℝ :=
  (Finsupp.lapply q).comp (LinearMap.fst ℝ (ℕ →₀ ℝ) (ℕ →₀ ℝ))

lemma rawEval_apply (q : ℕ) (v : LinearValue) : rawEval q v = v.1 q := rfl

lemma batchMomentum_sharp (B : ℕ) : (batchMomentum B).2 = 0 := by
  simp only [batchMomentum, linearValue_snd_smul, linearValue_snd_sum, rawBasis, sum_const_zero, smul_zero]

lemma batchMomentum_raw (B q : ℕ) :
    (batchMomentum B).1 q = if q ∈ (range B).image (fun j => 1 + j) then 1 / (B : ℝ) else 0 := by
  have hi : Function.Injective (fun j : ℕ => 1 + j) := fun a b h => Nat.add_left_cancel h
  simp only [batchMomentum, rawBasis, linearValue_fst_smul, linearValue_fst_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, smul_eq_mul]
  rw [show (∑ j ∈ range B, (Finsupp.single (1 + j) 1 : ℕ →₀ ℝ) q) =
      ∑ x ∈ (range B).image (fun j => 1 + j), (Finsupp.single x 1 : ℕ →₀ ℝ) q from
      (sum_image (f := fun x => (Finsupp.single x 1 : ℕ →₀ ℝ) q)
        (g := fun j => 1 + j) (s := range B) (fun a _ b _ he => hi he)).symm]
  simp only [Finsupp.single_apply, sum_ite_eq', mul_ite, mul_one, mul_zero]

noncomputable def estimator (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (B : ℕ) (raw : ℕ → ℕ) (n : ℕ) : LinearValue :=
  (1 / (B : ℝ)) • rawBasis (raw n) + (1 - 1 / (B : ℝ)) •
    causalState history hpast (1 / (B : ℝ)) (batchMomentum B) (fun q => rawBasis (raw q)) n

lemma causalState_sharp (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (B : ℕ) (raw : ℕ → ℕ) (n : ℕ) :
    (causalState history hpast (1 / (B : ℝ)) (batchMomentum B) (fun q => rawBasis (raw q)) n).2 = 0 := by
  have h := causalState_map history hpast (1 / (B : ℝ)) (batchMomentum B)
    (fun q => rawBasis (raw q)) (LinearMap.snd ℝ (ℕ →₀ ℝ) (ℕ →₀ ℝ)) n
  change _ = causalState history hpast _ (batchMomentum B).2 (fun q => (rawBasis (raw q)).2) n at h
  rw [batchMomentum_sharp] at h
  exact h.trans (causalState_zero history hpast _ n)

lemma estimator_sharp (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (B : ℕ) (raw : ℕ → ℕ) (n : ℕ) : (estimator history hpast B raw n).2 = 0 := by
  simp only [estimator, Prod.snd_add, linearValue_snd_smul, causalState_sharp]
  simp [rawBasis]

lemma causalState_raw_batch (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (B : ℕ) (raw : ℕ → ℕ) (n j : ℕ) (hj : j < B)
    (hsep : ∀ q, q < n → 1 + j ≠ raw q) :
    (causalState history hpast (1 / (B : ℝ)) (batchMomentum B) (fun q => rawBasis (raw q)) n).1 (1 + j) =
      (1 / (B : ℝ)) * initialCoefficient history hpast (1 / (B : ℝ)) n := by
  have h := causalState_map history hpast (1 / (B : ℝ)) (batchMomentum B)
    (fun q => rawBasis (raw q)) (rawEval (1 + j)) n
  simp only [rawEval_apply, batchMomentum_raw] at h
  rw [ite_eq_left (mem_image.mpr ⟨j, mem_range.mpr hj, rfl⟩)] at h
  rw [h]
  trans causalState history hpast (1 / (B : ℝ)) (1 / (B : ℝ)) (fun _ => 0) n
  · apply causalState_congr
    intro q hq
    simp [rawBasis, hsep q hq]
  · exact causalState_constant history hpast _ _ n

lemma estimator_raw_batch (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (B : ℕ) (raw : ℕ → ℕ) (n j : ℕ) (hj : j < B)
    (hsep : ∀ q, q ≤ n → 1 + j ≠ raw q) :
    (estimator history hpast B raw n).1 (1 + j) = initialWeight history hpast B n / B := by
  simp only [estimator, Prod.fst_add, linearValue_fst_smul, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul]
  rw [causalState_raw_batch history hpast B raw n j hj (fun q hq => hsep q hq.le)]
  simp only [rawBasis, Finsupp.single_apply, ite_eq_right (hsep n le_rfl).symm, mul_zero, zero_add,
    initialWeight, estimatorInitial]
  ring

lemma causalState_raw_source (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (B N : ℕ) (raw : ℕ → ℕ) (n q : ℕ) (hn : n < N) (hq : q < N)
    (hinj : Set.InjOn raw (Set.Iio N))
    (hsep : raw q ∉ (range B).image (fun j => 1 + j)) :
    (causalState history hpast (1 / (B : ℝ)) (batchMomentum B) (fun j => rawBasis (raw j)) n).1 (raw q) =
      sourceCoefficient history hpast (1 / (B : ℝ)) q n := by
  have h := causalState_map history hpast (1 / (B : ℝ)) (batchMomentum B)
    (fun j => rawBasis (raw j)) (rawEval (raw q)) n
  simp only [rawEval_apply, batchMomentum_raw, ite_eq_right hsep] at h
  rw [h]
  trans causalState history hpast (1 / (B : ℝ)) 0 (fun j => if j = q then 1 else 0) n
  · apply causalState_congr
    intro j hj
    have he : raw j = raw q ↔ j = q := ⟨fun h => hinj (hj.trans hn) hq h, congrArg raw⟩
    simp only [rawBasis, Finsupp.single_apply, he]
  · exact causalState_source history hpast _ q n

lemma estimator_raw_source (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (B N : ℕ) (raw : ℕ → ℕ) (n q : ℕ) (hn : n < N) (hq : q < N)
    (hinj : Set.InjOn raw (Set.Iio N))
    (hsep : raw q ∉ (range B).image (fun j => 1 + j)) :
    (estimator history hpast B raw n).1 (raw q) = sourceWeight history hpast B n q := by
  simp only [estimator, Prod.fst_add, linearValue_fst_smul, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul]
  rw [causalState_raw_source history hpast B N raw n q hn hq hinj hsep]
  have he : raw n = raw q ↔ n = q := ⟨fun h => hinj hn hq h, congrArg raw⟩
  simp only [rawBasis, Finsupp.single_apply, he, sourceWeight, estimatorSource]
  split_ifs <;> first | omega | ring

lemma query_sum (B N : ℕ) (raw : ℕ → ℕ) (f : ℕ → ℝ)
    (hinj : Set.InjOn raw (Set.Iio N))
    (hsep : ∀ q, q < N → raw q ∉ (range B).image (fun j => 1 + j)) :
    (∑ q ∈ (range B).image (fun j => 1 + j) ∪ (range N).image raw, f q) =
      (∑ j ∈ range B, f (1 + j)) + ∑ q ∈ range N, f (raw q) := by
  have hd : Disjoint ((range B).image (fun j => 1 + j)) ((range N).image raw) := by
    apply disjoint_left.mpr
    intro x hx hr
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
    exact hsep q (mem_range.mp hq) hx
  rw [sum_union hd, sum_image (fun a _ b _ he => Nat.add_left_cancel he),
    sum_image (fun a ha b hb he => hinj (mem_range.mp ha) (mem_range.mp hb) he)]

lemma estimator_mass_encoded (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (B N : ℕ) (raw : ℕ → ℕ) (n : ℕ) (hB : 0 < B) (hn : n < N)
    (hinj : Set.InjOn raw (Set.Iio N))
    (hsep : ∀ q, q < N → raw q ∉ (range B).image (fun j => 1 + j))
    (hmass : initialWeight history hpast B n + ∑ q ∈ range N, sourceWeight history hpast B n q = 1) :
    (∑ q ∈ (range B).image (fun j => 1 + j) ∪ (range N).image raw,
      (estimator history hpast B raw n).1 q) = 1 := by
  rw [query_sum B N raw _ hinj hsep]
  have hb (j : ℕ) (hj : j ∈ range B) : (estimator history hpast B raw n).1 (1 + j) =
      initialWeight history hpast B n / B := by
    apply estimator_raw_batch history hpast B raw n j (mem_range.mp hj)
    intro q hq he
    exact hsep q (hq.trans_lt hn) (mem_image.mpr ⟨j, hj, he⟩)
  have hq (q : ℕ) (hq : q ∈ range N) :=
    estimator_raw_source history hpast B N raw n q hn (mem_range.mp hq) hinj (hsep q (mem_range.mp hq))
  rw [sum_congr rfl hb, sum_congr rfl hq, sum_const, card_range, nsmul_eq_mul]
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hB)
  convert hmass using 1
  field_simp

lemma estimator_noise_encoded (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (B N : ℕ) (raw : ℕ → ℕ) (n : ℕ) (hB : 0 < B) (hn : n < N)
    (hinj : Set.InjOn raw (Set.Iio N))
    (hsep : ∀ q, q < N → raw q ∉ (range B).image (fun j => 1 + j)) :
    (∑ q ∈ (range B).image (fun j => 1 + j) ∪ (range N).image raw,
      (estimator history hpast B raw n).1 q ^ 2) =
      initialWeight history hpast B n ^ 2 / B + ∑ q ∈ range N, sourceWeight history hpast B n q ^ 2 := by
  rw [query_sum B N raw _ hinj hsep]
  have hb (j : ℕ) (hj : j ∈ range B) : (estimator history hpast B raw n).1 (1 + j) =
      initialWeight history hpast B n / B := by
    apply estimator_raw_batch history hpast B raw n j (mem_range.mp hj)
    intro q hq he
    exact hsep q (hq.trans_lt hn) (mem_image.mpr ⟨j, hj, he⟩)
  have hq (q : ℕ) (hq : q ∈ range N) :=
    estimator_raw_source history hpast B N raw n q hn (mem_range.mp hq) hinj (hsep q (mem_range.mp hq))
  rw [sum_congr rfl (fun j hj => congrArg (fun x : ℝ => x ^ 2) (hb j hj)),
    sum_congr rfl (fun q hq' => congrArg (fun x : ℝ => x ^ 2) (hq q hq')),
    sum_const, card_range, nsmul_eq_mul]
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hB)
  congr 1
  field_simp

noncomputable def path (γ : ℝ) (sharp : ℕ → ℕ) (s : Finset ℕ) : LinearValue :=
  γ • ∑ j ∈ s, sharpBasis (sharp j)

lemma path_raw (γ : ℝ) (sharp : ℕ → ℕ) (s : Finset ℕ) : (path γ sharp s).1 = 0 := by
  simp only [path, linearValue_fst_smul, linearValue_fst_sum, sharpBasis, sum_const_zero, smul_zero]

lemma path_sharp (γ : ℝ) (sharp : ℕ → ℕ) (s : Finset ℕ) (N t : ℕ)
    (ht : t < N) (hs : s ⊆ range N) (hinj : Set.InjOn sharp (Set.Iio N)) :
    (path γ sharp s).2 (sharp t) = γ * (if t ∈ s then 1 else 0) := by
  simp only [path, linearValue_snd_smul, linearValue_snd_sum, sharpBasis,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
  congr 1
  have he (j : ℕ) (hj : j ∈ s) : sharp j = sharp t ↔ j = t :=
    ⟨fun h => hinj (mem_range.mp (hs hj)) ht h, congrArg sharp⟩
  calc
    _ = ∑ j ∈ s, (if j = t then (1 : ℝ) else 0) :=
      sum_congr rfl (fun j hj => by simp only [Finsupp.single_apply, he j hj])
    _ = _ := by simp

lemma sourceWeight_later (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n) (B n q : ℕ) (hnq : n < q) :
    sourceWeight history hpast B n q = 0 := by
  have hn : q ∉ history n := fun h => (Nat.not_lt_of_ge hnq.le) (mem_range.mp (hpast n h))
  have hz := source_zero history q (1 / (B : ℝ)) (sourceCoefficient history hpast (1 / (B : ℝ)) q)
    hpast hclosed (sourceCoefficient_rec history hpast (1 / (B : ℝ)) q) n hn
  simp only [sourceWeight, estimatorSource, ite_eq_right (ne_of_gt hnq), hz, mul_zero, add_zero]

end LongTails.Proofs.BirchCausalEncoding
