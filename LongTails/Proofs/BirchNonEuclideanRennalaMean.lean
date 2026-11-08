import LongTails.Proofs.BirchNonEuclideanRennalaBatchAnchor
import LongTails.Proofs.BirchNonEuclideanDelta

namespace LongTails.Proofs.BirchNonEuclideanRennalaMean

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanRennalaAnchor
open LongTails.Proofs.BirchNonEuclideanShared (termSum termSum_extends)
open LongTails.Proofs.BirchNonEuclideanDelta (linearValue_fst_smul linearValue_snd_smul
  linearValue_fst_sum linearValue_snd_sum)

noncomputable def queryMean (B : ℕ) (qs : Finset ℕ) : LinearValue :=
  (1 / (B : ℝ)) • ∑ q ∈ qs, ((Finsupp.single q 1, 0) : LinearValue)

lemma queryMean_direction (B : ℕ) (qs : Finset ℕ) : (queryMean B qs).2 = 0 := by
  simp only [queryMean, linearValue_snd_smul, linearValue_snd_sum, Finset.sum_const_zero, smul_zero]

lemma queryMean_raw (B : ℕ) (qs : Finset ℕ) (q : ℕ) :
    (queryMean B qs).1 q = if q ∈ qs then 1 / (B : ℝ) else 0 := by
  simp only [queryMean, linearValue_fst_smul, linearValue_fst_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, smul_eq_mul, Finsupp.single_apply]
  by_cases hq : q ∈ qs <;> simp [hq]

lemma termSum_queryMean (t : Tuning) (s : CodeState) (B x : ℕ) (terms : List (Coefficient × ℕ))
    (hc : ∀ term ∈ terms, term.1 = .constant (1 / (B : ℝ)))
    (hd : (terms.map Prod.snd).Nodup) (hr : ∀ term ∈ terms, RawRecord t s term.2 x) :
    termSum t s terms = queryMean B (terms.map Prod.snd).toFinset := by
  have he : termSum t s terms =
      ((terms.map Prod.snd).map (fun q => (1 / (B : ℝ)) • ((Finsupp.single q 1, 0) : LinearValue))).sum := by
    unfold termSum
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro term ht
    rw [hc term ht, (hr term ht).vector]
    rfl
  rw [he, ← List.sum_toFinset _ hd]
  exact (Finset.smul_sum).symm

structure MeanWitness (t : Tuning) (s : CodeState) (B e x : ℕ) where
  queries : Finset ℕ
  card : queries.card = B
  included : queries ⊆ (codeSymbolic t s).queries
  points : ∀ q ∈ queries, (codeSymbolic t s).queryPoints q = (codeSymbolic t s).points x
  input : (codeSymbolic t s).sharpInputs e = queryMean B queries

lemma codeSymbolic_beforeNext (t : Tuning) (s : CodeState) :
    LongTails.Proofs.BirchNonEuclideanSymbolic.BeforeNext (codeSymbolic t s) := by
  exact LongTails.Proofs.BirchNonEuclideanSymbolic.symbolic_beforeNext
    { instructions := codeInstructions t s, outputCount := 0, outputWorker := 0, outputPoint := fun _ => 0 }

noncomputable def MeanWitness.mono {t : Tuning} {s s' : CodeState} {B e x : ℕ} (hw : MeanWitness t s B e x)
    (he : CodeExtends s s') (hd : e < (codeSymbolic t s).next) (hx : x < (codeSymbolic t s).next) :
    MeanWitness t s' B e x := by
  refine ⟨hw.queries, hw.card, hw.included.trans (codeExtends_queries t s s' he), ?_, ?_⟩
  · intro q hq
    have hqb := (codeSymbolic_beforeNext t s).1 q (hw.included hq)
    rw [(codeExtends_symbolic t s s' he q hqb).2.2.1,
      (codeExtends_symbolic t s s' he x hx).1, hw.points q hq]
  · rw [(codeExtends_symbolic t s s' he e hd).2.2.2, hw.input]

noncomputable def meanWitnessOfTerms (t : Tuning) (s : CodeState) (B e x : ℕ) (terms : List (Coefficient × ℕ))
    (hl : terms.length = B) (hc : ∀ term ∈ terms, term.1 = .constant (1 / (B : ℝ)))
    (hd : (terms.map Prod.snd).Nodup) (hr : ∀ term ∈ terms, RawRecord t s term.2 x)
    (hi : (codeSymbolic t s).sharpInputs e = termSum t s terms) : MeanWitness t s B e x := by
  refine ⟨(terms.map Prod.snd).toFinset, ?_, ?_, ?_, hi.trans (termSum_queryMean t s B x terms hc hd hr)⟩
  · rw [List.toFinset_card_of_nodup hd, List.length_map, hl]
  · intro q hq
    obtain ⟨term, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact (hr term ht).query
  · intro q hq
    obtain ⟨term, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact (hr term ht).point

lemma MeanWitness.estimator {t : Tuning} {s : CodeState} {B e x : ℕ}
    (hw : MeanWitness t s B e x) (hB : 0 < B) :
    ((codeSymbolic t s).sharpInputs e).2 = 0 ∧
      (∑ q ∈ (codeSymbolic t s).queries, ((codeSymbolic t s).sharpInputs e).1 q) = 1 ∧
      (∑ q ∈ (codeSymbolic t s).queries, ((codeSymbolic t s).sharpInputs e).1 q ^ 2) = 1 / (B : ℝ) := by
  rw [hw.input]
  refine ⟨queryMean_direction B hw.queries, ?_, ?_⟩
  · simp only [queryMean_raw]
    rw [← Finset.sum_subset hw.included (by intro q _ hq; simp [hq])]
    simp only [Finset.sum_ite_mem, Finset.inter_self]
    simp [hw.card, ne_of_gt hB]
  · simp only [queryMean_raw]
    rw [← Finset.sum_subset hw.included (by intro q _ hq; simp [hq])]
    have he : (∑ q ∈ hw.queries, (if q ∈ hw.queries then 1 / (B : ℝ) else 0) ^ 2) =
        (B : ℝ) * (1 / (B : ℝ)) ^ 2 := by
      simp [hw.card]
    rw [he]
    field_simp

lemma MeanWitness.transport_zero {t : Tuning} {s : CodeState} {B e x : ℕ}
    (hw : MeanWitness t s B e x) (η : ℝ) (j : ℕ) :
    (∑ q ∈ (codeSymbolic t s).queries, |((codeSymbolic t s).sharpInputs e).1 q| *
      |(((codeSymbolic t s).queryPoints q).2 j - ((codeSymbolic t s).points x).2 j) / η|) = 0 := by
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q ∈ hw.queries
  · rw [hw.points q hq]
    simp
  · rw [hw.input, queryMean_raw, ite_eq_right hq]
    simp

end LongTails.Proofs.BirchNonEuclideanRennalaMean
