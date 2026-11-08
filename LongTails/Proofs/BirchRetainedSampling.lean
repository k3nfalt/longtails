import LongTails.Proofs.BirchRetainedCoefficients
import LongTails.Proofs.BirchNonEuclideanCertificate

namespace LongTails.Proofs.BirchRetainedSampling

open Finset
open LongTails.Proofs.BirchRetainedCoefficients

noncomputable def rawRow (s : Finset ℕ) (raw : ℕ → Finset ℕ)
    (mass : ℕ → ℝ) : ℕ →₀ ℝ :=
  ∑ j ∈ s, ∑ q ∈ raw j, Finsupp.single q (mass j / (raw j).card)

lemma rawRow_apply (s : Finset ℕ) (raw : ℕ → Finset ℕ) (mass : ℕ → ℝ)
    (q : ℕ) : rawRow s raw mass q =
      ∑ j ∈ s, if q ∈ raw j then mass j / (raw j).card else 0 := by
  classical
  simp [rawRow, Finsupp.single_apply, eq_comm]

lemma rawRow_at (s : Finset ℕ) (raw : ℕ → Finset ℕ) (mass : ℕ → ℝ)
    (hdisjoint : (s : Set ℕ).PairwiseDisjoint raw)
    (j q : ℕ) (hj : j ∈ s) (hq : q ∈ raw j) :
    rawRow s raw mass q = mass j / (raw j).card := by
  rw [rawRow_apply, sum_eq_single j]
  · simp [hq]
  · intro k hk hkj
    have hn : q ∉ raw k := by
      intro hkq
      exact disjoint_left.mp (hdisjoint hk hj hkj) hkq hq
    simp [hn]
  · simp [hj]

lemma rawRow_outside (s : Finset ℕ) (raw : ℕ → Finset ℕ) (mass : ℕ → ℝ)
    (q : ℕ) (hq : q ∉ s.biUnion raw) : rawRow s raw mass q = 0 := by
  rw [rawRow_apply]
  apply sum_eq_zero
  intro j hj
  have hn : q ∉ raw j := fun h => hq (mem_biUnion.mpr ⟨j, hj, h⟩)
  simp [hn]

lemma rawRow_supported (s queries : Finset ℕ) (raw : ℕ → Finset ℕ)
    (mass : ℕ → ℝ) (hraw : ∀ j ∈ s, raw j ⊆ queries) :
    rawRow s raw mass ∈
      (Finsupp.supported ℝ ℝ (queries : Set ℕ) : Set (ℕ →₀ ℝ)) := by
  apply (Finsupp.mem_supported' ℝ _).mpr
  intro q hq
  apply rawRow_outside
  intro h
  obtain ⟨j, hj, hqj⟩ := mem_biUnion.mp h
  exact hq (hraw j hj hqj)

lemma rawRow_sum {M : Type*} [AddCommMonoid M] (s queries : Finset ℕ)
    (raw : ℕ → Finset ℕ) (mass : ℕ → ℝ) (F : ℝ → ℕ → M)
    (hzero : ∀ q, F 0 q = 0)
    (hdisjoint : (s : Set ℕ).PairwiseDisjoint raw)
    (hraw : ∀ j ∈ s, raw j ⊆ queries) :
    (∑ q ∈ queries, F (rawRow s raw mass q) q) =
      ∑ j ∈ s, ∑ q ∈ raw j, F (mass j / (raw j).card) q := by
  classical
  have hsub : s.biUnion raw ⊆ queries := by
    intro q hq
    obtain ⟨j, hj, hq⟩ := mem_biUnion.mp hq
    exact hraw j hj hq
  rw [← sum_subset hsub (by
    intro q _ hq
    rw [rawRow_outside s raw mass q hq, hzero]), sum_biUnion hdisjoint]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro q hq
  rw [rawRow_at s raw mass hdisjoint j q hj hq]

lemma rawRow_mass (s queries : Finset ℕ) (raw : ℕ → Finset ℕ) (mass : ℕ → ℝ)
    (hdisjoint : (s : Set ℕ).PairwiseDisjoint raw)
    (hraw : ∀ j ∈ s, raw j ⊆ queries)
    (hsize : ∀ j ∈ s, (raw j).Nonempty) :
    (∑ q ∈ queries, rawRow s raw mass q) = ∑ j ∈ s, mass j := by
  rw [rawRow_sum s queries raw mass (fun a _ => a) (fun _ => rfl) hdisjoint hraw]
  apply sum_congr rfl
  intro j hj
  have hb : (0 : ℝ) < (raw j).card := Nat.cast_pos.mpr (card_pos.mpr (hsize j hj))
  simp [mul_div_cancel₀ _ hb.ne']

lemma rawRow_square (s queries : Finset ℕ) (raw : ℕ → Finset ℕ) (mass : ℕ → ℝ)
    (hdisjoint : (s : Set ℕ).PairwiseDisjoint raw)
    (hraw : ∀ j ∈ s, raw j ⊆ queries)
    (hsize : ∀ j ∈ s, (raw j).Nonempty) :
    (∑ q ∈ queries, rawRow s raw mass q ^ 2) =
      ∑ j ∈ s, mass j ^ 2 / (raw j).card := by
  rw [rawRow_sum s queries raw mass (fun a _ => a ^ 2) (by simp) hdisjoint hraw]
  apply sum_congr rfl
  intro j hj
  have hb : (0 : ℝ) < (raw j).card := Nat.cast_pos.mpr (card_pos.mpr (hsize j hj))
  simp only [sum_const, nsmul_eq_mul]
  field_simp

lemma rawRow_square_bound (s queries : Finset ℕ) (raw : ℕ → Finset ℕ)
    (mass β : ℕ → ℝ) (B : ℝ) (hB : 0 < B)
    (hdisjoint : (s : Set ℕ).PairwiseDisjoint raw)
    (hraw : ∀ j ∈ s, raw j ⊆ queries)
    (hsize : ∀ j ∈ s, (raw j).Nonempty)
    (hm : ∀ j ∈ s, 0 ≤ mass j) (hcap : ∀ j ∈ s, mass j ≤ β j)
    (hbatch : ∀ j ∈ s, β j * B ≤ (raw j).card)
    (hmass : ∑ j ∈ s, mass j = 1) :
    (∑ q ∈ queries, rawRow s raw mass q ^ 2) ≤ 1 / B := by
  rw [rawRow_square s queries raw mass hdisjoint hraw hsize]
  apply block_square_mass s mass (fun j => (raw j).card) B
    (fun j hj => Nat.cast_pos.mpr (card_pos.mpr (hsize j hj))) hm _ hmass
  intro j hj
  exact (hcap j hj).trans ((le_div_iff₀ hB).mpr (hbatch j hj))

lemma rawRow_smul {M : Type*} [AddCommGroup M] [Module ℝ M]
    (s queries : Finset ℕ) (raw : ℕ → Finset ℕ) (mass : ℕ → ℝ) (v : ℕ → M)
    (hdisjoint : (s : Set ℕ).PairwiseDisjoint raw)
    (hraw : ∀ j ∈ s, raw j ⊆ queries) :
    (∑ q ∈ queries, rawRow s raw mass q • v q) =
      ∑ j ∈ s, mass j • ((1 / (raw j).card : ℝ) • ∑ q ∈ raw j, v q) := by
  rw [rawRow_sum s queries raw mass (fun a q => a • v q) (by simp) hdisjoint hraw]
  apply sum_congr rfl
  intro j _
  simp [smul_smul, smul_sum, div_eq_mul_inv]

open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanCausality
open LongTails.Proofs.BirchNonEuclideanRecords (sampledQueryPoint)
open LongTails.Proofs.BirchNonEuclideanExecution (queryCount)
open MeasureTheory

lemma collection_noise {Ω : Type} [MeasurableSpace Ω] (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (ho : StochasticGradient p (μ : Measure Ω) f g)
    (regular : DualRegularityWitness p.N p.κ)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (s : Finset ℕ) (raw : ℕ → Finset ℕ) (mass β : ℕ → ℝ) (B : ℝ)
    (hB : 0 < B) (hdisjoint : (s : Set ℕ).PairwiseDisjoint raw)
    (hraw : ∀ j ∈ s, raw j ⊆ a.symbolic.queries)
    (hsize : ∀ j ∈ s, (raw j).Nonempty)
    (hm : ∀ j ∈ s, 0 ≤ mass j) (hcap : ∀ j ∈ s, mass j ≤ β j)
    (hbatch : ∀ j ∈ s, β j * B ≤ (raw j).card)
    (hmass : ∑ j ∈ s, mass j = 1) :
    Integrable (fun ξ => dualNorm p.N (∑ q ∈ a.symbolic.queries,
      rawRow s raw mass q •
        (g (sampledQueryPoint p a lmo g q ξ) (ξ (queryCount (a.instructions.take (q - 1)))) -
          gradient f (sampledQueryPoint p a lmo g q ξ))) ^ 2) (P : Measure (ℕ → Ω)) ∧
    (∫ ξ, dualNorm p.N (∑ q ∈ a.symbolic.queries, rawRow s raw mass q •
      (g (sampledQueryPoint p a lmo g q ξ) (ξ (queryCount (a.instructions.take (q - 1)))) -
        gradient f (sampledQueryPoint p a lmo g q ξ))) ^ 2 ∂(P : Measure (ℕ → Ω))) ≤
      p.κ * p.σ ^ 2 / B := by
  have h := LongTails.Proofs.BirchNonEuclideanCertificate.coefficient_noise
    p a lmo hlmo μ P hiid f g ho regular hR hR0 (rawRow s raw mass)
      (rawRow_supported s a.symbolic.queries raw mass hraw)
  refine ⟨h.1, h.2.trans ?_⟩
  have hκ : 0 ≤ p.κ := (by norm_num : (0 : ℝ) ≤ 1).trans
    (regular.smoothness_lower.trans regular.smoothness_upper)
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
    (rawRow_square_bound s a.symbolic.queries raw mass β B hB hdisjoint hraw
      hsize hm hcap hbatch hmass) (mul_nonneg hκ (sq_nonneg p.σ))

end LongTails.Proofs.BirchRetainedSampling
