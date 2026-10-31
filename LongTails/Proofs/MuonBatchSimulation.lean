import LongTails.Proofs.MuonSimulation
import LongTails.Proofs.SampledQueryPlan

namespace LongTails.Proofs.MuonBatchSimulation

open OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon
open LongTails.Setups.FiniteVarianceSpectralSmooth
open LongTails.Proofs.MuonSimulation

lemma sampledEval_resumeMuonPlan_validating_samples {Ω : Type*} {m n T b k q : ℕ}
    (α η ρ : ℝ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (sources : Fin (q + 1) → Space m n) (i : Fin (q + 1)) (j : Fin (k + 1))
    (sample : Fin b) (acc : Space m n) (means : Fin (k + 1) → Space m n)
    (reps : Fin (q + 1) → Space m n) (hb : 0 < b) (r fuel call : ℕ)
    (hr : sample.val + r = b) :
    QueryPlan.sampledEval g ξ
        (resumeMuonPlan (T := T) (b := b) (k := k) (q := q) α η ρ x0 (r + fuel)
          (.validating sources i j sample acc means reps)) call =
      QueryPlan.sampledEval g ξ
        (resumeMuonPlan (T := T) (b := b) (k := k) (q := q) α η ρ x0 fuel
          ((validatedMuon α η ρ T b k q x0).update
            (show (validatedMuon α η ρ T b k q x0).State from
              .validating sources i j ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩ 0 means reps)
            (acc + ∑ t ∈ Finset.range r, g (sources i) (ξ (call + t)))))
        (call + r) := by
  induction r generalizing sample acc fuel call with
  | zero => omega
  | succ r ih =>
      have hbudget : r + 1 + fuel = (r + fuel) + 1 := by omega
      have hfirst :
          QueryPlan.sampledEval g ξ
              (resumeMuonPlan (T := T) (b := b) (k := k) (q := q) α η ρ x0
                (r + 1 + fuel) (.validating sources i j sample acc means reps)) call =
            QueryPlan.sampledEval g ξ
              (resumeMuonPlan (T := T) (b := b) (k := k) (q := q) α η ρ x0
                (r + fuel)
                ((validatedMuon α η ρ T b k q x0).update
                  (show (validatedMuon α η ρ T b k q x0).State from
                    .validating sources i j sample acc means reps)
                  (g (sources i) (ξ call))))
              (call + 1) := by
        rw [hbudget]
        simp [resumeMuonPlan, QueryPlan.sampledEval, validatedMuon, validatedMuonDirect]
      rw [hfirst]
      by_cases hr0 : r = 0
      · subst r
        have hsample : sample = ⟨b - 1, by omega⟩ := by
          apply Fin.ext
          change sample.val = b - 1
          omega
        have hfinal :
            (validatedMuon α η ρ T b k q x0).update
                (show (validatedMuon α η ρ T b k q x0).State from
                  .validating sources i j sample acc means reps)
                (g (sources i) (ξ call)) =
              (validatedMuon α η ρ T b k q x0).update
                (show (validatedMuon α η ρ T b k q x0).State from
                  .validating sources i j ⟨b - 1, Nat.sub_lt hb Nat.one_pos⟩ 0 means reps)
                (acc + ∑ t ∈ Finset.range 1, g (sources i) (ξ (call + t))) := by
          rw [hsample]
          simp [validatedMuon, validatedMuonDirect]
        rw [hfinal]
        rw [Nat.zero_add]
      · have hs : sample.val + 1 < b := by omega
        let sample' : Fin b := ⟨sample.val + 1, by omega⟩
        have hupdate :
            (validatedMuon α η ρ T b k q x0).update
              (show (validatedMuon α η ρ T b k q x0).State from
                .validating sources i j sample acc means reps)
              (g (sources i) (ξ call)) =
            .validating sources i j sample' (acc + g (sources i) (ξ call)) means reps := by
          simp [validatedMuon, validatedMuonDirect, sample', hs]
        rw [hupdate]
        have hrec := ih sample' (acc + g (sources i) (ξ call)) fuel (call + 1) (by
          dsimp [sample']
          omega)
        have hsum :
            acc + g (sources i) (ξ call) +
                ∑ t ∈ Finset.range r, g (sources i) (ξ (call + 1 + t)) =
              acc + ∑ t ∈ Finset.range (r + 1), g (sources i) (ξ (call + t)) := by
          rw [Finset.sum_range_succ']
          have hshift :
              ∑ t ∈ Finset.range r, g (sources i) (ξ (call + 1 + t)) =
                ∑ t ∈ Finset.range r, g (sources i) (ξ (call + (t + 1))) := by
            apply Finset.sum_congr rfl
            intro t ht
            congr 2
            omega
          rw [hshift]
          have hindices :
              ∑ t ∈ Finset.range r, g (sources i) (ξ (call + (t + 1))) =
                ∑ t ∈ Finset.range r, g (sources i) (ξ (call + (1 + t))) := by
            apply Finset.sum_congr rfl
            intro t ht
            congr 2
            omega
          rw [hindices]
          abel
        rw [hrec]
        have hcall : call + 1 + r = call + (r + 1) := by omega
        rw [hcall, ← hsum]

end LongTails.Proofs.MuonBatchSimulation
