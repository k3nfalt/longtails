import LongTails.TemplateLowerBound
import LongTails.Proofs.HolderNoiseHardExecution
import LongTails.Proofs.HolderNoiseCoinExposure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseHardLower

open OracleTemplate LongTails.Setups.HolderNoiseNonconvexLower
open HolderNoiseHardScaling HolderNoiseHardOracle HolderNoiseHardAdmissible HolderNoiseHardExecution
open HolderNoiseHiding HolderNoiseCoinExposure QuasarCoinLaw FrontierChainWall
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerExposure FiniteSumNondualLowerBound

lemma exists_failure (q : LowerParams) {k : ℕ} (A : Alg q) {a b p : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hp : 0 < p) (hp1 : p ≤ 1) (N : ℕ)
    (D : ℝ) (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ q.d)
    (hsize : 4 * ((3 * ((N : ℝ) + 1)) * (k + 1 : ℕ) * (radius k ^ 2 / (1 / 4) ^ 2)) ≤ D)
    (hacc : q.ε < (a / b) * (3 / 8 : ℝ) * (1 - N * p / (k + 1))) :
    ∃ π : Fin (k + 1) ↪ Fin q.d,
      ¬ spec.successful q (objective π a b q.x0)
        (fun z : A.Seed × (ℕ → Bool) =>
          execute (pairOracle q hp.le hp1 (oracleValue p (field π a b q.x0) (noise π a b q.x0)))
            A (fun _ => N) z.1 z.2)
        ⟨(A.law : Measure _).prod (coinPath p hp.le hp1 : Measure _), inferInstance⟩ := by
  classical
  by_contra hfail
  push Not at hfail
  let P : ProbabilityMeasure (A.Seed × (ℕ → Bool)) :=
    ⟨(A.law : Measure _).prod (coinPath p hp.le hp1 : Measure _), inferInstance⟩
  let f := fun (w : CoordinateWords q.d k) (z : A.Seed × (ℕ → Bool)) =>
    ‖gradient (objective (coordinateEmbedding w) a b q.x0)
      (execute (pairOracle q hp.le hp1 (oracleValue p (field (coordinateEmbedding w) a b q.x0)
        (noise (coordinateEmbedding w) a b q.x0))) A (fun _ => N) z.1 z.2)‖
  have hint (w : CoordinateWords q.d k) : Integrable (f w) (P : Measure _) :=
    (hfail (coordinateEmbedding w)).2.1
  have hbound (w : CoordinateWords q.d k) : (∫ z, f w z ∂(P : Measure _)) ≤ q.ε :=
    (hfail (coordinateEmbedding w)).2.2
  have hsint : Integrable (fun z => ∑ w, f w z) (P : Measure _) :=
    integrable_finsetSum Finset.univ (fun w _ => hint w)
  have heint : Integrable (fun z : A.Seed × (ℕ → Bool) => (exposure z.2 N : ℝ)) (P : Measure _) := by
    simpa only [P, ProbabilityMeasure.coe_mk] using (exposure_integrable p hp.le hp1 N).comp_snd (A.law : Measure A.Seed)
  let C : ℝ := (a / b) * (3 / 8) * Fintype.card (CoordinateWords q.d k)
  have hlint : Integrable (fun z : A.Seed × (ℕ → Bool) => C * (1 - (exposure z.2 N : ℝ) / (k + 1)))
      (P : Measure _) := ((integrable_const 1).sub (heint.div_const _)).const_mul C
  have hpoint (z : A.Seed × (ℕ → Bool)) : C * (1 - (exposure z.2 N : ℝ) / (k + 1)) ≤ ∑ w, f w z :=
    execution_gradient_sum q A ha hb hp.le hp1 N z.1 z.2 D hD hDs hsize
  have hl := integral_mono hlint hsint hpoint
  have he : (∫ z : A.Seed × (ℕ → Bool), (exposure z.2 N : ℝ) ∂(P : Measure _)) = N * p := by
    change (∫ z, (exposure z.2 N : ℝ) ∂((A.law : Measure A.Seed).prod (coinPath p hp.le hp1 : Measure (ℕ → Bool)))) = _
    have hprod := integral_fun_snd (μ := (A.law : Measure A.Seed))
      (ν := (coinPath p hp.le hp1 : Measure (ℕ → Bool))) (fun β : ℕ → Bool => (exposure β N : ℝ))
    rw [exposure_integral] at hprod
    simpa only [probReal_univ, one_smul] using hprod
  rw [integral_const_mul, integral_sub (integrable_const 1) (heint.div_const _),
    integral_const, integral_div, he, integral_finsetSum Finset.univ (fun w _ => hint w)] at hl
  simp only [probReal_univ, one_smul] at hl
  have hu := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (CoordinateWords q.d k))) => hbound w)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
  have hkd : k + 1 ≤ q.d := by exact_mod_cast (show (k + 1 : ℕ) ≤ (q.d : ℝ) by linarith)
  have hc : 0 < (Fintype.card (CoordinateWords q.d k) : ℝ) :=
    Nat.cast_pos.mpr (coordinateWords_card_pos q.d k hkd)
  have hstrict := mul_lt_mul_of_pos_right hacc hc
  dsimp only [C] at hl
  nlinarith

end LongTails.Proofs.HolderNoiseHardLower
