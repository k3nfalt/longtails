import LongTails.Proofs.DuelingSignTesting
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate
open scoped unitInterval
open LongTails.Setups.StronglyConvexDueling (Ball)
open LongTails.Setups.FlatTransferDueling (spec)
open LongTails.Proofs.DuelingTestingExecution
open LongTails.Proofs.DuelingSignFamily
open LongTails.Proofs.DuelingSignOracle
open LongTails.Proofs.DuelingSignTesting

namespace LongTails.Proofs.DuelingReferenceLowerBound

lemma testing_budget {p : Params} (hε : 0 < p.ε) {n : ℕ}
    (hn : n ≤ ⌊(p.d:ℝ)^2 / (65536*(2*(p.j:ℝ)+1)^2*p.ε^2)⌋₊) :
    (n:ℝ)*((2*(p.j:ℝ)+1)*scale p^2/8)^2 ≤ 1/4 := by
  have ha : (n:ℝ) ≤ (p.d:ℝ)^2 / (65536*(2*(p.j:ℝ)+1)^2*p.ε^2) :=
    (Nat.cast_le.mpr hn).trans (Nat.floor_le (by positivity))
  have h := (le_div_iff₀ (by positivity)).mp ha
  have hd : 0 < (p.d:ℝ) := by exact_mod_cast NeZero.pos p.d
  have he : scale p^2 = 1024*p.ε/p.d := (eq_div_iff hd.ne').mpr (by linarith [scale_sq p hε.le])
  rw [he]
  field_simp
  nlinarith only [h]

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma exists_bad {p : Params} (hp : 0 < p.ε ∧ p.ε ≤ 1/64) (A : Method p) (n : ℕ)
    (hn : (n:ℝ)*((2*(p.j:ℝ)+1)*scale p^2/8)^2 ≤ 1/4) :
    ∃ θ : Fin p.d → Bool, ¬ spec.successful p (loss (scale p) θ)
      (fun s : A.Seed × (ℕ → I) => execute (oracle (chance p θ)) A (fun _ => n) s.1 s.2)
      ⟨(A.law : Measure _).prod (uniforms : Measure (ℕ → I)),inferInstance⟩ := by
  classical
  by_contra! hall
  let Θ := Fin p.d → Bool
  let P := (A.law : Measure A.Seed).prod (uniforms : Measure (ℕ → I))
  let out := fun (θ : Θ) (s : A.Seed × (ℕ → I)) =>
    execute (oracle (chance p θ)) A (fun _ => n) s.1 s.2
  let bad := fun (θ : Θ) (i : Fin p.d) (s : A.Seed × (ℕ → I)) =>
    if mistake θ i (out θ s) then (1:ℝ) else 0
  have hm (θ : Θ) : Measurable (out θ) := (hall θ).1
  have hbi (θ : Θ) (i : Fin p.d) : Integrable (bad θ i) P := by
    have hb := (mistake_measurable θ i).comp (hm θ)
    have hb' : Measurable (bad θ i) :=
      (show Measurable (fun b : Bool => if b then (1:ℝ) else 0) from Measurable.of_discrete).comp hb
    apply Integrable.of_bound hb'.aestronglyMeasurable 1
    filter_upwards [] with s
    dsimp [bad]
    split <;> norm_num
  let row := fun (θ : Θ) (s : A.Seed × (ℕ → I)) => ∑ i : Fin p.d, bad θ i s
  let total := fun s : A.Seed × (ℕ → I) => ∑ θ : Θ, row θ s
  have hrow (θ : Θ) : Integrable (row θ) P := integrable_finsetSum _ (fun i _ => hbi θ i)
  have htotal : Integrable total P := integrable_finsetSum _ (fun θ _ => hrow θ)
  have hlow (a : A.Seed) : (Fintype.card Θ:ℝ)*p.d/8 ≤
      ∫ ξ, total (a,ξ) ∂(uniforms : Measure (ℕ → I)) := by
    have hslice (θ : Θ) (i : Fin p.d) : Integrable (fun ξ => bad θ i (a,ξ)) (uniforms : Measure _) := by
      have m := (hm θ).comp (show Measurable (fun ξ : ℕ → I => (a,ξ)) from measurable_prodMk_left)
      have mb := (mistake_measurable θ i).comp m
      apply Integrable.of_bound ((show Measurable (fun b : Bool => if b then (1:ℝ) else 0)
        from Measurable.of_discrete).comp mb).aestronglyMeasurable 1
      filter_upwards [] with ξ
      dsimp [bad]; split <;> norm_num
    have hri (θ : Θ) : Integrable (fun ξ => row θ (a,ξ)) (uniforms : Measure _) :=
      integrable_finsetSum _ (fun i _ => hslice θ i)
    dsimp only [total]
    rw [integral_finsetSum _ (fun θ _ => hri θ)]
    simp only [row, integral_finsetSum _ (fun i _ => hslice _ i),bad,out,execute_error]
    exact average_errors A n (A.initial a) hn
  have hlower : (Fintype.card Θ:ℝ)*p.d/8 ≤ ∫ s, total s ∂P := by
    rw [show (∫ s, total s ∂P) = _ from integral_prod total htotal]
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (integrable_const _) htotal.integral_prod_left hlow
  have hh := scale_pos hp.1
  have hupper (θ : Θ) : scale p^2/64 * (∫ s, row θ s ∂P) ≤ p.ε := by
    obtain ⟨u,hu,hi,he⟩ := (hall θ).2
    have huc := hu (center_ball hp θ)
    have hpoint (s : A.Seed × (ℕ → I)) :
        scale p^2/64 * row θ s ≤ loss (scale p) θ (out θ s).val - loss (scale p) θ u.val := by
      have := mistakes_gap hh θ (out θ s).val
      rw [error_rewrite θ (out θ s)] at this
      change scale p^2/64 * row θ s ≤ _ at this
      change loss (scale p) θ u.val ≤ loss (scale p) θ (center (scale p) θ) at huc
      linarith
    have hb := integral_mono ((hrow θ).const_mul (scale p^2/64)) hi hpoint
    rw [integral_const_mul] at hb
    exact hb.trans he
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun θ _ => hupper θ)
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun θ _ => hrow θ)] at hu
  change scale p^2/64*(∫ s, total s ∂P) ≤ _ at hu
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hu
  have hl := mul_le_mul_of_nonneg_left hlower (show 0 ≤ scale p^2/64 by positivity)
  have hc : 0 < (Fintype.card Θ:ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith only [hu,hl,congrArg (fun z : ℝ => (Fintype.card Θ:ℝ)*z) (scale_sq p hp.1.le),
    mul_pos hc hp.1]

end LongTails.Proofs.DuelingReferenceLowerBound
