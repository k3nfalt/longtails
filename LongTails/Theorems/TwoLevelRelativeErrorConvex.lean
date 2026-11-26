import LongTails.Setups.RelativeErrorSmoothConvex
import LongTails.Proofs.TwoLevelRelativeErrorConvex

namespace LongTails.Theorems.TwoLevelRelativeErrorConvex

open OracleTemplate LongTails.Setups.RelativeErrorSmoothConvex
open LongTails.Algorithms.TwoLevelRelativeErrorConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let T := p.L * p.R^2 / p.ε
  let U := T / (1-p.α)
  let N := ⌈7 * Real.sqrt U + 11 * p.α^2 * U⌉₊
  let s := 1 / p.α ^ 4
  let r := (1 + s) / (1 - 2 * p.α)
  let H := 8 * Real.sqrt r + 128 * p.α ^ 2 * r
  let m := ⌈H * Real.log ((1 + s) / (32 * p.α ^ 2))⌉₊
  let K := ⌈Real.sqrt (12 * Real.exp 1 * p.α ^ 4 * T) + 1536 * Real.exp 1 * p.α ^ 6 * T⌉₊
  if 0 < p.α ∧ p.α ≤ 1 / 32 ∧ 1 ≤ T then min N (K * m) else N

theorem result : Convergence LongTails.Setups.RelativeErrorSmoothConvex.spec budget := by
  classical
  let scale := fun p : Public => p.L*p.R^2/p.ε
  let base := fun p : Public =>
    let U := scale p/(1-p.α)
    ⌈7*Real.sqrt U + 11*p.α^2*U⌉₊
  let range := fun p : Public => 0 < p.α ∧ p.α ≤ 1/32 ∧ 1 ≤ scale p
  let count := fun p : Public => horizon p.α (scale p)*innerCount p.α
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => if range p ∧ count p < base p then output p.L p.α (scale p) p.x0
    else RelativeErrorConvex.dampedAccelerated p.L (RelativeErrorConvex.damping p.α (base p)) p.x0,
    ?_, fun _ _ => trivial⟩
  rintro p ⟨hL,ha0,ha1,-,hε⟩ f O ⟨-,hcv,hup,herr,xs,hm,hd⟩
  have hB : budget p 0 = if range p then min (base p) (count p) else base p := rfl
  let succeeds (A : Algorithm p.E p.E p.E) := spec.successful p f
    (fun ω : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => budget p 0) ω.1 ω.2)
    ⟨(A.law : MeasureTheory.Measure _).prod (O.law : MeasureTheory.Measure _), inferInstance⟩
  change succeeds (if range p ∧ count p < base p then output p.L p.α (scale p) p.x0
    else RelativeErrorConvex.dampedAccelerated p.L (RelativeErrorConvex.damping p.α (base p)) p.x0)
  split
  · rename_i hs
    have he : budget p 0 = count p := by simp only [hB,hs.1, ↓reduceIte,min_eq_right hs.2.le]
    refine ⟨xs,hm,Filter.Eventually.of_forall ?_⟩
    rintro ⟨seed,ξ⟩
    rw [he]
    exact Proofs.TwoLevelRelativeErrorConvex.execute_accuracy
      ⟨hL, hcv, hup⟩ hs.1.1 hs.1.2.1 hε hs.1.2.2
      (fun t => hm (Set.mem_univ t)) hd O herr seed ξ
  · rename_i hs
    have he : budget p 0 = base p := by
      rw [hB]; split
      · rename_i hr
        exact min_eq_left (le_of_not_gt (fun hh => hs ⟨hr,hh⟩))
      · rfl
    refine ⟨xs,hm,Filter.Eventually.of_forall ?_⟩
    rintro ⟨seed,ξ⟩
    rw [he]
    refine RelativeErrorConvex.execute_accuracy hL ha0 ha1 hε hcv hup hm hd O herr (base p) ?_ seed ξ
    have hratio : p.L*p.R^2/((1-p.α)*p.ε) = scale p/(1-p.α) := by dsimp [scale]; field_simp
    have hnoise : 11*p.α^2*p.L*p.R^2/((1-p.α)*p.ε) = 11*p.α^2*(scale p/(1-p.α)) := by
      dsimp [scale]; field_simp
    rw [hratio,hnoise]
    exact Nat.le_ceil _

end LongTails.Theorems.TwoLevelRelativeErrorConvex
