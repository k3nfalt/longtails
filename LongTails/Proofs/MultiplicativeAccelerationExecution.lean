import LongTails.Proofs.MultiplicativeAccelerationTuning
import LongTails.Algorithms.SplitRobustAcceleration
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.GapStrongGrowthAccuracy
import LongTails.Proofs.MultiplicativeRobustSampling

open MeasureTheory

namespace OracleTemplate.SplitRobustAcceleration

open StochasticGradient

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma advance_core {S : Type} (G : E → S → E × E) (L V : ℝ) (x0 : E) (ξ : ℕ → S)
    (K call k : ℕ) (x z : E) :
    advance (fun j state => (core L V x0).update state
      (G (((core L V x0).query state).2) (ξ j))) K call (k,x,z) =
      (k+K,run G L V K k x z (fun i => ξ (call+i))) := by
  dsimp only [core]
  induction K generalizing call k x z with
  | zero => simp [advance, run]
  | succ K ih =>
    rw [advance]
    change advance _ K (call+1) (k+1,
      Gradient.acceleratedQuery (k,x,z)-(1/L) • (G (Gradient.acceleratedQuery (k,x,z)) (ξ call)).1,
      z-(((k : ℝ)+1)/(32*L*V)) • (G (Gradient.acceleratedQuery (k,x,z)) (ξ call)).2) = _
    simpa only [run, Fin.val_zero, Nat.add_zero, Fin.val_succ,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (call+1) (k+1)
        (Gradient.acceleratedQuery (k,x,z)-(1/L) • (G (Gradient.acceleratedQuery (k,x,z)) (ξ call)).1)
        (z-(((k : ℝ)+1)/(32*L*V)) • (G (Gradient.acceleratedQuery (k,x,z)) (ξ call)).2)

lemma execute_method [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : E → Ω → E) (L V Λ : ℝ) (k b N : ℕ) (x0 : E) (ξ : ℕ → Ω) :
    output {Seed := fun _ => Ω, law := P, answer := fun _ (_,x) ω => g x ω}
      L V Λ k b N x0 ξ =
      (run (fun x (ω : Fin (k+2) → Fin (b+1) → Ω) => MultiplicativeRobustEstimator.estimate Λ (fun i j => g x (ω i j)))
        L V N 0 x0 x0
        (fun t i j => ξ (t.val*((k+2)*(b+1))+(finProdFinEquiv (i,j)).val))).1 := by
  unfold output method
  erw [show (fun _ : Fin 1 => (k+2)*(b+1)*N) = (fun _ => N*((k+2)*(b+1))) by
    funext; ring]
  erw [execute_batched]
  let G := fun x (ω : Fin (k+2) → Fin (b+1) → Ω) =>
    MultiplicativeRobustEstimator.estimate Λ (fun i j => g x (ω i j))
  let blocks := fun (t : ℕ) (i : Fin (k+2)) (j : Fin (b+1)) => ξ (t*((k+2)*(b+1))+(finProdFinEquiv (i,j)).val)
  change (core L V x0).output (advance
    (fun t state => (core L V x0).update state
      (G (((core L V x0).query state).2) (blocks t))) N 0 (0,x0,x0)) = _
  erw [advance_core]
  simp only [core, Nat.zero_add]
  rfl

lemma matrix_samples_law [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun t (ξ : ℕ → Ω) => ξ t) μ P) (k b N : ℕ) :
    MeasurePreserving
      (fun ξ : ℕ → Ω => fun t : Fin N => fun i : Fin (k+2) => fun j : Fin (b+1) =>
        ξ (t.val*((k+2)*(b+1))+(finProdFinEquiv (i,j)).val))
      P (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin (k+2) =>
        Measure.pi fun _ : Fin (b+1) => μ) := by
  let Q := Measure.pi (fun _ : Fin (b+1) => μ)
  have hb := FiniteVariance.infinite_block_law μ P h.independent h.marginal (b+1)
  have hr := GapStrongGrowth.iid_groups_law Q (Measure.infinitePi fun _ : ℕ => Q)
    (StochasticGeneralized.infinitePi_iid Q) N (k+2)
  have hh := hr.comp hb
  convert hh using 1
  funext ξ t i j
  simp only [Function.comp_apply]
  congr 1
  change t.val*((k+2)*(b+1))+(j.val+(b+1)*i.val) = (t.val*(k+2)+i.val)*(b+1)+j.val
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma advance_capped {Q R U : Type} (A : Algorithm Q R U) (limit : ℕ)
    (reply : ℕ → Q → R) (n call remaining : ℕ) (state : A.State) :
    advance (fun j s => (capped A limit).update s (reply j ((capped A limit).query s).2))
      n call (remaining,state) =
      (remaining-n, advance (fun j s => A.update s (reply j (A.query s).2))
        (min n remaining) call state) := by
  induction n generalizing call remaining state with
  | zero => simp only [advance, Nat.sub_zero, Nat.zero_min]; rfl
  | succ n ih =>
    cases remaining with
    | zero => simpa [advance, capped] using ih (call+1) 0 state
    | succ remaining =>
        simpa [advance, capped] using
          ih (call+1) remaining (A.update state (reply call (A.query state).2))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma execute_capped {Q R U : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Q → Ω → R) (A : Algorithm Q R U)
    (K B : ℕ) (hKB : K ≤ B) (seed : A.Seed) (ξ : ℕ → Ω) :
    execute {Seed := fun _ => Ω, law := P, answer := fun _ (_,x) ω => g x ω}
      (capped A K) (fun _ => B) seed ξ =
    execute {Seed := fun _ => Ω, law := P, answer := fun _ (_,x) ω => g x ω}
      A (fun _ => K) seed ξ := by
  erw [execute_advance P g (capped A K) B seed ξ, execute_advance P g A K seed ξ]
  change A.output (advance _ B 0 (K,A.initial seed)).2 = _
  erw [advance_capped A K (fun j x => g x (ξ j)) B 0 K (A.initial seed)]
  simp only [Nat.min_eq_right hKB]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma execute_algorithm
    (q : LongTails.Setups.HeavyTailedStrongGrowthConvex.Params)
    (P : ProbabilityMeasure (ℕ → q.Ω)) (g : q.E → q.Ω → q.E)
    (B : ℕ) (hB : calls q ≤ B) (ξ : ℕ → q.Ω) :
    execute {Seed := fun _ => q.Ω, law := P, answer := fun _ (_,x) ω => g x ω}
      (algorithm q) (fun _ => B) () ξ =
    lastIterate q {Seed := fun _ => q.Ω, law := P, answer := fun _ (_,x) ω => g x ω} ξ := by
  exact execute_capped P g _ (calls q) B hB () ξ

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma calls_bound (q : LongTails.Setups.HeavyTailedStrongGrowthConvex.Params)
    (hρ : 0 ≤ q.ρ) (hp : 1 < q.p) :
    calls q ≤ 130*⌈128*Real.sqrt (scale q)⌉₊ +
      2*⌈(17179869184*q.ρ)^(1/(q.p-1))⌉₊*(130+⌈2*Real.log (scale q)⌉₊)*
        ⌈128*(scale q)^(q.p/(3*q.p-2))⌉₊ := by
  by_cases hz : q.ρ = 0
  · simp [calls, pilotCount, batchExtra, iterations, hz,
      Real.zero_rpow (by exact inv_ne_zero (by linarith : q.p-1 ≠ 0) : (q.p-1)⁻¹ ≠ 0)]
  · have hb := LongTails.Proofs.MultiplicativeAccelerationTuning.batch_cost
      (p := q.p) (lt_of_le_of_ne hρ (Ne.symm hz))
    simp only [calls, pilotCount, batchExtra, iterations, hz, ite_false]
    have hh := Nat.mul_le_mul_right
      ⌈128*(scale q)^(q.p/(3*q.p-2))⌉₊
      (Nat.mul_le_mul_left (130+⌈2*Real.log (scale q)⌉₊) hb)
    nlinarith only [hh]

end OracleTemplate.SplitRobustAcceleration
