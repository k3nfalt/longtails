import LongTails.Proofs.DuelingSignOracle

open MeasureTheory OracleTemplate
open scoped unitInterval
open LongTails.Setups.StronglyConvexDueling

namespace LongTails.Proofs.DuelingSignTesting

open DuelingSignFamily DuelingSignOracle DuelingBinaryTesting DuelingTestingExecution

abbrev Method (p : DuelingSignOracle.Params) := Algorithm (Ball p.d × Ball p.d) Bool (Ball p.d)

noncomputable def mistake {d : ℕ} (θ : Fin d → Bool) (i : Fin d) (x : Ball d) : Bool :=
  decide (decide (0 ≤ x.val i) ≠ θ i)

lemma mistake_flip {d : ℕ} (θ : Fin d → Bool) (i : Fin d) (x : Ball d) :
    mistake (flip i θ) i x = !(mistake θ i x) := by
  unfold mistake
  rw [flip_at]
  cases decide (0 ≤ x.val i) <;> cases θ i <;> decide

lemma acceptance_not {S : Type*} (step : S → Bool → S) (q : S → ℝ) (t : S → Bool)
    (n : ℕ) (s : S) :
    acceptance step q (fun s => !(t s)) n s = 1 - acceptance step q t n s := by
  induction n generalizing s with
  | zero => cases h : t s <;> simp [acceptance,h]
  | succ n ih => simp only [acceptance,ih,mix]; ring

noncomputable def errorRate {p : DuelingSignOracle.Params} (A : Method p)
    (θ : Fin p.d → Bool) (i : Fin p.d) (n : ℕ) (s : A.State) : ℝ :=
  acceptance A.update (fun s => (chance p θ (A.query s).2 : ℝ)) (fun s => mistake θ i (A.output s)) n s

lemma neighbor_testing {p : DuelingSignOracle.Params} (A : Method p) (θ : Fin p.d → Bool)
    (i : Fin p.d) (n : ℕ) (s : A.State)
    (hn : (n:ℝ)*((2*(p.j:ℝ)+1)*scale p^2/8)^2 ≤ 1/4) :
    1/4 ≤ errorRate A θ i n s + errorRate A (flip i θ) i n s := by
  let p₁ := fun s : A.State => (chance p θ (A.query s).2 : ℝ)
  let p₂ := fun s : A.State => (chance p (flip i θ) (A.query s).2 : ℝ)
  let t := fun s : A.State => mistake θ i (A.output s)
  have he := acceptance_affinity A.update p₁ p₂ t (fun s => chance_range p θ _)
    (fun s => chance_range p (flip i θ) _) (fun s => chance_flip p θ i _) n s
  have hr (v : Fin p.d → Bool) (q : Ball p.d × Ball p.d) : (chance p v q : ℝ) ∈ Set.Icc 0 1 :=
    (chance p v q).property
  have hsum := sum_errors (acceptance_mem A.update p₁ t (fun s => hr θ _) n s)
    (acceptance_mem A.update p₂ t (fun s => hr (flip i θ) _) n s) (by linarith)
  unfold errorRate
  simp_rw [mistake_flip, acceptance_not]
  exact hsum

lemma average_errors {p : DuelingSignOracle.Params} (A : Method p) (n : ℕ) (s : A.State)
    (hn : (n:ℝ)*((2*(p.j:ℝ)+1)*scale p^2/8)^2 ≤ 1/4) :
    (Fintype.card (Fin p.d → Bool):ℝ) * p.d / 8 ≤
      ∑ θ : Fin p.d → Bool, ∑ i : Fin p.d, errorRate A θ i n s := by
  classical
  have h (i : Fin p.d) : (Fintype.card (Fin p.d → Bool):ℝ)/8 ≤
      ∑ θ : Fin p.d → Bool, errorRate A θ i n s := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun θ _ => neighbor_testing A θ i n s hn)
    have he := Equiv.sum_comp (flip_involutive i).toPerm (fun θ => errorRate A θ i n s)
    simp only [Function.Involutive.coe_toPerm] at he
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib,he] at hsum
    linarith
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at ht
  linarith

lemma execute_error {p : DuelingSignOracle.Params} (A : Method p) (θ : Fin p.d → Bool)
    (i : Fin p.d) (n : ℕ) (a : A.Seed) :
    (∫ ξ : ℕ → I, if mistake θ i (execute (oracle (chance p θ)) A (fun _ => n) a ξ)
      then (1:ℝ) else 0 ∂(uniforms : Measure (ℕ → I))) = errorRate A θ i n (A.initial a) := by
  simp_rw [execute_readout A (chance p θ) (mistake θ i)]
  exact readout_integral _ _ _ _ _

lemma error_rewrite {d : ℕ} (θ : Fin d → Bool) (x : Ball d) :
    mistakes θ x.val = ∑ i, if mistake θ i x then (1:ℝ) else 0 := by
  unfold mistakes mistake
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : decide (0 ≤ x.val i) = θ i <;> simp [hi]

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma mistake_measurable {d : ℕ} (θ : Fin d → Bool) (i : Fin d) :
    Measurable (mistake θ i) := by
  have hm : Measurable (fun x : Ball d => decide (0 ≤ x.val i)) := by
    apply measurable_to_bool
    simp only [Set.preimage,Set.mem_singleton_iff,decide_eq_true_eq]
    exact measurableSet_le measurable_const ((EuclideanSpace.proj i).continuous.measurable.comp measurable_subtype_coe)
  exact (show Measurable (fun b : Bool => decide (b ≠ θ i)) from Measurable.of_discrete).comp hm

end LongTails.Proofs.DuelingSignTesting
