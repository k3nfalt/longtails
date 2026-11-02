import LongTails.Setups.UscgConstant
import LongTails.Proofs.Execution

open MeasureTheory

namespace OracleTemplate.NormBallLMO

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO Problem ConstrainedProblem State lmoMethod uscg scg
  constantMomentum vanishingMomentum)

variable {d : ℕ} {Ω : Type}

noncomputable def path (step : Space d → Space d → Space d) (α : ℕ → ℝ) (x₁ : Space d)
    (g : Space d → Ω → Space d) (ξ : ℕ → Ω) : ℕ → Space d × Space d
  | 0 => (x₁, 0)
  | k + 1 =>
      (step (path step α x₁ g ξ k).1
          (α (k + 1) • g (path step α x₁ g ξ k).1 (ξ k) + (1 - α (k + 1)) • (path step α x₁ g ξ k).2),
        α (k + 1) • g (path step α x₁ g ξ k).1 (ξ k) + (1 - α (k + 1)) • (path step α x₁ g ξ k).2)

lemma path_zero (step : Space d → Space d → Space d) (α : ℕ → ℝ) (x₁ : Space d)
    (g : Space d → Ω → Space d) (ξ : ℕ → Ω) : path step α x₁ g ξ 0 = (x₁, 0) := by
  rfl

lemma path_succ (step : Space d → Space d → Space d) (α : ℕ → ℝ) (x₁ : Space d)
    (g : Space d → Ω → Space d) (ξ : ℕ → Ω) (k : ℕ) :
    path step α x₁ g ξ (k + 1) =
      (step (path step α x₁ g ξ k).1
          (α (k + 1) • g (path step α x₁ g ξ k).1 (ξ k) + (1 - α (k + 1)) • (path step α x₁ g ξ k).2),
        α (k + 1) • g (path step α x₁ g ξ k).1 (ξ k) + (1 - α (k + 1)) • (path step α x₁ g ξ k).2) := by
  rfl

lemma path_congr (step : Space d → Space d → Space d) (α : ℕ → ℝ) (x₁ : Space d)
    (g : Space d → Ω → Space d) {ξ ξ' : ℕ → Ω} :
    ∀ k, (∀ i, i < k → ξ i = ξ' i) → path step α x₁ g ξ k = path step α x₁ g ξ' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      rw [path_succ, path_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

lemma measurable_path [MeasurableSpace Ω] {step : Space d → Space d → Space d}
    (hstep : Measurable (fun z : Space d × Space d => step z.1 z.2)) (α : ℕ → ℝ) (x₁ : Space d)
    {g : Space d → Ω → Space d} (hg : Measurable (Function.uncurry g)) :
    ∀ k, Measurable (fun ξ : ℕ → Ω => path step α x₁ g ξ k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k hk =>
      have hgk : Measurable (fun ξ : ℕ → Ω => g (path step α x₁ g ξ k).1 (ξ k)) :=
        hg.comp (hk.fst.prodMk (measurable_pi_apply k))
      have hm : Measurable (fun ξ : ℕ → Ω =>
          α (k + 1) • g (path step α x₁ g ξ k).1 (ξ k) + (1 - α (k + 1)) • (path step α x₁ g ξ k).2) :=
        (hgk.const_smul (α (k + 1))).add (hk.snd.const_smul (1 - α (k + 1)))
      simp_rw [path_succ]
      exact (hstep.comp (hk.fst.prodMk hm)).prodMk hm

section Execution

lemma run_path (step : Space d → Space d → Space d) (α : ℕ → ℝ) (T : ℕ) (x₁ : Space d)
    (g : Space d → Ω → Space d) (ξ : ℕ → Ω) (j : ℕ) :
    ∀ k, k ≤ j →
      (fun sc : State d × ℕ =>
          ((lmoMethod step α T x₁).update sc.1 (g ((lmoMethod step α T x₁).query sc.1).2 (ξ sc.2)),
            sc.2 + 1))^[k] (⟨j, 0, x₁, 0⟩, 0) =
        (⟨j, k, (path step α x₁ g ξ k).1, (path step α x₁ g ξ k).2⟩, k) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hk : k < j := by omega
      simp only [lmoMethod, hk, ite_true, path_succ]

lemma run_frozen (step : Space d → Space d → Space d) (α : ℕ → ℝ) (T : ℕ) (x₁ : Space d)
    (g : Space d → Ω → Space d) (ξ : ℕ → Ω) (j : ℕ) :
    ∀ m, ((fun sc : State d × ℕ =>
          ((lmoMethod step α T x₁).update sc.1 (g ((lmoMethod step α T x₁).query sc.1).2 (ξ sc.2)),
            sc.2 + 1))^[j + m] (⟨j, 0, x₁, 0⟩, 0)).1 =
        ⟨j, j, (path step α x₁ g ξ j).1, (path step α x₁ g ξ j).2⟩ := by
  intro m
  induction m with
  | zero => rw [Nat.add_zero, run_path step α T x₁ g ξ j j le_rfl]
  | succ m ih =>
      rw [show j + (m + 1) = (j + m) + 1 by omega, Function.iterate_succ_apply']
      set sc := (fun sc : State d × ℕ =>
          ((lmoMethod step α T x₁).update sc.1 (g ((lmoMethod step α T x₁).query sc.1).2 (ξ sc.2)),
            sc.2 + 1))^[j + m] (⟨j, 0, x₁, 0⟩, 0)
      obtain ⟨s, c⟩ := sc
      simp only at ih
      subst ih
      simp [lmoMethod]

lemma execute_lmoMethod [MeasurableSpace Ω] (step : Space d → Space d → Space d) (α : ℕ → ℝ) (T : ℕ) (x₁ : Space d)
    (g : Space d → Ω → Space d) (P : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) (hK : T ≤ K)
    (j : (lmoMethod step α T x₁).Seed) (ξ : ℕ → Ω) :
    execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } :
        Oracle (Space d) (Space d)) (lmoMethod step α T x₁) (fun _ => K) j ξ =
      (path step α x₁ g ξ (j : Fin (T + 1)).val).1 := by
  refine (execute_indexed_of_answer
    ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } : Oracle (Space d) (Space d))
    (lmoMethod step α T x₁) K j ξ
    (fun k q => g q.2 (ξ k)) (fun _ _ => rfl)).trans ?_
  change Fin (T + 1) at j
  obtain ⟨m, hm⟩ : ∃ m, K = j.val + m := ⟨K - j.val, by have := j.isLt; omega⟩
  subst hm
  have h := run_frozen step α T x₁ g ξ j.val m
  change (((fun sc : State d × ℕ =>
          ((lmoMethod step α T x₁).update sc.1 (g ((lmoMethod step α T x₁).query sc.1).2 (ξ sc.2)),
            sc.2 + 1))^[j.val + m] (⟨j.val, 0, x₁, 0⟩, 0)).1).point = _
  rw [h]

end Execution

attribute [local simp] path

end OracleTemplate.NormBallLMO
