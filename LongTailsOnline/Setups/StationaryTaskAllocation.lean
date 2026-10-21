import LongTailsOnline.Setups.StochasticBandit

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LongTailsOnline.Setups.StationaryTaskAllocation

abbrev Worker (k : ℕ) := Fin (k + 1)

abbrev Sample (k : ℕ) := Worker k × ℕ → ℝ

abbrev Allocation (k B : ℕ) :=
  {a : Worker k → Fin (B + 1) // ∑ i, (a i).val = B}

def concentrated {k B : ℕ} (i : Worker k) : Allocation k B :=
  ⟨fun j => if j = i then ⟨B, Nat.lt_succ_self B⟩ else 0, by
    simp only [apply_ite (fun a : Fin (B + 1) => a.val), Fin.val_zero]
    simp⟩

instance {k B : ℕ} : Nonempty (Allocation k B) := ⟨concentrated 0⟩

noncomputable def loss {k B : ℕ} (v : Worker k → ℝ) (a : Allocation k B) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (a.val i).val * v i)

noncomputable def oracle {k B : ℕ} (v : Worker k → ℝ) : Allocation k B :=
  Classical.choose (Finset.exists_min_image (Finset.univ : Finset (Allocation k B))
    (loss v) Finset.univ_nonempty)

noncomputable def optimum {k B : ℕ} (v : Worker k → ℝ) : ℝ :=
  loss v (oracle (B := B) v)

abbrev Counts (k : ℕ) := Worker k → ℕ

abbrev Feedback (k B : ℕ) := Worker k → Fin B → ℝ

def increment {k B : ℕ} (c : Counts k) (a : Allocation k B) : Counts k :=
  fun i => c i + (a.val i).val

noncomputable def batch {k B : ℕ} (w : Sample k) (c : Counts k)
    (a : Allocation k B) : Feedback k B :=
  fun i j => if j.val < (a.val i).val then w (i, c i + j.val) else 0

@[fun_prop]
lemma measurable_increment (k B : ℕ) :
    Measurable (fun p : Counts k × Allocation k B => increment p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  unfold increment
  fun_prop

@[fun_prop]
lemma measurable_batch (k B : ℕ) :
    Measurable (fun p : Sample k × Counts k × Allocation k B =>
      batch p.1 p.2.1 p.2.2) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold batch
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (by fun_prop)
  · apply LongTailsOnline.Setups.StochasticBandit.measurable_eval_countable
    · fun_prop
    · fun_prop
  · fun_prop

noncomputable abbrev environment {k B : ℕ} (P : ProbabilityMeasure (Sample k)) :
    OnlineTemplate.Environment Unit (Allocation k B) (Feedback k B) Unit where
  State := Sample k × Counts k
  initial := ⟨P.toMeasure.map (fun w => (w, fun _ => 0)), inferInstance⟩
  observe _ := Kernel.deterministic (fun s => ((), s)) (by fun_prop)
  respond _ := Kernel.deterministic
    (fun s => (batch s.1.1 s.1.2 s.2.2, (), s.1.1, increment s.1.2 s.2.2)) (by
      apply Measurable.prodMk
      · exact (measurable_batch k B).comp
          (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd.snd))
      · fun_prop)

structure Public where
  k : ℕ
  B : ℕ
  T : ℕ
  σ : ℝ≥0

structure Params where
  config : Public
  μ : Worker config.k → ℝ

structure Sampling (p : Params) (P : ProbabilityMeasure (Sample p.config.k)) : Prop where
  independent : iIndepFun (fun q : Worker p.config.k × ℕ =>
    fun w : Sample p.config.k => w q) P.toMeasure
  stationary : ∀ i n, P.toMeasure.map (fun w => w (i, n)) =
    P.toMeasure.map (fun w => w (i, 0))
  positive : ∀ i n, ∀ᵐ w ∂P.toMeasure, 0 < w (i, n)
  mean : ∀ i n, (∫ w, w (i, n) ∂P.toMeasure) = p.μ i
  subgaussian : ∀ i n, HasSubgaussianMGF
    (fun w => w (i, n) - p.μ i) (p.config.σ ^ 2) P.toMeasure

noncomputable def regret (p : Params)
    (h : OnlineTemplate.Trace Unit (Allocation p.config.k p.config.B)
      (Feedback p.config.k p.config.B) Unit p.config.T) : ℝ :=
  ∑ t, (loss p.μ (h t).2.1 - optimum (B := p.config.B) p.μ)

abbrev spec : OnlineTemplate.Setup where
  Params := Params
  Public := Public
  Instance p := ProbabilityMeasure (Sample p.k)
  Observation _ := Unit
  Action p := Allocation p.k p.B
  Feedback p := Feedback p.k p.B
  Outcome _ := Unit
  Bound _ := ℝ
  publicInput := Params.config
  horizon p := p.config.T
  valid p := 0 < p.config.B ∧ 0 < p.config.T ∧ ∀ i, p.μ i ∈ Set.Ioc (0 : ℝ) 1
  admissible p P E := Sampling p P ∧ E = environment P
  successful p _ b law := Integrable (regret p) law.toMeasure ∧
    (∫ h, regret p h ∂law.toMeasure) / p.config.T ≤ b

end LongTailsOnline.Setups.StationaryTaskAllocation
