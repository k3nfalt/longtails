import LongTails.Template
import LongTails.Proofs.FreyaExecution
import LongTails.Setups.FreyaPageIterations

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Proofs.FreyaIterations

open LongTails.Proofs.FreyaModel LongTails.Proofs.FreyaCollectors LongTails.Proofs.FreyaIndependence
open LongTails.Algorithms.FreyaInputs LongTails.Algorithms.FreyaRandomness
open LongTails.Algorithms.FreyaPage LongTails.Algorithms.FreyaTuning

theorem iteration_accuracy (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1) (hη : 0 < q.η)
    (f : Fin q.m → Space q.d → ℝ) (lower Lminus Lplus Lpm Δ : ℝ)
    (hL : 0 ≤ Lminus) (hD : 0 ≤ Lpm)
    (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
    (htune : q.η ≤ 1 / (Lminus + Lpm * Real.sqrt ((1 - q.ρ) / (q.ρ * q.S))))
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
    (N : ℕ) (hN : eventLimit q ≤ N) :
    let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
    let accuracy := fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
      ‖gradient (objective f) (execute O (factory q) (fun _ => N) z.1 z.2).1‖ ^ 2
    Integrable accuracy P ∧
      (∫ z, accuracy z ∂P) ≤ 2 * (objective f q.x0 - lower) / (q.η * q.K) ∧
      ∀ ε : ℝ, 0 < ε → 2 * (objective f q.x0 - lower) / (q.η * ε) ≤ q.K →
        (∫ z, accuracy z ∂P) ≤ ε := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      dsimp only
      have hlip : LipschitzWith ⟨Lminus,hL⟩ (gradient (objective f)) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        change ‖gradient (objective f) x-gradient (objective f) y‖≤Lminus*‖x-y‖
        exact hreg.smooth x y
      have hG : Continuous (fun x : Space q.d => ‖gradient (objective f) x‖^2) :=
        hlip.continuous.norm.pow 2
      have hlaw := (LongTails.Proofs.FreyaExecution.scheduled_page_law q hm hn hS hK hρ hρone
        f hreg.differentiable τ O hservice hind N hN).2
      have hrate := LongTails.Proofs.FreyaSerialAnalysis.page_rate
        (LongTails.Proofs.FreyaExecution.serialInput q) hm hS hK hρ hρone hη f
        lower Lminus Lplus Lpm Δ hL hD hreg htune
      have hi := LongTails.Proofs.FreyaExecution.selected_gradient_integrable q hm hn hS hK
        hρ hρone f lower Lminus Lplus Lpm Δ hL hreg τ O hservice hind N hN
      have hout : Measurable (LongTails.Algorithms.FreyaSerial.idealOutput
          (LongTails.Proofs.FreyaExecution.serialInput q) f) := by
        have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
            (b : β) (f : α → β) (hf : Measurable f) :
            Measurable (fun o : Option α => o.elim b f) := by
          have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
            apply Measurable.of_comap_le
            delta instMeasurableSpaceOption
            apply le_of_eq
            congr 1
            funext o
            cases o <;> rfl
          have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
          convert hs.comp he using 1
          funext o
          cases o <;> rfl
        have freyaOptionSingleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] :
            MeasurableSingletonClass (Option α) := by
          constructor
          intro x
          let encode := fun o : Option α => o.elim (Sum.inl ()) Sum.inr
          have he : {x}=encode ⁻¹' {encode x} := by
            ext y
            cases x <;> cases y <;> simp (config := { iota := false }) [encode]
          have hsingleton : MeasurableSet {encode x} := by
            rw [measurableSet_sum_iff]
            cases x <;> constructor <;> simp (config := { iota := false }) [encode]
            · have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inl ()}=∅ := by ext a; simp (config := { iota := false })
              rw [he]
              exact MeasurableSet.empty
            · rename_i b
              have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inr b}={b} := by ext a; simp (config := { iota := false })
              rw [he]
              exact measurableSet_singleton _
          rw [he]
          exact (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr)
            hsingleton
        let : MeasurableSingletonClass (Option (Fin (LongTails.Proofs.FreyaExecution.serialInput q).m)) := freyaOptionSingleton
        exact measurable_of_countable _
      have he := hlaw.integral_comp hG.aestronglyMeasurable
      have he' := integral_map (μ:=(LongTails.Algorithms.FreyaSerial.canonicalLaw
        (LongTails.Proofs.FreyaExecution.serialInput q) : Measure _))
        hout.aemeasurable hG.aestronglyMeasurable
      have hbound : (∫ z, ‖gradient (objective f)
          (execute O (factory q) (fun _ => N) z.1 z.2).1‖^2
            ∂(executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))) ≤
          2*(objective f q.x0-lower)/(q.η*q.K) := by
        exact (he.trans he').trans_le hrate.2
      refine ⟨hi,hbound,?_⟩
      intro ε hε hKε
      have hKR : (0 : ℝ)<q.K := Nat.cast_pos.mpr hK
      have hh := (div_le_iff₀ (mul_pos hη hε)).mp hKε
      apply hbound.trans
      apply (div_le_iff₀ (mul_pos hη hKR)).mpr
      nlinarith


theorem family_tuning_legal (p : Family) (hS : 0 < p.S)
    (hρ : 0 < p.ρ) (hρone : p.ρ ≤ 1) (hL : 0 ≤ p.Lminus) (hD : 0 ≤ p.Lpm)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hA : 0 < familyCoefficient p.toWorkers.toBase p.S p.ρ) :
    0 < familyStep p.toWorkers.toBase p.S p.ρ ∧
      1 ≤ familyHorizon p.toWorkers.toBase p.S p.ρ ∧
      2 * p.Δ / (familyStep p.toWorkers.toBase p.S p.ρ *
        familyHorizon p.toWorkers.toBase p.S p.ρ) ≤ p.ε := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      have _ := hL
      have _ := hD
      have _ := hS
      have _ := hρ
      have _ := hρone
      have _ := hΔ
      let A := familyCoefficient p.toWorkers.toBase p.S p.ρ
      change 0 < A at hA
      have hη : 0 < familyStep p.toWorkers.toBase p.S p.ρ := by change 0 < 1 / A; positivity
      have hK : 1 ≤ familyHorizon p.toWorkers.toBase p.S p.ρ := le_max_left _ _
      have hKreal : (0 : ℝ) < familyHorizon p.toWorkers.toBase p.S p.ρ := by exact_mod_cast hK
      refine ⟨hη, hK, ?_⟩
      have hceil : 2 * p.Δ * A / p.ε ≤ (familyHorizon p.toWorkers.toBase p.S p.ρ : ℝ) := by
        exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈2 * p.Δ * A / p.ε⌉₊))
      have hnum : 2 * p.Δ * A ≤ (familyHorizon p.toWorkers.toBase p.S p.ρ : ℝ) * p.ε :=
        (div_le_iff₀ hε).mp hceil
      apply (div_le_iff₀ (mul_pos hη hKreal)).mpr
      change 2 * p.Δ ≤ p.ε * ((1 / A) * (familyHorizon p.toWorkers.toBase p.S p.ρ : ℝ))
      calc
        2 * p.Δ = (2 * p.Δ * A) * (1 / A) := by field_simp [hA.ne']
        _ ≤ ((familyHorizon p.toWorkers.toBase p.S p.ρ : ℝ) * p.ε) * (1 / A) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
        _ = p.ε * ((1 / A) * (familyHorizon p.toWorkers.toBase p.S p.ρ : ℝ)) := by ring


theorem iterations_execution_accuracy (p : LongTails.Setups.FreyaPageIterations.Params)
    (hp : LongTails.Setups.FreyaPageIterations.spec.valid p) (f : Fin p.m → Space p.d → ℝ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hO : LongTails.Setups.FreyaPageIterations.spec.admissible p f O) :
    LongTails.Setups.FreyaPageIterations.spec.successful p f
      (fun z : (LongTails.Algorithms.FreyaTuning.iterations (LongTails.Setups.FreyaPageIterations.publicInput p)).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (LongTails.Algorithms.FreyaTuning.iterations (LongTails.Setups.FreyaPageIterations.publicInput p)) (fun _ => p.n * p.m + (p.n * p.m + p.S) * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1)) z.1 z.2)
      ⟨((LongTails.Algorithms.FreyaTuning.iterations (LongTails.Setups.FreyaPageIterations.publicInput p)).law : Measure (LongTails.Algorithms.FreyaTuning.iterations (LongTails.Setups.FreyaPageIterations.publicInput p)).Seed).prod
        (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩ := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      have hbudget : eventLimit (familyRaw (LongTails.Setups.FreyaPageIterations.publicInput p) false) ≤
          p.n*p.m+(p.n*p.m+p.S)*(⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S)))/p.ε⌉₊+1) := by
        let C : ℕ := ⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S)))/p.ε⌉₊
        change p.n*p.m+max 1 C*max (p.n*p.m) p.S ≤ p.n*p.m+(p.n*p.m+p.S)*(C+1)
        have hK : max 1 C≤C+1 := by omega
        have hmax : max (p.n*p.m) p.S≤p.n*p.m+p.S := by omega
        have h := Nat.mul_le_mul hK hmax
        rw [Nat.mul_comm (C+1)] at h
        exact Nat.add_le_add_left h (p.n*p.m)
      dsimp only [LongTails.Setups.FreyaPageIterations.spec, LongTails.Setups.FreyaPageIterations.publicInput] at hp hO ⊢
      obtain ⟨hm,hL,hLplus,hD,hΔ,hε,hS,hρ,hρone,hn,hmono⟩ := hp
      obtain ⟨hf,hlower,hgap,hsmooth,hmean,hcentered,hservice,hind⟩ := hO
      have _ := hLplus
      have _ := hmono
      let B := p.n*p.m+(p.n*p.m+p.S)*(⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S)))/p.ε⌉₊+1)
      let success (A : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d) 1) : Prop :=
        Integrable (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
          ‖gradient (objective f) (execute O A (fun _ => B) z.1 z.2)‖^2)
          ((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k))) ∧
        (∫ z : A.Seed × ((k : ℕ) → O.Seed k),
          ‖gradient (objective f) (execute O A (fun _ => B) z.1 z.2)‖^2
          ∂((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)))) ≤ p.ε
      change success (iterations (LongTails.Setups.FreyaPageIterations.publicInput p))
      have hfobj : Differentiable ℝ (objective f) := by
        intro x
        delta objective
        simpa only [Finset.sum_apply] using ((HasFDerivAt.sum (u := Finset.univ)
          (fun i _ => (hf i x).hasGradientAt.hasFDerivAt)).const_mul (p.m : ℝ)⁻¹).differentiableAt
      by_cases hzero : p.Δ=0 ∨ p.Lminus=0
      · have hz : gradient (objective f) p.x0=0 := by
          rcases hzero with h | h
          · exact LongTails.Proofs.FreyaSerialAnalysis.zero_gap_stationary (objective f) hfobj p.lower hlower p.x0
              (by simpa only [h] using hgap)
          · exact LongTails.Proofs.FreyaSerialAnalysis.zero_smoothness_stationary (objective f) hfobj p.lower hlower
              (by intro x y; have hh := hsmooth x y; rw [h] at hh; exact hh) p.x0
        have halg : iterations (LongTails.Setups.FreyaPageIterations.publicInput p)=
            (constantPoint none p.x0 : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d) 1) := by
          delta iterations
          exact ite_eq_left hzero
        rw [halg]
        dsimp only [success]
        have hout (z : (constantPoint (none : Option (Request p.d p.m p.n)) p.x0).Seed × ((k : ℕ) → O.Seed k)) :
            execute O (constantPoint none p.x0) (fun _ => B) z.1 z.2=p.x0 := by
          erw [StochasticGradient.execute_advance]
          rfl
        simp only [hout,hz,norm_zero,zero_pow (by decide : 2≠0)]
        exact ⟨integrable_const (0 : ℝ),by simpa only [integral_zero] using hε.le⟩
      · have hLpos : 0<p.Lminus := lt_of_le_of_ne hL (fun h => hzero (Or.inr h.symm))
        let q : Raw :=
          { d := p.d, m := p.m, n := p.n, x0 := p.x0,
            η := familyStep (LongTails.Setups.FreyaPageIterations.publicInput p).toWorkers.toBase p.S p.ρ,
            S := p.S, ρ := p.ρ, K := familyHorizon (LongTails.Setups.FreyaPageIterations.publicInput p).toWorkers.toBase p.S p.ρ,
            «prefix» := false }
        have hA : 0<familyCoefficient (LongTails.Setups.FreyaPageIterations.publicInput p).toWorkers.toBase p.S p.ρ := by
          change 0<p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S))
          positivity
        have htune := family_tuning_legal (LongTails.Setups.FreyaPageIterations.publicInput p)
          hS hρ hρone hL hD hΔ hε hA
        have hη : 0<q.η := htune.1
        have hK : 0<q.K := lt_of_lt_of_le Nat.zero_lt_one htune.2.1
        have hreg : RegularObjective f q.x0 p.lower p.Lminus p.Lplus p.Lpm p.Δ :=
          ⟨hf,hlower,hsmooth,hmean,hcentered,hgap⟩
        have hacc := iteration_accuracy q hm hn hS hK hρ hρone hη f
          p.lower p.Lminus p.Lplus p.Lpm p.Δ hL hD hreg (by exact le_rfl)
          p.τ O hservice hind B hbudget
        have halg : iterations (LongTails.Setups.FreyaPageIterations.publicInput p)=pointOnly q := by
          delta iterations
          exact ite_eq_right hzero
        rw [halg]
        have hout (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
            execute O (pointOnly q) (fun _ => B) seed ω=(execute O (factory q) (fun _ => B) seed ω).1 := by
          erw [StochasticGradient.execute_advance,StochasticGradient.execute_advance]
          rfl
        have he : (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
            ‖gradient (objective f) (execute O (pointOnly q) (fun _ => B) z.1 z.2)‖^2)=ᵐ[(executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))]
            (fun z => ‖gradient (objective f) (execute O (factory q) (fun _ => B) z.1 z.2).1‖^2) :=
          Filter.Eventually.of_forall (fun z => congrArg (fun x => ‖gradient (objective f) x‖^2) (hout z.1 z.2))
        dsimp only [success]
        refine ⟨hacc.1.congr he.symm,(integral_congr_ae he).trans_le (hacc.2.1.trans ?_)⟩
        calc
          2*(objective f q.x0-p.lower)/(q.η*q.K) ≤ 2*p.Δ/(q.η*q.K) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (by norm_num))
              (mul_nonneg hη.le (Nat.cast_nonneg _))
          _ ≤ p.ε := htune.2.2


theorem iterations_cost (p : LongTails.Setups.FreyaPageIterations.Params)
    (hp : LongTails.Setups.FreyaPageIterations.spec.valid p) :
    eventLimit (familyRaw (LongTails.Setups.FreyaPageIterations.publicInput p) false) ≤ p.n * p.m + (p.n * p.m + p.S) * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1) := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      have _ := hp
      let C : ℕ := ⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1-p.ρ)/(p.ρ*p.S))) / p.ε⌉₊
      change p.n*p.m + max 1 C * max (p.n*p.m) p.S ≤ p.n*p.m + (p.n*p.m + p.S)*(C+1)
      have hK : max 1 C ≤ C+1 := by omega
      have hmax : max (p.n*p.m) p.S ≤ p.n*p.m + p.S := by omega
      have h := Nat.mul_le_mul hK hmax
      rw [Nat.mul_comm (C+1)] at h
      exact Nat.add_le_add_left h (p.n*p.m)


end LongTails.Proofs.FreyaIterations
