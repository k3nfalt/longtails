import LongTails.Template
import LongTails.Proofs.FreyaIterations
import LongTails.Setups.FreyaPageTime

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Proofs.FreyaFreeTime

open LongTails.Setups.FreyaModel LongTails.Proofs.FreyaCollectors LongTails.Setups.FreyaIndependence
open LongTails.Algorithms.FreyaInputs LongTails.Algorithms.FreyaRandomness
open LongTails.Algorithms.FreyaPage LongTails.Algorithms.FreyaTuning

theorem free_time_accuracy (p : Family) (hm : 0 < p.m) (hn : 0 < p.n)
    (hS : 0 < p.S) (hρ : 0 < p.ρ) (hρone : p.ρ ≤ 1)
    (hL : 0 ≤ p.Lminus) (hD : 0 ≤ p.Lpm) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hA : 0 < familyCoefficient p.toWorkers.toBase p.S p.ρ)
    (hlarge : largeSample p.m p.n) (f : Fin p.m → Space p.d → ℝ) (lower Lplus : ℝ)
    (hreg : RegularObjective f p.x0 lower p.Lminus Lplus p.Lpm p.Δ)
    (τ : Fin p.n → ℝ≥0∞) (hmono : Monotone τ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hservice : PrimitiveService f τ O)
    (hind : batchScheduleIndependent (familyRaw p true) f τ O)
    (N : ℕ) (hN : eventLimit (familyRaw p true) ≤ N) :
    let q := familyRaw p true
    let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
    let out := fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
      execute O (factory q) (fun _ => N) z.1 z.2
    Integrable (fun z => ‖gradient (objective f) (out z).1‖ ^ 2) P ∧
      (∫ z, ‖gradient (objective f) (out z).1‖ ^ 2 ∂P) ≤ p.ε ∧
      (∫⁻ z, ((out z).2 : ℝ≥0∞) ∂P) ≤ 12 * (equilibriumTime τ (p.m : ℝ≥0∞)) + ENNReal.ofReal (48 * p.Δ / p.ε * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S)))) * (ENNReal.ofReal p.ρ * (equilibriumTime τ (p.m : ℝ≥0∞)) + ENNReal.ofReal (1-p.ρ) * (equilibriumTime τ (p.S : ℝ≥0∞))) := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      let q := familyRaw p true
      have htune := LongTails.Proofs.FreyaIterations.family_tuning_legal p hS hρ hρone hL hD hΔ hε hA
      have hη : 0<q.η := htune.1
      have hK : 0<q.K := lt_of_lt_of_le Nat.zero_lt_one htune.2.1
      have hacc := LongTails.Proofs.FreyaIterations.iteration_accuracy q hm hn hS hK hρ hρone hη f
        lower p.Lminus Lplus p.Lpm p.Δ hL hD hreg (by exact le_rfl) τ O hservice hind N hN
      refine ⟨hacc.1,hacc.2.1.trans ?_,?_⟩
      · calc
          2*(objective f q.x0-lower)/(q.η*q.K) ≤ 2*p.Δ/(q.η*q.K) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hreg.gap (by norm_num))
              (mul_nonneg hη.le (Nat.cast_nonneg _))
          _ ≤ p.ε := htune.2.2
      · have hcost := (LongTails.Proofs.FreyaExecution.cost_composition q hm hn hS hK hρ hρone f τ hmono O hservice N hN).2.2 hlarge
        let A := familyCoefficient p.toWorkers.toBase p.S p.ρ
        let C : ℝ := 2*p.Δ*A/p.ε
        have hC : 0≤C := by dsimp only [C]; positivity
        have hceil : (⌈C⌉₊ : ℝ)<C+1 := Nat.ceil_lt_add_one hC
        have hround : (rounds q : ℝ)≤C := by
          change ((max 1 ⌈C⌉₊-1 : ℕ) : ℝ)≤C
          rw [Nat.cast_sub (le_max_left _ _),Nat.cast_one]
          by_cases hc : ⌈C⌉₊≤1
          · rw [max_eq_left hc,Nat.cast_one,sub_self]
            exact hC
          · rw [max_eq_right (by omega)]
            linarith
        have hc : (5 : ℝ≥0∞)*(rounds q : ℝ≥0∞)≤ENNReal.ofReal (48*p.Δ/p.ε*A) := by
          calc
            (5 : ℝ≥0∞)*(rounds q : ℝ≥0∞)=ENNReal.ofReal (5*(rounds q : ℝ)) := by
              rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_natCast]
              norm_num
            _ ≤ ENNReal.ofReal (48*p.Δ/p.ε*A) := ENNReal.ofReal_le_ofReal (by
              calc
                5*(rounds q : ℝ)≤5*C := mul_le_mul_of_nonneg_left hround (by norm_num)
                _ ≤ 24*C := by nlinarith
                _ = 48*p.Δ/p.ε*A := by dsimp only [C]; ring)
        let tm := equilibriumTime τ p.m
        let ts := equilibriumTime τ p.S
        let a := ENNReal.ofReal p.ρ
        let b := ENNReal.ofReal (1-p.ρ)
        change _ ≤ 12*tm+ENNReal.ofReal (48*p.Δ/p.ε*A)*(a*tm+b*ts)
        calc
          _ ≤ 5*tm+(rounds q : ℝ≥0∞)*(a*(5*tm)+b*(4*ts)) := hcost
          _ ≤ 5*tm+(rounds q : ℝ≥0∞)*(a*(5*tm)+b*(5*ts)) := by gcongr; norm_num
          _ = 5*tm+(5*(rounds q : ℝ≥0∞))*(a*tm+b*ts) := by ring
          _ ≤ 12*tm+ENNReal.ofReal (48*p.Δ/p.ε*A)*(a*tm+b*ts) := by gcongr; norm_num


theorem free_time_execution_accuracy (p : LongTails.Setups.FreyaPageTime.Params)
    (hp : LongTails.Setups.FreyaPageTime.spec.valid p) (f : Fin p.m → Space p.d → ℝ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hO : LongTails.Setups.FreyaPageTime.spec.admissible p f O) :
    LongTails.Setups.FreyaPageTime.spec.successful p f
      (fun z : (LongTails.Algorithms.FreyaTuning.freeTime (LongTails.Setups.FreyaPageTime.publicInput p)).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (LongTails.Algorithms.FreyaTuning.freeTime (LongTails.Setups.FreyaPageTime.publicInput p)) (fun _ => p.n * p.m + (p.n * p.m + p.S) * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1)) z.1 z.2)
      ⟨((LongTails.Algorithms.FreyaTuning.freeTime (LongTails.Setups.FreyaPageTime.publicInput p)).law : Measure (LongTails.Algorithms.FreyaTuning.freeTime (LongTails.Setups.FreyaPageTime.publicInput p)).Seed).prod
        (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩ := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      have hbudget : eventLimit (familyRaw (LongTails.Setups.FreyaPageTime.publicInput p) true) ≤
          p.n*p.m+(p.n*p.m+p.S)*(⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S)))/p.ε⌉₊+1) := by
        let C : ℕ := ⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S)))/p.ε⌉₊
        change p.n*p.m+max 1 C*max (p.n*p.m) p.S ≤ p.n*p.m+(p.n*p.m+p.S)*(C+1)
        have hK : max 1 C≤C+1 := by omega
        have hmax : max (p.n*p.m) p.S≤p.n*p.m+p.S := by omega
        have h := Nat.mul_le_mul hK hmax
        rw [Nat.mul_comm (C+1)] at h
        exact Nat.add_le_add_left h (p.n*p.m)
      dsimp only [LongTails.Setups.FreyaPageTime.spec, LongTails.Setups.FreyaPageTime.publicInput] at hp hO ⊢
      obtain ⟨hm,hL,hLplus,hD,hΔ,hε,hS,hρ,hρone,hn,hmono,hlarge⟩ := hp
      obtain ⟨hf,hlower,hgap,hsmooth,hmean,hcentered,hservice,hind⟩ := hO
      have _ := hLplus
      let B := p.n*p.m+(p.n*p.m+p.S)*(⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S)))/p.ε⌉₊+1)
      let success (A : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) : Prop :=
        let P := ((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)))
        let out := fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => B) z.1 z.2
        Integrable (fun z => ‖gradient (objective f) (out z).1‖^2) P ∧
        (∫ z, ‖gradient (objective f) (out z).1‖^2 ∂P) ≤ p.ε ∧
        (∫⁻ z, ((out z).2 : ℝ≥0∞) ∂P) ≤
          12*equilibriumTime p.τ p.m+ENNReal.ofReal (48*p.Δ/p.ε*(p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S))))*
          (ENNReal.ofReal p.ρ*equilibriumTime p.τ p.m+ENNReal.ofReal (1-p.ρ)*equilibriumTime p.τ p.S)
      change success (freeTime (LongTails.Setups.FreyaPageTime.publicInput p))
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
        have halg : freeTime (LongTails.Setups.FreyaPageTime.publicInput p)=
            (constantPoint none (p.x0,0) : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) := by
          delta freeTime
          exact ite_eq_left hzero
        rw [halg]
        dsimp only [success]
        have hout (z : (constantPoint (none : Option (Request p.d p.m p.n)) (p.x0,(0 : ℝ≥0))).Seed × ((k : ℕ) → O.Seed k)) :
            execute O (constantPoint none (p.x0,0)) (fun _ => B) z.1 z.2=(p.x0,0) := by
          erw [execute_advance_history]
          rfl
        simp only [hout,hz,norm_zero,zero_pow (by decide : 2≠0),ENNReal.coe_zero,lintegral_zero]
        exact ⟨integrable_const (0 : ℝ),by simpa only [integral_zero] using hε.le,zero_le⟩
      · have hLpos : 0<p.Lminus := lt_of_le_of_ne hL (fun h => hzero (Or.inr h.symm))
        have hA : 0<familyCoefficient (LongTails.Setups.FreyaPageTime.publicInput p).toWorkers.toBase p.S p.ρ := by
          change 0<p.Lminus+p.Lpm*Real.sqrt ((1-p.ρ)/(p.ρ*p.S))
          positivity
        have hreg : RegularObjective f p.x0 p.lower p.Lminus p.Lplus p.Lpm p.Δ :=
          ⟨hf,hlower,hsmooth,hmean,hcentered,hgap⟩
        have hacc := free_time_accuracy (LongTails.Setups.FreyaPageTime.publicInput p)
          hm hn hS hρ hρone hL hD hΔ hε hA hlarge f p.lower p.Lplus hreg
          p.τ hmono O hservice hind B hbudget
        have halg : freeTime (LongTails.Setups.FreyaPageTime.publicInput p)=
            factory (familyRaw (LongTails.Setups.FreyaPageTime.publicInput p) true) := by
          delta freeTime
          exact ite_eq_right hzero
        rw [halg]
        exact hacc


theorem free_time_cost (p : LongTails.Setups.FreyaPageTime.Params)
    (hp : LongTails.Setups.FreyaPageTime.spec.valid p) :
    eventLimit (familyRaw (LongTails.Setups.FreyaPageTime.publicInput p) true) ≤ p.n * p.m + (p.n * p.m + p.S) * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt ((1 - p.ρ) / (p.ρ * p.S))) / p.ε⌉₊ + 1) := by
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


end LongTails.Proofs.FreyaFreeTime
