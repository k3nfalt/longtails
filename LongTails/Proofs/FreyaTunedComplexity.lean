import LongTails.Template
import LongTails.Proofs.FreyaFreeTime
import LongTails.Proofs.FreyaParameterTuning
import LongTails.Setups.FreyaPageOptimizedTime
import LongTails.Setups.FreyaPageSimpleTime

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Proofs.FreyaTunedComplexity

open LongTails.Proofs.FreyaModel LongTails.Proofs.FreyaCollectors LongTails.Proofs.FreyaIndependence
open LongTails.Algorithms.FreyaInputs LongTails.Algorithms.FreyaRandomness
open LongTails.Algorithms.FreyaPage LongTails.Algorithms.FreyaTuning

open LongTails.Proofs.FreyaParameterTuning

theorem optimized_event_budget (p : LongTails.Setups.FreyaPageOptimizedTime.Params)
    (hp : LongTails.Setups.FreyaPageOptimizedTime.spec.valid p) :
    eventLimit (optimizedRaw (LongTails.Setups.FreyaPageOptimizedTime.publicInput p)) ≤ p.n * p.m * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt p.m) / p.ε⌉₊ + 2) := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      dsimp only [LongTails.Setups.FreyaPageOptimizedTime.spec,LongTails.Setups.FreyaPageOptimizedTime.publicInput] at hp
      obtain ⟨hm,hL,hLp,hD,hΔ,hε,hn,hmono,hlarge⟩ := hp
      have _ := hLp
      have _ := hlarge
      let a := LongTails.Setups.FreyaPageOptimizedTime.publicInput p
      obtain ⟨hS,hSm,hmin⟩ := finite_batch_minimum a hm
      have _ := hmin
      have hA : familyCoefficient a.toWorkers.toBase (optimizedBatch a) (optimizedProbability a) ≤
          p.Lminus+p.Lpm*Real.sqrt p.m := by
        by_cases hz : p.Lminus=0
        · have hprob : optimizedProbability a=1 := by
            delta optimizedProbability
            dsimp only
            split
            · rfl
            · apply ite_eq_left
              change ENNReal.ofReal p.Lminus*_≤ENNReal.ofReal p.Lminus*_+_
              rw [hz,ENNReal.ofReal_zero,zero_mul,zero_mul,zero_add]
              exact zero_le
          change p.Lminus+p.Lpm*Real.sqrt ((1-optimizedProbability a)/(optimizedProbability a*optimizedBatch a))≤_
          rw [hprob]
          norm_num
          positivity
        · have hpos : 0<p.Lminus := lt_of_le_of_ne hL (Ne.symm hz)
          obtain ⟨_,_,_,_,_,_,hc,_⟩ := optimized_tuning_legal a hm hn hpos hD hΔ hε hmono
          exact hc
      let C : ℕ := ⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt p.m)/p.ε⌉₊
      have hc : ⌈2*p.Δ*familyCoefficient a.toWorkers.toBase (optimizedBatch a) (optimizedProbability a)/p.ε⌉₊≤C :=
        Nat.ceil_mono (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by positivity)) hε.le)
      have hK : optimizedHorizon a≤C+1 := by
        change max 1 ⌈2*p.Δ*familyCoefficient a.toWorkers.toBase (optimizedBatch a) (optimizedProbability a)/p.ε⌉₊≤C+1
        omega
      have hSmn : optimizedBatch a≤p.n*p.m := hSm.trans (by change p.m≤p.n*p.m; nlinarith)
      change p.n*p.m+optimizedHorizon a*max (p.n*p.m) (optimizedBatch a)≤p.n*p.m*(C+2)
      rw [max_eq_left hSmn]
      nlinarith


theorem simple_event_budget (p : LongTails.Setups.FreyaPageSimpleTime.Params)
    (hp : LongTails.Setups.FreyaPageSimpleTime.spec.valid p) :
    eventLimit (simpleRaw (LongTails.Setups.FreyaPageSimpleTime.publicInput p)) ≤ p.n * p.m * (⌈4 * p.Δ * max p.Lminus p.Lpm / p.ε⌉₊ + 2) := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      dsimp only [LongTails.Setups.FreyaPageSimpleTime.spec,LongTails.Setups.FreyaPageSimpleTime.publicInput] at hp
      obtain ⟨hm,hL,hLp,hD,hΔ,hε,hn,hmono,hlarge⟩ := hp
      have _ := hLp
      have _ := hmono
      have _ := hlarge
      let a := LongTails.Setups.FreyaPageSimpleTime.publicInput p
      have hSm : simpleBatch a≤p.m := by
        change ⌈Real.sqrt p.m⌉₊≤p.m
        apply Nat.ceil_le.mpr
        have hmreal : (1 : ℝ)≤p.m := by exact_mod_cast hm
        exact (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
      have hA := simple_coefficient a hm hL hD
      let C : ℕ := ⌈4*p.Δ*max p.Lminus p.Lpm/p.ε⌉₊
      have hc : ⌈2*p.Δ*familyCoefficient a.toWorkers.toBase (simpleBatch a) (simpleProbability a)/p.ε⌉₊≤C := by
        apply Nat.ceil_mono
        calc
          _ ≤ 2*p.Δ*(2*max p.Lminus p.Lpm)/p.ε :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by positivity)) hε.le
          _ = _ := by ring
      have hK : simpleHorizon a≤C+1 := by
        change max 1 ⌈2*p.Δ*familyCoefficient a.toWorkers.toBase (simpleBatch a) (simpleProbability a)/p.ε⌉₊≤C+1
        omega
      have hSmn : simpleBatch a≤p.n*p.m := hSm.trans (by nlinarith)
      change p.n*p.m+simpleHorizon a*max (p.n*p.m) (simpleBatch a)≤p.n*p.m*(C+2)
      rw [max_eq_left hSmn]
      nlinarith


theorem literal_time_bound (p : Family) (hm : 0 < p.m) (hn : 0 < p.n)
    (hS : 0 < p.S) (hSm : p.S ≤ p.m) (hρ : 0 < p.ρ) (hρone : p.ρ ≤ 1)
    (hL : 0 ≤ p.Lminus) (hD : 0 ≤ p.Lpm) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hlarge : largeSample p.m p.n) (f : Fin p.m → Space p.d → ℝ)
    (τ : Fin p.n → ℝ≥0∞) (hmono : Monotone τ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hservice : PrimitiveService f τ O)
    (N : ℕ) (hN : eventLimit (familyRaw p false) ≤ N) :
    let q := familyRaw p false
    let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
    (∫⁻ z, ((execute O (factory q) (fun _ => N) z.1 z.2).2 : ℝ≥0∞) ∂P) ≤
      10 * equilibriumTime τ p.m +
        ENNReal.ofReal (10 * p.Δ * familyCoefficient p.toWorkers.toBase p.S p.ρ / p.ε) *
          (ENNReal.ofReal p.ρ * equilibriumTime τ p.m +
            ENNReal.ofReal (1 - p.ρ) * equilibriumTime τ p.S) := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      have _ := hS
      let q := familyRaw p false
      have hK : 0<q.K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      have hcost := (LongTails.Proofs.FreyaExecution.cost_composition q hm hn hS hK hρ hρone f τ hmono O hservice N hN).2.2 hlarge
      let A := familyCoefficient p.toWorkers.toBase p.S p.ρ
      let C : ℝ := 2*p.Δ*A/p.ε
      have hA : 0≤A := by change 0≤p.Lminus+p.Lpm*Real.sqrt _; positivity
      have hC : 0≤C := by dsimp only [C]; positivity
      have hceil : (⌈C⌉₊ : ℝ)<C+1 := Nat.ceil_lt_add_one hC
      have hround : (rounds q : ℝ)≤C+1 := by
        change ((max 1 ⌈C⌉₊ : ℕ) : ℝ)≤C+1
        by_cases hc : ⌈C⌉₊≤1
        · rw [max_eq_left hc,Nat.cast_one]
          linarith
        · rw [max_eq_right (by omega)]
          exact hceil.le
      have hc : (5 : ℝ≥0∞)*(rounds q : ℝ≥0∞)≤5+ENNReal.ofReal (10*p.Δ*A/p.ε) := by
        calc
          (5 : ℝ≥0∞)*(rounds q : ℝ≥0∞)=ENNReal.ofReal (5*(rounds q : ℝ)) := by
            rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_natCast]
            norm_num
          _ ≤ ENNReal.ofReal (5+10*p.Δ*A/p.ε) := ENNReal.ofReal_le_ofReal (by
            calc
              5*(rounds q : ℝ)≤5*(C+1) := mul_le_mul_of_nonneg_left hround (by norm_num)
              _ = 5+10*p.Δ*A/p.ε := by dsimp only [C]; ring)
          _ = 5+ENNReal.ofReal (10*p.Δ*A/p.ε) := by
            rw [ENNReal.ofReal_add (by norm_num) (by positivity)]
            norm_num
      let tm := equilibriumTime τ p.m
      let ts := equilibriumTime τ p.S
      let a := ENNReal.ofReal p.ρ
      let b := ENNReal.ofReal (1-p.ρ)
      have hts : ts≤tm := (LongTails.Proofs.FreyaEquilibrium.equilibrium_comparisons τ).1 (by exact_mod_cast hSm)
      have hab : a+b=1 := by
        dsimp only [a,b]
        rw [←ENNReal.ofReal_add hρ.le (sub_nonneg.mpr hρone)]
        norm_num
      have hmix : a*tm+b*ts≤tm := by
        calc
          a*tm+b*ts≤a*tm+b*tm := by gcongr
          _ = tm := by rw [←add_mul,hab,one_mul]
      change _ ≤ 10*tm+ENNReal.ofReal (10*p.Δ*A/p.ε)*(a*tm+b*ts)
      calc
        _ ≤ 5*tm+(rounds q : ℝ≥0∞)*(a*(5*tm)+b*(4*ts)) := hcost
        _ ≤ 5*tm+(rounds q : ℝ≥0∞)*(a*(5*tm)+b*(5*ts)) := by gcongr; norm_num
        _ = 5*tm+(5*(rounds q : ℝ≥0∞))*(a*tm+b*ts) := by ring
        _ ≤ 5*tm+(5+ENNReal.ofReal (10*p.Δ*A/p.ε))*(a*tm+b*ts) := by gcongr
        _ = 5*tm+5*(a*tm+b*ts)+ENNReal.ofReal (10*p.Δ*A/p.ε)*(a*tm+b*ts) := by ring
        _ ≤ 5*tm+5*tm+ENNReal.ofReal (10*p.Δ*A/p.ε)*(a*tm+b*ts) := by gcongr
        _ = 10*tm+ENNReal.ofReal (10*p.Δ*A/p.ε)*(a*tm+b*ts) := by ring


theorem optimized_accuracy (p : LongTails.Setups.FreyaPageOptimizedTime.Params)
    (hp : LongTails.Setups.FreyaPageOptimizedTime.spec.valid p) (f : Fin p.m → Space p.d → ℝ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hO : LongTails.Setups.FreyaPageOptimizedTime.spec.admissible p f O) :
    let A := LongTails.Algorithms.FreyaTuning.optimized (LongTails.Setups.FreyaPageOptimizedTime.publicInput p)
    let P := (A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k))
    let out := fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
      execute O A (fun _ => p.n * p.m * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt p.m) / p.ε⌉₊ + 2)) z.1 z.2
    Integrable (fun z => ‖gradient (objective f) (out z).1‖ ^ 2) P ∧
      (∫ z, ‖gradient (objective f) (out z).1‖ ^ 2 ∂P) ≤ p.ε := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      have hbudget := optimized_event_budget p hp
      dsimp only [LongTails.Setups.FreyaPageOptimizedTime.spec,LongTails.Setups.FreyaPageOptimizedTime.publicInput] at hp hO
      obtain ⟨hm,hL,hLp,hD,hΔ,hε,hn,hmono,hlarge⟩ := hp
      obtain ⟨hf,hlower,hgap,hsmooth,hmean,hcentered,hservice,hind⟩ := hO
      have _ := hLp
      have _ := hlarge
      let a := LongTails.Setups.FreyaPageOptimizedTime.publicInput p
      let B : ℕ := p.n*p.m*(⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt p.m)/p.ε⌉₊+2)
      let success (A : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) : Prop :=
        let P := ((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)))
        let out := fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => B) z.1 z.2
        Integrable (fun z => ‖gradient (objective f) (out z).1‖^2) P ∧
        (∫ z, ‖gradient (objective f) (out z).1‖^2 ∂P) ≤ p.ε
      change success (optimized a)
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
        have halg : optimized a=
            (constantPoint none (p.x0,0) : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) := by
          delta optimized
          exact ite_eq_left hzero
        rw [halg]
        dsimp only [success]
        have hout (z : (constantPoint (none : Option (Request p.d p.m p.n)) (p.x0,(0 : ℝ≥0))).Seed × ((k : ℕ) → O.Seed k)) :
            execute O (constantPoint none (p.x0,0)) (fun _ => B) z.1 z.2=(p.x0,0) := by
          erw [StochasticGradient.execute_advance]
          rfl
        simp only [hout,hz,norm_zero,zero_pow (by decide : 2≠0)]
        exact ⟨integrable_const (0 : ℝ),by simpa only [integral_zero] using hε.le⟩
      · have hLpos : 0<p.Lminus := lt_of_le_of_ne hL (fun h => hzero (Or.inr h.symm))
        obtain ⟨hS,hSm,hρ,hρone,hη,hK,hcoeff,hrate⟩ := optimized_tuning_legal a hm hn hLpos hD hΔ hε hmono
        have _ := hSm
        have _ := hcoeff
        let q : Raw :=
          { d := p.d, m := p.m, n := p.n, x0 := p.x0,
            η := optimizedStep a, S := optimizedBatch a, ρ := optimizedProbability a,
            K := optimizedHorizon a, «prefix» := false }
        have hreg : RegularObjective f q.x0 p.lower p.Lminus p.Lplus p.Lpm p.Δ :=
          ⟨hf,hlower,hsmooth,hmean,hcentered,hgap⟩
        have hacc := LongTails.Proofs.FreyaIterations.iteration_accuracy q hm hn
          (lt_of_lt_of_le Nat.zero_lt_one hS) (lt_of_lt_of_le Nat.zero_lt_one hK)
          hρ hρone hη f p.lower p.Lminus p.Lplus p.Lpm p.Δ hL hD hreg (by exact le_rfl)
          p.τ O hservice hind B hbudget
        have halg : optimized a=factory q := by
          delta optimized
          exact ite_eq_right hzero
        rw [halg]
        refine ⟨hacc.1,hacc.2.1.trans ?_⟩
        calc
          2*(objective f q.x0-p.lower)/(q.η*q.K) ≤ 2*p.Δ/(q.η*q.K) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (by norm_num))
              (mul_nonneg hη.le (Nat.cast_nonneg _))
          _ ≤ p.ε := hrate


theorem optimized_time (p : LongTails.Setups.FreyaPageOptimizedTime.Params)
    (hp : LongTails.Setups.FreyaPageOptimizedTime.spec.valid p) (f : Fin p.m → Space p.d → ℝ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hO : LongTails.Setups.FreyaPageOptimizedTime.spec.admissible p f O) :
    let A := LongTails.Algorithms.FreyaTuning.optimized (LongTails.Setups.FreyaPageOptimizedTime.publicInput p)
    let P := (A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k))
    let out := fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
      execute O A (fun _ => p.n * p.m * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt p.m) / p.ε⌉₊ + 2)) z.1 z.2
    (∫⁻ z, ((out z).2 : ℝ≥0∞) ∂P) ≤ 12 * (equilibriumTime p.τ (p.m : ℝ≥0∞)) + ENNReal.ofReal (96 * p.Δ / p.ε) * (⨅ S : Fin p.m, min (ENNReal.ofReal p.Lminus * (equilibriumTime p.τ (p.m : ℝ≥0∞))) (ENNReal.ofReal p.Lminus * equilibriumTime p.τ (S.val + 1) + ENNReal.ofReal p.Lpm * (((equilibriumTime p.τ (p.m : ℝ≥0∞)) * equilibriumTime p.τ (S.val + 1) / (S.val + 1)) ^ (1 / (2 : ℝ))))) := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      have hbudget := optimized_event_budget p hp
      dsimp only [LongTails.Setups.FreyaPageOptimizedTime.spec,LongTails.Setups.FreyaPageOptimizedTime.publicInput] at hp hO
      obtain ⟨hm,hL,hLp,hD,hΔ,hε,hn,hmono,hlarge⟩ := hp
      obtain ⟨hf,hlower,hgap,hsmooth,hmean,hcentered,hservice,hind⟩ := hO
      have _ := hLp
      have _ := hf
      have _ := hlower
      have _ := hgap
      have _ := hsmooth
      have _ := hmean
      have _ := hcentered
      have _ := hind
      let a := LongTails.Setups.FreyaPageOptimizedTime.publicInput p
      let B : ℕ := p.n*p.m*(⌈2*p.Δ*(p.Lminus+p.Lpm*Real.sqrt p.m)/p.ε⌉₊+2)
      let bound : ℝ≥0∞ := 12*equilibriumTime p.τ p.m+ENNReal.ofReal (96*p.Δ/p.ε)*(⨅ j : Fin p.m,batchObjective a (j.val+1))
      let success (A : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) : Prop :=
        (∫⁻ z : A.Seed × ((k : ℕ) → O.Seed k), ((execute O A (fun _ => B) z.1 z.2).2 : ℝ≥0∞)
          ∂((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)))) ≤ bound
      suffices h : success (optimized a) by
        dsimp only [success] at h
        convert h using 1
        · rfl
        · dsimp only [bound,batchObjective,a,LongTails.Setups.FreyaPageOptimizedTime.publicInput]
          simp only [Nat.cast_add,Nat.cast_one]
      by_cases hzero : p.Δ=0 ∨ p.Lminus=0
      · have halg : optimized a=
            (constantPoint none (p.x0,0) : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) := by
          delta optimized
          exact ite_eq_left hzero
        rw [halg]
        dsimp only [success]
        have hout (z : (constantPoint (none : Option (Request p.d p.m p.n)) (p.x0,(0 : ℝ≥0))).Seed × ((k : ℕ) → O.Seed k)) :
            execute O (constantPoint none (p.x0,0)) (fun _ => B) z.1 z.2=(p.x0,0) := by
          erw [StochasticGradient.execute_advance]
          rfl
        simp only [hout,ENNReal.coe_zero,lintegral_zero]
        exact zero_le
      · have hLpos : 0<p.Lminus := lt_of_le_of_ne hL (fun h => hzero (Or.inr h.symm))
        obtain ⟨hS,hSm,hρ,hρone,hη,hK,hcoeff,hrate⟩ := optimized_tuning_legal a hm hn hLpos hD hΔ hε hmono
        have _ := hcoeff
        have _ := hη
        have _ := hK
        have _ := hrate
        let fam : Family :=
          { d := p.d, m := p.m, n := p.n, x0 := p.x0,
            Lminus := p.Lminus, Lpm := p.Lpm, Δ := p.Δ, ε := p.ε,
            S := optimizedBatch a, ρ := optimizedProbability a }
        have htime := literal_time_bound fam hm hn (lt_of_lt_of_le Nat.zero_lt_one hS) hSm
          hρ hρone hL hD hΔ hε hlarge f p.τ hmono O hservice B hbudget
        have halg : optimized a=factory (familyRaw fam false) := by
          delta optimized
          exact ite_eq_right hzero
        rw [halg]
        dsimp only [success]
        let tm := equilibriumTime p.τ p.m
        let ts := equilibriumTime p.τ (optimizedBatch a)
        let A := familyCoefficient a.toWorkers.toBase (optimizedBatch a) (optimizedProbability a)
        let mix := ENNReal.ofReal (optimizedProbability a)*tm+ENNReal.ofReal (1-optimizedProbability a)*ts
        change _ ≤ 10*tm+ENNReal.ofReal (10*p.Δ*A/p.ε)*mix at htime
        by_cases htop : tm=⊤
        · change _ ≤ 12*tm+_
          simp only [htop,ENNReal.mul_top (by norm_num : (12 : ℝ≥0∞)≠0),top_add]
          exact le_top
        · by_cases hzeroT : tm=0
          · have hts : ts=0 := le_antisymm
              ((LongTails.Proofs.FreyaEquilibrium.equilibrium_comparisons p.τ).1 (by exact_mod_cast hSm) |>.trans_eq hzeroT) zero_le
            have hmz : mix=0 := by dsimp only [mix]; rw [hzeroT,hts,mul_zero,mul_zero,add_zero]
            rw [hzeroT,hmz,mul_zero,mul_zero,add_zero] at htime
            exact htime.trans zero_le
          · have hc := (optimized_comparison a hm hn hL hD hmono (lt_of_le_of_ne zero_le (Ne.symm hzeroT)) htop).1
            let obj := ⨅ j : Fin p.m,batchObjective a (j.val+1)
            change ENNReal.ofReal A*mix≤2*obj at hc
            have hΔε : 0≤p.Δ/p.ε := div_nonneg hΔ hε.le
            have hfactor : ENNReal.ofReal (10*p.Δ*A/p.ε)=ENNReal.ofReal (10*p.Δ/p.ε)*ENNReal.ofReal A := by
              rw [←ENNReal.ofReal_mul (by positivity)]
              congr 1
              ring
            have hnum : ENNReal.ofReal (10*p.Δ/p.ε)*(2 : ℝ≥0∞)≤ENNReal.ofReal (96*p.Δ/p.ε) := by
              calc
                _ = ENNReal.ofReal ((10*p.Δ/p.ε)*2) := by rw [ENNReal.ofReal_mul (by positivity)]; norm_num
                _ ≤ _ := ENNReal.ofReal_le_ofReal (by ring_nf at hΔε ⊢; linarith)
            change _ ≤ 12*tm+ENNReal.ofReal (96*p.Δ/p.ε)*obj
            calc
              _ ≤ 10*tm+ENNReal.ofReal (10*p.Δ*A/p.ε)*mix := htime
              _ = 10*tm+ENNReal.ofReal (10*p.Δ/p.ε)*(ENNReal.ofReal A*mix) := by rw [hfactor,mul_assoc]
              _ ≤ 12*tm+ENNReal.ofReal (10*p.Δ/p.ε)*(2*obj) := by gcongr; norm_num
              _ = 12*tm+(ENNReal.ofReal (10*p.Δ/p.ε)*2)*obj := by rw [mul_assoc]
              _ ≤ 12*tm+ENNReal.ofReal (96*p.Δ/p.ε)*obj := by gcongr


theorem simple_accuracy (p : LongTails.Setups.FreyaPageSimpleTime.Params)
    (hp : LongTails.Setups.FreyaPageSimpleTime.spec.valid p) (f : Fin p.m → Space p.d → ℝ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hO : LongTails.Setups.FreyaPageSimpleTime.spec.admissible p f O) :
    let A := LongTails.Algorithms.FreyaTuning.simple (LongTails.Setups.FreyaPageSimpleTime.publicInput p)
    let P := (A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k))
    let out := fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
      execute O A (fun _ => p.n * p.m * (⌈4 * p.Δ * max p.Lminus p.Lpm / p.ε⌉₊ + 2)) z.1 z.2
    Integrable (fun z => ‖gradient (objective f) (out z).1‖ ^ 2) P ∧
      (∫ z, ‖gradient (objective f) (out z).1‖ ^ 2 ∂P) ≤ p.ε := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      have hbudget := simple_event_budget p hp
      dsimp only [LongTails.Setups.FreyaPageSimpleTime.spec,LongTails.Setups.FreyaPageSimpleTime.publicInput] at hp hO
      obtain ⟨hm,hL,hLp,hD,hΔ,hε,hn,hmono,hlarge⟩ := hp
      obtain ⟨hf,hlower,hgap,hsmooth,hmean,hcentered,hservice,hind⟩ := hO
      have _ := hLp
      have _ := hlarge
      let a := LongTails.Setups.FreyaPageSimpleTime.publicInput p
      let B : ℕ := p.n*p.m*(⌈4*p.Δ*max p.Lminus p.Lpm/p.ε⌉₊+2)
      let success (A : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) : Prop :=
        let P := ((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)))
        let out := fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => B) z.1 z.2
        Integrable (fun z => ‖gradient (objective f) (out z).1‖^2) P ∧
        (∫ z, ‖gradient (objective f) (out z).1‖^2 ∂P) ≤ p.ε
      change success (simple a)
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
        have halg : simple a=
            (constantPoint none (p.x0,0) : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) := by
          delta simple
          exact ite_eq_left hzero
        rw [halg]
        dsimp only [success]
        have hout (z : (constantPoint (none : Option (Request p.d p.m p.n)) (p.x0,(0 : ℝ≥0))).Seed × ((k : ℕ) → O.Seed k)) :
            execute O (constantPoint none (p.x0,0)) (fun _ => B) z.1 z.2=(p.x0,0) := by
          erw [StochasticGradient.execute_advance]
          rfl
        simp only [hout,hz,norm_zero,zero_pow (by decide : 2≠0)]
        exact ⟨integrable_const (0 : ℝ),by simpa only [integral_zero] using hε.le⟩
      · have hLpos : 0<p.Lminus := lt_of_le_of_ne hL (fun h => hzero (Or.inr h.symm))
        have _ := hmono
        obtain ⟨hS,hSm,hρ,hρone,hη,hK,hrate⟩ := simple_tuning_legal a hm hLpos hD hΔ hε
        have _ := hSm
        let q : Raw :=
          { d := p.d, m := p.m, n := p.n, x0 := p.x0,
            η := simpleStep a, S := simpleBatch a, ρ := simpleProbability a,
            K := simpleHorizon a, «prefix» := false }
        have hreg : RegularObjective f q.x0 p.lower p.Lminus p.Lplus p.Lpm p.Δ :=
          ⟨hf,hlower,hsmooth,hmean,hcentered,hgap⟩
        have hacc := LongTails.Proofs.FreyaIterations.iteration_accuracy q hm hn
          (lt_of_lt_of_le Nat.zero_lt_one hS) (lt_of_lt_of_le Nat.zero_lt_one hK)
          hρ hρone hη f p.lower p.Lminus p.Lplus p.Lpm p.Δ hL hD hreg (by exact le_rfl)
          p.τ O hservice hind B hbudget
        have halg : simple a=factory q := by
          delta simple
          exact ite_eq_right hzero
        rw [halg]
        refine ⟨hacc.1,hacc.2.1.trans ?_⟩
        calc
          2*(objective f q.x0-p.lower)/(q.η*q.K) ≤ 2*p.Δ/(q.η*q.K) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (by norm_num))
              (mul_nonneg hη.le (Nat.cast_nonneg _))
          _ ≤ p.ε := hrate


theorem simple_time (p : LongTails.Setups.FreyaPageSimpleTime.Params)
    (hp : LongTails.Setups.FreyaPageSimpleTime.spec.valid p) (f : Fin p.m → Space p.d → ℝ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hO : LongTails.Setups.FreyaPageSimpleTime.spec.admissible p f O) :
    let A := LongTails.Algorithms.FreyaTuning.simple (LongTails.Setups.FreyaPageSimpleTime.publicInput p)
    let P := (A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k))
    let out := fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
      execute O A (fun _ => p.n * p.m * (⌈4 * p.Δ * max p.Lminus p.Lpm / p.ε⌉₊ + 2)) z.1 z.2
    (∫⁻ z, ((out z).2 : ℝ≥0∞) ∂P) ≤ 12 * (equilibriumTime p.τ (p.m : ℝ≥0∞)) + ENNReal.ofReal (192 * p.Δ * max p.Lminus p.Lpm / p.ε) * (equilibriumTime p.τ (ENNReal.ofReal (Real.sqrt p.m))) := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      have hbudget := simple_event_budget p hp
      dsimp only [LongTails.Setups.FreyaPageSimpleTime.spec,LongTails.Setups.FreyaPageSimpleTime.publicInput] at hp hO
      obtain ⟨hm,hL,hLp,hD,hΔ,hε,hn,hmono,hlarge⟩ := hp
      obtain ⟨hf,hlower,hgap,hsmooth,hmean,hcentered,hservice,hind⟩ := hO
      have _ := hLp
      have _ := hf
      have _ := hlower
      have _ := hgap
      have _ := hsmooth
      have _ := hmean
      have _ := hcentered
      have _ := hind
      let a := LongTails.Setups.FreyaPageSimpleTime.publicInput p
      let B : ℕ := p.n*p.m*(⌈4*p.Δ*max p.Lminus p.Lpm/p.ε⌉₊+2)
      let bound : ℝ≥0∞ := 12*equilibriumTime p.τ p.m+ENNReal.ofReal (192*p.Δ*max p.Lminus p.Lpm/p.ε)*equilibriumTime p.τ (ENNReal.ofReal (Real.sqrt p.m))
      let success (A : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) : Prop :=
        (∫⁻ z : A.Seed × ((k : ℕ) → O.Seed k), ((execute O A (fun _ => B) z.1 z.2).2 : ℝ≥0∞)
          ∂((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)))) ≤ bound
      change success (simple a)
      by_cases hzero : p.Δ=0 ∨ p.Lminus=0
      · have halg : simple a=
            (constantPoint none (p.x0,0) : Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1) := by
          delta simple
          exact ite_eq_left hzero
        rw [halg]
        dsimp only [success]
        have hout (z : (constantPoint (none : Option (Request p.d p.m p.n)) (p.x0,(0 : ℝ≥0))).Seed × ((k : ℕ) → O.Seed k)) :
            execute O (constantPoint none (p.x0,0)) (fun _ => B) z.1 z.2=(p.x0,0) := by
          erw [StochasticGradient.execute_advance]
          rfl
        simp only [hout,ENNReal.coe_zero,lintegral_zero]
        exact zero_le
      · have hLpos : 0<p.Lminus := lt_of_le_of_ne hL (fun h => hzero (Or.inr h.symm))
        obtain ⟨hS,hSm,hρ,hρone,hη,hK,hrate⟩ := simple_tuning_legal a hm hLpos hD hΔ hε
        have _ := hη
        have _ := hK
        have _ := hrate
        let fam : Family :=
          { d := p.d, m := p.m, n := p.n, x0 := p.x0,
            Lminus := p.Lminus, Lpm := p.Lpm, Δ := p.Δ, ε := p.ε,
            S := simpleBatch a, ρ := simpleProbability a }
        have htime := literal_time_bound fam hm hn (lt_of_lt_of_le Nat.zero_lt_one hS) hSm
          hρ hρone hL hD hΔ hε hlarge f p.τ hmono O hservice B hbudget
        have halg : simple a=factory (familyRaw fam false) := by
          delta simple
          exact ite_eq_right hzero
        rw [halg]
        dsimp only [success]
        let tm := equilibriumTime p.τ p.m
        let ts := equilibriumTime p.τ (simpleBatch a)
        let A := familyCoefficient a.toWorkers.toBase (simpleBatch a) (simpleProbability a)
        let mix := ENNReal.ofReal (simpleProbability a)*tm+ENNReal.ofReal (1-simpleProbability a)*ts
        change _ ≤ 10*tm+ENNReal.ofReal (10*p.Δ*A/p.ε)*mix at htime
        let M := max p.Lminus p.Lpm
        let troot := equilibriumTime p.τ (ENNReal.ofReal (Real.sqrt p.m))
        have hM : 0≤M := le_trans hL (le_max_left _ _)
        have hcoef : A≤2*M := simple_coefficient a hm hL hD
        obtain ⟨hfirst,hsecond⟩ := simple_time_comparisons a hm p.τ
        have hmix : mix≤2*troot := by
          calc
            mix≤troot+troot := add_le_add hfirst hsecond
            _ = 2*troot := by ring
        have hnum : ENNReal.ofReal (10*p.Δ*A/p.ε)*2≤ENNReal.ofReal (192*p.Δ*M/p.ε) := by
          calc
            _ = ENNReal.ofReal ((10*p.Δ*A/p.ε)*2) := by
              rw [ENNReal.ofReal_mul' (by norm_num : (0 : ℝ)≤2)]
              norm_num
            _ ≤ ENNReal.ofReal (192*p.Δ*M/p.ε) := ENNReal.ofReal_le_ofReal (by
              have hh := mul_le_mul_of_nonneg_left hcoef (show 0≤20*p.Δ/p.ε by positivity)
              have hnon : 0≤p.Δ*M/p.ε := by positivity
              ring_nf at hh hnon ⊢
              linarith)
        change _ ≤ 12*tm+ENNReal.ofReal (192*p.Δ*M/p.ε)*troot
        calc
          _ ≤ 10*tm+ENNReal.ofReal (10*p.Δ*A/p.ε)*mix := htime
          _ ≤ 12*tm+ENNReal.ofReal (10*p.Δ*A/p.ε)*(2*troot) := by gcongr; norm_num
          _ = 12*tm+(ENNReal.ofReal (10*p.Δ*A/p.ε)*2)*troot := by ring
          _ ≤ 12*tm+ENNReal.ofReal (192*p.Δ*M/p.ε)*troot := by gcongr


theorem optimized_factory (p : Optimized) :
    (p.Δ = 0 ∨ p.Lminus = 0 → optimized p = constantPoint none (p.x0, 0)) ∧
      (p.Δ ≠ 0 → p.Lminus ≠ 0 → optimized p = literal (optimizedRaw p)) ∧
      (equilibriumTime p.τ p.m = 0 ∨ equilibriumTime p.τ p.m = ⊤ →
        optimizedProbability p = 1) ∧
      (optimizedRaw p).S = optimizedBatch p ∧
      (optimizedRaw p).ρ = optimizedProbability p ∧
      (optimizedRaw p).η = optimizedStep p ∧
      (optimizedRaw p).K = optimizedHorizon p := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
      · intro h
        delta optimized
        exact ite_eq_left h
      · intro hΔ hL
        delta optimized
        exact ite_eq_right (not_or.mpr ⟨hΔ, hL⟩)
      · intro h
        delta optimizedProbability
        exact ite_eq_left h


noncomputable def normalizedInput (p : Simple) (τ : Fin p.n → ℝ≥0∞) : Optimized where
  d := p.d
  m := p.m
  n := p.n
  x0 := p.x0
  Δ := p.Δ
  ε := p.ε
  Lminus := max p.Lminus p.Lpm
  Lpm := max p.Lminus p.Lpm
  τ := τ

theorem normalized_optimality (p : Simple) (hm : 0 < p.m) (hn : 0 < p.n)
    (hL : 0 ≤ p.Lminus) (hD : 0 ≤ p.Lpm) (hM : 0 < max p.Lminus p.Lpm)
    (hnm : (p.n : ℝ) ≤ Real.sqrt p.m) (τ : Fin p.n → ℝ≥0∞) (hmono : Monotone τ) :
    ∀ S : ℕ, 0 < S → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      timeCoefficient (normalizedInput p τ) (simpleBatch p) (simpleProbability p) ≤
        20 * timeCoefficient (normalizedInput p τ) S ρ := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      classical
      have _ := hL
      have _ := hD
      let M := max p.Lminus p.Lpm
      let a := normalizedInput p τ
      have hMs : (a.Lpm*Real.sqrt a.m/a.Lminus)=Real.sqrt p.m := by
        change M*Real.sqrt p.m/M=Real.sqrt p.m
        field_simp [show M≠0 from hM.ne']
      have hs : Real.sqrt p.m≤p.m := by
        apply Real.sqrt_le_iff.mpr
        have hmreal : (1 : ℝ)≤p.m := by exact_mod_cast hm
        exact ⟨by positivity,by nlinarith⟩
      have hratio := ratio_case_one a hm hn hM hM hmono
        (by rw [hMs]; exact hnm) (by rw [hMs]; exact hs)
      have hspos : 0<Real.sqrt p.m := Real.sqrt_pos.2 (by exact_mod_cast hm)
      have hsq : Real.sqrt (p.m : ℝ)^2=p.m := Real.sq_sqrt (Nat.cast_nonneg _)
      have he : Real.sqrt (p.m : ℝ)/p.m=1/Real.sqrt p.m := by
        apply (div_eq_div_iff (by exact_mod_cast Nat.ne_of_gt hm) hspos.ne').mpr
        nlinarith
      have h := hratio.2.2.2.2
      rw [hMs] at h
      change ∀ S,0<S → ∀ ρ,0<ρ → ρ≤1 →
        timeCoefficient a ⌈Real.sqrt p.m⌉₊ (Real.sqrt p.m/p.m)≤20*timeCoefficient a S ρ at h
      change ∀ S,0<S → ∀ ρ,0<ρ → ρ≤1 →
        timeCoefficient a ⌈Real.sqrt p.m⌉₊ (1/Real.sqrt p.m)≤20*timeCoefficient a S ρ
      simpa only [he] using h


theorem optimized_execution_accuracy (p : LongTails.Setups.FreyaPageOptimizedTime.Params)
    (hp : LongTails.Setups.FreyaPageOptimizedTime.spec.valid p) (f : Fin p.m → Space p.d → ℝ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hO : LongTails.Setups.FreyaPageOptimizedTime.spec.admissible p f O) :
    LongTails.Setups.FreyaPageOptimizedTime.spec.successful p f
      (fun z : (LongTails.Algorithms.FreyaTuning.optimized (LongTails.Setups.FreyaPageOptimizedTime.publicInput p)).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (LongTails.Algorithms.FreyaTuning.optimized (LongTails.Setups.FreyaPageOptimizedTime.publicInput p)) (fun _ => p.n * p.m * (⌈2 * p.Δ * (p.Lminus + p.Lpm * Real.sqrt p.m) / p.ε⌉₊ + 2)) z.1 z.2)
      ⟨((LongTails.Algorithms.FreyaTuning.optimized (LongTails.Setups.FreyaPageOptimizedTime.publicInput p)).law : Measure (LongTails.Algorithms.FreyaTuning.optimized (LongTails.Setups.FreyaPageOptimizedTime.publicInput p)).Seed).prod
        (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩ := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      obtain ⟨hi,ha⟩ := optimized_accuracy p hp f O hO
      exact ⟨hi,ha,optimized_time p hp f O hO⟩


theorem simple_execution_accuracy (p : LongTails.Setups.FreyaPageSimpleTime.Params)
    (hp : LongTails.Setups.FreyaPageSimpleTime.spec.valid p) (f : Fin p.m → Space p.d → ℝ)
    (O : Oracle (Option (Request p.d p.m p.n)) (Reply p.d p.n) 1)
    (hO : LongTails.Setups.FreyaPageSimpleTime.spec.admissible p f O) :
    LongTails.Setups.FreyaPageSimpleTime.spec.successful p f
      (fun z : (LongTails.Algorithms.FreyaTuning.simple (LongTails.Setups.FreyaPageSimpleTime.publicInput p)).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (LongTails.Algorithms.FreyaTuning.simple (LongTails.Setups.FreyaPageSimpleTime.publicInput p)) (fun _ => p.n * p.m * (⌈4 * p.Δ * max p.Lminus p.Lpm / p.ε⌉₊ + 2)) z.1 z.2)
      ⟨((LongTails.Algorithms.FreyaTuning.simple (LongTails.Setups.FreyaPageSimpleTime.publicInput p)).law : Measure (LongTails.Algorithms.FreyaTuning.simple (LongTails.Setups.FreyaPageSimpleTime.publicInput p)).Seed).prod
        (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩ := by
  exact
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    by
      obtain ⟨hi,ha⟩ := simple_accuracy p hp f O hO
      exact ⟨hi,ha,simple_time p hp f O hO⟩


end LongTails.Proofs.FreyaTunedComplexity
