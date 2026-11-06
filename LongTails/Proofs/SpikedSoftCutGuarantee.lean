import LongTails.Proofs.SpikedSoftCutConvergence

open MeasureTheory

namespace LongTails.Proofs.SpikedSoftCutGuarantee

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutMethodExecution
open SpikedSoftCutSeededExecution
open SpikedSoftCutOuterProbability
open SpikedSoftCutTuning
open SpikedSoftCutConvergence

lemma execute_method_seeded (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n) (hb : 0 < c.b)
    (g : Space q → q.Ω → Space q) (P : ProbabilityMeasure (ℕ → q.Ω)) (N : ℕ)
    (hN : remainingCost c 0 c.K ≤ N) (seed : Unit) (ξ : ℕ → q.Ω) :
    let O : OracleTemplate.Oracle (Space q) (Space q) :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample }
    OracleTemplate.execute O (method q c) (fun _ => N) seed ξ =
      saved q (terminalState q c g 0 c.K (initialState q) ξ) := by
  cases seed
  dsimp only
  have hh := execute_method q c hT hn
    { Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample }
    N hN ξ (fun i point => g point.2 (ξ i)) (by intros; rfl)
    (seededReplies q c g 0 c.K (initialState q) ξ)
    (fun i _ => seededReplies_response q c hT hn hb g c.K 0 (initialState q) ξ i)
  exact hh.trans (seeded_output q c hT hn g c.K 0 (initialState q) ξ)

lemma measurable_execute_method (q : Params) (c : Config) (hR : 0 < q.R)
    (hT : 0 < c.T) (hn : 0 < c.n) (hb : 0 < c.b)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g))
    (P : ProbabilityMeasure (ℕ → q.Ω)) (N : ℕ) (hN : remainingCost c 0 c.K ≤ N) :
    let O : OracleTemplate.Oracle (Space q) (Space q) :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample }
    Measurable (fun ξ => OracleTemplate.execute O (method q c) (fun _ => N) () ξ) := by
  have he : (fun ξ => OracleTemplate.execute
      ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample } :
        OracleTemplate.Oracle (Space q) (Space q)) (method q c) (fun _ => N) () ξ) =
      (fun ξ => saved q (terminalState q c g 0 c.K (initialState q) ξ)) :=
    funext (execute_method_seeded q c hT hn hb g P N hN ())
  dsimp only
  rw [he]
  exact measurable_seeded_output q c hR g hg c.K 0 (initialState q)

lemma execute_zero (q : Params) (O : OracleTemplate.Oracle (Space q) (Space q))
    (N : ℕ) (seed : Unit) (ξ : (k : ℕ) → O.Seed k) :
    OracleTemplate.execute O
      ({ State := Unit
         initial _ := ()
         query _ := (0,0)
         update _ _ := ()
         output _ := (0 : Space q) } :
        OracleTemplate.Algorithm (Space q) (Space q) (Space q)) (fun _ => N) seed ξ = 0 := by
  rw [OracleTemplate.execute_indexed]

lemma execute_method_failure (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε)
    (hrest : 0 ≤ q.vRest) (horder : q.vRest ≤ q.vTop)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : ProbabilityMeasure (ℕ → q.Ω))
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) p (P : Measure _))
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R)
    (hmin : IsMinOn f Set.univ xstar) (hconvex : ConvexOn ℝ Set.univ f)
    (hlip : ∀ x y, |f x-f y| ≤ q.G*‖x-y‖) (N : ℕ)
    (hN : remainingCost (tunedConfig q) 0 (tunedConfig q).K ≤ N) :
    let O : OracleTemplate.Oracle (Space q) (Space q) :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample }
    (P : Measure _) {ξ | q.ε < f (OracleTemplate.execute O (method q (tunedConfig q)) (fun _ => N) () ξ)-f xstar} ≤
      (1/3 : ENNReal) := by
  have hc := tunedConfig_positive q hG hR hε
  have hp := seeded_failure_probability q hG hR hε hrest horder p (P : Measure _) (fun k (ξ : ℕ → q.Ω) => ξ k)
    hs f v g hg xstar hxstar hmin hconvex hlip
  have he : {ξ | q.ε < f (OracleTemplate.execute
      ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample } :
        OracleTemplate.Oracle (Space q) (Space q)) (method q (tunedConfig q)) (fun _ => N) () ξ)-f xstar} =
      {ξ | q.ε < f (saved q (terminalState q (tunedConfig q) g 0 (tunedConfig q).K (initialState q) ξ))-f xstar} := by
    ext ξ
    have hh := execute_method_seeded q (tunedConfig q) hc.2.1 hc.2.2.2.1 hc.2.2.1 g P N hN () ξ
    exact iff_of_eq (congrArg (fun x => q.ε < f x-f xstar) hh)
  dsimp only
  rw [he]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)).mp
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  exact hp.trans (by norm_num)

lemma successful_tuned (q : Params) (hq : spec.valid q) (N : ℕ)
    (hN : remainingCost (tunedConfig q) 0 (tunedConfig q).K ≤ N)
    (f : Space q → ℝ) (O : OracleTemplate.Oracle (Space q) (Space q)) (hadm : spec.admissible q f O) :
    let A := algorithm q
    spec.successful q f
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => OracleTemplate.execute O A (fun _ => N) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hG,hR,hrest,horder,hε⟩ := hq
  obtain ⟨v,g,p,P,hs,rfl,hconv,hlip,⟨xstar,hmin,hxstar⟩,hg⟩ := hadm
  have hf := measurable_objective q hG f hlip
  dsimp only
  by_cases hsmall : q.G*q.R ≤ q.ε
  · have heA : algorithm q =
        ({ State := Unit
           initial _ := ()
           query _ := (0,0)
           update _ _ := ()
           output _ := (0 : Space q) } :
          OracleTemplate.Algorithm (Space q) (Space q) (Space q)) := by
      simp only [algorithm,hsmall,ite_true]
    rw [heA]
    have he (seed : Unit × (ℕ → q.Ω)) := execute_zero q
      ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample } :
        OracleTemplate.Oracle (Space q) (Space q)) N seed.1 seed.2
    have hzero : f 0-f xstar ≤ q.ε := by
      have hh := hlip 0 xstar
      simp only [zero_sub,norm_neg] at hh
      have hr := mul_le_mul_of_nonneg_left hxstar hG.le
      have hl := le_abs_self (f 0-f xstar)
      linarith
    have hfun : (fun seed : Unit × (ℕ → q.Ω) => OracleTemplate.execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample } :
          OracleTemplate.Oracle (Space q) (Space q))
        ({ State := Unit
           initial _ := ()
           query _ := (0,0)
           update _ _ := ()
           output _ := (0 : Space q) } :
          OracleTemplate.Algorithm (Space q) (Space q) (Space q)) (fun _ => N) seed.1 seed.2) =
        (fun _ => (0 : Space q)) := funext he
    refine ⟨hfun.symm ▸ measurable_const,xstar,hmin,?_⟩
    simp only [OracleTemplate.execute_indexed]
    have hempty : {seed : Unit × (ℕ → q.Ω) | q.ε < f 0-f xstar} = ∅ := by
      ext seed
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact not_lt.mpr hzero
    rw [hempty]
    simp
  · have heA : algorithm q = method q (tunedConfig q) := by simp only [algorithm,hsmall,ite_false]
    rw [heA]
    have hc := tunedConfig_positive q hG hR hε
    have hm := measurable_execute_method q (tunedConfig q) hR hc.2.1 hc.2.2.2.1 hc.2.2.1 g hg.measurable P N hN
    have hprod : Measurable (fun seed : Unit × (ℕ → q.Ω) => OracleTemplate.execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample } :
          OracleTemplate.Oracle (Space q) (Space q)) (method q (tunedConfig q)) (fun _ => N) seed.1 seed.2) :=
      hm.comp measurable_snd
    refine ⟨hprod,xstar,hmin,?_⟩
    have hbad := measurableSet_lt (measurable_const (a := q.ε)) ((hf.comp hm).sub_const (f xstar))
    have hp := (measurePreserving_snd (μ := (Measure.dirac () : Measure Unit))
      (ν := (P : Measure (ℕ → q.Ω)))).measure_preimage hbad.nullMeasurableSet
    exact hp.le.trans (execute_method_failure q hG hR hε hrest horder (p : Measure q.Ω) P hs
      f v g hg xstar hxstar hmin hconv hlip N hN)

end LongTails.Proofs.SpikedSoftCutGuarantee
