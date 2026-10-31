import LongTails.Proofs.CohypomonotoneNewtonOuter

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CohypomonotoneNewtonRun

open LongTails.Setups.CohypomonotoneNewton
open LongTails.Algorithms.CohypomonotoneNewton
open LongTails.Proofs.CohypomonotoneNewtonGeometry
open LongTails.Proofs.CohypomonotoneNewtonTransform
open LongTails.Proofs.CohypomonotoneNewtonSearch
open LongTails.Proofs.CohypomonotoneNewtonOuter
open OracleTemplate.ComponentEnvelope (Program)

universe u

structure GraphFacts (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E) (root : p.E) (G : p.E → p.E)
    (D : p.E → p.E →L[ℝ] p.E) : Prop where
  root_zero : G root = 0
  monotone : ∀ x y, 0 ≤ ⟪G x - G y, x - y⟫
  lipschitz : ∀ x y, ‖G x - G y‖ ≤ (p.H * p.R) * ‖x - y‖
  derivative : ∀ x, HasFDerivAt G (D x) x
  derivative_norm : ∀ x, ‖D x‖ ≤ p.H * p.R
  derivative_lipschitz : ∀ x y, ‖D x - D y‖ ≤ p.H * ‖x - y‖
  derivative_monotone : ∀ x v, 0 ≤ ⟪D x v, v⟫
  graph_value : ∀ x, G (x + shift p • F x) = F x
  graph_derivative : ∀ x, D (x + shift p • F x) = graphJacobian (shift p) (J x)

lemma exists_graphFacts (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E) (root : p.E)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hroot : F root = 0) : ∃ G D, GraphFacts p F J root G D := by
  have hγ := shift_bounds p hH hρ hR
  obtain ⟨V, hright, hleft⟩ := exists_graph_inverse hF hγ.2.1 hγ.1.le hco
  have hexp := shifted_expansive hγ.2.1 hγ.1.le hco
  have hd := graph_derivative hF hexp hright
  have hm := graph_monotone hγ.2.2.1.le hco hright
  refine ⟨fun x => F (V x), fun x => graphJacobian (shift p) (J (V x)), ?_⟩
  constructor
  · have hh := hleft root
    rw [hroot, smul_zero, add_zero] at hh
    rw [hh, hroot]
  · exact hm
  · intro x y
    exact (graph_lipschitz hγ.2.2.1 hco hright x y).trans
      (mul_le_mul_of_nonneg_right hγ.2.2.2 (norm_nonneg _))
  · exact hd
  · exact graphJacobian_norm hF hγ.2.2.1 (mul_nonneg hH.le hR.le) hγ.2.2.2 hco hexp hright
  · exact graph_jacobian_lipschitz hF hH.le hJ hexp hright
  · intro x
    exact monotone_derivative (hd x) (fun y => hm y x)
  · intro x
    rw [hleft]
  · intro x
    rw [hleft]

lemma invariant_search (p : Public.{u}) (F G : p.E → p.E)
    (J D : p.E → p.E →L[ℝ] p.E) (root : p.E)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hg : GraphFacts p F J root G D)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (hinit : initial.2 = (F initial.1, J initial.1) ∧
      ‖initial.1 + shift p • F initial.1 - p.x0‖ ≤
        min (p.R / 64) (1 / (4096 * p.H * maxStep p)))
    (st : OuterState p.E) (hs : StateInvariant p F root st) :
    ∃ trial, Program.eval (fun x => (F x, J x))
      (searchPlan p st initial (searchFuel p) 0 0 st.previous) = some trial := by
  have hb := invariant_value_bounds p F G root st hH.le hR.le hroot hg.root_zero
    hg.monotone hg.lipschitz hg.graph_value hs
  apply search_from_graph_bounds p st root F G J D initial hH hρ hR hε hs.mass_case
    hroot hs.radius hb.1 hb.2 hg.root_zero hg.lipschitz hg.derivative hg.derivative_norm
    hg.derivative_lipschitz hg.derivative_monotone hg.graph_value hg.graph_derivative _ hs.previous_bounds
  intro a ha hmax
  have ha0 := (tuning_positive p hH hR hε).1.trans_le ha
  have ht := trialPlan_correct p hH hρ hR hF hJ hco st hs.mass_nonneg ha0 initial (by
    intro hk
    refine ⟨hinit.1, ?_⟩
    rw [initial_midpoint p st hk (hs.zero_mass hk) ha0.ne']
    exact hinit.2.trans (initial_tolerance_le p st hH hR hε hk (hs.zero_mass hk) ha0 hmax))
  exact ht.2

structure TrialFacts (p : Public.{u}) (F G : p.E → p.E)
    (J D : p.E → p.E →L[ℝ] p.E) (st : OuterState p.E) (t : Trial p.E) : Prop where
  step_bounds : baseStep p ≤ t.step ∧ t.step ≤ maxStep p
  sample_exact : t.sample.2 = (F t.sample.1, J t.sample.1)
  center_accuracy : ‖t.sample.1 + shift p • F t.sample.1 - midpoint p st t.step‖ ≤
    centerTolerance p st t.step
  model_equation : t.model + t.step • (G (t.sample.1 + shift p • F t.sample.1) +
    D (t.sample.1 + shift p • F t.sample.1)
      (t.model - (t.sample.1 + shift p • F t.sample.1))) = anchorMix p st t.step
  merit_upper : t.step * p.H * ‖t.model - (t.sample.1 + shift p • F t.sample.1)‖ ≤ 1 / 32
  merit_lower : 1 / 64 ≤ t.step * p.H * ‖t.model - (t.sample.1 + shift p • F t.sample.1)‖ ∨
    t.step = maxStep p

lemma search_facts (p : Public.{u}) (F G : p.E → p.E)
    (J D : p.E → p.E →L[ℝ] p.E) (root : p.E)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hg : GraphFacts p F J root G D)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (hinit : initial.2 = (F initial.1, J initial.1) ∧
      ‖initial.1 + shift p • F initial.1 - p.x0‖ ≤
        min (p.R / 64) (1 / (4096 * p.H * maxStep p)))
    (st : OuterState p.E) (hs : StateInvariant p F root st) (t : Trial p.E)
    (ht : Program.eval (fun x => (F x, J x))
      (searchPlan p st initial (searchFuel p) 0 0 st.previous) = some t) :
    TrialFacts p F G J D st t := by
  have hbase := (tuning_positive p hH hR hε).1
  obtain ⟨a, ha, hamax, heval, hupper, hlower⟩ := search_result_certificate p st initial
    (fun x => (F x, J x)) hbase (searchFuel p) (Or.inl rfl) (Or.inl rfl) hs.previous_bounds ht
  have ha0 := hbase.trans_le ha
  have hc := trialPlan_correct p hH hρ hR hF hJ hco st hs.mass_nonneg ha0 initial (by
    intro hk
    refine ⟨hinit.1, ?_⟩
    rw [initial_midpoint p st hk (hs.zero_mass hk) ha0.ne']
    exact hinit.2.trans (initial_tolerance_le p st hH hR hε hk (hs.zero_mass hk) ha0 hamax))
  rw [← heval] at hc
  have hm := trialPlan_model p st initial a (fun x => (F x, J x))
  rw [← heval] at hm
  dsimp only at hc hm
  rw [hc.2.1] at hm
  dsimp only at hm
  rw [← hc.1] at hm hlower
  have hme := affinePoint_spec (D (t.sample.1 + shift p • F t.sample.1))
    (show 0 ≤ t.step by rw [hc.1]; exact ha0.le)
    (hg.derivative_monotone _) (anchorMix p st t.step)
    (t.sample.1 + shift p • F t.sample.1) (F t.sample.1)
  have hmodel : t.model = affinePoint t.step (anchorMix p st t.step)
      (t.sample.1 + shift p • F t.sample.1) (F t.sample.1)
      (D (t.sample.1 + shift p • F t.sample.1)) := by
    rw [hg.graph_derivative]
    exact hm
  dsimp only at hme
  rw [← hmodel] at hme
  constructor
  · simpa only [hc.1] using And.intro ha hamax
  · exact hc.2.1
  · simpa only [hc.1] using hc.2.2
  · rw [hg.graph_value]
    exact hme.1
  · simpa only [merit, hc.2.1] using hupper
  · simpa only [merit, hc.2.1] using hlower

lemma endpoint_facts (p : Public.{u}) (F G : p.E → p.E)
    (J D : p.E → p.E →L[ℝ] p.E) (root : p.E)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hg : GraphFacts p F J root G D)
    (st : OuterState p.E) (hs : StateInvariant p F root st)
    (t : Trial p.E) (ht : TrialFacts p F G J D st t) :
    let endpoint := Program.eval (fun x => (F x, J x))
      (inversePlan (shift p * p.H) (shift p) (endpointTolerance p st t.step) t.model t.sample.1)
    let z := endpoint.1 + shift p • F endpoint.1
    endpoint.2 = (F endpoint.1, J endpoint.1) ∧
      StateInvariant p F root ⟨st.k + 1, st.mass + t.step, t.step, endpoint.1, F endpoint.1⟩ ∧
      ((st.mass + t.step) / t.step) * ‖z - midpoint p st t.step‖ ≤ 3 * p.R ∧
      ‖t.model - (t.sample.1 + shift p • F t.sample.1)‖ ≤ 4 * p.R * (t.step / (st.mass + t.step)) ∧
      (t.step ≠ maxStep p → 1 / 128 ≤ t.step * p.H * ‖z - midpoint p st t.step‖) ∧
      (t.step = maxStep p → ‖F endpoint.1‖ ≤ p.ε) := by
  have ha := (tuning_positive p hH hR hε).1.trans_le ht.step_bounds.1
  have he := inverse_public_correct p hH hρ hR hF hJ hco
    (tolerances_positive p st hH hR hs.mass_nonneg ha).2 t.model t.sample.1
  dsimp only at he ⊢
  generalize hx : Program.eval (fun x => (F x, J x))
    (inversePlan (shift p * p.H) (shift p) (endpointTolerance p st t.step) t.model t.sample.1) = out at he ⊢
  let z := out.1 + shift p • F out.1
  have hb := endpoint_bounds p st G D hH hR hg.derivative hg.derivative_lipschitz hg.lipschitz
    ha (t.sample.1 + shift p • F t.sample.1) t.model z ht.model_equation ht.center_accuracy he.2 ht.merit_upper
  rw [hg.graph_value] at hb
  have hi := invariant_step p F G root st hs hH hR hε hroot hg.root_zero hg.monotone hg.graph_value
    ht.step_bounds.1 ht.step_bounds.2 out.1 hb.1
  have hw := endpoint_warm_start p st hH.le hR.le hs.mass_nonneg ha
    (t.sample.1 + shift p • F t.sample.1) t.model z ht.center_accuracy he.2 hi.2
  refine ⟨he.1, hi.1, hi.2, hw, ?_, ?_⟩
  · intro hn
    exact hb.2 (ht.merit_lower.resolve_right hn)
  · intro hcap
    have hv := invariant_value_bounds p F G root st hH.le hR.le hroot hg.root_zero
      hg.monotone hg.lipschitz hg.graph_value hs
    have hmodel := ht.model_equation
    have hc := ht.center_accuracy
    have hh := he.2
    have hm := ht.merit_upper
    rw [hcap] at hmodel hc hh hm
    have hterm := terminal_endpoint_residual p st G D hH hR hε hs.mass_nonneg hv.1
      hg.derivative hg.derivative_lipschitz hg.lipschitz
      (t.sample.1 + shift p • F t.sample.1) t.model z hmodel hc hh hm
    rwa [hg.graph_value] at hterm

noncomputable def chosenTrial (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E))) (st : OuterState p.E) : Trial p.E :=
  (Program.eval (fun x => (F x, J x))
    (searchPlan p st initial (searchFuel p) 0 0 st.previous)).getD ⟨baseStep p, initial, p.x0⟩

noncomputable def chosenEndpoint (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E) (st : OuterState p.E) (t : Trial p.E) :
    p.E × (p.E × (p.E →L[ℝ] p.E)) :=
  Program.eval (fun x => (F x, J x))
    (inversePlan (shift p * p.H) (shift p) (endpointTolerance p st t.step) t.model t.sample.1)

noncomputable def advance (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E))) (st : OuterState p.E) : OuterState p.E :=
  let t := chosenTrial p F J initial st
  let out := chosenEndpoint p F J st t
  ⟨st.k + 1, st.mass + t.step, t.step, out.1, out.2.1⟩

noncomputable def trajectory (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E))) : ℕ → OuterState p.E
  | 0 => ⟨0, 0, baseStep p, initial.1, initial.2.1⟩
  | k + 1 => advance p F J initial (trajectory p F J initial k)

lemma trajectory_index (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E))) (k : ℕ) :
    (trajectory p F J initial k).k = k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [trajectory, advance] using congrArg Nat.succ ih

section Execution

variable (p : Public.{u}) (F G : p.E → p.E) (J D : p.E → p.E →L[ℝ] p.E) (root : p.E)
  (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
  (hF : ∀ x, HasFDerivAt F (J x) x)
  (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
  (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
  (hroot : ‖p.x0 - root‖ ≤ p.R) (hg : GraphFacts p F J root G D)
  (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
  (hinit : initial.2 = (F initial.1, J initial.1) ∧
    ‖initial.1 + shift p • F initial.1 - p.x0‖ ≤
      min (p.R / 64) (1 / (4096 * p.H * maxStep p)))

include hH hρ hR hε hF hJ hco hroot hg hinit

lemma chosenTrial_success (st : OuterState p.E) (hs : StateInvariant p F root st) :
    Program.eval (fun x => (F x, J x))
      (searchPlan p st initial (searchFuel p) 0 0 st.previous) =
        some (chosenTrial p F J initial st) := by
  obtain ⟨t, ht⟩ := invariant_search p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs
  simp only [chosenTrial, ht, Option.getD_some]

lemma chosenTrial_facts (st : OuterState p.E) (hs : StateInvariant p F root st) :
    TrialFacts p F G J D st (chosenTrial p F J initial st) := by
  exact search_facts p F G J D root hH hρ hR hε hF hJ hco hg initial hinit st hs _
    (chosenTrial_success p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs)

lemma advance_invariant (st : OuterState p.E) (hs : StateInvariant p F root st) :
    StateInvariant p F root (advance p F J initial st) := by
  have ht := chosenTrial_facts p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs
  have he := endpoint_facts p F G J D root hH hρ hR hε hF hJ hco hroot hg st hs _ ht
  change (chosenEndpoint p F J st (chosenTrial p F J initial st)).2 = _ ∧ _ at he
  dsimp only [advance]
  rw [he.1]
  exact he.2.1

lemma trajectory_invariant (k : ℕ) : StateInvariant p F root (trajectory p F J initial k) := by
  induction k with
  | zero =>
      have hi := invariant_initial p F root initial.1 hH hR hε hroot
      simpa only [trajectory, hinit.1] using hi
  | succ k ih =>
      exact advance_invariant p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit _ ih

lemma advance_bounds (st : OuterState p.E) (hs : StateInvariant p F root st) :
    let t := chosenTrial p F J initial st
    let next := advance p F J initial st
    let d := ‖currentPoint p next - midpoint p st t.step‖
    potential p next + 7 / 16 * ((st.mass + t.step) / t.step) ^ 2 * d ^ 2 ≤
      potential p st + p.R ^ 2 / ((st.k : ℝ) + 1) ^ 2 ∧
      (t.step ≠ maxStep p → 1 / 128 ≤ t.step * p.H * d) ∧
      (t.step = maxStep p → ‖F next.point‖ ≤ p.ε) ∧
      ‖t.model - (t.sample.1 + shift p • F t.sample.1)‖ ≤
        4 * p.R * (t.step / (st.mass + t.step)) := by
  let t := chosenTrial p F J initial st
  let out := chosenEndpoint p F J st t
  have ht := chosenTrial_facts p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs
  have he := endpoint_facts p F G J D root hH hρ hR hε hF hJ hco hroot hg st hs t ht
  change out.2 = (F out.1, J out.1) ∧ _ at he
  have hp : currentPoint p (advance p F J initial st) = out.1 + shift p • F out.1 := by
    simp only [advance, currentPoint, Nat.add_one_ne_zero, ite_false]
    change out.1 + shift p • out.2.1 = _
    rw [he.1]
  have hv : currentValue p (advance p F J initial st) = F out.1 := by
    simp only [advance, currentValue, Nat.add_one_ne_zero, ite_false]
    change out.2.1 = _
    rw [he.1]
  have ha := (tuning_positive p hH hR hε).1.trans_le ht.step_bounds.1
  have hi := inverse_public_correct p hH hρ hR hF hJ hco
    (tolerances_positive p st hH hR hs.mass_nonneg ha).2 t.model t.sample.1
  change out.2 = _ ∧ _ at hi
  have hb := endpoint_bounds p st G D hH hR hg.derivative hg.derivative_lipschitz hg.lipschitz
    ha (t.sample.1 + shift p • F t.sample.1) t.model (out.1 + shift p • F out.1)
    ht.model_equation ht.center_accuracy hi.2 ht.merit_upper
  rw [hg.graph_value] at hb
  have hcur : ∀ _ : st.k ≠ 0, currentValue p st = G (currentPoint p st) := by
    intro hk
    simp only [currentValue, currentPoint, ite_eq_right hk, hs.value_exact, hg.graph_value]
  have hm := weighted_monotonicity p st G hs.mass_nonneg hs.zero_mass hcur hg.monotone
    (out.1 + shift p • F out.1)
  rw [hg.graph_value] at hm
  have henergy := step_energy p st hs.mass_nonneg ha (out.1 + shift p • F out.1) (F out.1) hm hb.1
  dsimp only
  rw [hp]
  refine ⟨?_, he.2.2.2.2.1, he.2.2.2.2.2, he.2.2.2.1⟩
  unfold potential
  rw [hp, hv]
  exact henergy

lemma outer_step (st : OuterState p.E) (hs : StateInvariant p F root st) (fuel : ℕ)
    (hcontinue : ¬(st.k ≠ 0 ∧ ‖st.value‖ ≤ p.ε)) :
    Program.eval (fun x => (F x, J x)) (outerPlan p initial (fuel + 1) st) =
      if (chosenTrial p F J initial st).step = maxStep p then
        (advance p F J initial st).point else
        Program.eval (fun x => (F x, J x)) (outerPlan p initial fuel (advance p F J initial st)) := by
  have ht := chosenTrial_success p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs
  rw [outerPlan, ite_eq_right hcontinue, Program.eval_bind, ht, Program.eval_bind]
  change Program.eval (fun x => (F x, J x))
    (if (chosenTrial p F J initial st).step = maxStep p then
      Program.done (advance p F J initial st).point else
      outerPlan p initial fuel (advance p F J initial st)) = _
  split_ifs <;> rfl

lemma outer_failure_prefix (fuel k : ℕ)
    (hbad : p.ε < ‖F (Program.eval (fun x => (F x, J x))
      (outerPlan p initial fuel (trajectory p F J initial k)))‖) :
    (∀ i < fuel, (chosenTrial p F J initial (trajectory p F J initial (k + i))).step ≠ maxStep p) ∧
    Program.eval (fun x => (F x, J x)) (outerPlan p initial fuel (trajectory p F J initial k)) =
      (trajectory p F J initial (k + fuel)).point := by
  induction fuel generalizing k with
  | zero => simp [outerPlan, Program.eval]
  | succ fuel ih =>
      let st := trajectory p F J initial k
      have hs := trajectory_invariant p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit k
      have hn : ¬(st.k ≠ 0 ∧ ‖st.value‖ ≤ p.ε) := by
        intro hh
        have heval : Program.eval (fun x => (F x, J x)) (outerPlan p initial (fuel + 1) st) = st.point := by
          rw [outerPlan, ite_eq_left hh, Program.eval]
        change p.ε < ‖F (Program.eval (fun x => (F x, J x)) (outerPlan p initial (fuel + 1) st))‖ at hbad
        rw [heval] at hbad
        rw [hs.value_exact] at hh
        exact (not_lt_of_ge hh.2) hbad
      have he := outer_step p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs fuel hn
      have hab := advance_bounds p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs
      have hcap : (chosenTrial p F J initial st).step ≠ maxStep p := by
        intro hh
        rw [ite_eq_left hh] at he
        change p.ε < ‖F (Program.eval (fun x => (F x, J x)) (outerPlan p initial (fuel + 1) st))‖ at hbad
        rw [he] at hbad
        exact (not_lt_of_ge (hab.2.2.1 hh)) hbad
      rw [ite_eq_right hcap] at he
      have he' : Program.eval (fun x => (F x, J x)) (outerPlan p initial (fuel + 1) (trajectory p F J initial k)) =
          Program.eval (fun x => (F x, J x)) (outerPlan p initial fuel (trajectory p F J initial (k + 1))) := he
      rw [he'] at hbad
      have hi := ih (k + 1) hbad
      refine ⟨?_, ?_⟩
      · intro i hi'
        cases i with
        | zero => simpa only [Nat.add_zero] using hcap
        | succ i =>
            have hh := hi.1 i (by omega)
            simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hh
      · rw [he', hi.2]
        congr 2
        omega

lemma outer_accuracy :
    ‖F (Program.eval (fun x => (F x, J x))
      (outerPlan p initial (horizon p) (trajectory p F J initial 0)))‖ ≤ p.ε := by
  by_contra hn
  have hbad := lt_of_not_ge hn
  have hf := outer_failure_prefix p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit
    (horizon p) 0 hbad
  simp only [Nat.zero_add] at hf
  rw [hf.2] at hbad
  let states := trajectory p F J initial
  let A := fun k => (states k).mass
  let a := fun k => (chosenTrial p F J initial (states k)).step
  let d := fun k => ‖currentPoint p (states (k + 1)) - midpoint p (states k) (a k)‖
  let V := fun k => potential p (states k)
  let w := fun k => (A (k + 1) / a k) ^ 2 * d k ^ 2
  have hs : ∀ k, StateInvariant p F root (states k) :=
    trajectory_invariant p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit
  have hA : ∀ k, 0 ≤ A k := fun k => (hs k).mass_nonneg
  have ha : ∀ k, 0 < a k := by
    intro k
    have ht := chosenTrial_facts p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit
      (states k) (hs k)
    exact (tuning_positive p hH hR hε).1.trans_le ht.step_bounds.1
  have hrec : ∀ k, A (k + 1) = A k + a k := fun _ => rfl
  have hb : ∀ k, V (k + 1) + 7 / 16 * w k ≤ V k + p.R ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    have hh := advance_bounds p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit
      (states k) (hs k)
    have hi : (states k).k = k := trajectory_index p F J initial k
    rw [hi] at hh
    simpa only [V, w, d, A, a, states, trajectory, advance, mul_assoc] using hh.1
  have hd : ∀ k < horizon p, 1 / 128 ≤ a k * p.H * d k := by
    intro k hk
    have hh := advance_bounds p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit
      (states k) (hs k)
    exact hh.2.1 (hf.1 k hk)
  have hNpos : 0 < horizon p := by
    have hh := LongTails.Proofs.CohypomonotoneNewtonBudget.horizon_growth p hH hR hε
    by_contra hz
    have he : horizon p = 0 := by omega
    rw [he] at hh
    norm_num at hh
    nlinarith [sq_nonneg (p.H * p.R ^ 2 / p.ε)]
  have hvalue : currentValue p (states (horizon p)) = F (states (horizon p)).point := by
    unfold currentValue
    rw [show (states (horizon p)).k = horizon p from trajectory_index p F J initial _]
    rw [ite_eq_right (Nat.ne_of_gt hNpos), (hs (horizon p)).value_exact]
  have hgraph : currentValue p (states (horizon p)) = G (currentPoint p (states (horizon p))) := by
    simp only [currentValue, currentPoint, show (states (horizon p)).k = horizon p from
      trajectory_index p F J initial _, ite_eq_right (Nat.ne_of_gt hNpos),
      (hs (horizon p)).value_exact, hg.graph_value]
  have hm := hg.monotone (currentPoint p (states (horizon p))) root
  rw [hg.root_zero, sub_zero, ← hgraph] at hm
  have hroot' : ‖root - p.x0‖ ≤ p.R := by rwa [norm_sub_rev]
  have hfloor := LongTails.Proofs.CohypomonotoneNewtonEnergy.potential_floor
    (hA (horizon p)) hm hroot'
  have he := LongTails.Proofs.CohypomonotoneNewtonEnergy.energy_bounds V w p.R
    (N := horizon p) (by simp [V, potential, states, trajectory])
    (fun k _ => by dsimp [w]; positivity) hfloor (fun k _ => hb k)
  have hweights := LongTails.Proofs.CohypomonotoneNewtonEnergy.large_step_sum
    (fun k => A (k + 1)) a d hd he.2
  have hgrowth := LongTails.Proofs.CohypomonotoneNewtonEnergy.mass_growth A a
    (fun k _ => hA k) (fun k _ => ha k) (fun k _ => hrec k) hweights
  have hres := invariant_value_bounds p F G root (states (horizon p)) hH.le hR.le hroot hg.root_zero
    hg.monotone hg.lipschitz hg.graph_value (hs (horizon p))
  rw [hvalue] at hres
  have hmass : A (horizon p) ≤ 4 * p.R / p.ε := by
    apply (le_div_iff₀ hε).mpr
    have hh := mul_le_mul_of_nonneg_left hbad.le (hA (horizon p))
    exact hh.trans hres.1
  have hsq := pow_le_pow_left₀ (hA (horizon p)) hmass 2
  have hmul := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ 1572864 * p.H ^ 2 * p.R ^ 2)
  have hfinal : (horizon p : ℝ) ^ 5 ≤ 25165824 * (p.H * p.R ^ 2 / p.ε) ^ 2 := by
    have hid : (4 * p.R / p.ε) ^ 2 * (1572864 * p.H ^ 2 * p.R ^ 2) =
        25165824 * (p.H * p.R ^ 2 / p.ε) ^ 2 := by ring
    rw [hid] at hmul
    nlinarith only [hgrowth, hmul]
  exact (not_lt_of_ge hfinal) (LongTails.Proofs.CohypomonotoneNewtonBudget.horizon_growth p hH hR hε)

end Execution

lemma plan_accuracy (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E) (root : p.E)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hzero : F root = 0) (hroot : ‖p.x0 - root‖ ≤ p.R) :
    ‖F (Program.eval (fun x => (F x, J x)) (plan p))‖ ≤ p.ε := by
  obtain ⟨G, D, hg⟩ := exists_graphFacts p F J root hH hρ hR hF hJ hco hzero
  let d := trustRegion (ContinuousLinearMap.id ℝ p.E + shift p • J p.x0) (shift p • F p.x0) p.R
  let tol := min (p.R / 64) (1 / (4096 * p.H * maxStep p))
  let initial := Program.eval (fun x => (F x, J x))
    (inversePlan (shift p * p.H) (shift p) tol p.x0 (p.x0 + d))
  have hmax : 0 < maxStep p := (tuning_positive p hH hR hε).1.trans_le (tuning_positive p hH hR hε).2
  have htol : 0 < tol := by dsimp [tol]; positivity
  have hi := inverse_public_correct p hH hρ hR hF hJ hco htol p.x0 (p.x0 + d)
  have hh := outer_accuracy p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hi
  simpa only [plan, Program.eval, Program.eval_bind, trajectory, initial, tol, d] using hh

end LongTails.Proofs.CohypomonotoneNewtonRun
