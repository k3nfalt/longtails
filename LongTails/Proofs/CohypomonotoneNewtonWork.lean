import LongTails.Proofs.CohypomonotoneNewtonRun

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CohypomonotoneNewtonWork

open LongTails.Setups.CohypomonotoneNewton
open LongTails.Algorithms.CohypomonotoneNewton
open LongTails.Proofs.CohypomonotoneNewtonSearch
open OracleTemplate.ComponentEnvelope (Program)

universe u

structure SearchRange (floor cap previous low high a : ℝ) : Prop where
  floor_pos : 0 < floor
  query_bounds : floor ≤ a ∧ a ≤ cap
  low_nonneg : 0 ≤ low
  low_le : low ≤ a
  high_le : high = 0 ∨ a ≤ high
  high_cap : high ≤ cap
  query_envelope : a ≤ max previous (2 * low)
  high_envelope : high ≤ max previous (2 * low)
  low_floor : low = 0 ∨ floor ≤ low

lemma searchRange_initial {floor cap a : ℝ} (hf : 0 < floor) (ha : floor ≤ a ∧ a ≤ cap) :
    SearchRange floor cap a 0 0 a := by
  have hapos := hf.trans_le ha.1
  refine ⟨hf, ha, le_rfl, hapos.le, Or.inl rfl, ?_, ?_, ?_, Or.inl rfl⟩
  · exact hapos.le.trans ha.2
  · exact le_max_left _ _
  · exact hapos.le.trans (le_max_left _ _)

lemma searchRange_up {floor cap previous low high a : ℝ}
    (h : SearchRange floor cap previous low high a) :
    SearchRange floor cap previous a high (if high = 0 then min (2 * a) cap else (a + high) / 2) := by
  have ha : 0 < a := h.floor_pos.trans_le h.query_bounds.1
  have he : max previous (2 * low) ≤ max previous (2 * a) := max_le_max_left _ (by linarith [h.low_le])
  have hh := h.high_envelope.trans he
  by_cases hz : high = 0
  · rw [ite_eq_left hz]
    refine ⟨h.floor_pos, ⟨?_, min_le_right _ _⟩, ha.le, ?_, Or.inl hz, h.high_cap, ?_, hh, Or.inr h.query_bounds.1⟩
    · exact h.query_bounds.1.trans (le_min (by linarith) h.query_bounds.2)
    · exact le_min (by linarith) h.query_bounds.2
    · exact (min_le_left _ _).trans (le_max_right _ _)
  · rw [ite_eq_right hz]
    have hahi := h.high_le.resolve_left hz
    refine ⟨h.floor_pos, ⟨by linarith [h.query_bounds.1], by linarith [h.query_bounds.2, h.high_cap]⟩,
      ha.le, by linarith, Or.inr (by linarith), h.high_cap, ?_, hh, Or.inr h.query_bounds.1⟩
    have hh' : a ≤ max previous (2 * a) := (show a ≤ 2 * a by linarith).trans (le_max_right _ _)
    linarith

lemma searchRange_down {floor cap previous low high a : ℝ}
    (h : SearchRange floor cap previous low high a) :
    SearchRange floor cap previous low a (if low = 0 then max (a / 2) floor else (low + a) / 2) := by
  have ha : 0 < a := h.floor_pos.trans_le h.query_bounds.1
  by_cases hz : low = 0
  · rw [ite_eq_left hz]
    have hn : max (a / 2) floor ≤ a := max_le (by linarith) h.query_bounds.1
    refine ⟨h.floor_pos, ⟨le_max_right _ _, hn.trans h.query_bounds.2⟩, h.low_nonneg,
      ?_, Or.inr hn, h.query_bounds.2, hn.trans h.query_envelope, h.query_envelope, h.low_floor⟩
    rw [hz]
    exact h.floor_pos.le.trans (le_max_right _ _)
  · rw [ite_eq_right hz]
    have hlofloor : floor ≤ low := h.low_floor.resolve_left hz
    refine ⟨h.floor_pos, ⟨by linarith [h.query_bounds.1], by linarith [h.low_le, h.query_bounds.2]⟩,
      h.low_nonneg, by linarith [h.low_le], Or.inr (by linarith [h.low_le]), h.query_bounds.2,
      ?_, h.query_envelope, h.low_floor⟩
    exact (show (low + a) / 2 ≤ a by linarith [h.low_le]).trans h.query_envelope

lemma trial_step (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) (a : ℝ) :
    (Program.eval reply (trialPlan p st initial a)).step = a := by
  simp only [trialPlan, Program.eval_map]

lemma search_cost_envelope (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) (previous C : ℝ) (hC : 0 ≤ C)
    (fuel : ℕ) {lo hi a : ℝ} {t : Trial p.E}
    (hrange : SearchRange (baseStep p) (maxStep p) previous lo hi a)
    (hsuccess : Program.eval reply (searchPlan p st initial fuel lo hi a) = some t)
    (hcost : ∀ b, baseStep p ≤ b → b ≤ maxStep p → b ≤ max previous (2 * t.step) →
      (Program.cost reply (trialPlan p st initial b) : ℝ) ≤ C) :
    lo ≤ t.step ∧ (Program.cost reply (searchPlan p st initial fuel lo hi a) : ℝ) ≤ fuel * C := by
  induction fuel generalizing lo hi a with
  | zero => simp [searchPlan, Program.eval] at hsuccess
  | succ fuel ih =>
      rw [searchPlan, Program.eval_bind] at hsuccess
      by_cases hacc : merit p (Program.eval reply (trialPlan p st initial a)) ≤ 1 / 32 ∧
          (1 / 64 ≤ merit p (Program.eval reply (trialPlan p st initial a)) ∨ a = maxStep p)
      · rw [ite_eq_left hacc, Program.eval] at hsuccess
        have ht : Program.eval reply (trialPlan p st initial a) = t := Option.some.inj hsuccess
        have hs : t.step = a := by rw [← ht, trial_step]
        refine ⟨by simpa only [hs] using hrange.low_le, ?_⟩
        have ha : 0 ≤ a := (hrange.floor_pos.trans_le hrange.query_bounds.1).le
        have he : a ≤ max previous (2 * t.step) := by
          rw [hs]
          exact (show a ≤ 2 * a by linarith).trans (le_max_right _ _)
        have hc := hcost a hrange.query_bounds.1 hrange.query_bounds.2 he
        simp only [searchPlan, Program.cost_bind, ite_eq_left hacc, Program.cost, add_zero,
          Nat.cast_add, Nat.cast_one]
        have hn := mul_nonneg (Nat.cast_nonneg fuel) hC
        nlinarith only [hc, hn]
      · rw [ite_eq_right hacc] at hsuccess
        by_cases hlow : merit p (Program.eval reply (trialPlan p st initial a)) < 1 / 64
        · rw [ite_eq_left hlow] at hsuccess
          have hh := ih (searchRange_up hrange) hsuccess
          have hl : lo ≤ t.step := hrange.low_le.trans hh.1
          have he := hrange.query_envelope.trans (max_le_max_left previous (by linarith : 2 * lo ≤ 2 * t.step))
          have hc := hcost a hrange.query_bounds.1 hrange.query_bounds.2 he
          refine ⟨hl, ?_⟩
          simp only [searchPlan, Program.cost_bind, ite_eq_right hacc, ite_eq_left hlow,
            Nat.cast_add, Nat.cast_one]
          nlinarith only [hc, hh.2]
        · rw [ite_eq_right hlow] at hsuccess
          have hh := ih (searchRange_down hrange) hsuccess
          have he := hrange.query_envelope.trans (max_le_max_left previous (by linarith [hh.1] : 2 * lo ≤ 2 * t.step))
          have hc := hcost a hrange.query_bounds.1 hrange.query_bounds.2 he
          refine ⟨hh.1, ?_⟩
          simp only [searchPlan, Program.cost_bind, ite_eq_right hacc, ite_eq_right hlow,
            Nat.cast_add, Nat.cast_one]
          nlinarith only [hc, hh.2]

lemma tolerance_floor (p : Public.{u}) (st : OuterState p.E)
    (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hA : 0 ≤ st.mass) (hmax : st.mass ≤ maxStep p) (hk : st.k ≤ horizon p)
    {a : ℝ} (ha : baseStep p ≤ a) (hamax : a ≤ maxStep p) :
    p.R / (400000000 * (1 + p.H * p.R ^ 2 / p.ε) ^ 3) ≤ endpointTolerance p st a ∧
    p.R / (400000000 * (1 + p.H * p.R ^ 2 / p.ε) ^ 3) ≤ centerTolerance p st a := by
  let S := 1 + p.H * p.R ^ 2 / p.ε
  have hS : 1 ≤ S := by
    dsimp [S]
    have : 0 ≤ p.H * p.R ^ 2 / p.ε := by positivity
    linarith
  have ht := tuning_positive p hH hR hε
  have ha0 := ht.1.trans_le ha
  have hmax0 := ht.1.trans_le ht.2
  have hr := LongTails.Proofs.CohypomonotoneNewtonBudget.maxStep_ratio p hH hR hε
  have hB : (st.mass + a) / a ≤ 4608 * S := by
    have hh := div_le_div_of_nonneg_left hmax0.le ht.1 ha
    have hh' : st.mass / a ≤ maxStep p / a := div_le_div_of_nonneg_right hmax ha0.le
    have he : (st.mass + a) / a = st.mass / a + 1 := by field_simp
    rw [he]
    have hS0 : 1 ≤ S := hS
    nlinarith only [hh, hh', hr, hS0]
  have hhorizon := LongTails.Proofs.CohypomonotoneNewtonBudget.horizon_upper p hH hR hε
  have hpow := Real.rpow_le_self_of_one_le hS (by norm_num : (2 / 5 : ℝ) ≤ 1)
  have hcast : (st.k : ℝ) ≤ horizon p := by exact_mod_cast hk
  have hkS : (st.k : ℝ) + 1 ≤ 66 * S := by nlinarith only [hhorizon, hpow, hcast, hS]
  have hamul := mul_le_mul_of_nonneg_left hamax (by positivity : 0 ≤ p.H * p.R)
  have hscaled := LongTails.Proofs.CohypomonotoneNewtonBudget.maxStep_scaled p hH hR hε
  have haS : a * p.H * p.R ≤ 18 * S := by nlinarith only [hamul, hscaled]
  have hb := LongTails.Proofs.CohypomonotoneNewtonBudget.tolerance_floor_scalar hA ha0 hH hR hS
    (by positivity : 0 < (st.k : ℝ) + 1) hB hkS haS
  change p.R / (400000000 * S ^ 3) ≤ endpointTolerance p st a at hb
  refine ⟨hb, hb.trans ?_⟩
  apply min_le_min _ le_rfl
  have he : 0 ≤ errorScale p st a := by unfold errorScale; positivity
  exact div_le_div_of_nonneg_left he (by norm_num : (0 : ℝ) < 64)
    (by nlinarith [mul_nonneg (mul_nonneg ha0.le hH.le) hR.le] : 64 ≤ 64 * (1 + a * p.H * p.R))

lemma initial_tolerance_floor (p : Public.{u}) (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε) :
    p.R / (400000000 * (1 + p.H * p.R ^ 2 / p.ε) ^ 3) ≤
      min (p.R / 64) (1 / (4096 * p.H * maxStep p)) := by
  let st : OuterState p.E := ⟨0, 0, baseStep p, p.x0, 0⟩
  have ht := tuning_positive p hH hR hε
  have hh := tolerance_floor p st hH hR hε le_rfl (ht.1.le.trans ht.2) (Nat.zero_le _)
    ht.2 le_rfl
  have hm : 0 < maxStep p := ht.1.trans_le ht.2
  simpa [centerTolerance, errorScale, st, hm.ne'] using hh.2

noncomputable def coupling (p : Public.{u}) : ℝ := shift p * p.H * p.R

noncomputable def accuracyScale (p : Public.{u}) : ℝ := 1 + p.H * p.R ^ 2 / p.ε

noncomputable def logFactor (p : Public.{u}) : ℝ :=
  1 + Real.log (2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε)

lemma scale_bounds (p : Public.{u}) (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε) :
    1 ≤ coupling p ∧ 1 ≤ accuracyScale p ∧ 1 ≤ logFactor p := by
  have hc : coupling p = 1 + 2 * p.ρ * p.H * p.R := by
    unfold coupling shift
    field_simp
    ring
  have hq : 1 ≤ coupling p := by
    rw [hc]
    have := mul_nonneg (mul_nonneg (by linarith : 0 ≤ 2 * p.ρ) hH.le) hR.le
    linarith
  have hS : 1 ≤ accuracyScale p := by
    unfold accuracyScale
    have hh : 0 ≤ p.H * p.R ^ 2 / p.ε := by positivity
    linarith
  have hid : 2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε =
      1 + coupling p + accuracyScale p := by unfold coupling accuracyScale; ring
  have hl := Real.log_nonneg (show 1 ≤ 1 + coupling p + accuracyScale p by linarith)
  refine ⟨hq, hS, ?_⟩
  unfold logFactor
  rw [hid]
  linarith

lemma searchFuel_upper (p : Public.{u}) (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε) :
    (searchFuel p : ℝ) ≤ 202 * logFactor p := by
  have he := (scale_bounds p hH hρ hR hε).2.2
  have hpos : 0 ≤ 200 * logFactor p := by positivity
  have hc := Nat.ceil_lt_add_one hpos
  change ((⌈200 * logFactor p⌉₊ + 1 : ℕ) : ℝ) ≤ _
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

lemma log_mass_ratio (p : Public.{u}) (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε) :
    1 + Real.log (2 * maxStep p / baseStep p) ≤ 14 * logFactor p := by
  have hs := scale_bounds p hH hρ hR hε
  have ht := tuning_positive p hH hR hε
  have hm : 0 < maxStep p := ht.1.trans_le ht.2
  have hS : 0 < accuracyScale p := by linarith [hs.2.1]
  have hr := LongTails.Proofs.CohypomonotoneNewtonBudget.maxStep_ratio p hH hR hε
  have hr' : 2 * maxStep p / baseStep p ≤ 4608 * accuracyScale p := by
    change 2 * maxStep p / baseStep p ≤ 4608 * (1 + p.H * p.R ^ 2 / p.ε)
    rw [mul_div_assoc]
    linarith
  have hl := Real.log_le_log (div_pos (mul_pos (by norm_num) hm) ht.1) hr'
  rw [Real.log_mul (by norm_num : (4608 : ℝ) ≠ 0) hS.ne'] at hl
  have hconst := Real.log_le_log (by norm_num : (0 : ℝ) < 4608)
    (by norm_num : (4608 : ℝ) ≤ 2 ^ 13)
  rw [Real.log_pow] at hconst
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hconst' : Real.log 4608 ≤ 13 := by norm_num at hconst hlog2; linarith
  have hSL : accuracyScale p ≤ 2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε := by
    have hq := hs.1
    unfold coupling at hq
    unfold accuracyScale
    linarith
  have hlogS := Real.log_le_log hS hSL
  change 1 + Real.log (2 * maxStep p / baseStep p) ≤ 14 *
    (1 + Real.log (2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε))
  unfold logFactor at hs
  linarith only [hl, hconst', hlogS, hs.2.2]

lemma inverse_work (p : Public.{u}) (F : p.E → p.E) (J : p.E → p.E →L[ℝ] p.E)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (target start : p.E) {B tol : ℝ}
    (hB : ‖start + shift p • F start - target‖ ≤ B)
    (hupper : B ≤ 8 * coupling p * p.R)
    (htol : p.R / (400000000 * (accuracyScale p) ^ 3) ≤ tol) :
    (Program.cost (fun x => (F x, J x))
      (inversePlan (shift p * p.H) (shift p) tol target start) : ℝ) ≤
        200 * logFactor p * (1 + shift p * p.H * B) := by
  have hs := scale_bounds p hH hρ hR hε
  have hSpos : 0 < accuracyScale p := by linarith [hs.2.1]
  have ht : 0 < tol := lt_of_lt_of_le (by positivity) htol
  have hγ := (shift_bounds p hH hρ hR).1
  have hl := LongTails.Proofs.CohypomonotoneNewtonBudget.inverse_log_bound hs.1 hs.2.1 hR
    (norm_nonneg (start + shift p • F start - target)) (hB.trans hupper) htol
  have hid : 1 + coupling p + accuracyScale p =
      2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε := by unfold coupling accuracyScale; ring
  rw [hid] at hl
  have hc := LongTails.Proofs.CohypomonotoneNewtonBudget.inverseLength_cost
    (mul_nonneg hγ.le hH.le) (norm_nonneg (start + shift p • F start - target)) ht hs.2.2 hl
  rw [LongTails.Proofs.CohypomonotoneNewtonExecution.inversePlan_cost]
  apply hc.trans
  have hell : 0 ≤ logFactor p := by linarith [hs.2.2]
  gcongr

lemma trial_work (p : Public.{u}) (F : p.E → p.E) (J : p.E → p.E →L[ℝ] p.E)
    (root : p.E) (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (st : OuterState p.E) (hs : LongTails.Proofs.CohypomonotoneNewtonOuter.StateInvariant p F root st)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hroot : ‖p.x0 - root‖ ≤ p.R)
    (hg : st.mass * ‖currentValue p st‖ ≤ 4 * p.R)
    (hmax : st.mass ≤ maxStep p) (hk : st.k ≤ horizon p)
    {a : ℝ} (ha : baseStep p ≤ a) (hamax : a ≤ maxStep p) :
    (Program.cost (fun x => (F x, J x)) (trialPlan p st initial a) : ℝ) ≤
      200 * logFactor p * (1 + 8 * coupling p * (a / (st.mass + a))) := by
  have hsc := scale_bounds p hH hρ hR hε
  have hell : 0 ≤ logFactor p := by linarith [hsc.2.2]
  have hq : 0 ≤ coupling p := by linarith [hsc.1]
  have ha0 := (tuning_positive p hH hR hε).1.trans_le ha
  have hB : 0 < st.mass + a := add_pos_of_nonneg_of_pos hs.mass_nonneg ha0
  have halpha : 0 ≤ a / (st.mass + a) := (div_pos ha0 hB).le
  by_cases hz : st.k = 0
  · simp only [trialPlan, ite_eq_left hz, Program.cost_map, Program.cost, Nat.cast_zero]
    positivity
  · have hw := warm_start_bound p st root hs.mass_nonneg ha0 hroot hs.radius hg
    have hc : currentPoint p st = st.point + shift p • F st.point := by
      simp only [currentPoint, ite_eq_right hz, hs.value_exact]
    rw [hc] at hw
    have ht := (tolerance_floor p st hH hR hε hs.mass_nonneg hmax hk ha hamax).2
    have halpha1 : a / (st.mass + a) ≤ 1 := (div_le_one hB).mpr (by linarith [hs.mass_nonneg])
    have hupper : 8 * p.R * (a / (st.mass + a)) ≤ 8 * coupling p * p.R := by
      have hh := mul_le_mul_of_nonneg_left halpha1 (by positivity : 0 ≤ 8 * p.R)
      have hh' := mul_le_mul_of_nonneg_right hsc.1 (by positivity : 0 ≤ 8 * p.R)
      nlinarith only [hh, hh']
    have hi := inverse_work p F J hH hρ hR hε (midpoint p st a) st.point hw hupper ht
    simp only [trialPlan, ite_eq_right hz, Program.cost_map]
    convert hi using 1
    unfold coupling
    ring

lemma fraction_envelope {A a b previous : ℝ} (hA : 0 < A) (ha : 0 ≤ a) (hb : 0 < b)
    (hp : 0 ≤ previous) (henv : a ≤ max previous (2 * b)) :
    a / (A + a) ≤ previous / A + 2 * (b / (A + b)) := by
  have hda : 0 < A + a := by positivity
  have hdb : 0 < A + b := by positivity
  rcases le_max_iff.mp henv with h | h
  · have hh := div_le_div_of_nonneg_left ha hA (by linarith : A ≤ A + a)
    have hh' := div_le_div_of_nonneg_right h hA.le
    have hn : 0 ≤ 2 * (b / (A + b)) := by positivity
    linarith
  · have hh : a / (A + a) ≤ (2 * b) / (A + b) := by
      apply (div_le_div_iff₀ hda hdb).mpr
      have hm := mul_nonneg hA.le (sub_nonneg.mpr h)
      nlinarith [mul_nonneg ha hb.le]
    have hn : 0 ≤ previous / A := div_nonneg hp hA.le
    have he : 2 * b / (A + b) = 2 * (b / (A + b)) := by ring
    rw [he] at hh
    linarith

open LongTails.Proofs.CohypomonotoneNewtonOuter
open LongTails.Proofs.CohypomonotoneNewtonRun

noncomputable def previousCharge (st : OuterState E) : ℝ :=
  if st.k = 0 then 0 else st.previous / st.mass

noncomputable def stepWork (p : Public.{u}) (F : p.E → p.E) (J : p.E → p.E →L[ℝ] p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E))) (st : OuterState p.E) : ℕ :=
  let t := chosenTrial p F J initial st
  Program.cost (fun x => (F x, J x)) (searchPlan p st initial (searchFuel p) 0 0 st.previous) +
    Program.cost (fun x => (F x, J x))
      (inversePlan (shift p * p.H) (shift p) (endpointTolerance p st t.step) t.model t.sample.1)

lemma active_mass_bound (p : Public.{u}) (F G : p.E → p.E)
    (J D : p.E → p.E →L[ℝ] p.E) (root : p.E)
    (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hg : GraphFacts p F J root G D)
    (st : OuterState p.E) (hs : StateInvariant p F root st)
    (hactive : ¬(st.k ≠ 0 ∧ ‖st.value‖ ≤ p.ε)) :
    st.mass ≤ 4 * p.R / p.ε ∧ st.mass ≤ maxStep p := by
  have hm : st.mass ≤ 4 * p.R / p.ε := by
    by_cases hz : st.k = 0
    · rw [hs.zero_mass hz]
      positivity
    · have hv := invariant_value_bounds p F G root st hH.le hR.le hroot hg.root_zero
        hg.monotone hg.lipschitz hg.graph_value hs
      have hn : p.ε < ‖st.value‖ := lt_of_not_ge (fun h => hactive ⟨hz, h⟩)
      simp only [currentValue, ite_eq_right hz] at hv
      apply (le_div_iff₀ hε).mpr
      exact (mul_le_mul_of_nonneg_left hn.le hs.mass_nonneg).trans hv.1
  refine ⟨hm, hm.trans ?_⟩
  unfold maxStep
  have hb := (tuning_positive p hH hR hε).1.le
  have h1 : 0 ≤ p.R / p.ε := by positivity
  have h2 : 0 ≤ 2 / Real.sqrt (p.H * p.ε) := by positivity
  simp only [mul_div_assoc]
  linarith

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

lemma search_work (st : OuterState p.E) (hs : StateInvariant p F root st)
    (hmax : st.mass ≤ maxStep p) (hk : st.k ≤ horizon p) :
    let t := chosenTrial p F J initial st
    (Program.cost (fun x => (F x, J x)) (searchPlan p st initial (searchFuel p) 0 0 st.previous) : ℝ) ≤
      (searchFuel p : ℝ) * (200 * logFactor p *
        (1 + 8 * coupling p * (previousCharge st + 2 * (t.step / (st.mass + t.step))))) := by
  let t := chosenTrial p F J initial st
  have ht := chosenTrial_facts p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs
  have hbase := (tuning_positive p hH hR hε).1
  have hb : 0 < t.step := hbase.trans_le ht.step_bounds.1
  have hden : 0 < st.mass + t.step := add_pos_of_nonneg_of_pos hs.mass_nonneg hb
  have hprev : 0 ≤ previousCharge st := by
    unfold previousCharge
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hbase.le.trans hs.previous_bounds.1) hs.mass_nonneg
  have hscale := scale_bounds p hH hρ hR hε
  have hlog : 0 ≤ logFactor p := by linarith [hscale.2.2]
  have hq : 0 ≤ coupling p := by linarith [hscale.1]
  have hα : 0 ≤ t.step / (st.mass + t.step) := (div_pos hb hden).le
  have hv := invariant_value_bounds p F G root st hH.le hR.le hroot hg.root_zero
    hg.monotone hg.lipschitz hg.graph_value hs
  have hc := search_cost_envelope p st initial (fun x => (F x, J x)) st.previous
    (200 * logFactor p * (1 + 8 * coupling p * (previousCharge st + 2 * (t.step / (st.mass + t.step)))))
    (by positivity) (searchFuel p) (searchRange_initial hbase hs.previous_bounds)
    (chosenTrial_success p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs) (by
      intro a ha hamax henv
      by_cases hz : st.k = 0
      · simp only [trialPlan, ite_eq_left hz, Program.cost_map, Program.cost, Nat.cast_zero]
        positivity
      · have hA : 0 < st.mass := by
          rcases hs.mass_case with hm | ⟨hk0, _⟩
          · exact hbase.trans_le hm
          · exact False.elim (hz hk0)
        have hαbound := fraction_envelope hA (hbase.le.trans ha) hb
          (hbase.le.trans hs.previous_bounds.1) henv
        have hprevEq : previousCharge st = st.previous / st.mass := by simp only [previousCharge, ite_eq_right hz]
        rw [← hprevEq] at hαbound
        have hh := trial_work p F J root initial st hs hH hρ hR hε hroot hv.1 hmax hk ha hamax
        apply hh.trans
        gcongr)
  exact hc.2

lemma endpoint_work (st : OuterState p.E) (hs : StateInvariant p F root st)
    (hmax : st.mass ≤ maxStep p) (hk : st.k ≤ horizon p) :
    let t := chosenTrial p F J initial st
    (Program.cost (fun x => (F x, J x))
      (inversePlan (shift p * p.H) (shift p) (endpointTolerance p st t.step) t.model t.sample.1) : ℝ) ≤
      200 * logFactor p * (1 + 4 * coupling p * (t.step / (st.mass + t.step))) := by
  let t := chosenTrial p F J initial st
  have ht := chosenTrial_facts p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs
  have ha := (tuning_positive p hH hR hε).1.trans_le ht.step_bounds.1
  have hden : 0 < st.mass + t.step := add_pos_of_nonneg_of_pos hs.mass_nonneg ha
  have hα : t.step / (st.mass + t.step) ≤ 1 := (div_le_one hden).mpr (by linarith [hs.mass_nonneg])
  have hscl := scale_bounds p hH hρ hR hε
  have hw := (advance_bounds p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs).2.2.2
  rw [norm_sub_rev] at hw
  have htolerance := (tolerance_floor p st hH hR hε hs.mass_nonneg hmax hk ht.step_bounds.1 ht.step_bounds.2).1
  have hupper : 4 * p.R * (t.step / (st.mass + t.step)) ≤ 8 * coupling p * p.R := by
    have hh := mul_le_mul_of_nonneg_left hα (by positivity : 0 ≤ 4 * p.R)
    have hh' := mul_le_mul_of_nonneg_right hscl.1 (by positivity : 0 ≤ 8 * p.R)
    nlinarith only [hh, hh', hR]
  have hi := inverse_work p F J hH hρ hR hε t.model t.sample.1 hw hupper htolerance
  convert hi using 1
  unfold coupling
  ring

lemma step_work_bound (st : OuterState p.E) (hs : StateInvariant p F root st)
    (hmax : st.mass ≤ maxStep p) (hk : st.k ≤ horizon p) :
    let t := chosenTrial p F J initial st
    (stepWork p F J initial st : ℝ) ≤ 200 * logFactor p *
      ((searchFuel p : ℝ) + 1 + 8 * coupling p * searchFuel p *
        (previousCharge st + 2 * (t.step / (st.mass + t.step))) +
        4 * coupling p * (t.step / (st.mass + t.step))) := by
  have hswork := search_work p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs hmax hk
  have hework := endpoint_work p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs hmax hk
  dsimp only at hswork hework ⊢
  rw [stepWork, Nat.cast_add]
  nlinarith only [hswork, hework]

lemma outer_cost_step (st : OuterState p.E) (hs : StateInvariant p F root st) (fuel : ℕ)
    (hcontinue : ¬(st.k ≠ 0 ∧ ‖st.value‖ ≤ p.ε)) :
    Program.cost (fun x => (F x, J x)) (outerPlan p initial (fuel + 1) st) =
      stepWork p F J initial st +
        if (chosenTrial p F J initial st).step = maxStep p then 0 else
          Program.cost (fun x => (F x, J x)) (outerPlan p initial fuel (advance p F J initial st)) := by
  have ht := chosenTrial_success p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs
  rw [outerPlan, ite_eq_right hcontinue, Program.cost_bind, ht, Program.cost_bind]
  unfold stepWork
  dsimp only
  split_ifs <;> simp only [Program.cost, advance, chosenEndpoint, add_assoc]

lemma outer_cost_prefix (fuel k : ℕ) : ∃ n ≤ fuel,
    (∀ i < n, ¬((trajectory p F J initial (k + i)).k ≠ 0 ∧
      ‖(trajectory p F J initial (k + i)).value‖ ≤ p.ε)) ∧
    Program.cost (fun x => (F x, J x)) (outerPlan p initial fuel (trajectory p F J initial k)) =
      ∑ i ∈ Finset.range n, stepWork p F J initial (trajectory p F J initial (k + i)) := by
  induction fuel generalizing k with
  | zero => exact ⟨0, le_rfl, by simp, by simp [outerPlan, Program.cost]⟩
  | succ fuel ih =>
      let st := trajectory p F J initial k
      have hs := trajectory_invariant p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit k
      by_cases hstop : st.k ≠ 0 ∧ ‖st.value‖ ≤ p.ε
      · refine ⟨0, Nat.zero_le _, by simp, ?_⟩
        change Program.cost (fun x => (F x, J x)) (outerPlan p initial (fuel + 1) st) = _
        simp only [outerPlan, ite_eq_left hstop, Program.cost, Finset.sum_range_zero]
      · have he := outer_cost_step p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit st hs fuel hstop
        by_cases hcap : (chosenTrial p F J initial st).step = maxStep p
        · refine ⟨1, by omega, ?_, ?_⟩
          · intro i hi
            have hi0 : i = 0 := by omega
            simpa only [hi0, Nat.add_zero] using hstop
          · rw [ite_eq_left hcap, Nat.add_zero] at he
            simpa only [Finset.sum_range_one, Nat.add_zero] using he
        · rw [ite_eq_right hcap] at he
          obtain ⟨n, hn, hactive, hcost⟩ := ih (k + 1)
          refine ⟨n + 1, by omega, ?_, ?_⟩
          · intro i hi
            cases i with
            | zero => simpa only [Nat.add_zero] using hstop
            | succ i =>
                have hh := hactive i (by omega)
                simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hh
          · change Program.cost (fun x => (F x, J x)) (outerPlan p initial (fuel + 1) st) = _
            rw [he]
            change stepWork p F J initial st +
              Program.cost (fun x => (F x, J x)) (outerPlan p initial fuel (trajectory p F J initial (k + 1))) = _
            rw [hcost, Finset.sum_range_succ']
            dsimp only [st]
            simp only [Nat.add_zero]
            rw [Nat.add_comm (stepWork p F J initial (trajectory p F J initial k))]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            congr 2
            omega

end Execution

end LongTails.Proofs.CohypomonotoneNewtonWork
