import LongTails.Proofs.CohypomonotoneNewtonExecution
import LongTails.Proofs.CohypomonotoneNewtonTransform
import LongTails.Proofs.CohypomonotoneNewtonEnergy
import LongTails.Proofs.CohypomonotoneNewtonBudget

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CohypomonotoneNewtonSearch

open LongTails.Setups.CohypomonotoneNewton
open LongTails.Algorithms.CohypomonotoneNewton
open LongTails.Proofs.CohypomonotoneNewtonGeometry
open LongTails.Proofs.CohypomonotoneNewtonExecution
open LongTails.Proofs.CohypomonotoneNewtonTransform
open OracleTemplate.ComponentEnvelope (Program)

universe u

lemma shift_bounds (p : Public.{u}) (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) :
    0 < shift p ∧ 2 * p.ρ ≤ shift p ∧ p.ρ < shift p ∧
      1 / (shift p - p.ρ) ≤ p.H * p.R := by
  have hi : 0 < 1 / (p.H * p.R) := by positivity
  have he : 1 / (p.H * p.R) * (p.H * p.R) = 1 := by field_simp
  dsimp only [shift]
  refine ⟨by positivity, by linarith, by linarith, ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 2 * p.ρ + 1 / (p.H * p.R) - p.ρ)).mpr
  have hp := mul_nonneg hρ (mul_pos hH hR).le
  nlinarith only [he, hp]

lemma tuning_positive (p : Public.{u}) (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε) :
    0 < baseStep p ∧ baseStep p ≤ maxStep p := by
  dsimp only [baseStep, maxStep]
  constructor
  · positivity
  · have hs : 0 < Real.sqrt (p.H * p.ε) := Real.sqrt_pos.mpr (mul_pos hH hε)
    have h1 : 0 ≤ 16 * p.R / p.ε := by positivity
    have h2 : 0 ≤ 2 / Real.sqrt (p.H * p.ε) := by positivity
    linarith

lemma tolerances_positive (p : Public.{u}) (st : OuterState p.E)
    (hH : 0 < p.H) (hR : 0 < p.R) (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a) :
    0 < centerTolerance p st a ∧ 0 < endpointTolerance p st a := by
  have he : 0 < errorScale p st a := by unfold errorScale; positivity
  unfold centerTolerance endpointTolerance
  constructor <;> apply lt_min <;> positivity

lemma inverse_public_correct (p : Public.{u}) {F : p.E → p.E}
    {J : p.E → p.E →L[ℝ] p.E} (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    {tol : ℝ} (htol : 0 < tol) (target start : p.E) :
    let out := Program.eval (fun x => (F x, J x))
      (inversePlan (shift p * p.H) (shift p) tol target start)
    out.2 = (F out.1, J out.1) ∧ ‖out.1 + shift p • F out.1 - target‖ ≤ tol := by
  have hγ := shift_bounds p hH hρ hR
  apply inversePlan_correct (mul_nonneg hγ.1.le hH.le) htol
    (fun x => (hasFDerivAt_id x).add ((hF x).const_smul (shift p)))
  · intro x y
    have he : (ContinuousLinearMap.id ℝ p.E + shift p • J x) -
        (ContinuousLinearMap.id ℝ p.E + shift p • J y) = shift p • (J x - J y) := by module
    rw [he, norm_smul, Real.norm_of_nonneg hγ.1.le]
    have hh := mul_le_mul_of_nonneg_left (hJ x y) hγ.1.le
    nlinarith only [hh]
  · exact shifted_expansive hγ.2.1 hγ.1.le hco

lemma trialPlan_correct (p : Public.{u}) {F : p.E → p.E}
    {J : p.E → p.E →L[ℝ] p.E} (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (st : OuterState p.E) (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (hini : st.k = 0 → initial.2 = (F initial.1, J initial.1) ∧
      ‖initial.1 + shift p • F initial.1 - midpoint p st a‖ ≤ centerTolerance p st a) :
    let trial := Program.eval (fun x => (F x, J x)) (trialPlan p st initial a)
    trial.step = a ∧ trial.sample.2 = (F trial.sample.1, J trial.sample.1) ∧
      ‖trial.sample.1 + shift p • F trial.sample.1 - midpoint p st a‖ ≤ centerTolerance p st a := by
  have ht := (tolerances_positive p st hH hR hA ha).1
  by_cases hk : st.k = 0
  · simpa only [trialPlan, ite_eq_left hk, Program.eval_map, Program.eval, true_and] using hini hk
  · have hh := inverse_public_correct p hH hρ hR hF hJ hco ht (midpoint p st a) st.point
    simpa only [trialPlan, ite_eq_right hk, Program.eval_map, true_and] using hh

lemma trialPlan_model (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E))) (a : ℝ)
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) :
    let trial := Program.eval reply (trialPlan p st initial a)
    trial.model = modelPoint (shift p) a (anchorMix p st a)
      (trial.sample.1 + shift p • trial.sample.2.1) trial.sample.2.1 trial.sample.2.2 := by
  simp only [trialPlan, Program.eval_map]

lemma modelPoint_graph_spec (p : Public.{u}) {F V : p.E → p.E}
    {J : p.E → p.E →L[ℝ] p.E} (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hright : ∀ y, V y + shift p • F (V y) = y)
    (hleft : ∀ x, V (x + shift p • F x) = x)
    {a : ℝ} (ha : 0 ≤ a) (c x : p.E) :
    let n := x + shift p • F x
    let w := modelPoint (shift p) a c n (F x) (J x)
    w + a • (F x + graphJacobian (shift p) (J x) (w - n)) = c ∧
      ‖w - n‖ ≤ ‖c - n - a • F x‖ := by
  have hγ := shift_bounds p hH hρ hR
  have he := shifted_expansive hγ.2.1 hγ.1.le hco
  have hd := graph_derivative hF he hright (x + shift p • F x)
  have hm := graph_monotone hγ.2.2.1.le hco hright
  have hmono := monotone_derivative hd (fun y => hm y (x + shift p • F x))
  rw [hleft] at hmono
  exact affinePoint_spec _ ha hmono c _ _

lemma initial_midpoint (p : Public.{u}) (st : OuterState p.E) (hk : st.k = 0)
    (hA : st.mass = 0) {a : ℝ} (ha : a ≠ 0) : midpoint p st a = p.x0 := by
  simp [LongTails.Algorithms.CohypomonotoneNewton.midpoint, anchorMix, currentValue, hk, hA, ha]

lemma initial_tolerance_le (p : Public.{u}) (st : OuterState p.E)
    (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε) (hk : st.k = 0) (hA : st.mass = 0)
    {a : ℝ} (ha : 0 < a) (haMax : a ≤ maxStep p) :
    min (p.R / 64) (1 / (4096 * p.H * maxStep p)) ≤ centerTolerance p st a := by
  have ht := tuning_positive p hH hR hε
  have hmax : 0 < maxStep p := ht.1.trans_le ht.2
  have he : errorScale p st a = p.R := by simp [errorScale, hk, hA, ha.ne']
  unfold centerTolerance
  rw [he]
  apply min_le_min le_rfl
  apply one_div_le_one_div_of_le (by positivity : 0 < 4096 * p.H * a)
  exact mul_le_mul_of_nonneg_left haMax (by positivity)

lemma initialized_trial_accuracy (p : Public.{u}) {F : p.E → p.E}
    {J : p.E → p.E →L[ℝ] p.E} (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R)
    (hε : 0 < p.ε) (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (start : p.E) (st : OuterState p.E) (hk : st.k = 0) (hA : st.mass = 0)
    {a : ℝ} (ha : 0 < a) (haMax : a ≤ maxStep p) :
    let initial := Program.eval (fun x => (F x, J x))
      (inversePlan (shift p * p.H) (shift p)
        (min (p.R / 64) (1 / (4096 * p.H * maxStep p))) p.x0 start)
    initial.2 = (F initial.1, J initial.1) ∧
      ‖initial.1 + shift p • F initial.1 - midpoint p st a‖ ≤ centerTolerance p st a := by
  have ht := tuning_positive p hH hR hε
  have hmax : 0 < maxStep p := ht.1.trans_le ht.2
  have htol : 0 < min (p.R / 64) (1 / (4096 * p.H * maxStep p)) := by
    apply lt_min <;> positivity
  have hi := inverse_public_correct p hH hρ hR hF hJ hco htol p.x0 start
  refine ⟨hi.1, ?_⟩
  rw [initial_midpoint p st hk hA ha.ne']
  exact hi.2.trans (initial_tolerance_le p st hH hR hε hk hA ha haMax)

lemma search_bracket_success (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) (q : ℝ → ℝ)
    (hq : ∀ a, merit p (Program.eval reply (trialPlan p st initial a)) = q a)
    {amin amax gap : ℝ} (hmin : 0 < amin)
    (hsep : ∀ l h, amin ≤ l → h ≤ amax → l ≤ h → q l < 1 / 64 → 1 / 32 < q h → gap ≤ h - l)
    (fuel : ℕ) {lo hi : ℝ} (hlo : amin ≤ lo) (hhi : hi ≤ amax) (horder : lo ≤ hi)
    (hlow : q lo < 1 / 64) (hhigh : 1 / 32 < q hi)
    (hwidth : hi - lo < (2 : ℝ) ^ fuel * gap) :
    ∃ trial, Program.eval reply (searchPlan p st initial fuel lo hi ((lo + hi) / 2)) = some trial := by
  induction fuel generalizing lo hi with
  | zero =>
      have hs := hsep lo hi hlo hhi horder hlow hhigh
      simp only [pow_zero, one_mul] at hwidth
      linarith
  | succ fuel ih =>
      have hlo0 : lo ≠ 0 := ne_of_gt (hmin.trans_le hlo)
      have hhi0 : hi ≠ 0 := ne_of_gt ((hmin.trans_le hlo).trans_le horder)
      have hmidlo : lo ≤ (lo + hi) / 2 := by linarith
      have hmidhi : (lo + hi) / 2 ≤ hi := by linarith
      rw [searchPlan, Program.eval_bind]
      simp only [hq]
      by_cases hacc : q ((lo + hi) / 2) ≤ 1 / 32 ∧
          (1 / 64 ≤ q ((lo + hi) / 2) ∨ (lo + hi) / 2 = maxStep p)
      · rw [ite_eq_left hacc]
        exact ⟨_, rfl⟩
      · rw [ite_eq_right hacc]
        by_cases hlowmid : q ((lo + hi) / 2) < 1 / 64
        · rw [ite_eq_left hlowmid, ite_eq_right hhi0]
          apply ih (hlo.trans hmidlo) hhi hmidhi hlowmid hhigh
          rw [pow_succ] at hwidth
          nlinarith only [hwidth]
        · rw [ite_eq_right hlowmid, ite_eq_right hlo0]
          have hhighmid : 1 / 32 < q ((lo + hi) / 2) := by
            by_contra hn
            exact hacc ⟨le_of_not_gt hn, Or.inl (le_of_not_gt hlowmid)⟩
          apply ih hlo (hmidhi.trans hhi) hmidlo hlow hhighmid
          rw [pow_succ] at hwidth
          nlinarith only [hwidth]

lemma search_up_success (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) (q : ℝ → ℝ)
    (hq : ∀ a, merit p (Program.eval reply (trialPlan p st initial a)) = q a)
    {amin gap : ℝ} (hmin : 0 < amin) (hgap : 0 < gap)
    (hsep : ∀ l h, amin ≤ l → h ≤ maxStep p → l ≤ h →
      q l < 1 / 64 → 1 / 32 < q h → gap ≤ h - l)
    (bis geom : ℕ) (hbis : maxStep p < (2 : ℝ) ^ bis * gap)
    {lo a : ℝ} (hlo : amin ≤ lo) (hla : lo ≤ a) (ha : a ≤ maxStep p)
    (hlow : q lo < 1 / 64) (hreach : maxStep p ≤ (2 : ℝ) ^ geom * a) :
    ∃ trial, Program.eval reply (searchPlan p st initial (geom + bis + 1) lo 0 a) = some trial := by
  induction geom generalizing lo a with
  | zero =>
      have hEq : a = maxStep p := le_antisymm ha (by simpa using hreach)
      rw [searchPlan, Program.eval_bind]
      simp only [hq]
      by_cases hacc : q a ≤ 1 / 32 ∧ (1 / 64 ≤ q a ∨ a = maxStep p)
      · rw [ite_eq_left hacc]; exact ⟨_, rfl⟩
      · have hhigh : 1 / 32 < q a := by
          by_contra hn
          exact hacc ⟨le_of_not_gt hn, Or.inr hEq⟩
        have hnlow : ¬q a < 1 / 64 := by linarith
        rw [ite_eq_right hacc, ite_eq_right hnlow, ite_eq_right (ne_of_gt (hmin.trans_le hlo))]
        simp only [Nat.zero_add]
        apply search_bracket_success p st initial reply q hq hmin hsep bis hlo ha hla hlow hhigh
        have hl0 := (hmin.trans_le hlo).le
        simpa only [zero_add] using (show a - lo < (2 : ℝ) ^ bis * gap by linarith)
  | succ geom ih =>
      have hf : geom + 1 + bis + 1 = (geom + bis + 1) + 1 := by omega
      rw [hf, searchPlan, Program.eval_bind]
      simp only [hq]
      by_cases hacc : q a ≤ 1 / 32 ∧ (1 / 64 ≤ q a ∨ a = maxStep p)
      · rw [ite_eq_left hacc]; exact ⟨_, rfl⟩
      · rw [ite_eq_right hacc]
        by_cases hlowA : q a < 1 / 64
        · rw [ite_eq_left hlowA, ite_eq_left True.intro]
          have ha0 : 0 < a := (hmin.trans_le hlo).trans_le hla
          have hnext : a ≤ min (2 * a) (maxStep p) := le_min (by linarith) ha
          apply ih (hlo.trans hla) hnext (min_le_right _ _) hlowA
          rw [pow_succ] at hreach
          by_cases hdouble : 2 * a ≤ maxStep p
          · rw [min_eq_left hdouble]
            nlinarith only [hreach]
          · rw [min_eq_right (le_of_not_ge hdouble)]
            have hp : 1 ≤ (2 : ℝ) ^ geom := one_le_pow₀ (by norm_num)
            have hm := mul_le_mul_of_nonneg_right hp (ha0.le.trans ha)
            simpa using hm
        · rw [ite_eq_right hlowA, ite_eq_right (ne_of_gt (hmin.trans_le hlo))]
          have hhigh : 1 / 32 < q a := by
            by_contra hn
            exact hacc ⟨le_of_not_gt hn, Or.inl (le_of_not_gt hlowA)⟩
          apply search_bracket_success p st initial reply q hq hmin hsep (geom + bis + 1)
            hlo ha hla hlow hhigh
          have hp : (2 : ℝ) ^ bis ≤ 2 ^ (geom + bis + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have hm := mul_le_mul_of_nonneg_right hp hgap.le
          have hl0 := (hmin.trans_le hlo).le
          linarith

lemma search_down_success (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) (q : ℝ → ℝ)
    (hq : ∀ a, merit p (Program.eval reply (trialPlan p st initial a)) = q a)
    {gap : ℝ} (hmin : 0 < baseStep p) (hgap : 0 < gap) (hfloor : q (baseStep p) < 1 / 64)
    (hsep : ∀ l h, baseStep p ≤ l → h ≤ maxStep p → l ≤ h →
      q l < 1 / 64 → 1 / 32 < q h → gap ≤ h - l)
    (bis geom : ℕ) (hbis : maxStep p < (2 : ℝ) ^ bis * gap)
    {hi a : ℝ} (hhi : hi ≤ maxStep p) (hah : a ≤ hi) (ha : baseStep p ≤ a)
    (hhigh : 1 / 32 < q hi) (hreach : a ≤ (2 : ℝ) ^ geom * baseStep p) :
    ∃ trial, Program.eval reply (searchPlan p st initial (geom + bis + 1) 0 hi a) = some trial := by
  induction geom generalizing hi a with
  | zero =>
      have hEq : a = baseStep p := le_antisymm (by simpa using hreach) ha
      have hlow : q a < 1 / 64 := by simpa [hEq] using hfloor
      have hhi0 : hi ≠ 0 := ne_of_gt ((hmin.trans_le ha).trans_le hah)
      rw [searchPlan, Program.eval_bind]
      simp only [hq]
      by_cases hacc : q a ≤ 1 / 32 ∧ (1 / 64 ≤ q a ∨ a = maxStep p)
      · rw [ite_eq_left hacc]; exact ⟨_, rfl⟩
      · rw [ite_eq_right hacc, ite_eq_left hlow, ite_eq_right hhi0]
        simp only [Nat.zero_add]
        apply search_bracket_success p st initial reply q hq hmin hsep bis ha hhi hah hlow hhigh
        have ha0 := (hmin.trans_le ha).le
        linarith
  | succ geom ih =>
      have hf : geom + 1 + bis + 1 = (geom + bis + 1) + 1 := by omega
      rw [hf, searchPlan, Program.eval_bind]
      simp only [hq]
      by_cases hacc : q a ≤ 1 / 32 ∧ (1 / 64 ≤ q a ∨ a = maxStep p)
      · rw [ite_eq_left hacc]; exact ⟨_, rfl⟩
      · rw [ite_eq_right hacc]
        by_cases hlowA : q a < 1 / 64
        · have hhi0 : hi ≠ 0 := ne_of_gt ((hmin.trans_le ha).trans_le hah)
          rw [ite_eq_left hlowA, ite_eq_right hhi0]
          apply search_bracket_success p st initial reply q hq hmin hsep (geom + bis + 1)
            ha hhi hah hlowA hhigh
          have hp : (2 : ℝ) ^ bis ≤ 2 ^ (geom + bis + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have hm := mul_le_mul_of_nonneg_right hp hgap.le
          have ha0 := (hmin.trans_le ha).le
          linarith
        · rw [ite_eq_right hlowA, ite_eq_left True.intro]
          have hhighA : 1 / 32 < q a := by
            by_contra hn
            exact hacc ⟨le_of_not_gt hn, Or.inl (le_of_not_gt hlowA)⟩
          have ha0 : 0 < a := hmin.trans_le ha
          have hnext : max (a / 2) (baseStep p) ≤ a := max_le (by linarith) ha
          apply ih (hah.trans hhi) hnext (le_max_right _ _) hhighA
          apply max_le
          · rw [pow_succ] at hreach
            nlinarith only [hreach]
          · have hp : 1 ≤ (2 : ℝ) ^ geom := one_le_pow₀ (by norm_num)
            have hm := mul_le_mul_of_nonneg_right hp hmin.le
            simpa using hm

lemma search_initial_success (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) (q : ℝ → ℝ)
    (hq : ∀ a, merit p (Program.eval reply (trialPlan p st initial a)) = q a)
    {gap : ℝ} (hmin : 0 < baseStep p) (hgap : 0 < gap) (hfloor : q (baseStep p) < 1 / 64)
    (hsep : ∀ l h, baseStep p ≤ l → h ≤ maxStep p → l ≤ h →
      q l < 1 / 64 → 1 / 32 < q h → gap ≤ h - l)
    (bis geom : ℕ) (hbis : maxStep p < (2 : ℝ) ^ bis * gap)
    (hgeom : maxStep p ≤ (2 : ℝ) ^ geom * baseStep p)
    {a : ℝ} (haMin : baseStep p ≤ a) (haMax : a ≤ maxStep p) :
    ∃ trial, Program.eval reply (searchPlan p st initial (geom + bis + 2) 0 0 a) = some trial := by
  rw [show geom + bis + 2 = (geom + bis + 1) + 1 by omega, searchPlan, Program.eval_bind]
  simp only [hq]
  by_cases hacc : q a ≤ 1 / 32 ∧ (1 / 64 ≤ q a ∨ a = maxStep p)
  · rw [ite_eq_left hacc]; exact ⟨_, rfl⟩
  · rw [ite_eq_right hacc]
    by_cases hlow : q a < 1 / 64
    · rw [ite_eq_left hlow, ite_eq_left True.intro]
      have ha0 : 0 < a := hmin.trans_le haMin
      have hnext : a ≤ min (2 * a) (maxStep p) := le_min (by linarith) haMax
      apply search_up_success p st initial reply q hq hmin hgap hsep bis geom hbis
        haMin hnext (min_le_right _ _) hlow
      exact hgeom.trans (mul_le_mul_of_nonneg_left (haMin.trans hnext) (by positivity))
    · rw [ite_eq_right hlow, ite_eq_left True.intro]
      have hhigh : 1 / 32 < q a := by
        by_contra hn
        exact hacc ⟨le_of_not_gt hn, Or.inl (le_of_not_gt hlow)⟩
      have ha0 : 0 < a := hmin.trans_le haMin
      have hnext : max (a / 2) (baseStep p) ≤ a := max_le (by linarith) haMin
      apply search_down_success p st initial reply q hq hmin hgap hfloor hsep bis geom hbis
        haMax hnext (le_max_right _ _) hhigh
      exact hnext.trans (haMax.trans hgeom)

lemma search_more_fuel (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) (fuel extra : ℕ)
    {lo hi a : ℝ} {trial : Trial p.E}
    (hsuccess : Program.eval reply (searchPlan p st initial fuel lo hi a) = some trial) :
    Program.eval reply (searchPlan p st initial (fuel + extra) lo hi a) = some trial := by
  induction fuel generalizing lo hi a with
  | zero => simp [searchPlan, Program.eval] at hsuccess
  | succ fuel ih =>
      rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
      simp only [searchPlan, Program.eval_bind] at hsuccess ⊢
      split_ifs at hsuccess ⊢ <;> first | exact hsuccess | exact ih hsuccess

lemma search_result_certificate (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) (hmin : 0 < baseStep p) (fuel : ℕ)
    {lo hi a : ℝ} (hlo : lo = 0 ∨ baseStep p ≤ lo ∧ lo ≤ maxStep p)
    (hhi : hi = 0 ∨ baseStep p ≤ hi ∧ hi ≤ maxStep p)
    (ha : baseStep p ≤ a ∧ a ≤ maxStep p) {trial : Trial p.E}
    (hsuccess : Program.eval reply (searchPlan p st initial fuel lo hi a) = some trial) :
    ∃ b, baseStep p ≤ b ∧ b ≤ maxStep p ∧
      trial = Program.eval reply (trialPlan p st initial b) ∧
      merit p trial ≤ 1 / 32 ∧ (1 / 64 ≤ merit p trial ∨ b = maxStep p) := by
  induction fuel generalizing lo hi a with
  | zero => simp [searchPlan, Program.eval] at hsuccess
  | succ fuel ih =>
      rw [searchPlan, Program.eval_bind] at hsuccess
      by_cases hacc : merit p (Program.eval reply (trialPlan p st initial a)) ≤ 1 / 32 ∧
          (1 / 64 ≤ merit p (Program.eval reply (trialPlan p st initial a)) ∨ a = maxStep p)
      · rw [ite_eq_left hacc, Program.eval] at hsuccess
        have ht := Option.some.inj hsuccess
        exact ⟨a, ha.1, ha.2, ht.symm, by simpa [← ht] using hacc⟩
      · rw [ite_eq_right hacc] at hsuccess
        by_cases hlow : merit p (Program.eval reply (trialPlan p st initial a)) < 1 / 64
        · rw [ite_eq_left hlow] at hsuccess
          apply ih (Or.inr ha) hhi _ hsuccess
          by_cases hh : hi = 0
          · rw [ite_eq_left hh]
            constructor
            · apply le_min
              · linarith [ha.1]
              · exact ha.1.trans ha.2
            · exact min_le_right _ _
          · rw [ite_eq_right hh]
            have hb := hhi.resolve_left hh
            constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
        · rw [ite_eq_right hlow] at hsuccess
          apply ih hlo (Or.inr ha) _ hsuccess
          by_cases hl : lo = 0
          · rw [ite_eq_left hl]
            constructor
            · exact le_max_right _ _
            · apply max_le
              · linarith [ha.1, ha.2]
              · exact ha.1.trans ha.2
          · rw [ite_eq_right hl]
            have hb := hlo.resolve_left hl
            constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma public_search_success (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (reply : p.E → p.E × (p.E →L[ℝ] p.E)) (q : ℝ → ℝ)
    (hq : ∀ a, merit p (Program.eval reply (trialPlan p st initial a)) = q a)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hfloor : q (baseStep p) < 1 / 64)
    (hsep : ∀ l h, baseStep p ≤ l → h ≤ maxStep p → l ≤ h →
      q l < 1 / 64 → 1 / 32 < q h →
      1 / (16000000000 * p.H * p.R * (1 + p.H * p.R ^ 2 / p.ε) ^ 3) ≤ h - l)
    {a : ℝ} (ha : baseStep p ≤ a ∧ a ≤ maxStep p) :
    ∃ trial, Program.eval reply (searchPlan p st initial (searchFuel p) 0 0 a) = some trial := by
  let B := 2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε
  let geom := ⌈30 * (1 + Real.log B)⌉₊
  let bis := ⌈100 * (1 + Real.log B)⌉₊
  have hd := LongTails.Proofs.CohypomonotoneNewtonBudget.public_search_depths p hH hρ hR hε
  have ht := tuning_positive p hH hR hε
  have hg : 0 < 1 / (16000000000 * p.H * p.R * (1 + p.H * p.R ^ 2 / p.ε) ^ 3) := by positivity
  obtain ⟨trial, htrial⟩ := search_initial_success p st initial reply q hq ht.1 hg hfloor hsep
    bis geom hd.1 hd.2.1 ha.1 ha.2
  have hh := search_more_fuel p st initial reply (geom + bis + 2)
    (searchFuel p - (geom + bis + 2)) htrial
  rw [Nat.add_sub_of_le hd.2.2] at hh
  exact ⟨trial, hh⟩

lemma anchorMix_rewrite (p : Public.{u}) (st : OuterState p.E) {a : ℝ}
    (hden : st.mass + a ≠ 0) :
    anchorMix p st a = currentPoint p st +
      (a / (st.mass + a)) • (p.x0 - currentPoint p st) := by
  have he : st.mass / (st.mass + a) = 1 - a / (st.mass + a) := by field_simp; ring
  unfold anchorMix
  rw [he]
  module

lemma midpoint_rewrite (p : Public.{u}) (st : OuterState p.E) {a : ℝ}
    (hden : st.mass + a ≠ 0) :
    midpoint p st a = currentPoint p st + (a / (st.mass + a)) •
      (p.x0 - currentPoint p st - st.mass • currentValue p st) := by
  unfold LongTails.Algorithms.CohypomonotoneNewton.midpoint
  rw [anchorMix_rewrite p st hden]
  have he : a * st.mass / (st.mass + a) = a / (st.mass + a) * st.mass := by ring
  rw [he, mul_smul]
  module

lemma warm_start_bound (p : Public.{u}) (st : OuterState p.E) (root : p.E)
    (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hy : ‖currentPoint p st - root‖ ≤ 3 * p.R)
    (hg : st.mass * ‖currentValue p st‖ ≤ 4 * p.R) :
    ‖currentPoint p st - midpoint p st a‖ ≤ 8 * p.R * (a / (st.mass + a)) := by
  have hden : 0 < st.mass + a := by positivity
  rw [midpoint_rewrite p st hden.ne']
  have he : currentPoint p st - (currentPoint p st + (a / (st.mass + a)) •
      (p.x0 - currentPoint p st - st.mass • currentValue p st)) =
      -(a / (st.mass + a)) • (p.x0 - currentPoint p st - st.mass • currentValue p st) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos ha hden)]
  have hxy : ‖p.x0 - currentPoint p st‖ ≤ 4 * p.R := by
    have he' : p.x0 - currentPoint p st = (p.x0 - root) - (currentPoint p st - root) := by abel
    rw [he']
    exact (norm_sub_le _ _).trans (by linarith)
  have hn := norm_sub_le (p.x0 - currentPoint p st) (st.mass • currentValue p st)
  rw [norm_smul, Real.norm_of_nonneg hA] at hn
  have hb : ‖p.x0 - currentPoint p st - st.mass • currentValue p st‖ ≤ 8 * p.R := by
    linarith
  have hh := mul_le_mul_of_nonneg_left hb (div_pos ha hden).le
  nlinarith only [hh]

lemma anchorMix_radius (p : Public.{u}) (st : OuterState p.E) (root : p.E)
    (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hy : ‖currentPoint p st - root‖ ≤ 3 * p.R) :
    ‖anchorMix p st a - root‖ ≤ 3 * p.R := by
  have hR : 0 ≤ p.R := (norm_nonneg _).trans hroot
  have hden : 0 < st.mass + a := by positivity
  have he : a / (st.mass + a) + st.mass / (st.mass + a) = 1 := by field_simp; ring
  have hid : anchorMix p st a - root = (a / (st.mass + a)) • (p.x0 - root) +
      (st.mass / (st.mass + a)) • (currentPoint p st - root) := by
    unfold anchorMix
    rw [smul_sub, smul_sub]
    have hr := congrArg (fun r : ℝ => r • root) he
    simp only [add_smul, one_smul] at hr
    linear_combination (norm := module) hr
  rw [hid]
  have ht := norm_add_le ((a / (st.mass + a)) • (p.x0 - root))
    ((st.mass / (st.mass + a)) • (currentPoint p st - root))
  simp only [norm_smul, Real.norm_of_nonneg (div_nonneg ha.le hden.le),
    Real.norm_of_nonneg (div_nonneg hA hden.le)] at ht
  have h1 := mul_le_mul_of_nonneg_left (show ‖p.x0 - root‖ ≤ 3 * p.R by linarith)
    (div_nonneg ha.le hden.le)
  have h2 := mul_le_mul_of_nonneg_left hy (div_nonneg hA hden.le)
  have heR := congrArg (fun t : ℝ => t * (3 * p.R)) he
  nlinarith only [ht, h1, h2, heR]

lemma anchor_midpoint_distance (p : Public.{u}) (st : OuterState p.E)
    (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a) :
    ‖anchorMix p st a - midpoint p st a‖ =
      (a / (st.mass + a)) * (st.mass * ‖currentValue p st‖) := by
  have hden : 0 < st.mass + a := by positivity
  unfold LongTails.Algorithms.CohypomonotoneNewton.midpoint
  rw [sub_sub_cancel, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ a * st.mass / (st.mass + a))]
  ring

lemma midpoint_radius (p : Public.{u}) (st : OuterState p.E) (root : p.E)
    (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hy : ‖currentPoint p st - root‖ ≤ 3 * p.R)
    (hg : st.mass * ‖currentValue p st‖ ≤ 4 * p.R) :
    ‖midpoint p st a - root‖ ≤ 7 * p.R := by
  have hR : 0 ≤ p.R := (norm_nonneg _).trans hroot
  have hden : 0 < st.mass + a := by positivity
  have halpha : a / (st.mass + a) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hdist := anchor_midpoint_distance p st hA ha
  have h1 := mul_le_mul_of_nonneg_left hg (div_pos ha hden).le
  have h2 := mul_le_mul_of_nonneg_right halpha (by positivity : 0 ≤ 4 * p.R)
  have h3 := anchorMix_radius p st root hA ha hroot hy
  have he : midpoint p st a - root =
      (anchorMix p st a - root) - (anchorMix p st a - midpoint p st a) := by abel
  rw [he]
  have ht := norm_sub_le (anchorMix p st a - root) (anchorMix p st a - midpoint p st a)
  nlinarith only [hdist, h1, h2, h3, ht]

lemma midpoint_lipschitz (p : Public.{u}) (st : OuterState p.E) (root : p.E)
    (hA : 0 < st.mass) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hy : ‖currentPoint p st - root‖ ≤ 3 * p.R)
    (hg : st.mass * ‖currentValue p st‖ ≤ 4 * p.R) :
    ‖midpoint p st a - midpoint p st b‖ ≤ (8 * p.R / st.mass) * |a - b| := by
  have hAa : st.mass + a ≠ 0 := ne_of_gt (by positivity)
  have hAb : st.mass + b ≠ 0 := ne_of_gt (by positivity)
  rw [midpoint_rewrite p st hAa, midpoint_rewrite p st hAb]
  have he : currentPoint p st + (a / (st.mass + a)) •
      (p.x0 - currentPoint p st - st.mass • currentValue p st) -
      (currentPoint p st + (b / (st.mass + b)) •
        (p.x0 - currentPoint p st - st.mass • currentValue p st)) =
      (a / (st.mass + a) - b / (st.mass + b)) •
        (p.x0 - currentPoint p st - st.mass • currentValue p st) := by module
  rw [he, norm_smul, Real.norm_eq_abs]
  have hxy : ‖p.x0 - currentPoint p st‖ ≤ 4 * p.R := by
    have he' : p.x0 - currentPoint p st = (p.x0 - root) - (currentPoint p st - root) := by abel
    rw [he']
    exact (norm_sub_le _ _).trans (by linarith)
  have hn := norm_sub_le (p.x0 - currentPoint p st) (st.mass • currentValue p st)
  rw [norm_smul, Real.norm_of_nonneg hA.le] at hn
  have hv : ‖p.x0 - currentPoint p st - st.mass • currentValue p st‖ ≤ 8 * p.R := by linarith
  have hh := mul_le_mul (fraction_difference_bound hA ha hb) hv (norm_nonneg _)
    (by positivity : 0 ≤ |a - b| / st.mass)
  convert hh using 1; ring

lemma anchorMix_lipschitz (p : Public.{u}) (st : OuterState p.E) (root : p.E)
    (hA : 0 < st.mass) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hy : ‖currentPoint p st - root‖ ≤ 3 * p.R) :
    ‖anchorMix p st a - anchorMix p st b‖ ≤ (4 * p.R / st.mass) * |a - b| := by
  rw [anchorMix_rewrite p st (ne_of_gt (by positivity : 0 < st.mass + a)),
    anchorMix_rewrite p st (ne_of_gt (by positivity : 0 < st.mass + b))]
  have he : currentPoint p st + (a / (st.mass + a)) • (p.x0 - currentPoint p st) -
      (currentPoint p st + (b / (st.mass + b)) • (p.x0 - currentPoint p st)) =
      (a / (st.mass + a) - b / (st.mass + b)) • (p.x0 - currentPoint p st) := by module
  rw [he, norm_smul, Real.norm_eq_abs]
  have hxy : ‖p.x0 - currentPoint p st‖ ≤ 4 * p.R := by
    have he' : p.x0 - currentPoint p st = (p.x0 - root) - (currentPoint p st - root) := by abel
    rw [he']
    exact (norm_sub_le _ _).trans (by linarith)
  have hh := mul_le_mul (fraction_difference_bound hA ha hb) hxy (norm_nonneg _)
    (by positivity : 0 ≤ |a - b| / st.mass)
  convert hh using 1; ring

lemma anchor_midpoint_distance_le (p : Public.{u}) (st : OuterState p.E)
    (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a) :
    ‖anchorMix p st a - midpoint p st a‖ ≤ a * ‖currentValue p st‖ := by
  have hden : 0 < st.mass + a := by positivity
  have hr : st.mass / (st.mass + a) ≤ 1 := (div_le_one hden).mpr (by linarith)
  calc
    _ = (st.mass / (st.mass + a)) * (a * ‖currentValue p st‖) := by
      rw [anchor_midpoint_distance p st hA ha]
      ring
    _ ≤ 1 * (a * ‖currentValue p st‖) :=
      mul_le_mul_of_nonneg_right hr (mul_nonneg ha.le (norm_nonneg _))
    _ = _ := one_mul _

lemma exact_model_displacement (p : Public.{u}) (st : OuterState p.E) (root : p.E)
    (G : p.E → p.E) (D : p.E →L[ℝ] p.E) {L a : ℝ} (hL : 0 ≤ L)
    (hA : 0 ≤ st.mass) (ha : 0 < a) (hmono : ∀ v, 0 ≤ ⟪D v, v⟫)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hy : ‖currentPoint p st - root‖ ≤ 3 * p.R)
    (hg : st.mass * ‖currentValue p st‖ ≤ 4 * p.R)
    (hcurrent : ‖currentValue p st‖ ≤ 3 * L * p.R)
    (hGroot : G root = 0) (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) :
    ‖affinePoint a (anchorMix p st a) (midpoint p st a) (G (midpoint p st a)) D - midpoint p st a‖ ≤
      10 * a * L * p.R := by
  have hm := midpoint_radius p st root hA ha hroot hy hg
  have hGm := hlip (midpoint p st a) root
  rw [hGroot, sub_zero] at hGm
  have hGm' : ‖G (midpoint p st a)‖ ≤ 7 * L * p.R := by
    have hh := mul_le_mul_of_nonneg_left hm hL
    nlinarith only [hGm, hh]
  have hw := (affinePoint_spec D ha.le hmono (anchorMix p st a) (midpoint p st a)
    (G (midpoint p st a))).2
  have ht := norm_sub_le (anchorMix p st a - midpoint p st a) (a • G (midpoint p st a))
  rw [norm_smul, Real.norm_of_nonneg ha.le] at ht
  have hc := anchor_midpoint_distance_le p st hA ha
  have h1 := mul_le_mul_of_nonneg_left hcurrent ha.le
  have h2 := mul_le_mul_of_nonneg_left hGm' ha.le
  nlinarith only [hw, ht, hc, h1, h2]

lemma exact_floor_merit (p : Public.{u}) {w m : p.E} (hH : 0 < p.H) (hR : 0 < p.R)
    (hdisp : ‖w - m‖ ≤ 10 * baseStep p * (p.H * p.R) * p.R) :
    baseStep p * p.H * ‖w - m‖ ≤ 10 / 128 ^ 2 := by
  have ha : 0 < baseStep p := by unfold baseStep; positivity
  have hh := mul_le_mul_of_nonneg_left hdisp (mul_nonneg ha.le hH.le)
  have he : baseStep p * p.H * (10 * baseStep p * (p.H * p.R) * p.R) = 10 / 128 ^ 2 := by
    unfold baseStep
    field_simp
  exact hh.trans_eq he

lemma exact_merit_lipschitz (p : Public.{u}) (st : OuterState p.E) (root : p.E)
    (G : p.E → p.E) (J : p.E → p.E →L[ℝ] p.E)
    (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε) (hA : baseStep p ≤ st.mass)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hy : ‖currentPoint p st - root‖ ≤ 3 * p.R)
    (hg : st.mass * ‖currentValue p st‖ ≤ 4 * p.R)
    (hcurrent : ‖currentValue p st‖ ≤ 3 * (p.H * p.R) * p.R)
    (hGroot : G root = 0) (hlip : ∀ x y, ‖G x - G y‖ ≤ (p.H * p.R) * ‖x - y‖)
    (hJn : ∀ x, ‖J x‖ ≤ p.H * p.R)
    (hJL : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hmono : ∀ x v, 0 ≤ ⟪J x v, v⟫)
    {a b : ℝ} (ha : baseStep p ≤ a ∧ a ≤ maxStep p) (hb : baseStep p ≤ b ∧ b ≤ maxStep p) :
    let m := fun t => midpoint p st t
    let w := fun t => affinePoint t (anchorMix p st t) (m t) (G (m t)) (J (m t))
    |a * p.H * ‖w a - m a‖ - b * p.H * ‖w b - m b‖| ≤
      160000000 * p.H * p.R * (1 + p.H * p.R ^ 2 / p.ε) ^ 3 * |a - b| := by
  let m := fun t => midpoint p st t
  let w := fun t => affinePoint t (anchorMix p st t) (m t) (G (m t)) (J (m t))
  let U := p.H * p.R * maxStep p
  have ht := tuning_positive p hH hR hε
  have hA0 : 0 < st.mass := ht.1.trans_le hA
  have ha0 : 0 < a := ht.1.trans_le ha.1
  have hb0 : 0 < b := ht.1.trans_le hb.1
  have hmax : 0 < maxStep p := ht.1.trans_le ht.2
  have hL : 0 ≤ p.H * p.R := mul_nonneg hH.le hR.le
  have hc0 := LongTails.Proofs.CohypomonotoneNewtonBudget.center_lipschitz_constants p hH hR hA
  have hc : ‖anchorMix p st a - anchorMix p st b‖ ≤ 512 * p.H * p.R ^ 2 * |a - b| :=
    (anchorMix_lipschitz p st root hA0 ha0.le hb0.le hroot hy).trans
      (mul_le_mul_of_nonneg_right hc0.1 (abs_nonneg _))
  have hm : ‖m a - m b‖ ≤ 1024 * p.H * p.R ^ 2 * |a - b| :=
    (midpoint_lipschitz p st root hA0 ha0.le hb0.le hroot hy hg).trans
      (mul_le_mul_of_nonneg_right hc0.2 (abs_nonneg _))
  have hmn : ‖m b - m a‖ ≤ 1024 * p.H * p.R ^ 2 * |a - b| := by
    rwa [norm_sub_rev] at hm
  have hspecA := affinePoint_spec (J (m a)) ha0.le (hmono (m a)) (anchorMix p st a) (m a) (G (m a))
  have hspecB := affinePoint_spec (J (m b)) hb0.le (hmono (m b)) (anchorMix p st b) (m b) (G (m b))
  have hdisp := exact_model_displacement p st root G (J (m b)) hL hA0.le hb0 (hmono (m b))
    hroot hy hg hcurrent hGroot hlip
  have hD : ‖w b - m b‖ ≤ 10 * U * p.R := by
    have hh := mul_le_mul_of_nonneg_right hb.2 (by positivity : 0 ≤ 10 * (p.H * p.R) * p.R)
    dsimp only [U]
    nlinarith only [hdisp, hh]
  have hmr := midpoint_radius p st root hA0.le hb0 hroot hy hg
  have hGm := hlip (m b) root
  rw [hGroot, sub_zero] at hGm
  have hGn : ‖G (m b)‖ ≤ 7 * (p.H * p.R) * p.R := by
    have hh := mul_le_mul_of_nonneg_left hmr hL
    nlinarith only [hGm, hh]
  have hv := affine_path_lipschitz ha0.le ha.2 hL hH.le
    (by positivity : 0 ≤ 1024 * p.H * p.R ^ 2) (by dsimp [U]; positivity : 0 ≤ 10 * U * p.R)
    (m a) (m b) (w a) (w b) (anchorMix p st a) (anchorMix p st b) (hmono (m a))
    hspecA.1 hspecB.1 (hlip (m b) (m a)) (hJn (m a)) (hJn (m b)) (hJL (m b) (m a)) hGn hD hc hmn
  have hvconst := LongTails.Proofs.CohypomonotoneNewtonBudget.affine_path_constant hH.le hR.le hmax.le
  have hv' : ‖w a - w b‖ ≤ 20000 * p.H * p.R ^ 2 * (1 + U) ^ 2 * |a - b| :=
    hv.trans (mul_le_mul_of_nonneg_right hvconst (abs_nonneg _))
  have hmerit := merit_path_lipschitz ha0.le ha.2 hH.le
    (by positivity : 0 ≤ 20000 * p.H * p.R ^ 2 * (1 + U) ^ 2)
    (by positivity : 0 ≤ 1024 * p.H * p.R ^ 2) (w a) (w b) (m a) (m b) hD hv' hm
  have hconst := LongTails.Proofs.CohypomonotoneNewtonBudget.merit_path_constant hH.le hR.le hmax.le
  have hpublic := LongTails.Proofs.CohypomonotoneNewtonBudget.public_merit_path_constant p hH hR hε
  exact hmerit.trans (mul_le_mul_of_nonneg_right (hconst.trans hpublic) (abs_nonneg _))

lemma initial_centers (p : Public.{u}) (st : OuterState p.E) (hk : st.k = 0)
    (hA : 0 ≤ st.mass) {a : ℝ} (ha : 0 < a) :
    anchorMix p st a = p.x0 ∧ midpoint p st a = p.x0 := by
  have hden : st.mass + a ≠ 0 := ne_of_gt (by positivity)
  have hc : anchorMix p st a = p.x0 := by
    rw [anchorMix_rewrite p st hden]
    simp [currentPoint, hk]
  refine ⟨hc, ?_⟩
  unfold LongTails.Algorithms.CohypomonotoneNewton.midpoint
  simp [hc, currentValue, hk]

lemma initial_exact_merit_lipschitz (p : Public.{u}) (root : p.E)
    (G : p.E → p.E) (J : p.E → p.E →L[ℝ] p.E)
    (hH : 0 < p.H) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hGroot : G root = 0)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ (p.H * p.R) * ‖x - y‖)
    (hJn : ∀ x, ‖J x‖ ≤ p.H * p.R)
    (hJL : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hmono : ∀ x v, 0 ≤ ⟪J x v, v⟫)
    {a b : ℝ} (ha : baseStep p ≤ a ∧ a ≤ maxStep p) (hb : baseStep p ≤ b ∧ b ≤ maxStep p) :
    let w := fun t => affinePoint t p.x0 p.x0 (G p.x0) (J p.x0)
    |a * p.H * ‖w a - p.x0‖ - b * p.H * ‖w b - p.x0‖| ≤
      160000000 * p.H * p.R * (1 + p.H * p.R ^ 2 / p.ε) ^ 3 * |a - b| := by
  let st : OuterState p.E := ⟨0, baseStep p, baseStep p, p.x0, 0⟩
  have ht := tuning_positive p hH hR hε
  have hy : ‖currentPoint p st - root‖ ≤ 3 * p.R := by
    simp only [currentPoint, st, ite_eq_left True.intro]
    linarith
  have hg : st.mass * ‖currentValue p st‖ ≤ 4 * p.R := by
    simp only [currentValue, st, ite_eq_left True.intro, norm_zero, mul_zero]
    positivity
  have hcurrent : ‖currentValue p st‖ ≤ 3 * (p.H * p.R) * p.R := by
    simp only [currentValue, st, ite_eq_left True.intro, norm_zero]
    positivity
  have hh := exact_merit_lipschitz p st root G J hH hR hε le_rfl hroot hy hg hcurrent
    hGroot hlip hJn hJL hmono ha hb
  have hca := initial_centers p st rfl ht.1.le (ht.1.trans_le ha.1)
  have hcb := initial_centers p st rfl ht.1.le (ht.1.trans_le hb.1)
  dsimp only at hh ⊢
  simpa only [hca.1, hca.2, hcb.1, hcb.2] using hh

lemma trial_merit_error (p : Public.{u}) (st : OuterState p.E)
    (F G : p.E → p.E) (JF D : p.E → p.E →L[ℝ] p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (hH : 0 < p.H) (hG : ∀ x, HasFDerivAt G (D x) x)
    (hDL : ∀ x y, ‖D x - D y‖ ≤ p.H * ‖x - y‖)
    (hmono : ∀ x v, 0 ≤ ⟪D x v, v⟫)
    (hGgraph : ∀ x, G (x + shift p • F x) = F x)
    (hDgraph : ∀ x, D (x + shift p • F x) = graphJacobian (shift p) (JF x))
    {a : ℝ} (ha : 0 < a) (trial : Trial p.E)
    (htrial : trial = Program.eval (fun x => (F x, JF x)) (trialPlan p st initial a))
    (hsample : trial.sample.2 = (F trial.sample.1, JF trial.sample.1))
    (hcenter : ‖trial.sample.1 + shift p • F trial.sample.1 - midpoint p st a‖ ≤ centerTolerance p st a) :
    let m := midpoint p st a
    let v := affinePoint a (anchorMix p st a) m (G m) (D m)
    |merit p trial - a * p.H * ‖v - m‖| ≤
      (a * p.H * ‖v - m‖) / 4096 + 1 / 4096 + 1 / 4096 ^ 2 := by
  let m := midpoint p st a
  let n := trial.sample.1 + shift p • F trial.sample.1
  let v := affinePoint a (anchorMix p st a) m (G m) (D m)
  have hstep : trial.step = a := by
    rw [htrial]
    simp only [trialPlan, Program.eval_map]
  have hmodel := trialPlan_model p st initial a (fun x => (F x, JF x))
  rw [← htrial] at hmodel
  dsimp only at hmodel
  rw [hsample] at hmodel
  have hmodel' : trial.model = affinePoint a (anchorMix p st a) n (G n) (D n) := by
    dsimp only [n]
    rw [hGgraph, hDgraph]
    exact hmodel
  have hv := (affinePoint_spec (D m) ha.le (hmono m) (anchorMix p st a) m (G m)).1
  have hw := (affinePoint_spec (D n) ha.le (hmono n) (anchorMix p st a) n (G n)).1
  rw [← hmodel'] at hw
  have hsmall : a * p.H * ‖n - m‖ ≤ 1 / 4096 :=
    LongTails.Proofs.CohypomonotoneNewtonBudget.scaled_small_tolerance ha hH
      (hcenter.trans (min_le_right _ _))
  have hh := approximate_merit_error ha.le hH.le hG hDL m n v trial.model (anchorMix p st a)
    (hmono n) hv hw hsmall
  have he : merit p trial = a * p.H * ‖trial.model - n‖ := by
    unfold merit
    rw [hstep, hsample]
  rw [he]
  exact hh

lemma search_from_graph_bounds (p : Public.{u}) (st : OuterState p.E) (root : p.E)
    (F G : p.E → p.E) (JF D : p.E → p.E →L[ℝ] p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E)))
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hcase : baseStep p ≤ st.mass ∨ st.k = 0 ∧ st.mass = 0)
    (hroot : ‖p.x0 - root‖ ≤ p.R) (hy : ‖currentPoint p st - root‖ ≤ 3 * p.R)
    (hg : st.mass * ‖currentValue p st‖ ≤ 4 * p.R)
    (hcurrent : ‖currentValue p st‖ ≤ 3 * (p.H * p.R) * p.R)
    (hGroot : G root = 0) (hlip : ∀ x y, ‖G x - G y‖ ≤ (p.H * p.R) * ‖x - y‖)
    (hG : ∀ x, HasFDerivAt G (D x) x) (hDn : ∀ x, ‖D x‖ ≤ p.H * p.R)
    (hDL : ∀ x y, ‖D x - D y‖ ≤ p.H * ‖x - y‖)
    (hmono : ∀ x v, 0 ≤ ⟪D x v, v⟫)
    (hGgraph : ∀ x, G (x + shift p • F x) = F x)
    (hDgraph : ∀ x, D (x + shift p • F x) = graphJacobian (shift p) (JF x))
    (htrials : ∀ a, baseStep p ≤ a → a ≤ maxStep p →
      let trial := Program.eval (fun x => (F x, JF x)) (trialPlan p st initial a)
      trial.sample.2 = (F trial.sample.1, JF trial.sample.1) ∧
      ‖trial.sample.1 + shift p • F trial.sample.1 - midpoint p st a‖ ≤ centerTolerance p st a)
    {a : ℝ} (ha : baseStep p ≤ a ∧ a ≤ maxStep p) :
    ∃ trial, Program.eval (fun x => (F x, JF x))
      (searchPlan p st initial (searchFuel p) 0 0 a) = some trial := by
  let reply := fun x => (F x, JF x)
  let q := fun a => merit p (Program.eval reply (trialPlan p st initial a))
  let m := fun a => midpoint p st a
  let w := fun a => affinePoint a (anchorMix p st a) (m a) (G (m a)) (D (m a))
  let phi := fun a => a * p.H * ‖w a - m a‖
  let L := 160000000 * p.H * p.R * (1 + p.H * p.R ^ 2 / p.ε) ^ 3
  have ht := tuning_positive p hH hR hε
  have hA : 0 ≤ st.mass := by
    rcases hcase with h | ⟨_, h⟩
    · exact ht.1.le.trans h
    · rw [h]
  have herr : ∀ t, baseStep p ≤ t → t ≤ maxStep p →
      |q t - phi t| ≤ phi t / 4096 + 1 / 4096 + 1 / 4096 ^ 2 := by
    intro t htmin htmax
    have hs := htrials t htmin htmax
    exact trial_merit_error p st F G JF D initial hH hG hDL hmono hGgraph hDgraph
      (ht.1.trans_le htmin) _ rfl hs.1 hs.2
  have hpath : ∀ t u, baseStep p ≤ t → t ≤ maxStep p → baseStep p ≤ u → u ≤ maxStep p →
      |phi t - phi u| ≤ L * |t - u| := by
    intro t u htmin htmax humin humax
    rcases hcase with hmass | ⟨hk, _⟩
    · exact exact_merit_lipschitz p st root G D hH hR hε hmass hroot hy hg hcurrent
        hGroot hlip hDn hDL hmono ⟨htmin, htmax⟩ ⟨humin, humax⟩
    · have hh := initial_exact_merit_lipschitz p root G D hH hR hε hroot hGroot hlip hDn hDL
        hmono ⟨htmin, htmax⟩ ⟨humin, humax⟩
      have hct := initial_centers p st hk hA (ht.1.trans_le htmin)
      have hcu := initial_centers p st hk hA (ht.1.trans_le humin)
      dsimp only [phi, w, m, L]
      simpa only [hct.1, hct.2, hcu.1, hcu.2] using hh
  have hfloor : q (baseStep p) < 1 / 64 := by
    have hdisp := exact_model_displacement p st root G (D (m (baseStep p)))
      (mul_nonneg hH.le hR.le) hA ht.1 (hmono (m (baseStep p))) hroot hy hg hcurrent hGroot hlip
    have hh := exact_floor_merit p hH hR hdisp
    exact merit_safe_floor (herr _ le_rfl ht.2) hh
  apply public_search_success p st initial reply q (fun _ => rfl) hH hρ hR hε hfloor _ ha
  intro lo hi hlo hhi horder hlow hhigh
  have hlomax : lo ≤ maxStep p := horder.trans hhi
  have hhimin : baseStep p ≤ hi := hlo.trans horder
  have hp := hpath hi lo hhimin hhi hlo hlomax
  rw [abs_of_nonneg (sub_nonneg.mpr horder)] at hp
  have hw := merit_bracket_width hlow hhigh (herr lo hlo hlomax) (herr hi hhimin hhi) hp
  have hden : 0 < 16000000000 * p.H * p.R * (1 + p.H * p.R ^ 2 / p.ε) ^ 3 := by positivity
  apply (div_le_iff₀ hden).mpr
  dsimp only [L] at hw
  nlinarith only [hw]

end LongTails.Proofs.CohypomonotoneNewtonSearch
