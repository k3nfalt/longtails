import LongTails.Proofs.CohypomonotoneNewtonWork

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CohypomonotoneNewtonCost

open LongTails.Setups.CohypomonotoneNewton
open LongTails.Algorithms.CohypomonotoneNewton
open LongTails.Proofs.CohypomonotoneNewtonSearch
open LongTails.Proofs.CohypomonotoneNewtonOuter
open LongTails.Proofs.CohypomonotoneNewtonRun
open LongTails.Proofs.CohypomonotoneNewtonWork
open OracleTemplate.ComponentEnvelope (Program)

universe u

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

lemma prefix_charges (n : ℕ)
    (hactive : ∀ i < n, ¬((trajectory p F J initial i).k ≠ 0 ∧
      ‖(trajectory p F J initial i).value‖ ≤ p.ε)) :
    let states := trajectory p F J initial
    let alpha := fun k => (chosenTrial p F J initial (states k)).step /
      ((states k).mass + (chosenTrial p F J initial (states k)).step)
    (∑ k ∈ Finset.range n, alpha k) ≤ 14 * logFactor p ∧
      (∑ k ∈ Finset.range n, previousCharge (states k)) ≤ ∑ k ∈ Finset.range n, alpha k := by
  let states := trajectory p F J initial
  let A := fun k => (states k).mass
  let a := fun k => (chosenTrial p F J initial (states k)).step
  let alpha := fun k => a k / A (k + 1)
  have hs : ∀ k, StateInvariant p F root (states k) :=
    trajectory_invariant p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit
  have ht : ∀ k, TrialFacts p F G J D (states k) (chosenTrial p F J initial (states k)) :=
    fun k => chosenTrial_facts p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit _ (hs k)
  have hbase := (tuning_positive p hH hR hε).1
  have hmax := (tuning_positive p hH hR hε).2
  have ha : ∀ k, 0 < a k := fun k => hbase.trans_le (ht k).step_bounds.1
  have hA : ∀ k, 0 ≤ A k := fun k => (hs k).mass_nonneg
  have hrec : ∀ k, A (k + 1) = A k + a k := fun _ => rfl
  have hapos : ∀ k, 0 ≤ alpha k := by
    intro k
    dsimp only [alpha]
    rw [hrec]
    exact div_nonneg (ha k).le (add_nonneg (hA k) (ha k).le)
  have hlarge : ∀ k, 0 < k → baseStep p ≤ A k := by
    intro k hk
    rcases (hs k).mass_case with hh | ⟨hz, _⟩
    · exact hh
    · have hi : (states k).k = k := trajectory_index p F J initial k
      omega
  have hlast : A n ≤ 2 * maxStep p := by
    cases n with
    | zero =>
        change 0 ≤ 2 * maxStep p
        exact mul_nonneg (by norm_num) (hbase.le.trans hmax)
    | succ k =>
        have hm := active_mass_bound p F G J D root hH hR hε hroot hg (states k) (hs k)
          (hactive k (Nat.lt_succ_self k))
        rw [hrec]
        linarith [hm.2, (ht k).step_bounds.2]
  have hsum := LongTails.Proofs.CohypomonotoneNewtonEnergy.fraction_sum_from_zero A a hbase
    (show baseStep p ≤ 2 * maxStep p by linarith) rfl
    (fun k hk _ => hlarge k hk) (fun k _ => ha k) (fun k _ => hrec k) hlast
  have hlog := log_mass_ratio p hH hρ hR hε
  change (∑ k ∈ Finset.range n, alpha k) ≤ 14 * logFactor p ∧
    (∑ k ∈ Finset.range n, previousCharge (states k)) ≤ ∑ k ∈ Finset.range n, alpha k
  refine ⟨hsum.trans hlog, ?_⟩
  have hp0 : previousCharge (states 0) = 0 := by simp [states, trajectory, previousCharge]
  have hp : ∀ k, previousCharge (states (k + 1)) = alpha k := by
    intro k
    simp only [states, trajectory, advance, previousCharge, Nat.add_one_ne_zero, ite_false]
    rfl
  cases n with
  | zero => simp
  | succ n =>
      rw [Finset.sum_range_succ', hp0, add_zero, Finset.sum_range_succ]
      have he : (∑ k ∈ Finset.range n, previousCharge (states (k + 1))) =
          ∑ k ∈ Finset.range n, alpha k := Finset.sum_congr rfl (fun k _ => hp k)
      rw [he]
      exact le_add_of_nonneg_right (hapos n)

lemma outer_work :
    (Program.cost (fun x => (F x, J x))
      (outerPlan p initial (horizon p) (trajectory p F J initial 0)) : ℝ) ≤
      (3000000 * (accuracyScale p) ^ (2 / 5 : ℝ) + 14000000 * coupling p * logFactor p) *
        (logFactor p) ^ 2 := by
  obtain ⟨n, hn, hactive, hcost⟩ := outer_cost_prefix p F G J D root hH hρ hR hε hF hJ hco hroot hg
    initial hinit (horizon p) 0
  simp only [Nat.zero_add] at hactive hcost
  let states := trajectory p F J initial
  let alpha := fun k => (chosenTrial p F J initial (states k)).step /
    ((states k).mass + (chosenTrial p F J initial (states k)).step)
  let beta := fun k => previousCharge (states k)
  let U := ∑ k ∈ Finset.range n, alpha k
  let V := ∑ k ∈ Finset.range n, beta k
  have hs : ∀ k, StateInvariant p F root (states k) :=
    trajectory_invariant p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit
  have ht : ∀ k, TrialFacts p F G J D (states k) (chosenTrial p F J initial (states k)) :=
    fun k => chosenTrial_facts p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit _ (hs k)
  have hbase := (tuning_positive p hH hR hε).1
  have halpha : ∀ k, 0 ≤ alpha k := by
    intro k
    have ha := hbase.trans_le (ht k).step_bounds.1
    dsimp only [alpha]
    exact div_nonneg ha.le (add_nonneg (hs k).mass_nonneg ha.le)
  have hbeta : ∀ k, 0 ≤ beta k := by
    intro k
    dsimp only [beta, previousCharge]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hbase.le.trans (hs k).previous_bounds.1) (hs k).mass_nonneg
  have hcharges := prefix_charges p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit n hactive
  have hU : U ≤ 14 * logFactor p := hcharges.1
  have hV : V ≤ 14 * logFactor p := hcharges.2.trans hU
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun k _ => halpha k)
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun k _ => hbeta k)
  have hper : ∀ k ∈ Finset.range n, (stepWork p F J initial (states k) : ℝ) ≤
      200 * logFactor p * ((searchFuel p : ℝ) + 1 +
        8 * coupling p * searchFuel p * (beta k + 2 * alpha k) + 4 * coupling p * alpha k) := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    have hm := active_mass_bound p F G J D root hH hR hε hroot hg (states k) (hs k) (hactive k hkn)
    have hidx : (states k).k ≤ horizon p := by
      rw [show (states k).k = k from trajectory_index p F J initial k]
      omega
    exact step_work_bound p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hinit (states k) (hs k) hm.2 hidx
  have hsum := Finset.sum_le_sum hper
  have hid : (∑ k ∈ Finset.range n,
      200 * logFactor p * ((searchFuel p : ℝ) + 1 +
        8 * coupling p * searchFuel p * (beta k + 2 * alpha k) + 4 * coupling p * alpha k)) =
      200 * logFactor p * ((n : ℝ) * ((searchFuel p : ℝ) + 1) +
        8 * coupling p * searchFuel p * (V + 2 * U) + 4 * coupling p * U) := by
    dsimp only [U, V]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]
  rw [hid] at hsum
  have hsc := scale_bounds p hH hρ hR hε
  have hN := LongTails.Proofs.CohypomonotoneNewtonBudget.horizon_upper p hH hR hε
  have hncast : (n : ℝ) ≤ horizon p := by exact_mod_cast hn
  have hnr : (n : ℝ) ≤ 65 * (accuracyScale p) ^ (2 / 5 : ℝ) := hncast.trans hN
  have hb := LongTails.Proofs.CohypomonotoneNewtonBudget.outer_work_scalar
    (q := coupling p) (r := (accuracyScale p) ^ (2 / 5 : ℝ))
    (Nat.cast_nonneg (searchFuel p)) hsc.2.2 (by linarith [hsc.1])
    (Real.rpow_nonneg (by linarith [hsc.2.1]) _) hU0 hV0 hnr
    (searchFuel_upper p hH hρ hR hε) hU hV
  rw [hcost, Nat.cast_sum]
  exact hsum.trans hb

end Execution

lemma initial_work (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E) (root : p.E)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hzero : F root = 0) (hroot : ‖p.x0 - root‖ ≤ p.R) :
    let d := trustRegion (ContinuousLinearMap.id ℝ p.E + shift p • J p.x0) (shift p • F p.x0) p.R
    (Program.cost (fun x => (F x, J x))
      (inversePlan (shift p * p.H) (shift p)
        (min (p.R / 64) (1 / (4096 * p.H * maxStep p))) p.x0 (p.x0 + d)) : ℝ) ≤
          200 * logFactor p * (1 + 3 * (coupling p) ^ 2) := by
  let T := fun x => x + shift p • F x
  let D := fun x => ContinuousLinearMap.id ℝ p.E + shift p • J x
  let d := trustRegion (D p.x0) (shift p • F p.x0) p.R
  have hγ := (shift_bounds p hH hρ hR).1
  have hT : ∀ x, HasFDerivAt T (D x) x :=
    fun x => (hasFDerivAt_id x).add ((hF x).const_smul (shift p))
  have hD : ∀ x y, ‖D x - D y‖ ≤ (shift p * p.H) * ‖x - y‖ := by
    intro x y
    have he : D x - D y = shift p • (J x - J y) := by dsimp [D]; module
    rw [he, norm_smul, Real.norm_of_nonneg hγ.le]
    have hh := mul_le_mul_of_nonneg_left (hJ x y) hγ.le
    nlinarith only [hh]
  have ht := LongTails.Proofs.CohypomonotoneNewtonInverse.trustRegion_spec (D p.x0) (shift p • F p.x0) hR.le
  have hroot' : ‖root - p.x0‖ ≤ p.R := by rwa [norm_sub_rev]
  have hfixed : T root = root := by simp only [T, hzero, smul_zero, add_zero]
  have hb := LongTails.Proofs.CohypomonotoneNewtonGeometry.initial_trust_region_residual
    hT (mul_nonneg hγ.le hH.le) hD p.x0 root d hfixed hroot' ht.1 (by
      intro v hv
      simpa only [T, add_sub_cancel_left] using ht.2 v hv)
  have hs := scale_bounds p hH hρ hR hε
  have hb' : ‖T (p.x0 + d) - p.x0‖ ≤ 3 * coupling p * p.R := by
    have hh := mul_le_mul_of_nonneg_right hs.1 hR.le
    unfold coupling at hh ⊢
    nlinarith only [hb, hh]
  have hupper : 3 * coupling p * p.R ≤ 8 * coupling p * p.R := by
    have hq : 0 ≤ coupling p := by linarith [hs.1]
    nlinarith [mul_nonneg hq hR.le]
  have hi := inverse_work p F J hH hρ hR hε p.x0 (p.x0 + d) hb' hupper
    (initial_tolerance_floor p hH hR hε)
  convert hi using 1
  unfold coupling
  ring

lemma plan_work (p : Public.{u}) (F : p.E → p.E)
    (J : p.E → p.E →L[ℝ] p.E) (root : p.E)
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hF : ∀ x, HasFDerivAt F (J x) x)
    (hJ : ∀ x y, ‖J x - J y‖ ≤ p.H * ‖x - y‖)
    (hco : ∀ x y, -p.ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hzero : F root = 0) (hroot : ‖p.x0 - root‖ ≤ p.R) :
    (Program.cost (fun x => (F x, J x)) (plan p) : ℝ) ≤
      1 + 200 * logFactor p * (1 + 3 * (coupling p) ^ 2) +
        (3000000 * (accuracyScale p) ^ (2 / 5 : ℝ) + 14000000 * coupling p * logFactor p) *
          (logFactor p) ^ 2 := by
  obtain ⟨G, D, hg⟩ := exists_graphFacts p F J root hH hρ hR hF hJ hco hzero
  let d := trustRegion (ContinuousLinearMap.id ℝ p.E + shift p • J p.x0) (shift p • F p.x0) p.R
  let tol := min (p.R / 64) (1 / (4096 * p.H * maxStep p))
  let initial := Program.eval (fun x => (F x, J x))
    (inversePlan (shift p * p.H) (shift p) tol p.x0 (p.x0 + d))
  have hmax : 0 < maxStep p := (tuning_positive p hH hR hε).1.trans_le (tuning_positive p hH hR hε).2
  have htol : 0 < tol := by dsimp [tol]; positivity
  have hi := inverse_public_correct p hH hρ hR hF hJ hco htol p.x0 (p.x0 + d)
  have ho := outer_work p F G J D root hH hρ hR hε hF hJ hco hroot hg initial hi
  have hin := initial_work p F J root hH hρ hR hε hF hJ hzero hroot
  simp only [plan, Program.cost, Program.cost_bind, Nat.cast_add, Nat.cast_one]
  dsimp only at hin ho
  change (Program.cost (fun x => (F x, J x))
      (inversePlan (shift p * p.H) (shift p) tol p.x0 (p.x0 + d)) : ℝ) +
    Program.cost (fun x => (F x, J x))
      (outerPlan p initial (horizon p) (trajectory p F J initial 0)) + 1 ≤ _
  linarith only [hin, ho]

lemma public_work_bound (p : Public.{u})
    (hH : 0 < p.H) (hρ : 0 ≤ p.ρ) (hR : 0 < p.R) (hε : 0 < p.ε) :
    1 + 200 * logFactor p * (1 + 3 * (coupling p) ^ 2) +
        (3000000 * (accuracyScale p) ^ (2 / 5 : ℝ) + 14000000 * coupling p * logFactor p) *
          (logFactor p) ^ 2 ≤
      100000000000000 * ((1 + p.ρ * p.H * p.R) ^ 2 + (1 + p.H * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ)) *
        (1 + Real.log (2 + p.ρ * p.H * p.R + p.H * p.R ^ 2 / p.ε)) ^ 2 := by
  let P := p.ρ * p.H * p.R
  let Q := p.H * p.R ^ 2 / p.ε
  let L := 1 + Real.log (2 + P + Q)
  let r := (accuracyScale p) ^ (2 / 5 : ℝ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hs := scale_bounds p hH hρ hR hε
  have hr : 0 ≤ r := Real.rpow_nonneg (by linarith [hs.2.1]) _
  have hq : coupling p = 1 + 2 * P := by unfold coupling shift P; field_simp; ring
  have hqid : 1 + coupling p + accuracyScale p =
      2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε := by unfold coupling accuracyScale; ring
  have habs := LongTails.Proofs.CohypomonotoneNewtonBudget.amortization_absorption hs.1 hs.2.1
  rw [hqid] at habs
  have hnorm := LongTails.Proofs.CohypomonotoneNewtonBudget.normalized_work_scalar hs.1 hr hs.2.2 habs
  have hL : 1 ≤ L := by
    have hh := Real.log_nonneg (show 1 ≤ 2 + P + Q by linarith)
    dsimp [L]
    linarith
  have hell : logFactor p ≤ 2 * L := by
    have hinner : 2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε = 3 + 2 * P + Q := by
      change 2 + coupling p + Q = _
      rw [hq]
      ring
    have hh := Real.log_le_log (by positivity : 0 < 3 + 2 * P + Q)
      (show 3 + 2 * P + Q ≤ 2 * (2 + P + Q) by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 + P + Q ≠ 0)] at hh
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    unfold logFactor
    rw [hinner]
    dsimp [L] at hL ⊢
    norm_num at hlog2
    linarith
  have hq2 : (coupling p) ^ 2 ≤ 4 * (1 + P) ^ 2 := by rw [hq]; nlinarith
  have he2 := pow_le_pow_left₀ (by linarith [hs.2.2] : 0 ≤ logFactor p) hell 2
  have hsum : (coupling p) ^ 2 + r ≤ 4 * ((1 + P) ^ 2 + r) := by linarith
  have hmul := mul_le_mul hsum he2 (sq_nonneg (logFactor p)) (by positivity : 0 ≤ 4 * ((1 + P) ^ 2 + r))
  have hmul' := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 200000000)
  apply hnorm.trans
  change 200000000 * ((coupling p) ^ 2 + r) * (logFactor p) ^ 2 ≤
    100000000000000 * ((1 + P) ^ 2 + r) * L ^ 2
  have hn : 0 ≤ ((1 + P) ^ 2 + r) * L ^ 2 := by positivity
  nlinarith only [hmul', hn]

end LongTails.Proofs.CohypomonotoneNewtonCost
