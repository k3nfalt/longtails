import LongTails.Proofs.KnownValueNondualProgress
import LongTails.Proofs.KnownValueNondualExecution

open Set

namespace LongTails.Proofs.KnownValueNondualPotential

open LongTails.Setups.KnownValueNondualGeneralizedConvex
open LongTails.Algorithms.KnownValueNondual
open KnownValueNondualControl KnownValueNondualProgress KnownValueNondualExecution

noncomputable def squarePotential (p : Public) (f : Point p → ℝ) (xstar : Point p) (c : Control p) : ℝ :=
  if c.warm || c.finished then 0 else (f c.incumbent - f xstar) / c.target ^ 2

noncomputable def linearPotential (p : Public) (f : Point p → ℝ) (xstar : Point p) (c : Control p) : ℝ :=
  if c.warm || c.finished then 0 else (f c.incumbent - f xstar) / c.target

noncomputable def inverseTarget (p : Public) (c : Control p) : ℝ :=
  if c.warm then 0 else 1 / c.target

noncomputable def cutEnergy (p : Public) (c : Control p)
    (out : Point p × LongTails.Algorithms.NondualLineSearch.Reply (Point p) × Bool) : ℝ :=
  if c.warm || out.2.2 then 0 else
    let D := 5 * ‖out.2.1.2‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖out.2.1.2‖))
    if out.2.1.1 - D - p.fstar ≤ c.target then 0 else D

lemma squarePotential_nonneg (p : Public) {f : Point p → ℝ} (xstar : Point p)
    (hmin : IsMinOn f univ xstar) (c : Control p) : 0 ≤ squarePotential p f xstar c := by
  unfold squarePotential
  split_ifs
  · rfl
  · exact div_nonneg (sub_nonneg.mpr (hmin (mem_univ _))) (sq_nonneg _)

lemma linearPotential_nonneg (p : Public) {f : Point p → ℝ} (xstar : Point p)
    (hmin : IsMinOn f univ xstar) (c : Control p) (hΓ : 0 ≤ c.target) :
    0 ≤ linearPotential p f xstar c := by
  unfold linearPotential
  split_ifs
  · rfl
  · exact div_nonneg (sub_nonneg.mpr (hmin (mem_univ _))) hΓ

lemma cutEnergy_nonneg (p : Public) (hL0 : 0 < p.L0) (hL1 : 0 < p.L1)
    (c : Control p) (out : Point p × LongTails.Algorithms.NondualLineSearch.Reply (Point p) × Bool) :
    0 ≤ cutEnergy p c out := by
  unfold cutEnergy
  split_ifs <;> positivity

lemma finishLine_square_energy (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (c : Control p) (hc : Invariant p f xstar c) (hactive : c.finished = false)
    (out : Point p × LongTails.Algorithms.NondualLineSearch.Reply (Point p) × Bool)
    (hout : NondualLineSearch.Guarantee f g p.L0 p.L1 (4 * p.R) (p.ε / 2)
      (selector p c.body) c.incumbent out) :
    cutEnergy p c out / c.target ^ 2 ≤ squarePotential p f xstar c -
      squarePotential p f xstar (finishLine p c out) +
      3 * (inverseTarget p (finishLine p c out) - inverseTarget p c) := by
  rcases out with ⟨x, ⟨value, grad⟩, small⟩
  rcases hout with ⟨hrep, _, hsearch⟩
  dsimp only at hrep hsearch
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrep
  have hΓ : 0 < c.target := hε.trans_le hc.target_floor
  have hP := squarePotential_nonneg p xstar hmin c
  cases small with
  | true =>
    simpa [cutEnergy, finishLine, squarePotential, inverseTarget] using hP
  | false =>
    have hdes := SymmetricGeneralizedDescent.normalized_descent hgrad hg hL0 hL1 hgs x
    have hD : 0 ≤ 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) := by positivity
    have hmono : f (x - (1 / (4 * (p.L0 + p.L1 * ‖g x‖))) • g x) ≤ f c.incumbent := by
      linarith [hsearch.1]
    dsimp only [finishLine, cutEnergy]
    simp only [Bool.or_false, Bool.false_eq_true, ite_false]
    by_cases hdone : f x - 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) - p.fstar ≤ p.ε
    · have hp : f x - 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) - p.fstar ≤ c.target :=
        hdone.trans hc.target_floor
      simpa [hdone, hp, squarePotential, inverseTarget] using hP
    · simp only [hdone, ite_false]
      by_cases hphase : f x - 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) - p.fstar ≤ c.target
      · simp only [hphase, ite_true]
        have hb : 0 < max p.ε (c.target / 2) := hε.trans_le (le_max_left _ _)
        have hba : max p.ε (c.target / 2) ≤ c.target := max_le hc.target_floor (by linarith)
        have hab : c.target ≤ 2 * max p.ε (c.target / 2) := by linarith [le_max_right p.ε (c.target / 2)]
        have hgap : f (x - (1 / (4 * (p.L0 + p.L1 * ‖g x‖))) • g x) - f xstar ≤ c.target := by
          rw [hval]
          linarith
        cases hw : c.warm with
        | true =>
          simp [squarePotential, inverseTarget, hw, hactive]
          have hh := div_le_div_of_nonneg_right hgap (sq_nonneg (max p.ε (c.target / 2)))
          have hh' : c.target / (max p.ε (c.target / 2)) ^ 2 ≤ 3 / max p.ε (c.target / 2) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos hb) hb).mpr
            nlinarith
          have h := hh.trans hh'
          simpa [div_eq_mul_inv, mul_comm] using h
        | false =>
          simp only [squarePotential, inverseTarget, hw, hactive,
            Bool.false_eq_true, ite_false, zero_div, Bool.or_false]
          have hj := squared_target_potential_jump hΓ hb hba hab hgap
          have hm := div_le_div_of_nonneg_right (sub_le_sub_right hmono (f xstar)) (sq_nonneg c.target)
          linarith
      · simp only [hphase, ite_false]
        cases hw : c.warm with
        | true => simp [squarePotential, inverseTarget, hw, hactive]
        | false =>
          simp only [squarePotential, inverseTarget, hw, hactive,
            Bool.false_eq_true, ite_false, Bool.or_false, sub_self, mul_zero, add_zero]
          have he : 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) ≤
              (f c.incumbent - f xstar) -
                (f (x - (1 / (4 * (p.L0 + p.L1 * ‖g x‖))) • g x) - f xstar) := by
            linarith [hsearch.1]
          simpa [sub_div] using div_le_div_of_nonneg_right he (sq_nonneg c.target)

lemma finishLine_linear_energy (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (c : Control p) (hc : Invariant p f xstar c) (hactive : c.finished = false)
    (out : Point p × LongTails.Algorithms.NondualLineSearch.Reply (Point p) × Bool)
    (hout : NondualLineSearch.Guarantee f g p.L0 p.L1 (4 * p.R) (p.ε / 2)
      (selector p c.body) c.incumbent out) :
    cutEnergy p c out / c.target ≤ linearPotential p f xstar c -
      linearPotential p f xstar (finishLine p c out) +
      2 * (((finishLine p c out).phase : ℝ) - (c.phase : ℝ)) := by
  rcases out with ⟨x, ⟨value, grad⟩, small⟩
  rcases hout with ⟨hrep, _, hsearch⟩
  dsimp only at hrep hsearch
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrep
  have hΓ : 0 < c.target := hε.trans_le hc.target_floor
  have hP := linearPotential_nonneg p xstar hmin c hΓ.le
  cases small with
  | true =>
    simpa [cutEnergy, finishLine, linearPotential, inverseTarget] using hP
  | false =>
    have hdes := SymmetricGeneralizedDescent.normalized_descent hgrad hg hL0 hL1 hgs x
    have hD : 0 ≤ 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) := by positivity
    have hmono : f (x - (1 / (4 * (p.L0 + p.L1 * ‖g x‖))) • g x) ≤ f c.incumbent := by
      linarith [hsearch.1]
    dsimp only [finishLine, cutEnergy]
    simp only [Bool.or_false, Bool.false_eq_true, ite_false]
    by_cases hdone : f x - 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) - p.fstar ≤ p.ε
    · have hp : f x - 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) - p.fstar ≤ c.target :=
        hdone.trans hc.target_floor
      simpa [hdone, hp, linearPotential, inverseTarget] using hP
    · simp only [hdone, ite_false]
      by_cases hphase : f x - 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) - p.fstar ≤ c.target
      · simp only [hphase, ite_true]
        have hb : 0 < max p.ε (c.target / 2) := hε.trans_le (le_max_left _ _)
        have hba : max p.ε (c.target / 2) ≤ c.target := max_le hc.target_floor (by linarith)
        have hab : c.target ≤ 2 * max p.ε (c.target / 2) := by linarith [le_max_right p.ε (c.target / 2)]
        have hgap : f (x - (1 / (4 * (p.L0 + p.L1 * ‖g x‖))) • g x) - f xstar ≤ c.target := by
          rw [hval]
          linarith
        cases hw : c.warm with
        | true =>
          simp [linearPotential, hw, hactive, Nat.cast_add, Nat.cast_one]
          have hh : (f (x - (1 / (4 * (p.L0 + p.L1 * ‖g x‖))) • g x) - f xstar) /
              max p.ε (c.target / 2) ≤ 2 := (div_le_iff₀ hb).mpr (hgap.trans hab)
          simpa [div_eq_mul_inv, mul_comm] using hh
        | false =>
          simp only [linearPotential, hw, hactive, Nat.cast_add, Nat.cast_one,
            Bool.false_eq_true, ite_false, zero_div, Bool.or_false]
          have hj := target_potential_jump hΓ hb hba hab hgap
          have hm := div_le_div_of_nonneg_right (sub_le_sub_right hmono (f xstar)) hΓ.le
          linarith
      · simp only [hphase, ite_false]
        cases hw : c.warm with
        | true => simp [linearPotential, hw, hactive]
        | false =>
          simp only [linearPotential, hw, hactive,
            Bool.false_eq_true, ite_false, Bool.or_false, sub_self, mul_zero, add_zero]
          have he : 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) ≤
              (f c.incumbent - f xstar) -
                (f (x - (1 / (4 * (p.L0 + p.L1 * ‖g x‖))) • g x) - f xstar) := by
            linarith [hsearch.1]
          simpa [sub_div] using div_le_div_of_nonneg_right he hΓ.le

lemma inverseTarget_bounds (p : Public) (hε : 0 < p.ε) {f : Point p → ℝ} (xstar : Point p)
    (c : Control p) (hc : Invariant p f xstar c) : 0 ≤ inverseTarget p c ∧ inverseTarget p c ≤ 1 / p.ε := by
  have hΓ := hε.trans_le hc.target_floor
  unfold inverseTarget
  split_ifs
  · exact ⟨le_refl _, by positivity⟩
  · exact ⟨by positivity, one_div_le_one_div_of_le hε hc.target_floor⟩

lemma squarePotential_bound (p : Public) (hε : 0 < p.ε) {f : Point p → ℝ} (xstar : Point p)
    (c : Control p) (hc : Invariant p f xstar c) :
    squarePotential p f xstar c ≤ 2 * inverseTarget p c := by
  have hΓ := hε.trans_le hc.target_floor
  cases hw : c.warm with
  | true => simp [squarePotential, inverseTarget, hw]
  | false =>
    cases hf : c.finished with
    | true => simp [squarePotential, inverseTarget, hw, hf, hΓ.le]
    | false =>
      simp only [squarePotential, inverseTarget, hw, hf, Bool.or_false, Bool.false_eq_true, ite_false]
      have h := div_le_div_of_nonneg_right (hc.low_gap hw) (sq_nonneg c.target)
      have he : (2 * c.target) / c.target ^ 2 = 2 * (1 / c.target) := by field_simp
      rwa [he] at h

lemma linearPotential_bound (p : Public) (hε : 0 < p.ε) {f : Point p → ℝ} (xstar : Point p)
    (c : Control p) (hc : Invariant p f xstar c) : linearPotential p f xstar c ≤ 2 := by
  have hΓ := hε.trans_le hc.target_floor
  cases hw : c.warm with
  | true => simp [linearPotential, hw]
  | false =>
    cases hf : c.finished with
    | true => simp [linearPotential, hw, hf]
    | false =>
      simp only [linearPotential, hw, hf, Bool.or_false, Bool.false_eq_true, ite_false]
      exact (div_le_iff₀ hΓ).mpr (hc.low_gap hw)

noncomputable def charge (p : Public) (f : Point p → ℝ) (g : Point p → Point p) (c : Control p) : ℝ :=
  if c.finished then 0 else cutEnergy p c (lineOutput p f g c)

lemma advance_square_energy (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ‖p.x0 - xstar‖ ≤ p.R) (c : Control p) (hc : Invariant p f xstar c) :
    charge p f g c / c.target ^ 2 ≤ squarePotential p f xstar c -
      squarePotential p f xstar (advance p f g c) +
      3 * (inverseTarget p (advance p f g c) - inverseTarget p c) := by
  cases hf : c.finished with
  | true => simp [charge, advance, hf]
  | false =>
    simp only [charge, advance, hf, Bool.false_eq_true, ite_false]
    exact finishLine_square_energy p hgrad hg hL0 hL1 hε hgs xstar hmin hval c hc hf _
      (lineOutput_guarantee p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hprior c hc)

lemma advance_linear_energy (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ‖p.x0 - xstar‖ ≤ p.R) (c : Control p) (hc : Invariant p f xstar c) :
    charge p f g c / c.target ≤ linearPotential p f xstar c -
      linearPotential p f xstar (advance p f g c) +
      2 * (((advance p f g c).phase : ℝ) - (c.phase : ℝ)) := by
  cases hf : c.finished with
  | true => simp [charge, advance, hf]
  | false =>
    simp only [charge, advance, hf, Bool.false_eq_true, ite_false]
    exact finishLine_linear_energy p hgrad hg hL0 hL1 hε hgs xstar hmin hval c hc hf _
      (lineOutput_guarantee p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hprior c hc)

lemma telescope_energy (a P J : ℕ → ℝ) (C : ℝ) (hstep : ∀ k, a k ≤ P k - P (k + 1) + C * (J (k + 1) - J k))
    (n : ℕ) : (∑ k ∈ Finset.range n, a k) ≤ P 0 - P n + C * (J n - J 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [hstep n]

lemma square_energy_sum (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) (n : ℕ) :
    (∑ k ∈ Finset.range n, charge p f g ((advance p f g)^[k] (initialControl p)) /
      ((advance p f g)^[k] (initialControl p)).target ^ 2) ≤ 3 / p.ε := by
  let c := fun k => (advance p f g)^[k] (initialControl p)
  have hi : ∀ k, Invariant p f xstar (c k) :=
    iterate_invariant p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval hprior
  have hs : ∀ k, charge p f g (c k) / (c k).target ^ 2 ≤
      squarePotential p f xstar (c k) - squarePotential p f xstar (c (k + 1)) +
        3 * (inverseTarget p (c (k + 1)) - inverseTarget p (c k)) := by
    intro k
    simpa only [c, Function.iterate_succ_apply'] using
      advance_square_energy p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval
        (KnownValueNondualGeometry.initialBody_norm p hprior) (c k) (hi k)
  have ht := telescope_energy (fun k => charge p f g (c k) / (c k).target ^ 2)
    (fun k => squarePotential p f xstar (c k)) (fun k => inverseTarget p (c k)) 3 hs n
  have hP0 := squarePotential_bound p hε xstar (c 0) (hi 0)
  have hPn := squarePotential_nonneg p xstar hmin (c n)
  have hJ0 := (inverseTarget_bounds p hε xstar (c 0) (hi 0)).1
  have hJn := (inverseTarget_bounds p hε xstar (c n) (hi n)).2
  change (∑ k ∈ Finset.range n, charge p f g (c k) / (c k).target ^ 2) ≤ _
  calc
    _ ≤ 3 * (1 / p.ε) := by linarith
    _ = 3 / p.ε := by ring

lemma linear_energy_sum (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) (n : ℕ) :
    (∑ k ∈ Finset.range n, charge p f g ((advance p f g)^[k] (initialControl p)) /
      ((advance p f g)^[k] (initialControl p)).target) ≤
      2 + 2 * (((advance p f g)^[n] (initialControl p)).phase : ℝ) := by
  let c := fun k => (advance p f g)^[k] (initialControl p)
  have hi : ∀ k, Invariant p f xstar (c k) :=
    iterate_invariant p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval hprior
  have hs : ∀ k, charge p f g (c k) / (c k).target ≤
      linearPotential p f xstar (c k) - linearPotential p f xstar (c (k + 1)) +
        2 * (((c (k + 1)).phase : ℝ) - ((c k).phase : ℝ)) := by
    intro k
    simpa only [c, Function.iterate_succ_apply'] using
      advance_linear_energy p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval
        (KnownValueNondualGeometry.initialBody_norm p hprior) (c k) (hi k)
  have ht := telescope_energy (fun k => charge p f g (c k) / (c k).target)
    (fun k => linearPotential p f xstar (c k)) (fun k => ((c k).phase : ℝ)) 2 hs n
  have hP0 := linearPotential_bound p hε xstar (c 0) (hi 0)
  have hPn := linearPotential_nonneg p xstar hmin (c n) (hε.le.trans (hi n).target_floor)
  have hJ0 : ((c 0).phase : ℝ) = 0 := by simp [c, initialControl]
  change (∑ k ∈ Finset.range n, charge p f g (c k) / (c k).target) ≤ 2 + 2 * ((c n).phase : ℝ)
  linarith

end LongTails.Proofs.KnownValueNondualPotential
