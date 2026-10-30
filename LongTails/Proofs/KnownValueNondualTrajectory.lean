import LongTails.Proofs.KnownValueNondualPotential

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.KnownValueNondualTrajectory

open LongTails.Setups.KnownValueNondualGeneralizedConvex
open LongTails.Algorithms.KnownValueNondual
open KnownValueNondualExecution KnownValueNondualControl KnownValueNondualPotential

lemma advance_finished (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) (hf : c.finished = true) : advance p f g c = c := by simp [advance, hf]

lemma advance_body_subset (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) : (advance p f g c).body ⊆ c.body := by
  unfold advance
  split_ifs
  · exact Subset.refl _
  · dsimp only [finishLine]
    split_ifs <;> first | exact Subset.refl _ | exact inter_subset_left

lemma advance_phase_target (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) :
    ((advance p f g c).phase = c.phase ∧ (advance p f g c).target = c.target) ∨
      ((advance p f g c).phase = c.phase + 1 ∧
        (advance p f g c).target = max p.ε (c.target / 2) ∧ p.ε < c.target) := by
  unfold advance
  split_ifs
  · exact Or.inl ⟨rfl, rfl⟩
  · dsimp only [finishLine]
    split_ifs with hsmall hdone hphase
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, (lt_of_not_ge hdone).trans_le hphase⟩
    · exact Or.inl ⟨rfl, rfl⟩

lemma advance_phase_mono (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) : c.phase ≤ (advance p f g c).phase := by
  rcases advance_phase_target p f g c with h | h <;> omega

lemma finishLine_failure (p : Public) (c : Control p)
    (out : Point p × LongTails.Algorithms.NondualLineSearch.Reply (Point p) × Bool)
    (hf : (finishLine p c out).finished = false) (hp : (finishLine p c out).phase = c.phase) :
    out.2.2 = false ∧
      c.target < out.2.1.1 - 5 * ‖out.2.1.2‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖out.2.1.2‖)) - p.fstar ∧
      (finishLine p c out).body = rootCut p c out.1 out.2.1.1 out.2.1.2 := by
  by_cases hsmall : out.2.2 = true
  · simp [finishLine, hsmall] at hf
  · by_cases hdone : out.2.1.1 - 5 * ‖out.2.1.2‖ ^ 2 /
        (24 * (p.L0 + p.L1 * ‖out.2.1.2‖)) - p.fstar ≤ p.ε
    · simp [finishLine, hsmall, hdone] at hf
    · by_cases hphase : out.2.1.1 - 5 * ‖out.2.1.2‖ ^ 2 /
          (24 * (p.L0 + p.L1 * ‖out.2.1.2‖)) - p.fstar ≤ c.target
      · simp [finishLine, hsmall, hdone, hphase] at hp
      · exact ⟨Bool.eq_false_iff.mpr hsmall, lt_of_not_ge hphase,
          by simp [finishLine, hsmall, hdone, hphase]⟩

lemma advance_failure (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) (hc : c.finished = false)
    (hf : (advance p f g c).finished = false) (hp : (advance p f g c).phase = c.phase) :
    (lineOutput p f g c).2.2 = false ∧
      c.target < (lineOutput p f g c).2.1.1 -
        5 * ‖(lineOutput p f g c).2.1.2‖ ^ 2 /
          (24 * (p.L0 + p.L1 * ‖(lineOutput p f g c).2.1.2‖)) - p.fstar ∧
      (advance p f g c).body = rootCut p c (lineOutput p f g c).1
        (lineOutput p f g c).2.1.1 (lineOutput p f g c).2.1.2 := by
  simp only [advance, hc, Bool.false_eq_true, ite_false] at hf hp ⊢
  exact finishLine_failure p c _ hf hp

lemma max_half (ε a : ℝ) (hε : 0 ≤ ε) : max ε (max ε a / 2) = max ε (a / 2) := by
  rcases le_total ε a with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, max_eq_left (by linarith : ε / 2 ≤ ε), max_eq_left (by linarith : a / 2 ≤ ε)]

lemma target_formula (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (hε : 0 ≤ p.ε) (n : ℕ) :
    ((advance p f g)^[n] (initialControl p)).target =
      max p.ε ((initialControl p).target / (2 : ℝ) ^ ((advance p f g)^[n] (initialControl p)).phase) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero_apply, initialControl, pow_zero, div_one]
    split_ifs <;> simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases advance_phase_target p f g ((advance p f g)^[n] (initialControl p)) with h | h
    · rw [h.1, h.2, ih]
    · rw [h.1, h.2.1, ih, max_half _ _ hε, pow_succ, div_div]

lemma phase_exponential_bound (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (hε : 0 ≤ p.ε) (n : ℕ) :
    0 < ((advance p f g)^[n] (initialControl p)).phase →
      p.ε * (2 : ℝ) ^ (((advance p f g)^[n] (initialControl p)).phase - 1) < (initialControl p).target := by
  induction n with
  | zero => simp [initialControl]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases advance_phase_target p f g ((advance p f g)^[n] (initialControl p)) with h | h
    · rwa [h.1]
    · intro _
      rw [h.1, Nat.add_sub_cancel]
      have ht := h.2.2
      rw [target_formula p f g hε n, lt_max_iff] at ht
      rcases ht with ht | ht
      · exact False.elim (lt_irrefl _ ht)
      · exact (lt_div_iff₀ (by positivity)).mp ht

lemma charge_failure (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) (hc : c.finished = false) (hw : c.warm = false)
    (hf : (advance p f g c).finished = false) (hp : (advance p f g c).phase = c.phase) :
    charge p f g c = 5 * ‖(lineOutput p f g c).2.1.2‖ ^ 2 /
      (24 * (p.L0 + p.L1 * ‖(lineOutput p f g c).2.1.2‖)) := by
  have h := advance_failure p f g c hc hf hp
  simp [charge, cutEnergy, hc, hw, h.1, not_le.mpr h.2.1]

lemma failure_movement (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ‖p.x0 - xstar‖ ≤ p.R) (c : Control p) (hc : Invariant p f xstar c)
    (hactive : c.finished = false) (hf : (advance p f g c).finished = false)
    (hp : (advance p f g c).phase = c.phase) :
    (c.warm = false → c.target < ‖(lineOutput p f g c).2.1.2‖ *
      ‖selector p c.body - selector p (advance p f g c).body‖) ∧
    (c.warm = true → 7 * warmScale p / (16 * p.L1) ≤
      ‖selector p c.body - selector p (advance p f g c).body‖) := by
  have hfail := advance_failure p f g c hactive hf hp
  have hout := lineOutput_guarantee p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hprior c hc
  have hnext := advance_invariant p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval hprior c hc
  let x := (lineOutput p f g c).1
  have hv : (lineOutput p f g c).2.1.1 = f x := congrArg Prod.fst hout.1
  have hgr : (lineOutput p f g c).2.1.2 = g x := congrArg Prod.snd hout.1
  have hsearch := hout.2.2
  simp only [hfail.1, Bool.false_eq_true, ite_false] at hsearch
  have hcouple : ⟪(lineOutput p f g c).2.1.2, x - selector p c.body⟫ ≤
      ‖(lineOutput p f g c).2.1.2‖ ^ 2 /
        (16 * (p.L0 + p.L1 * ‖(lineOutput p f g c).2.1.2‖)) := by
    simpa only [hgr] using hsearch.2
  have hmem : selector p (advance p f g c).body - p.x0 ∈
      rootCut p c x (lineOutput p f g c).2.1.1 (lineOutput p f g c).2.1.2 := by
    rw [← hfail.2.2]
    exact KnownValueNondualGeometry.selector_mem p hd ⟨_, hnext.minimizer_mem⟩ hnext.compact hnext.convex
  constructor
  · intro hw
    exact KnownValueNondualProgress.normal_cut_movement p hL0 hL1 c hw x _ _ _ _ hmem hcouple hfail.2.1
  · intro hw
    have hz := KnownValueNondualGeometry.selector_distance p hd xstar hprior
      ⟨_, hc.minimizer_mem⟩ hc.compact hc.convex hc.subset
    have hx := KnownValueNondualGeometry.segment_distance p xstar _ _ x hz hc.radius hout.2.1
    have hl := KnownValueNondualGeometry.warmup_failure_gradient p hconv hgrad hL0 hL1 hR xstar x hval
      hx (hc.warm_target hw) (by simpa only [hv, hgr] using hfail.2.1)
    have hG : 0 < ‖(lineOutput p f g c).2.1.2‖ := by
      rw [hgr]
      exact lt_of_lt_of_le (by positivity) hl
    have hfx : p.fstar ≤ (lineOutput p f g c).2.1.1 := by rw [hv, ← hval]; exact hmin (mem_univ x)
    exact KnownValueNondualProgress.warm_cut_movement p hL0 hL1 c hw x _ _ _ _ hmem hcouple hfx hG

end LongTails.Proofs.KnownValueNondualTrajectory
