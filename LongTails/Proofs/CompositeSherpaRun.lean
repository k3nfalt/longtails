import LongTails.Proofs.CompositeSherpaSearch
import LongTails.Proofs.CompositeSherpaCount
import LongTails.Proofs.BacktrackingCompositeRun

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeSherpa

open LongTails.Setups.LipschitzCompositeGeneralizedSmooth
open RadiusFreeSherpa (theta theta_pos)

noncomputable def probeCap (q : ℝ) : ℕ := ⌈Real.logb 2 (2304 * (1 + 2 * q) ^ 2)⌉₊

lemma probeCap_ge {q : ℝ} (hq : 0 < q) {m : ℕ} (hm : (2 : ℝ) ^ m < 2304 * (1 + 2 * q) ^ 2) :
    m + 1 ≤ probeCap q := by
  unfold probeCap
  have hpos : (0 : ℝ) < 2304 * (1 + 2 * q) ^ 2 := by positivity
  have hlog : (m : ℝ) < Real.logb 2 (2304 * (1 + 2 * q) ^ 2) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) hpos]
    simpa using hm
  have hceil := Nat.le_ceil (Real.logb 2 (2304 * (1 + 2 * q) ^ 2))
  have : (m : ℝ) < (⌈Real.logb 2 (2304 * (1 + 2 * q) ^ 2)⌉₊ : ℝ) := lt_of_lt_of_le hlog hceil
  exact Nat.succ_le_of_lt (by exact_mod_cast this)

variable {p : Public}

noncomputable def answerOf (p : Public) (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E)
    (ψ : p.E → ℝ) : Query p → Reply p
  | .gradient x => .vector (grad x)
  | .prox a z v => .vector (prox a z v)
  | .value x => .scalar (ψ x)

noncomputable def T (p : Public) (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E)
    (ψ : p.E → ℝ) (s : State p.E) : State p.E :=
  stateUpdate p s (answerOf p grad prox ψ (stateQuery p s))

lemma T_first (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (ψ : p.E → ℝ) (ph : Phase p.E) :
    T p grad prox ψ (.first ph) = phaseUpdate p ph (answerOf p grad prox ψ (phaseQuery p ph)) := rfl

lemma T_second (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (ψ : p.E → ℝ)
    (s : CompositeParameterFree.BtState p.E) :
    T p grad prox ψ (.second s) = .second (secondUpdate p s (answerOf p grad prox ψ (secondQuery p s))) :=
  rfl

def coreOf (ph : Phase E) : Core E :=
  match ph with
  | .queryPx c => c
  | .queryGv c _ => c
  | .queryPv c _ _ => c
  | .probeG c _ _ _ _ => c
  | .probeP c _ _ _ _ _ => c
  | .proxX c _ _ => c
  | .proxV c _ _ _ => c

variable {f : p.E → ℝ} {ψ : p.E → ℝ} {g : p.E → p.E} {prox : ℝ → p.E → p.E → p.E} {xs : p.E}

def Accept (f ψ : p.E → ℝ) (g : p.E → p.E) (M R : ℝ) (c : Core p.E) (xs y gy : p.E) : Prop :=
  gy = g y ∧ gthr p.L0 p.L1 M < ‖gy‖ ∧ ‖y - xs‖ ≤ R ∧
    f y + ψ y ≤ f c.x + ψ c.x + tol p.L0 p.L1 M ‖gy‖ ∧
    ∀ w, ψ y - ψ w + ⟪gy, y - w⟫ ≤ tol p.L0 p.L1 M ‖gy‖ + (‖gy‖ + M) * ‖w - c.v‖

def SubInv (f ψ : p.E → ℝ) (g : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (q R : ℝ) (xs : p.E)
    (ph : Phase p.E) (j : ℕ) : Prop :=
  match ph with
  | .queryPx _ => j = 0
  | .queryGv c px => px = ψ c.x ∧ j = 1
  | .queryPv c px gv => px = ψ c.x ∧ gv = g c.v ∧ gthr p.L0 p.L1 p.M < ‖gv‖ ∧ j = 2
  | .probeG c px tm tp pm => px = ψ c.x ∧ pm = ψ (seg c tm) ∧ PInv f ψ g p.L0 p.L1 p.M c tm tp ∧
      ∃ m : ℕ, j = 3 + 2 * m ∧ tp - tm = (1 / 2) ^ m ∧ m + 1 ≤ probeCap q
  | .probeP c px tm tp pm gz => px = ψ c.x ∧ pm = ψ (seg c tm) ∧
      PInv f ψ g p.L0 p.L1 p.M c tm tp ∧ gz = g (seg c ((tm + tp) / 2)) ∧
      gthr p.L0 p.L1 p.M < ‖gz‖ ∧
      ∃ m : ℕ, j = 4 + 2 * m ∧ tp - tm = (1 / 2) ^ m ∧ m + 1 ≤ probeCap q
  | .proxX c y gy => Accept f ψ g p.M R c xs y gy ∧ j ≤ 3 + 2 * probeCap q
  | .proxV c y gy xn => Accept f ψ g p.M R c xs y gy ∧
      xn = prox (1 / (4 * curv p.L0 p.L1 p.M ‖gy‖)) y gy ∧ j ≤ 4 + 2 * probeCap q

def PhInv (f ψ : p.E → ℝ) (g : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (q R : ℝ) (xs : p.E)
    (n : ℕ) (ph : Phase p.E) : Prop :=
  ∃ (S : ℝ) (k j : ℕ), Inv f ψ xs R (coreOf ph) S ∧
    (k : ℝ) ≤ omega (p.L0 + p.L1 * p.M) p.L1 q (coreOf ph).A S + ind (p.L0 + p.L1 * p.M) q (coreOf ph).A ∧
    (k : ℝ) ≤ bigB q + 1 ∧
    (n : ℝ) ≤ k * (5 + 2 * probeCap q) + j ∧ SubInv f ψ g prox q R xs ph j

def GoodExit (g : p.E → p.E) (M R : ℝ) (xs z : p.E) : Prop :=
  ‖z - xs‖ ≤ R ∧ ‖g z‖ ≤ gthr p.L0 p.L1 M

lemma GoodExit.gap (H : Hyp f ψ g prox p.L0 p.L1 p.M xs) {R : ℝ} {z : p.E}
    (h : GoodExit g p.M R xs z) :
    f z + ψ z - (f xs + ψ xs) ≤ 6 * (p.L0 + p.L1 * p.M) * R / p.L1 := by
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  have hc := Gradient.convex_support H.convex H.grad z xs
  have hlip := H.ψ_sub_le z xs
  have h1 : ⟪g z, xs - z⟫ ≥ -(‖g z‖ * ‖z - xs‖) := by
    have := real_inner_le_norm (g z) (-(xs - z))
    rw [inner_neg_right, norm_neg, norm_sub_rev] at this
    linarith
  have h2 : ‖g z‖ * ‖z - xs‖ ≤ gthr p.L0 p.L1 p.M * R :=
    mul_le_mul h.2 h.1 (norm_nonneg _) (by unfold gthr; positivity)
  have h3 : p.M * ‖z - xs‖ ≤ p.M * R := mul_le_mul_of_nonneg_left h.1 hM
  have h4 : (gthr p.L0 p.L1 p.M + p.M) * R ≤ 6 * (p.L0 + p.L1 * p.M) * R / p.L1 := by
    unfold gthr
    rw [le_div_iff₀ hL1]
    have hR : 0 ≤ R := (norm_nonneg _).trans h.1
    have : (5 * p.M + p.L0 / p.L1 + p.M) * R * p.L1 = (6 * p.M * p.L1 + p.L0) * R := by
      field_simp; ring
    rw [this]
    nlinarith [mul_nonneg hL1.le hM, mul_nonneg hR hL0.le]
  nlinarith

lemma gap_lower_x (H : Hyp f ψ g prox p.L0 p.L1 p.M xs) {R : ℝ} {c : Core p.E} {y gy : p.E}
    (ha : Accept f ψ g p.M R c xs y gy) :
    (p.L0 + p.L1 * p.M) / (24 * p.L1 ^ 2) ≤ f c.x + ψ c.x - (f xs + ψ xs) := by
  obtain ⟨hgy, hG, -, hfy, -⟩ := ha
  subst hgy
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  have hraw := H.gap_lower_raw y hG
  have hc := gap_const_bound (c := 1 / 200) hL0 hL1 hM hG (by norm_num) (by norm_num)
  have hcpos : 0 < curv p.L0 p.L1 p.M ‖g y‖ := curv_pos hL0 hL1.le hM (norm_nonneg _)
  have htol : tol p.L0 p.L1 p.M ‖g y‖ = 1 / 200 * (‖g y‖ ^ 2 / curv p.L0 p.L1 p.M ‖g y‖) := by
    unfold tol; ring
  have e : (p.L0 + p.L1 * p.M) / (24 * p.L1 ^ 2) ≤
      (p.L0 + p.L1 * p.M) * (3 / 25 - 1 / 200) / (12 / 5 * p.L1 ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hL0 (pow_pos hL1 2), mul_nonneg (mul_nonneg hL1.le hM) (pow_pos hL1 2).le]
  linarith


lemma width_cap (H : Hyp f ψ g prox p.L0 p.L1 p.M xs) {q R : ℝ} (hq : q = p.L1 * R) (hR : 0 < R)
    {c : Core p.E} {S : ℝ} (hI : Inv f ψ xs R c S) {tm tp : ℝ}
    (hP : PInv f ψ g p.L0 p.L1 p.M c tm tp) {m : ℕ} (hm : tp - tm = (1 / 2) ^ m) :
    m + 1 ≤ probeCap q := by
  have hw := probe_width H hP
  rw [hm] at hw
  have hqpos : 0 < q := by rw [hq]; have := H.hL1; positivity
  apply probeCap_ge hqpos
  have hd := hI.d_le hR.le H.min
  have hL1 := H.hL1
  have h1 : (1 + p.L1 * ‖c.x - c.v‖) ^ 2 ≤ (1 + 2 * q) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [hq]; nlinarith [mul_le_mul_of_nonneg_left hd hL1.le]
  have h2 : (1 / 2 : ℝ) ^ m = 1 / 2 ^ m := by rw [one_div_pow]
  rw [h2, div_lt_div_iff₀ (by positivity) (by positivity)] at hw
  nlinarith

lemma accept_ledger (H : Hyp f ψ g prox p.L0 p.L1 p.M xs) {q R : ℝ} (hq : q = p.L1 * R)
    (hR : 0 < R) {c : Core p.E} {S : ℝ} (hI : Inv f ψ xs R c S) {k j n : ℕ}
    (hk : (k : ℝ) ≤ omega (p.L0 + p.L1 * p.M) p.L1 q c.A S + ind (p.L0 + p.L1 * p.M) q c.A)
    (hn : (n : ℝ) ≤ k * (5 + 2 * probeCap q) + j) (hj : j ≤ 4 + 2 * probeCap q)
    {y gy : p.E} (ha : Accept f ψ g p.M R c xs y gy) :
    PhInv f ψ g prox q R xs (n + 1) (.queryPx (acceptCore p.L0 p.L1 p.M c gy
      (prox (1 / (4 * curv p.L0 p.L1 p.M ‖gy‖)) y gy) (prox (cweight p.L0 p.L1 p.M c.A ‖gy‖) c.v gy))) := by
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  have hqpos : 0 < q := by rw [hq]; positivity
  have hLp : 0 < p.L0 + p.L1 * p.M := by positivity
  have hgapx := gap_lower_x H ha
  obtain ⟨hgy, hG, hyd, hfy, hE⟩ := ha
  subst hgy
  have hI' := accept_inv H hI hG hyd hfy (hE _)
  have hinc := iteration_increment (q := q) (S := S) hL0 hL1 hM hqpos.le hI.A_nonneg hG
  have hpot := hI.potential
  have hvn : 0 ≤ ‖c.v - xs‖ ^ 2 / 2 := by positivity
  have hgap0 : 0 < f c.x + ψ c.x - (f xs + ψ xs) := lt_of_lt_of_le (by positivity) hgapx
  have hSle : S ≤ R ^ 2 := by nlinarith [mul_nonneg hI.A_nonneg hgap0.le, hI.S_nonneg]
  have hAq : (p.L0 + p.L1 * p.M) * c.A ≤ 12 * q ^ 2 := by
    have h1 : c.A * ((p.L0 + p.L1 * p.M) / (24 * p.L1 ^ 2)) ≤ R ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hgapx hI.A_nonneg
      linarith [hI.S_nonneg]
    rw [hq]
    have h2 : c.A * ((p.L0 + p.L1 * p.M) / (24 * p.L1 ^ 2)) =
        (p.L0 + p.L1 * p.M) * c.A / (24 * p.L1 ^ 2) := by ring
    rw [h2, div_le_iff₀ (by positivity)] at h1
    nlinarith
  have hkB : (k : ℝ) ≤ bigB q := hk.trans (omega_bound hLp hL1 hq hR hSle hAq)
  refine ⟨S + cweight p.L0 p.L1 p.M c.A ‖g y‖ ^ 2 * ‖g y‖ ^ 2, k + 1, 0, hI', ?_, ?_, ?_, rfl⟩
  · simp only [coreOf, acceptCore]; push_cast; linarith
  · push_cast; linarith
  · push_cast
    have hjr : (j : ℝ) ≤ 4 + 2 * probeCap q := by exact_mod_cast hj
    have hpc : (0 : ℝ) ≤ probeCap q := by positivity
    nlinarith

lemma probeCap_pos {q : ℝ} (hq : 0 < q) : 1 ≤ probeCap q := by
  have := probeCap_ge hq (m := 0) (by norm_num; nlinarith)
  simpa using this

theorem phase_step (H : Hyp f ψ g prox p.L0 p.L1 p.M xs) {q R : ℝ} (hq : q = p.L1 * R)
    (hR : 0 < R) {n : ℕ} {ph : Phase p.E} (hinv : PhInv f ψ g prox q R xs n ph) :
    (∃ ph', T p g prox ψ (.first ph) = .first ph' ∧ PhInv f ψ g prox q R xs (n + 1) ph') ∨
    (∃ z, T p g prox ψ (.first ph) = exitState p.L0 p.L1 p.M z ∧ GoodExit g p.M R xs z) := by
  classical
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hM := H.hM
  have hqpos : 0 < q := by rw [hq]; positivity
  have hpc : (0 : ℝ) ≤ probeCap q := by positivity
  have hpc1 : (1 : ℝ) ≤ probeCap q := by exact_mod_cast probeCap_pos hqpos
  obtain ⟨S, k, j, hI, hk, hkB, hn, hsub⟩ := hinv
  rw [T_first]
  cases ph with
  | queryPx c =>
    simp only [coreOf] at hI hk
    simp only [SubInv] at hsub
    subst hsub
    left
    refine ⟨.queryGv c (ψ c.x), rfl, S, k, 1, hI, hk, hkB, ?_, rfl, rfl⟩
    push_cast at hn ⊢; linarith
  | queryGv c px =>
    simp only [coreOf] at hI hk
    obtain ⟨hpx, hj⟩ := hsub
    subst hpx hj
    simp only [phaseQuery, phaseUpdate, answerOf]
    unfold stepGv
    split_ifs with hexit
    · right
      exact ⟨c.v, rfl, hI.v_dist hR.le H.min, hexit⟩
    · left
      push Not at hexit
      refine ⟨_, rfl, S, k, 2, hI, hk, hkB, ?_, rfl, rfl, hexit, rfl⟩
      push_cast at hn ⊢; linarith
  | queryPv c px gv =>
    simp only [coreOf] at hI hk
    obtain ⟨hpx, hgv, hG, hj⟩ := hsub
    subst hpx hgv hj
    simp only [phaseQuery, phaseUpdate, answerOf]
    unfold stepPv
    have hτ : 0 < tol p.L0 p.L1 p.M ‖g c.v‖ :=
      tol_pos hL0 hL1.le hM (gthr_facts hL0 hL1 hM hG).1
    split_ifs with hacc
    · left
      refine ⟨_, rfl, S, k, 3, hI, hk, hkB, ?_, ?_⟩
      · push_cast at hn ⊢; linarith
      · refine ⟨⟨rfl, hG, hI.v_dist hR.le H.min, ?_, ?_⟩, by omega⟩
        · have := test_one H c (t := 0) (τ := tol p.L0 p.L1 p.M ‖g c.v‖) (by rw [seg_zero]; linarith)
          rwa [seg_zero] at this
        · intro w
          have := test_zero H c w
          linarith
    · left
      push Not at hacc
      have hP : PInv f ψ g p.L0 p.L1 p.M c 0 1 := by
        refine ⟨le_rfl, by norm_num, le_rfl, by rw [seg_zero]; exact hG, ?_, Or.inl rfl⟩
        rw [seg_zero]; linarith
      have hcap := width_cap H hq hR hI hP (m := 0) (by norm_num)
      refine ⟨_, rfl, S, k, 3, hI, hk, hkB, ?_, rfl, by rw [seg_zero], hP, 0, rfl, by norm_num, hcap⟩
      push_cast at hn ⊢; linarith
  | probeG c px tm tp pm =>
    simp only [coreOf] at hI hk
    obtain ⟨hpx, hpm, hP, m, hj, hm, hmcap⟩ := hsub
    subst hpx hpm hj
    simp only [phaseQuery, phaseUpdate, answerOf]
    unfold stepProbeG
    set t := (tm + tp) / 2 with ht
    have ht0 : 0 ≤ t := by rw [ht]; linarith [hP.tm_nonneg, hP.lt]
    have ht1 : t ≤ 1 := by rw [ht]; linarith [hP.tp_le, hP.lt]
    have hzd : ‖seg c t - xs‖ ≤ R := hI.segment_dist hR.le H.min ht0 ht1
    split_ifs with hexit
    · right
      exact ⟨seg c t, rfl, hzd, hexit⟩
    · left
      push Not at hexit
      refine ⟨_, rfl, S, k, 4 + 2 * m, hI, hk, hkB, ?_, rfl, rfl, hP, rfl, hexit, m, rfl, hm, hmcap⟩
      push_cast at hn ⊢; linarith
  | probeP c px tm tp pm gz =>
    simp only [coreOf] at hI hk
    obtain ⟨hpx, hpm, hP, hgz, hG, m, hj, hm, hmcap⟩ := hsub
    subst hpx hpm hgz hj
    simp only [phaseQuery, phaseUpdate, answerOf]
    unfold stepProbeP
    simp only
    set t := (tm + tp) / 2 with ht
    have ht0 : 0 ≤ t := by rw [ht]; linarith [hP.tm_nonneg, hP.lt]
    have ht1 : t ≤ 1 := by rw [ht]; linarith [hP.tp_le, hP.lt]
    have htmt : tm < t := by rw [ht]; linarith [hP.lt]
    have http : t < tp := by rw [ht]; linarith [hP.lt]
    have hzd : ‖seg c t - xs‖ ≤ R := hI.segment_dist hR.le H.min ht0 ht1
    have hm' : tp - t = (1 / 2) ^ (m + 1) := by rw [pow_succ, ← hm, ht]; ring
    have hm'' : t - tm = (1 / 2) ^ (m + 1) := by rw [pow_succ, ← hm, ht]; ring
    split_ifs with hfail1 hfail2
    · left
      have hP' := hP.move_left H.ψconvex htmt http hG hfail1
      have hcap := width_cap H hq hR hI hP' hm'
      refine ⟨_, rfl, S, k, 3 + 2 * (m + 1), hI, hk, hkB, ?_, rfl, rfl, hP', m + 1, rfl, hm', hcap⟩
      push_cast at hn ⊢; linarith
    · left
      have hP' := hP.move_right htmt http hG hfail2
      have hcap := width_cap H hq hR hI hP' hm''
      refine ⟨_, rfl, S, k, 3 + 2 * (m + 1), hI, hk, hkB, ?_, rfl, rfl, hP', m + 1, rfl, hm'', hcap⟩
      push_cast at hn ⊢; linarith
    · left
      push Not at hfail1 hfail2
      refine ⟨_, rfl, S, k, 5 + 2 * m, hI, hk, hkB, ?_, ?_⟩
      · push_cast at hn ⊢; linarith
      · refine ⟨⟨rfl, hG, hzd, test_one H c hfail1, fun w => ?_⟩, by omega⟩
        exact test_two H c hP.tm_nonneg htmt ht1 hfail2 w
  | proxX c y gy =>
    simp only [coreOf] at hI hk
    obtain ⟨ha, hj⟩ := hsub
    left
    refine ⟨_, rfl, S, k, j + 1, hI, hk, hkB, ?_, ha, rfl, by omega⟩
    push_cast at hn ⊢; linarith
  | proxV c y gy xn =>
    simp only [coreOf] at hI hk
    obtain ⟨ha, hxn, hj⟩ := hsub
    subst hxn
    left
    exact ⟨_, rfl, accept_ledger H hq hR hI hk hn hj ha⟩

noncomputable def phaseSteps (q : ℝ) : ℝ := (bigB q + 1) * (5 + 2 * probeCap q) + 4 + 2 * probeCap q

lemma PhInv.steps_le {q R : ℝ} {n : ℕ} {ph : Phase p.E}
    (hinv : PhInv f ψ g prox q R xs n ph) : (n : ℝ) ≤ phaseSteps q := by
  obtain ⟨S, k, j, _, _, hkB, hn, hsub⟩ := hinv
  have hpc : (0 : ℝ) ≤ probeCap q := by positivity
  have hj : (j : ℝ) ≤ 4 + 2 * probeCap q := by
    cases ph with
    | queryPx c => simp only [SubInv] at hsub; subst hsub; push_cast; linarith
    | queryGv c px => obtain ⟨_, hj⟩ := hsub; subst hj; push_cast; linarith
    | queryPv c px gv => obtain ⟨_, _, _, hj⟩ := hsub; subst hj; push_cast; linarith
    | probeG c px tm tp pm =>
      obtain ⟨_, _, _, m, hj, _, hm⟩ := hsub
      subst hj
      have : (m + 1 : ℝ) ≤ probeCap q := by exact_mod_cast hm
      push_cast; linarith
    | probeP c px tm tp pm gz =>
      obtain ⟨_, _, _, _, _, m, hj, _, hm⟩ := hsub
      subst hj
      have : (m + 1 : ℝ) ≤ probeCap q := by exact_mod_cast hm
      push_cast; linarith
    | proxX c y gy =>
      obtain ⟨_, hj⟩ := hsub
      have : (j : ℝ) ≤ 3 + 2 * probeCap q := by exact_mod_cast hj
      linarith
    | proxV c y gy xn =>
      obtain ⟨_, _, hj⟩ := hsub
      exact_mod_cast hj
  unfold phaseSteps
  nlinarith

def initState (x0 : E) : State E := .first (.queryPx ⟨0, x0, x0⟩)

lemma init_inv (H : Hyp f ψ g prox p.L0 p.L1 p.M xs) {q R : ℝ} {x0 : p.E} (hq : q = p.L1 * R)
    (hR : 0 < R) (hdist : ‖x0 - xs‖ ≤ R) :
    PhInv f ψ g prox q R xs 0 (.queryPx ⟨0, x0, x0⟩) := by
  have hLp : 0 < p.L0 + p.L1 * p.M := by have := H.hL0; have := H.hL1; have := H.hM; positivity
  have hqpos : 0 < q := by rw [hq]; have := H.hL1; positivity
  refine ⟨0, 0, 0, ⟨le_rfl, le_rfl, ?_, hdist⟩, ?_, ?_, by simp, rfl⟩
  · simp only [coreOf, zero_mul, zero_div, zero_add]
    have h := hdist
    have : ‖x0 - xs‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    linarith
  · simp only [coreOf, Nat.cast_zero]
    have h3 : 0 ≤ omega (p.L0 + p.L1 * p.M) p.L1 q 0 0 := by
      unfold omega
      have := lnm_nonneg (q := q) (A := (0:ℝ)) hLp
      have hθ := theta_pos hqpos.le
      positivity
    have h4 : (0 : ℝ) ≤ ind (p.L0 + p.L1 * p.M) q 0 := ind_nonneg
    linarith
  · simp only [Nat.cast_zero]
    have h3 : 0 ≤ bigB q := by
      unfold bigB
      have hθ := theta_pos hqpos.le
      have h1 : 0 ≤ Real.log (216 * (1 + q) ^ 2) := Real.log_nonneg (by nlinarith)
      positivity
    linarith

theorem run_dichotomy (H : Hyp f ψ g prox p.L0 p.L1 p.M xs) {q R : ℝ} {x0 : p.E}
    (hq : q = p.L1 * R) (hR : 0 < R) (hdist : ‖x0 - xs‖ ≤ R) (n : ℕ) :
    (∃ ph, (T p g prox ψ)^[n] (initState x0) = .first ph ∧ PhInv f ψ g prox q R xs n ph) ∨
    (∃ z c1, c1 ≤ n ∧ GoodExit g p.M R xs z ∧ (c1 : ℝ) ≤ phaseSteps q + 1 ∧
      (T p g prox ψ)^[n] (initState x0) = (T p g prox ψ)^[n - c1] (exitState p.L0 p.L1 p.M z)) := by
  induction n with
  | zero =>
    left
    exact ⟨_, rfl, init_inv H hq hR hdist⟩
  | succ n ih =>
    rcases ih with ⟨ph, hstate, hinv⟩ | ⟨z, c1, hc1, hz, hc1le, hstate⟩
    · rw [Function.iterate_succ_apply', hstate]
      rcases phase_step H hq hR hinv with ⟨ph', hstep, hinv'⟩ | ⟨z, hstep, hz⟩
      · left; exact ⟨ph', hstep, hinv'⟩
      · right
        refine ⟨z, n + 1, le_rfl, hz, ?_, ?_⟩
        · have := hinv.steps_le; push_cast; linarith
        · rw [hstep, Nat.sub_self]; rfl
    · right
      refine ⟨z, c1, by omega, hz, hc1le, ?_⟩
      rw [Function.iterate_succ_apply', hstate, ← Function.iterate_succ_apply' (T p g prox ψ),
        show n + 1 - c1 = (n - c1) + 1 by omega]

noncomputable def S2 (p : Public) (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (ψ : p.E → ℝ)
    (s : CompositeParameterFree.BtState p.E) : CompositeParameterFree.BtState p.E :=
  secondUpdate p s (answerOf p grad prox ψ (secondQuery p s))

lemma T_second_iterate (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (ψ : p.E → ℝ)
    (s : CompositeParameterFree.BtState p.E) (r : ℕ) :
    (T p grad prox ψ)^[r] (.second s) = .second ((S2 p grad prox ψ)^[r] s) := by
  induction r generalizing s with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T_second]
    exact ih _

noncomputable def embed (s : CompositeParameterFree.TState E) (gy q : E) :
    CompositeParameterFree.BtState E :=
  ⟨s.A, s.x, s.z, s.h, 0, gy, q⟩

open CompositeParameterFree in
lemma S2_three (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (ψ : p.E → ℝ)
    (s : TState p.E) (gy q : p.E) :
    (S2 p grad prox ψ)^[3] (embed s gy q) =
      embed (trial grad prox s) (grad (trialY s)) (trialP grad prox s) := by
  have h1 : S2 p grad prox ψ (embed s gy q) = ⟨s.A, s.x, s.z, s.h, 1, grad (trialY s), q⟩ := by
    simp +decide only [S2, secondUpdate, secondQuery, embed, answerOf, trialY, trialA, ↓reduceIte]
  have h2 : S2 p grad prox ψ ⟨s.A, s.x, s.z, s.h, 1, grad (trialY s), q⟩ =
      ⟨s.A, s.x, s.z, s.h, 2, grad (trialY s), trialP grad prox s⟩ := by
    simp +decide only [S2, secondUpdate, secondQuery, answerOf, trialP, trialY, trialA, ↓reduceIte]
  have h3 : S2 p grad prox ψ ⟨s.A, s.x, s.z, s.h, 2, grad (trialY s), trialP grad prox s⟩ =
      embed (trial grad prox s) (grad (trialY s)) (trialP grad prox s) := by
    by_cases hacc : Accepts grad prox s
    · rw [trial_accept hacc]
      simp +decide only [S2, secondUpdate, secondQuery, answerOf, embed, trialX, trialY, trialA,
        trialP, ↓reduceIte]
      exact ite_eq_left hacc
    · rw [trial_reject hacc]
      simp +decide only [S2, secondUpdate, secondQuery, answerOf, embed, trialY, trialA,
        trialP, ↓reduceIte]
      exact ite_eq_right hacc
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one, h1, h2, h3]

open CompositeParameterFree in
lemma S2_mul (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (ψ : p.E → ℝ) (x0 : p.E) (h0 : ℝ)
    (i : ℕ) : ∃ gy q, (S2 p grad prox ψ)^[3 * i] (embed ⟨0, x0, x0, h0⟩ 0 x0) =
      embed (run grad prox x0 h0 i) gy q := by
  induction i with
  | zero => exact ⟨0, x0, rfl⟩
  | succ i ih =>
    obtain ⟨gy, q, h⟩ := ih
    refine ⟨grad (trialY (run grad prox x0 h0 i)), trialP grad prox (run grad prox x0 h0 i), ?_⟩
    rw [show 3 * (i + 1) = 3 + 3 * i by ring, Function.iterate_add_apply, h]
    exact S2_three grad prox ψ _ gy q

open CompositeParameterFree in
lemma S2_partial_x (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (ψ : p.E → ℝ)
    (s : TState p.E) (gy q : p.E) {r : ℕ} (hr : r < 3) :
    ((S2 p grad prox ψ)^[r] (embed s gy q)).x = s.x := by
  interval_cases r
  · rfl
  · simp +decide only [Function.iterate_one, S2, secondUpdate, secondQuery, embed, answerOf, ↓reduceIte]
  · rw [Function.iterate_succ_apply', Function.iterate_one]
    simp +decide only [S2, secondUpdate, secondQuery, embed, answerOf, ↓reduceIte]

open CompositeParameterFree in
lemma output_second (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) (ψ : p.E → ℝ) (x0 : p.E)
    (h0 : ℝ) (r : ℕ) :
    stateOutput (E := p.E) (.second ((S2 p grad prox ψ)^[r] (embed ⟨0, x0, x0, h0⟩ 0 x0))) =
      (run grad prox x0 h0 (r / 3)).x := by
  obtain ⟨gy, q, h⟩ := S2_mul grad prox ψ x0 h0 (r / 3)
  have hr : r = (r % 3) + 3 * (r / 3) := by omega
  rw [hr, Function.iterate_add_apply, h]
  simp only [stateOutput]
  rw [show (r % 3 + 3 * (r / 3)) / 3 = r / 3 by omega]
  exact S2_partial_x grad prox ψ _ gy q (Nat.mod_lt _ (by norm_num))

lemma exitState_eq (z : p.E) :
    exitState p.L0 p.L1 p.M z = State.second (embed ⟨0, z, z, 1 / (p.L0 + p.L1 * p.M)⟩ 0 z) := rfl

end OracleTemplate.CompositeSherpa
