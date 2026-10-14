import LongTails.Proofs.SlidingRun
import LongTails.Proofs.SlidingExecution

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GeneralizedSliding

open LongTails.Setups.SlidingGeneralizedSmooth

open CompositeGeneralized (mixPoint potential potential_step)

variable (p : Public) (r : ℕ → Query p → p.E)

open Classical in
noncomputable def bnd : ℕ → SlideState p.E × ℕ
  | 0 => ((sliding p).initial (), 0)
  | j + 1 =>
    if (bnd j).1.stage = 0 ∧ ¬ Idle p (bnd j).1 then
      (trans p r)^[2 + 2 * lenAt p r (bnd j).1 (bnd j).2] ((bnd j).1, (bnd j).2)
    else bnd j

variable {p} {r}

lemma bnd_succ_active {j : ℕ} (h0 : (bnd p r j).1.stage = 0) (hI : ¬ Idle p (bnd p r j).1) :
    bnd p r (j + 1) =
      (trans p r)^[2 + 2 * lenAt p r (bnd p r j).1 (bnd p r j).2]
        ((bnd p r j).1, (bnd p r j).2) := by
  rw [bnd, ite_eq_left ⟨h0, hI⟩]

lemma bnd_succ_idle {j : ℕ} (h : ¬ ((bnd p r j).1.stage = 0 ∧ ¬ Idle p (bnd p r j).1)) :
    bnd p r (j + 1) = bnd p r j := by
  rw [bnd, ite_eq_right h]

lemma bnd_trans (j : ℕ) :
    (trans p r)^[(bnd p r j).2] ((sliding p).initial (), 0) = bnd p r j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases h : (bnd p r j).1.stage = 0 ∧ ¬ Idle p (bnd p r j).1
    · rw [bnd_succ_active h.1 h.2, trans_snd]
      rw [show (bnd p r j).2 + (2 + 2 * lenAt p r (bnd p r j).1 (bnd p r j).2) =
          (2 + 2 * lenAt p r (bnd p r j).1 (bnd p r j).2) + (bnd p r j).2 from Nat.add_comm _ _,
        Function.iterate_add_apply, ih]
    · rw [bnd_succ_idle h, ih]

lemma bnd_stage (j : ℕ) : (bnd p r j).1.stage = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases h : (bnd p r j).1.stage = 0 ∧ ¬ Idle p (bnd p r j).1
    · rw [bnd_succ_active h.1 h.2]
      obtain ⟨s', hs', hnext⟩ := outer_macro (r := r) h.1 h.2 (bnd p r j).2
      rw [hs']
      exact hnext.1
    · rw [bnd_succ_idle h]; exact ih

structure Inst (p : Public) (r : ℕ → Query p → p.E) (f h : p.E → ℝ) (g : p.E → p.E)
    (Q : Set p.E) (xs : p.E) : Prop where
  hyp : Hyp f h g Q p.L0 p.L1
  hM : 0 ≤ p.M
  hR : 0 < p.R
  hΔ : 0 < p.Δ
  hε : 0 < p.ε
  hG : 0 ≤ p.G
  grad : ∀ k x, r k (Query.gradient x) = g x
  sub : ∀ k t, SubgradientOracle h (subAt p r k t) Q p.M
  proj : ∀ k t, ProjectionOracle (projAt p r k t) Q
  x0 : p.x0 ∈ Q
  memxs : xs ∈ Q
  min : IsMinOn (fun x => f x + h x) Q xs
  dist : ‖p.x0 - xs‖ ≤ p.R
  gap : f p.x0 + h p.x0 - (f xs + h xs) ≤ p.Δ
  gs : ‖g xs‖ ≤ p.G

def Good (f h : p.E → ℝ) (Q : Set p.E) (xs : p.E) (sc : SlideState p.E × ℕ) (j : ℕ) : Prop :=
  0 < sc.1.A ∧ p.R ^ 2 / (4 * p.Δ) ≤ sc.1.A ∧ sc.1.A - p.R ^ 2 / (4 * p.Δ) ≤ 2 * p.R ^ 2 / p.ε ∧
    sc.1.x ∈ Q ∧ sc.1.z ∈ Q ∧
    sc.1.A * (f sc.1.x + h sc.1.x - (f xs + h xs)) + ‖sc.1.z - xs‖ ^ 2 / 2 ≤
      3 * p.R ^ 2 / 4 + (sc.1.A - p.R ^ 2 / (4 * p.Δ)) * p.ε / 8 ∧
    ‖sc.1.x - xs‖ ≤ 20 * p.R ∧ sc.1.k ≤ j ∧
    (sc.2 : ℝ) ≤ 8 * sc.1.k + 384 * p.M ^ 2 * (sc.1.A - p.R ^ 2 / (4 * p.Δ)) / p.ε

lemma inner_error {M ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    24 * M ^ 2 * a ^ 2 / ((innerLength M ε a : ℝ) + 3) ≤ a * ε / 8 := by
  have hT : 192 * M ^ 2 * a / ε ≤ (innerLength M ε a : ℝ) := by
    simp only [innerLength]; push_cast
    have := Nat.le_ceil (192 * M ^ 2 * a / ε)
    linarith
  have hT' : 192 * M ^ 2 * a ≤ ε * ((innerLength M ε a : ℝ) + 3) := by
    rw [div_le_iff₀ hε] at hT; nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma innerLength_le {M ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    (innerLength M ε a : ℝ) ≤ 192 * M ^ 2 * a / ε + 3 := by
  simp only [innerLength]; push_cast
  have := Nat.ceil_lt_add_one (show 0 ≤ 192 * M ^ 2 * a / ε by positivity)
  linarith

set_option maxHeartbeats 4000000 in
lemma bnd_good {f h : p.E → ℝ} {g : p.E → p.E} {Q : Set p.E} {xs : p.E}
    (hI : Inst p r f h g Q xs) (j : ℕ) : Good f h Q xs (bnd p r j) j := by
  have hR := hI.hR
  have hΔ := hI.hΔ
  have hε := hI.hε
  have hA0pos : 0 < p.R ^ 2 / (4 * p.Δ) := by positivity
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show 0 < p.R ^ 2 / (4 * p.Δ); exact hA0pos
    · show p.R ^ 2 / (4 * p.Δ) ≤ p.R ^ 2 / (4 * p.Δ); exact le_rfl
    · show p.R ^ 2 / (4 * p.Δ) - p.R ^ 2 / (4 * p.Δ) ≤ 2 * p.R ^ 2 / p.ε
      rw [sub_self]; positivity
    · exact hI.x0
    · exact hI.x0
    · show p.R ^ 2 / (4 * p.Δ) * (f p.x0 + h p.x0 - (f xs + h xs)) + ‖p.x0 - xs‖ ^ 2 / 2 ≤
        3 * p.R ^ 2 / 4 + (p.R ^ 2 / (4 * p.Δ) - p.R ^ 2 / (4 * p.Δ)) * p.ε / 8
      have h1 : p.R ^ 2 / (4 * p.Δ) * (f p.x0 + h p.x0 - (f xs + h xs)) ≤
          p.R ^ 2 / (4 * p.Δ) * p.Δ := mul_le_mul_of_nonneg_left hI.gap hA0pos.le
      have h2 : p.R ^ 2 / (4 * p.Δ) * p.Δ = p.R ^ 2 / 4 := by field_simp
      have h3 : ‖p.x0 - xs‖ ^ 2 ≤ p.R ^ 2 := by
        have := norm_nonneg (p.x0 - xs)
        nlinarith [hI.dist]
      rw [sub_self, zero_mul, zero_div, add_zero]
      linarith
    · show ‖p.x0 - xs‖ ≤ 20 * p.R
      linarith [hI.dist]
    · show (0 : ℕ) ≤ 0
      exact le_rfl
    · show ((0 : ℕ) : ℝ) ≤ 8 * ((0 : ℕ) : ℝ) +
        384 * p.M ^ 2 * (p.R ^ 2 / (4 * p.Δ) - p.R ^ 2 / (4 * p.Δ)) / p.ε
      simp
  | succ j ih =>
    by_cases hact : (bnd p r j).1.stage = 0 ∧ ¬ Idle p (bnd p r j).1
    · obtain ⟨hA, hAA0, hAup, hx, hz, hΦ, hxd, hkj, hcost⟩ := ih
      rw [bnd_succ_active hact.1 hact.2]
      set s := (bnd p r j).1 with hsdef
      set c := (bnd p r j).2 with hcdef
      obtain ⟨s', hs', hO, hk', hA', hx', hz'⟩ := outer_macro (r := r) hact.1 hact.2 c
      rw [hs']
      have hy := hI.hyp
      have hL0 := hy.hL0
      have hL1 := hy.hL1
      have hgx : r c (Query.gradient s.x) = g s.x := hI.grad c s.x
      set a := weightAt p r s c with hadef
      have hadef' : a = slideWeight p.L1 p.R s.A (p.L0 + p.L1 * ‖g s.x‖) := by
        rw [hadef, weightAt, hgx]
      have hMpos : 0 < p.L0 + p.L1 * ‖g s.x‖ := by positivity
      obtain ⟨ha, hcap, hroot⟩ := slideWeight_spec hL1 hR hA hMpos
      rw [← hadef'] at ha hcap hroot
      obtain ⟨haA, -, -⟩ := slide_cap hL1 hR hA ha hcap
      have hgy : gradY p r s c = g (mixPoint s.A a s.x s.z) := hI.grad (c + 1) _
      set T := lenAt p r s c with hTdef
      have hT1 : 1 ≤ T := le_trans (by norm_num) (lenAt_pos (r := r) s c)
      have hps := sliding_three_point hy.setConvex (hI.proj c) (hI.sub c) ha hT1
        (gradY p r s c) hz hI.memxs
      obtain ⟨hup, hub, hineq⟩ := hps
      set e := 24 * p.M ^ 2 * a ^ 2 / ((T : ℝ) + 3) with hedef
      have he0 : 0 ≤ e := by positivity
      have hea : e ≤ a * p.ε / 8 := inner_error hε ha
      have hnotA : s.A < p.R ^ 2 / p.ε := by
        have := hact.2
        simp only [Idle, not_or, not_le] at this
        exact this.1
      have hAa : s.A + a - p.R ^ 2 / (4 * p.Δ) ≤ 2 * p.R ^ 2 / p.ε := by
        have : s.A + a ≤ 2 * s.A := by linarith
        have h2 : 2 * s.A ≤ 2 * (p.R ^ 2 / p.ε) := by linarith
        have h3 : 0 < p.R ^ 2 / (4 * p.Δ) := hA0pos
        rw [mul_div_assoc]; linarith
      set P := 3 * p.R ^ 2 / 4 + (s.A - p.R ^ 2 / (4 * p.Δ)) * p.ε / 8 with hPdef
      have hPe : P + e ≤ p.R ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_right hAa (show 0 ≤ p.ε / 8 by positivity)
        have h2 : (2 * p.R ^ 2 / p.ε) * (p.ε / 8) = p.R ^ 2 / 4 := by field_simp; ring
        simp only [hPdef]
        linarith
      have hineq' : slideWeight p.L1 p.R s.A (p.L0 + p.L1 * ‖g s.x‖) *
          (⟪g (mixPoint s.A (slideWeight p.L1 p.R s.A (p.L0 + p.L1 * ‖g s.x‖)) s.x s.z),
            (innerAt p r s c T).2 - xs⟫ + h (innerAt p r s c T).2 - h xs) +
          1 / 3 * ‖(innerAt p r s c T).2 - s.z‖ ^ 2 + ‖(innerAt p r s c T).1 - xs‖ ^ 2 / 2 ≤
          ‖s.z - xs‖ ^ 2 / 2 + e := by
        rw [← hadef', ← hgy]
        exact hineq
      obtain ⟨hΦ', hxQ', hxd'⟩ := slide_step hy hR hI.memxs hI.min hA hx hΦ hPe he0 hxd hub hineq'
      rw [← hadef'] at hΦ' hxQ' hxd'
      have hA's : s'.A = s.A + a := hA'
      have hx's : s'.x = mixPoint s.A a s.x (innerAt p r s c T).2 := hx'
      have hz's : s'.z = (innerAt p r s c T).1 := hz'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only; rw [hA's]; linarith
      · simp only; rw [hA's]; linarith
      · simp only; rw [hA's]; exact hAa
      · simp only; rw [hx's]; exact hxQ'
      · simp only; rw [hz's]; exact hup
      · simp only; rw [hA's, hx's, hz's]
        have hΦ2 : (s.A + a) * (f (mixPoint s.A a s.x (innerAt p r s c T).2) +
            h (mixPoint s.A a s.x (innerAt p r s c T).2) - (f xs + h xs)) +
            ‖(innerAt p r s c T).1 - xs‖ ^ 2 / 2 ≤ P + e := hΦ'
        have : (s.A - p.R ^ 2 / (4 * p.Δ)) * p.ε / 8 + e ≤
            (s.A + a - p.R ^ 2 / (4 * p.Δ)) * p.ε / 8 := by linarith
        linarith [hPdef]
      · simp only; rw [hx's]; exact hxd'
      · simp only; rw [hk']; omega
      · simp only; rw [hk', hA's]
        have hT' : (T : ℝ) ≤ 192 * p.M ^ 2 * a / p.ε + 3 := innerLength_le hε ha
        have hcast : ((c + 2 + 2 * T : ℕ) : ℝ) = (c : ℝ) + 2 + 2 * (T : ℝ) := by push_cast; ring
        have hk1 : ((s.k + 1 : ℕ) : ℝ) = (s.k : ℝ) + 1 := by push_cast; ring
        have hdiv : 384 * p.M ^ 2 * (s.A + a - p.R ^ 2 / (4 * p.Δ)) / p.ε =
            384 * p.M ^ 2 * (s.A - p.R ^ 2 / (4 * p.Δ)) / p.ε + 2 * (192 * p.M ^ 2 * a / p.ε) := by
          ring
        rw [hcast, hk1, hdiv]
        linarith
    · rw [bnd_succ_idle hact]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ih
      exact ⟨h1, h2, h3, h4, h5, h6, h7, by omega, h9⟩

set_option maxHeartbeats 2000000 in
lemma bnd_potential {f h : p.E → ℝ} {g : p.E → p.E} {Q : Set p.E} {xs : p.E}
    (hI : Inst p r f h g Q xs) (j : ℕ) (hj : j ≤ outerCap p) :
    p.R ^ 2 / p.ε ≤ (bnd p r j).1.A ∨ ((bnd p r j).1.k = j ∧
      potential (1 / (8 * Real.sqrt (3 * (p.L0 + p.L1 * p.G)))) (1 / (3 + 240 * p.L1 * p.R))
          (Real.sqrt (p.R ^ 2 / (4 * p.Δ))) + 3 / 4 * (j : ℝ) ≤
        potential (1 / (8 * Real.sqrt (3 * (p.L0 + p.L1 * p.G)))) (1 / (3 + 240 * p.L1 * p.R))
          (Real.sqrt (bnd p r j).1.A)) := by
  have hR := hI.hR
  have hy := hI.hyp
  have hL0 := hy.hL0
  have hL1 := hy.hL1
  have hMs : 0 < p.L0 + p.L1 * p.G := by have := hI.hG; positivity
  have hδ : 0 < 1 / (8 * Real.sqrt (3 * (p.L0 + p.L1 * p.G))) := by
    have : 0 < Real.sqrt (3 * (p.L0 + p.L1 * p.G)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hρ : 0 < 1 / (3 + 240 * p.L1 * p.R) := by positivity
  have hρ3 : 1 / (3 + 240 * p.L1 * p.R) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_nonneg hL1 hR.le]
  induction j with
  | zero => right; exact ⟨rfl, by simp [bnd, sliding]⟩
  | succ j ih =>
    rcases ih (by omega) with hbig | ⟨hk, hpot⟩
    · left
      have hIdle : ¬ ((bnd p r j).1.stage = 0 ∧ ¬ Idle p (bnd p r j).1) := by
        rintro ⟨-, hn⟩; exact hn (Or.inl hbig)
      rw [bnd_succ_idle hIdle]; exact hbig
    · by_cases hbig : p.R ^ 2 / p.ε ≤ (bnd p r j).1.A
      · left
        have hIdle : ¬ ((bnd p r j).1.stage = 0 ∧ ¬ Idle p (bnd p r j).1) := by
          rintro ⟨-, hn⟩; exact hn (Or.inl hbig)
        rw [bnd_succ_idle hIdle]; exact hbig
      · right
        have hact : (bnd p r j).1.stage = 0 ∧ ¬ Idle p (bnd p r j).1 := by
          refine ⟨bnd_stage j, ?_⟩
          rintro (h1 | h2)
          · exact hbig h1
          · rw [hk] at h2; omega
        obtain ⟨hA, -, -, hx, -, hΦ, -, -, -⟩ := bnd_good hI j
        rw [bnd_succ_active hact.1 hact.2]
        set s := (bnd p r j).1
        set c := (bnd p r j).2
        obtain ⟨s', hs', -, hk', hA', -, -⟩ := outer_macro (r := r) hact.1 hact.2 c
        rw [hs']
        refine ⟨by simp only; rw [hk', hk], ?_⟩
        simp only
        have hgx : r c (Query.gradient s.x) = g s.x := hI.grad c s.x
        have hA's : s'.A = s.A + slideWeight p.L1 p.R s.A (p.L0 + p.L1 * ‖g s.x‖) := by
          rw [hA', weightAt, hgx]
        have hMpos : 0 < p.L0 + p.L1 * ‖g s.x‖ := by positivity
        have hΦR : s.A * (f s.x + h s.x - (f xs + h xs)) ≤ p.R ^ 2 := by
          have hAa : s.A - p.R ^ 2 / (4 * p.Δ) ≤ 2 * p.R ^ 2 / p.ε := (bnd_good hI j).2.2.1
          have h1 : (s.A - p.R ^ 2 / (4 * p.Δ)) * p.ε / 8 ≤ p.R ^ 2 / 4 := by
            have := mul_le_mul_of_nonneg_right hAa (show 0 ≤ p.ε / 8 by have := hI.hε; positivity)
            have h2 : (2 * p.R ^ 2 / p.ε) * (p.ε / 8) = p.R ^ 2 / 4 := by
              have := hI.hε; field_simp; ring
            linarith
          linarith [sq_nonneg ‖s.z - xs‖]
        have hMb := slide_curvature hy hI.memxs hI.min hI.gs hA hx hΦR
        have hgrow := slide_sqrt_growth hL1 hR hMs hA hMpos hMb
        have ha := (slideWeight_spec hL1 hR hA hMpos).1
        rw [hA's]
        have hstep := potential_step hδ hρ hρ3 (Real.sqrt_pos.mpr hA)
          (Real.sqrt_le_sqrt (by linarith)) hgrow
        push_cast
        linarith

lemma convergence_main :
    Convergence spec (fun q i => if i = 0 then 2 * outerCap q
      else 8 * outerCap q + ⌈768 * q.M ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊) := by
  refine ⟨fun p => sliding p, ?_, ?_⟩
  · rintro q ⟨hL0, hL1, hM, hR, hΔ, hG, hε⟩
    set N := 8 * outerCap q + ⌈768 * q.M ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊ with hNdef
    rintro I oracle ⟨hgradA, hsubA, hprojA, hc, hgrad, hcont,
      hsmooth, hQ, hx0, xs, hxs, hmin, hdist, hgap, hGx⟩
    have main : ∀ ξ : (k : ℕ) → oracle.Seed k,
        execute oracle (sliding q) (fun i => if i = 0 then 2 * outerCap q else N) () ξ ∈ I.Q ∧
          objective I (execute oracle (sliding q) (fun i => if i = 0 then 2 * outerCap q else N) () ξ) - objective I xs ≤ q.ε := by
      intro ξ
      set r : ℕ → Query q → q.E := fun k qq => oracle.answer k qq (ξ k) with hrdef
      have hsub0 : SubgradientOracle I.h (subAt q r 0 0) I.Q q.M := fun u hu =>
        hsubA _ (ξ _) u hu
      have hy : Hyp I.f I.h I.grad I.Q q.L0 q.L1 :=
        ⟨hL0, hL1, hc, hgrad, hcont, hsmooth, hQ, convexOn_of_subgradient hQ hsub0⟩
      have hI : Inst q r I.f I.h I.grad I.Q xs :=
        { hyp := hy, hM := hM, hR := hR, hΔ := hΔ, hε := hε, hG := hG
          grad := fun k x => hgradA k (ξ k) x
          sub := fun k t u hu => hsubA _ (ξ _) u hu
          proj := fun k t w => hprojA _ (ξ _) w
          x0 := hx0, memxs := hxs, min := hmin, dist := hdist, gap := hgap, gs := hGx }
      set K := outerCap q with hKdef
      have hbig : q.R ^ 2 / q.ε ≤ (bnd q r K).1.A := by
        rcases bnd_potential hI K le_rfl with h1 | ⟨-, hpot⟩
        · exact h1
        · obtain ⟨hA, -, -, -, -, -, -, -, -⟩ := bnd_good hI K
          refine slide_count hL0 hL1 hR hΔ hε (by linarith [mul_nonneg hL1 hG]) hA hpot ?_
          rw [hKdef, outerCap]
          exact Nat.le_ceil _
      obtain ⟨hA, -, hAup, hxK, -, hΦ, -, hkK, hcost⟩ := bnd_good hI K
      have hcN : (bnd q r K).2 ≤ N := by
        have h1 : ((bnd q r K).2 : ℝ) ≤ 8 * K + 768 * q.M ^ 2 * q.R ^ 2 / q.ε ^ 2 := by
          have hk : ((bnd q r K).1.k : ℝ) ≤ K := by exact_mod_cast hkK
          have h2 : 384 * q.M ^ 2 * ((bnd q r K).1.A - q.R ^ 2 / (4 * q.Δ)) / q.ε ≤
              768 * q.M ^ 2 * q.R ^ 2 / q.ε ^ 2 := by
            calc 384 * q.M ^ 2 * ((bnd q r K).1.A - q.R ^ 2 / (4 * q.Δ)) / q.ε
                ≤ 384 * q.M ^ 2 * (2 * q.R ^ 2 / q.ε) / q.ε := by gcongr
              _ = 768 * q.M ^ 2 * q.R ^ 2 / q.ε ^ 2 := by field_simp; ring
          linarith
        have h2 : (768 * q.M ^ 2 * q.R ^ 2 / q.ε ^ 2 : ℝ) ≤ ⌈768 * q.M ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊ :=
          Nat.le_ceil _
        have h3 : ((bnd q r K).2 : ℝ) ≤ (N : ℝ) := by
          rw [hNdef]; push_cast; linarith
        exact_mod_cast h3
      have hstage := bnd_stage (r := r) (p := q) K
      have hidle : Idle q (bnd q r K).1 := Or.inl hbig
      let B : Fin 3 → ℕ := fun i => if i = 0 then 2 * outerCap q else N
      let state : ℕ → (sliding q).State := fun n => ((trans q r)^[n] ((sliding q).initial (), 0)).1
      have houtput (n : ℕ) (hn : (bnd q r K).2 ≤ n) : (sliding q).output (state n) = (bnd q r K).1.x := by
        have hti := trans_idle (r := r) hstage hidle (bnd q r K).2 (n - (bnd q r K).2)
        dsimp only [state]
        rw [show n = (n - (bnd q r K).2) + (bnd q r K).2 from (Nat.sub_add_cancel hn).symm,
          Function.iterate_add_apply, bnd_trans, hti]
        rfl
      have hexec : execute oracle (sliding q) B () ξ = (bnd q r K).1.x := by
        apply execute_eq_of_safe_prefix oracle (sliding q) B () ξ state
          (fun n i => B i - calls q r n i) (bnd q r K).2 _ rfl
        · intro n
          dsimp only [state]
          rw [Function.iterate_succ_apply']
          change (sliding q).update _ (r (((trans q r)^[n] ((sliding q).initial (), 0)).2) _) = _
          rw [trans_snd]
          simp only [Nat.zero_add, hrdef]
        · funext i; simp [calls]
        · exact remaining_succ B
        · intro n hn
          let i := ((sliding q).query (state n)).1
          have hcount : calls q r (n + 1) i ≤ B i := by
            by_cases hi : i = 0
            · simpa [B, hi] using gradient_count (p := q) (r := r) (n + 1)
            · simp only [B, ite_eq_right hi]
              exact (calls_le (p := q) (r := r) (n + 1) i).trans (by omega)
          have hsucc : calls q r (n + 1) i = calls q r n i + 1 := by
            rw [calls_succ]
            exact congrArg (fun j => calls q r n i + j) (ite_eq_left rfl)
          change 0 < B i - calls q r n i
          omega
        · exact houtput
        · have hsum : N ≤ ∑ i, B i := by
            have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => Nat.zero_le (B i))
              (Finset.mem_univ (1 : Fin 3))
            simpa [B] using h
          exact hcN.trans hsum
      rw [hexec]
      refine ⟨hxK, ?_⟩
      have hgap0 : 0 ≤ objective I (bnd q r K).1.x - objective I xs := by
        have := hmin hxK
        simp only [mem_ofPred_eq] at this
        linarith
      have hAg : (bnd q r K).1.A * (objective I (bnd q r K).1.x - objective I xs) ≤ q.R ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_right hAup (show 0 ≤ q.ε / 8 by positivity)
        have h2 : (2 * q.R ^ 2 / q.ε) * (q.ε / 8) = q.R ^ 2 / 4 := by field_simp; ring
        simp only [objective]
        linarith [sq_nonneg ‖(bnd q r K).1.z - xs‖]
      have h1 : q.R ^ 2 / q.ε * (objective I (bnd q r K).1.x - objective I xs) ≤ q.R ^ 2 :=
        (mul_le_mul_of_nonneg_right hbig hgap0).trans hAg
      rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h1
      have hR2 : 0 < q.R ^ 2 := by positivity
      exact le_of_mul_le_mul_left h1 hR2
    refine ⟨xs, hxs, hmin, Filter.Eventually.of_forall fun seed => ?_⟩
    obtain ⟨⟨⟩, ξ⟩ := seed
    exact main ξ

  · intro _ _; trivial

end OracleTemplate.GeneralizedSliding
