import LongTails.Algorithms.BacktrackingComposite
import LongTails.Proofs.CompositeGeneralizedRun

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeParameterFree

open LongTails.Setups.CompositeGeneralizedParameterFree

open CompositeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma stepWeight_sq {h A : ℝ} (hh : 0 ≤ h) (hA : 0 ≤ A) :
    stepWeight h A ^ 2 = h * (A + stepWeight h A) := by
  unfold stepWeight
  have hs : Real.sqrt (h ^ 2 + 4 * h * A) ^ 2 = h ^ 2 + 4 * h * A :=
    Real.sq_sqrt (by positivity)
  linear_combination (1 / 4 : ℝ) * hs

lemma stepWeight_pos {h A : ℝ} (hh : 0 < h) (hA : 0 ≤ A) : 0 < stepWeight h A := by
  unfold stepWeight
  positivity

lemma sqrt_mul_le_stepWeight {h A : ℝ} (hh : 0 ≤ h) (hA : 0 ≤ A) :
    Real.sqrt (h * A) ≤ stepWeight h A := by
  unfold stepWeight
  have h1 : Real.sqrt (4 * (h * A)) ≤ Real.sqrt (h ^ 2 + 4 * h * A) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg h])
  rw [Real.sqrt_mul' _ (by positivity), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
  linarith

lemma stepWeight_le {h A : ℝ} (hh : 0 ≤ h) (hA : 0 ≤ A) :
    stepWeight h A ≤ h + Real.sqrt (h * A) := by
  unfold stepWeight
  have hr : 0 ≤ Real.sqrt (h * A) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (h * A) ^ 2 = h * A := Real.sq_sqrt (by positivity)
  have h1 : Real.sqrt (h ^ 2 + 4 * h * A) ≤ h + 2 * Real.sqrt (h * A) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [hr2, mul_nonneg hh hr]
  linarith

lemma stepWeight_le_two_mul {h A : ℝ} (hh : 0 ≤ h) (hA : 0 ≤ A) (hgt : A < stepWeight h A) :
    stepWeight h A ≤ 2 * h := by
  have hsq := stepWeight_sq hh hA
  have ha : 0 ≤ stepWeight h A := (hA.trans_lt hgt).le
  nlinarith [hsq, mul_le_mul_of_nonneg_left hgt.le hh]

lemma sqrt_growth_small {h A : ℝ} (hh : 0 < h) (hA : 0 < A) (hle : h ≤ A) :
    Real.sqrt A + Real.sqrt h / 4 ≤ Real.sqrt (A + stepWeight h A) := by
  have hsa : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  have hsh : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  have hsA0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  have hsh0 : 0 ≤ Real.sqrt h := Real.sqrt_nonneg _
  have hshA : Real.sqrt h ≤ Real.sqrt A := Real.sqrt_le_sqrt hle
  have hge := sqrt_mul_le_stepWeight hh.le hA.le
  rw [Real.sqrt_mul hh.le] at hge
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_le_mul_of_nonneg_left hshA hsh0]

lemma growth_large {h A : ℝ} (hh : 0 < h) (hA : 0 < A) (hlt : A < h) :
    2 * A ≤ A + stepWeight h A := by
  have hge := sqrt_mul_le_stepWeight hh.le hA.le
  have : A ≤ Real.sqrt (h * A) := Real.le_sqrt_of_sq_le (by nlinarith)
  linarith

structure TState (E : Type*) where
  A : ℝ
  x : E
  z : E
  h : ℝ

noncomputable def trialA (s : TState E) : ℝ := stepWeight s.h s.A

noncomputable def trialY (s : TState E) : E := mixPoint s.A (trialA s) s.x s.z

noncomputable def trialP (g : E → E) (prox : ℝ → E → E → E) (s : TState E) : E :=
  prox (trialA s) s.z (g (trialY s))

noncomputable def trialX (g : E → E) (prox : ℝ → E → E → E) (s : TState E) : E :=
  mixPoint s.A (trialA s) s.x (trialP g prox s)

def Accepts (g : E → E) (prox : ℝ → E → E → E) (s : TState E) : Prop :=
  2 * s.h * ⟪g (trialX g prox s) - g (trialY s), trialX g prox s - trialY s⟫ ≤
    ‖trialX g prox s - trialY s‖ ^ 2

open Classical in
noncomputable def trial (g : E → E) (prox : ℝ → E → E → E) (s : TState E) : TState E :=
  if Accepts g prox s then ⟨s.A + trialA s, trialX g prox s, trialP g prox s, 2 * s.h⟩
  else ⟨s.A, s.x, s.z, s.h / 2⟩

omit [CompleteSpace E] in
lemma trial_accept {g : E → E} {prox : ℝ → E → E → E} {s : TState E} (h : Accepts g prox s) :
    trial g prox s = ⟨s.A + trialA s, trialX g prox s, trialP g prox s, 2 * s.h⟩ := by
  unfold trial; rw [ite_eq_left h]

omit [CompleteSpace E] in
lemma trial_reject {g : E → E} {prox : ℝ → E → E → E} {s : TState E} (h : ¬ Accepts g prox s) :
    trial g prox s = ⟨s.A, s.x, s.z, s.h / 2⟩ := by
  unfold trial; rw [ite_eq_right h]

def InvT (f ψ : E → ℝ) (Q : Set E) (xs : E) (R : ℝ) (s : TState E) : Prop :=
  0 ≤ s.A ∧ s.x ∈ Q ∧ s.z ∈ Q ∧
    s.A * (f s.x + ψ s.x - (f xs + ψ xs)) + ‖s.z - xs‖ ^ 2 / 2 ≤ R ^ 2 ∧
    ‖s.x - xs‖ ≤ 2 * R ∧ ‖s.z - xs‖ ≤ 2 * R ∧ 0 < s.h

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma inv_of_invT {f ψ : E → ℝ} {Q : Set E} {xs : E} {R : ℝ} {s : TState E}
    (hs : InvT f ψ Q xs R s) (hA : 0 < s.A) : Inv f ψ Q xs R (s.A, s.x, s.z) :=
  ⟨hA, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩

lemma stm_step' {f ψ : E → ℝ} {g : E → E} {Q : Set E} (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    {A a M : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (hstep : 2 * M * a ^ 2 ≤ A + a)
    {x z p xs : E} (hx : x ∈ Q) (hp : p ∈ Q) (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪g (mixPoint A a x z), u - z⟫ + ψ u)
      Q p)
    (hdesc : f (mixPoint A a x p) ≤ f (mixPoint A a x z) +
      ⟪g (mixPoint A a x z), mixPoint A a x p - mixPoint A a x z⟫ +
        M * ‖mixPoint A a x p - mixPoint A a x z‖ ^ 2) :
    (A + a) * (f (mixPoint A a x p) + ψ (mixPoint A a x p) - (f xs + ψ xs)) +
        ‖p - xs‖ ^ 2 / 2 ≤
      A * (f x + ψ x - (f xs + ψ xs)) + ‖z - xs‖ ^ 2 / 2 := by
  have hS : 0 < A + a := by positivity
  set y := mixPoint A a x z
  set x' := mixPoint A a x p
  set gy := g y
  set l := A / (A + a)
  set m := a / (A + a)
  have hlm : l + m = 1 := by simp only [l, m]; field_simp
  have hl0 : 0 ≤ l := by positivity
  have hm0 : 0 ≤ m := by positivity
  have e1 : x' - y = m • (p - z) := mix_sub_mix A a x z p
  have e2 : x' - y = l • (x - y) + m • (p - y) := by
    have h : l • (x - y) + m • (p - y) = (l • x + m • p) - (l + m) • y := by module
    rw [h, hlm, one_smul]
    rfl
  have i1 : ⟪gy, x' - y⟫ = l * ⟪gy, x - y⟫ + m * (⟪gy, xs - y⟫ + ⟪gy, p - xs⟫) := by
    rw [e2, inner_add_right, inner_smul_right, inner_smul_right,
      show p - y = (xs - y) + (p - xs) by abel, inner_add_right]
  have n1 : ‖x' - y‖ ^ 2 = m ^ 2 * ‖p - z‖ ^ 2 := by
    rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have c1 := Gradient.convex_support hc hf y x
  have c2 := Gradient.convex_support hc hf y xs
  have hψx' : ψ x' ≤ l * ψ x + m * ψ p := by
    have h := hψ.2 hx hp hl0 hm0 hlm
    simp only [smul_eq_mul] at h
    exact h
  have tp := prox_three_point hQ hψ ha hp hmin hxs
  have hq : (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) ≤ ‖p - z‖ ^ 2 / 2 := by
    have e : (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) =
        (2 * M * a ^ 2) / (A + a) * (‖p - z‖ ^ 2 / 2) := by
      simp only [m]; field_simp
    rw [e]
    have hfrac : (2 * M * a ^ 2) / (A + a) ≤ 1 := (div_le_one hS).mpr hstep
    have hn : 0 ≤ ‖p - z‖ ^ 2 / 2 := by positivity
    nlinarith
  have hd := mul_le_mul_of_nonneg_left hdesc hS.le
  rw [i1, n1] at hd
  have ex1 : (A + a) * (f y + (l * ⟪gy, x - y⟫ + m * (⟪gy, xs - y⟫ + ⟪gy, p - xs⟫)) +
      M * (m ^ 2 * ‖p - z‖ ^ 2)) =
      (A + a) * f y + A * ⟪gy, x - y⟫ + a * ⟪gy, xs - y⟫ + a * ⟪gy, p - xs⟫ +
        (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) := by
    simp only [l, m]; field_simp; ring
  rw [ex1] at hd
  have hψ' := mul_le_mul_of_nonneg_left hψx' hS.le
  have ex2 : (A + a) * (l * ψ x + m * ψ p) = A * ψ x + a * ψ p := by
    simp only [l, m]; field_simp
  rw [ex2] at hψ'
  have k1 := mul_le_mul_of_nonneg_left c1 hA
  have k2 := mul_le_mul_of_nonneg_left c2 ha.le
  nlinarith

lemma accept_inv {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R : ℝ} (hyp : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) {s : TState E}
    (hs : InvT f ψ Q xs R s) (hacc : Accepts g prox s) :
    InvT f ψ Q xs R (trial g prox s) := by
  obtain ⟨hA, hx, hz, hΦ, hxd, hzd, hh⟩ := hs
  rw [trial_accept hacc]
  have ha : 0 < trialA s := stepWeight_pos hh hA
  have hsq : trialA s ^ 2 = s.h * (s.A + trialA s) := stepWeight_sq hh.le hA
  have hS : 0 < s.A + trialA s := by positivity
  obtain ⟨hp, hpmin⟩ := hyp.proxSpec (trialA s) ha s.z (g (trialY s))
  have hpT : trialP g prox s = prox (trialA s) s.z (g (trialY s)) := rfl
  have hx'T : trialX g prox s = mixPoint s.A (trialA s) s.x (prox (trialA s) s.z (g (trialY s))) :=
    rfl
  rw [hpT, hx'T]
  unfold Accepts at hacc
  rw [hx'T] at hacc
  set a := trialA s with hadef
  set y := trialY s with hydef
  set p := prox a s.z (g y) with hpdef
  set x' := mixPoint s.A a s.x p with hx'def
  have hdesc : f x' ≤ f y + ⟪g y, x' - y⟫ + (1 / (2 * s.h)) * ‖x' - y‖ ^ 2 := by
    have hc := Gradient.convex_support hyp.convex hyp.grad x' y
    have hsplit : ⟪g x', x' - y⟫ = ⟪g y, x' - y⟫ + ⟪g x' - g y, x' - y⟫ := by
      rw [inner_sub_left]; ring
    have ht : ⟪g x' - g y, x' - y⟫ ≤ (1 / (2 * s.h)) * ‖x' - y‖ ^ 2 := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      linarith
    have hc' : ⟪g x', y - x'⟫ ≤ f y - f x' := hc
    rw [show y - x' = -(x' - y) by abel, inner_neg_right] at hc'
    linarith
  have hstep : 2 * (1 / (2 * s.h)) * a ^ 2 ≤ s.A + a := by
    have e : 2 * (1 / (2 * s.h)) * (s.h * (s.A + a)) = s.A + a := by field_simp
    rw [hsq, e]
  have hmain := stm_step' hyp.convex hyp.grad hyp.setConvex hyp.regConvex hA ha hstep hx hp hxs
    hpmin hdesc
  have hx'Q : x' ∈ Q := mix_mem hyp.setConvex hA ha.le hS hx hp
  have hgap' : 0 ≤ f x' + ψ x' - (f xs + ψ xs) := by
    have := hmin hx'Q
    simp only [mem_ofPred_eq] at this
    linarith
  have hΦ' : (s.A + a) * (f x' + ψ x' - (f xs + ψ xs)) + ‖p - xs‖ ^ 2 / 2 ≤ R ^ 2 := by
    linarith
  have hp2 : ‖p - xs‖ ≤ 2 * R := by
    apply le_two_mul_of_sq hR.le
    have := mul_nonneg hS.le hgap'
    linarith
  exact ⟨hS.le, hx'Q, hp, hΦ', mix_dist hA ha.le hS s.x p xs hxd hp2, hp2, by positivity⟩

omit [CompleteSpace E] in
lemma reject_inv {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {R : ℝ} {xs : E} {s : TState E}
    (hs : InvT f ψ Q xs R s) (hrej : ¬ Accepts g prox s) :
    InvT f ψ Q xs R (trial g prox s) := by
  rw [trial_reject hrej]
  obtain ⟨hA, hx, hz, hΦ, hxd, hzd, hh⟩ := hs
  exact ⟨hA, hx, hz, hΦ, hxd, hzd, by positivity⟩

lemma trial_inv {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R : ℝ} (hyp : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) {s : TState E}
    (hs : InvT f ψ Q xs R s) : InvT f ψ Q xs R (trial g prox s) := by
  by_cases hacc : Accepts g prox s
  · exact accept_inv hyp hR hxs hmin hs hacc
  · exact reject_inv hs hacc

set_option maxHeartbeats 2000000 in
lemma accepts_of_small {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R : ℝ} (hyp : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) {s : TState E}
    (hs : InvT f ψ Q xs R s) (hApos : 0 < s.A)
    (hM : s.h ≤ 1 / (4 * (L0 + L1 * ‖g s.x‖)))
    (hc : s.h ≤ s.A / (4 * (1 + 32 * L1 * R) ^ 2)) :
    Accepts g prox s := by
  obtain ⟨-, hx, hz, hΦ, hxd, hzd, hh⟩ := hs
  have hA := hApos
  have hL0 := hyp.hL0
  have hL1 := hyp.hL1
  set M := L0 + L1 * ‖g s.x‖ with hMdef
  have hMpos : 0 < M := by positivity
  have ha : 0 < trialA s := stepWeight_pos hh hA.le
  have hsq : trialA s ^ 2 = s.h * (s.A + trialA s) := stepWeight_sq hh.le hA.le
  have hS : 0 < s.A + trialA s := by positivity
  obtain ⟨hp, hpmin⟩ := hyp.proxSpec (trialA s) ha s.z (g (trialY s))
  have hpT : trialP g prox s = prox (trialA s) s.z (g (trialY s)) := rfl
  have hx'T : trialX g prox s = mixPoint s.A (trialA s) s.x (prox (trialA s) s.z (g (trialY s))) :=
    rfl
  unfold Accepts
  rw [hx'T]
  set a := trialA s with hadef
  set y := trialY s with hydef
  set gy := g y with hgydef
  set p := prox a s.z gy with hpdef
  set x' := mixPoint s.A a s.x p with hx'def
  set c := 1 + 32 * L1 * R with hcdef
  have hc1 : 1 ≤ c := by simp only [c]; nlinarith [mul_nonneg hL1 hR.le]
  have hcap : a ≤ s.A / c := by
    have hle := stepWeight_le hh.le hA.le
    have hsqrt : Real.sqrt (s.h * s.A) ≤ s.A / (2 * c) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have := mul_le_mul_of_nonneg_right hc hA.le
      rw [div_pow]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hh' : s.h ≤ s.A / (2 * c) := by
      have h1 : s.A / (4 * c ^ 2) ≤ s.A / (2 * c) := by
        apply div_le_div_of_nonneg_left hA.le (by positivity)
        nlinarith
      linarith
    calc a ≤ s.h + Real.sqrt (s.h * s.A) := hle
      _ ≤ s.A / (2 * c) + s.A / (2 * c) := by linarith
      _ = s.A / c := by field_simp; ring
  obtain ⟨haA, hratio, haL⟩ := cap_ratio hL1 hR hA ha hcap
  have hroot : 4 * M * a ^ 2 ≤ s.A + a := by
    rw [hsq]
    have h1 : 4 * M * s.h ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hM
      linarith
    linarith [mul_le_mul_of_nonneg_right h1 hS.le]
  set t := a / (s.A + a) with htdef
  have ht0 : 0 ≤ t := by positivity
  have hRt : 0 ≤ R * t := by positivity
  have hzx : ‖s.z - s.x‖ ≤ 4 * R := by
    calc ‖s.z - s.x‖ = ‖(s.z - xs) - (s.x - xs)‖ := by congr 1; abel
      _ ≤ ‖s.z - xs‖ + ‖s.x - xs‖ := norm_sub_le _ _
      _ ≤ 4 * R := by linarith
  have hyx : ‖y - s.x‖ ≤ 4 * R * t := by
    rw [hydef, trialY, mix_sub_left hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have := mul_le_mul_of_nonneg_left hzx ht0
    linarith
  set gs := g xs with hgsdef
  have hoptx := optimality hyp.convex hyp.grad hyp.cont hyp.setConvex hyp.regConvex hxs hmin hx
  have hH0 : 0 ≤ f s.x - f xs - ⟪gs, s.x - xs⟫ := by
    have := Gradient.convex_support hyp.convex hyp.grad xs s.x
    linarith
  have hAH : s.A * (f s.x - f xs - ⟪gs, s.x - xs⟫) ≤ R ^ 2 := by
    have h1 : f s.x - f xs - ⟪gs, s.x - xs⟫ ≤ f s.x + ψ s.x - (f xs + ψ xs) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hA.le
    have h3 := sq_nonneg ‖s.z - xs‖
    linarith
  have hcoc := shifted_cocoercive hL0 hL1 hyp.convex hyp.grad hyp.cont hyp.smooth xs s.x
  have haγ : a * ‖g s.x - gs‖ ≤ 9 / 4 * R :=
    scaled_gap_bound ha (norm_nonneg _) hH0 hR hcoc hAH hroot haA (by linarith)
  have hLyx : L1 * ‖y - s.x‖ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hyx hL1
    linarith
  have hgyx : ‖gy - g s.x‖ ≤ 2 * M * ‖y - s.x‖ :=
    ball_lipschitz hL0.le hL1 hyp.cont hyp.smooth (x := s.x) (u := y) (v := s.x) hLyx le_rfl
      (by simp)
  have hagy : a * ‖gy - g s.x‖ ≤ 2 * R := by
    have h1 : a * ‖gy - g s.x‖ ≤ a * (2 * M * (4 * R * t)) :=
      mul_le_mul_of_nonneg_left (hgyx.trans (mul_le_mul_of_nonneg_left hyx (by positivity)))
        ha.le
    have h2 : a * (2 * M * (4 * R * t)) = 2 * R * (4 * M * a ^ 2 / (s.A + a)) := by
      simp only [t]; field_simp
    have h3 : 4 * M * a ^ 2 / (s.A + a) ≤ 1 := (div_le_one hS).mpr hroot
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * R by positivity)
    linarith
  have hoptp := optimality hyp.convex hyp.grad hyp.cont hyp.setConvex hyp.regConvex hxs hmin hp
  have hpd := prox_distance hyp.setConvex hyp.regConvex ha hp hxs hpmin hoptp
  have hgygs : ‖gy - gs‖ ≤ ‖gy - g s.x‖ + ‖g s.x - gs‖ := by
    calc ‖gy - gs‖ = ‖(gy - g s.x) + (g s.x - gs)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hpxs : ‖p - xs‖ ≤ 21 / 2 * R := by
    have := mul_le_mul_of_nonneg_left hgygs ha.le
    linarith
  have hpx : ‖p - s.x‖ ≤ 25 / 2 * R := by
    calc ‖p - s.x‖ = ‖(p - xs) - (s.x - xs)‖ := by congr 1; abel
      _ ≤ ‖p - xs‖ + ‖s.x - xs‖ := norm_sub_le _ _
      _ ≤ 25 / 2 * R := by linarith
  have hx'x : ‖x' - s.x‖ ≤ 25 / 2 * R * t := by
    rw [hx'def, mix_sub_left hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have := mul_le_mul_of_nonneg_left hpx ht0
    linarith
  have hr : L1 * (25 / 2 * R * t) ≤ 1 / 2 := by linarith
  have hlip : ‖g x' - gy‖ ≤ 2 * M * ‖x' - y‖ :=
    ball_lipschitz hL0.le hL1 hyp.cont hyp.smooth (x := s.x) (u := x') (v := y) hr hx'x
      (hyx.trans (by linarith))
  have hin : ⟪g x' - gy, x' - y⟫ ≤ 2 * M * ‖x' - y‖ ^ 2 := by
    calc ⟪g x' - gy, x' - y⟫ ≤ ‖g x' - gy‖ * ‖x' - y‖ := real_inner_le_norm _ _
      _ ≤ 2 * M * ‖x' - y‖ * ‖x' - y‖ := by gcongr
      _ = 2 * M * ‖x' - y‖ ^ 2 := by ring
  have h1 : 4 * M * s.h ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hM
    linarith
  linarith [mul_le_mul_of_nonneg_left hin (by positivity : (0:ℝ) ≤ 2 * s.h),
    mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x' - y‖)]

lemma stepWeight_zero {h : ℝ} (hh : 0 ≤ h) : stepWeight h 0 = h := by
  unfold stepWeight
  rw [mul_zero, add_zero, Real.sqrt_sq hh]
  ring

omit [CompleteSpace E] in
lemma mixPoint_zero {a : ℝ} (ha : 0 < a) (x z : E) : mixPoint 0 a x z = z := by
  unfold mixPoint
  rw [zero_div, zero_smul, zero_add, zero_add, div_self ha.ne', one_smul]

set_option maxHeartbeats 2000000 in
lemma accepts_first {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R G Δ : ℝ} (hyp : Hyp f ψ g Q prox L0 L1) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) (hG : ‖g xs‖ ≤ G) (hΔ : 0 < Δ)
    {s : TState E} (hs : InvT f ψ Q xs R s) (hA0 : s.A = 0)
    (hgap : f s.z + ψ s.z - (f xs + ψ xs) ≤ Δ)
    (hh : s.h ≤ 1 / (12 * (L0 + L1 * G) + 176 * L1 ^ 2 * Δ)) :
    Accepts g prox s := by
  obtain ⟨-, hx, hz, -, -, -, hhpos⟩ := hs
  have hL0 := hyp.hL0
  have hL1 := hyp.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hLs0 : 0 < L0 + L1 * G := by positivity
  have ha : trialA s = s.h := by
    simp only [trialA, hA0]; exact stepWeight_zero hhpos.le
  have hy : trialY s = s.z := by
    simp only [trialY, hA0, ha]; exact mixPoint_zero hhpos s.x s.z
  have hpT : trialP g prox s = prox s.h s.z (g s.z) := by
    simp only [trialP, ha, hy]
  have hx'T : trialX g prox s = prox s.h s.z (g s.z) := by
    simp only [trialX, hA0, ha, hpT]; exact mixPoint_zero hhpos s.x _
  obtain ⟨hp, hpmin⟩ := hyp.proxSpec s.h hhpos s.z (g s.z)
  unfold Accepts
  rw [hx'T, hy]
  set Ls := L0 + L1 * G with hLs
  set p := prox s.h s.z (g s.z) with hpdef
  set gz := g s.z with hgz
  set gs := g xs with hgsdef
  set d := ‖p - s.z‖ with hddef
  have hd0 : 0 ≤ d := norm_nonneg _
  have hoptp := optimality hyp.convex hyp.grad hyp.cont hyp.setConvex hyp.regConvex hxs hmin hp
  have hsupp := Gradient.convex_support hyp.convex hyp.grad xs s.z
  have hψ : ψ s.z - ψ p ≤ Δ + G * d := by
    have h1 : ⟪gs, p - s.z⟫ ≤ G * d := by
      calc ⟪gs, p - s.z⟫ ≤ ‖gs‖ * ‖p - s.z‖ := real_inner_le_norm _ _
        _ ≤ G * d := by gcongr
    have h2 : ⟪gs, p - xs⟫ = ⟪gs, p - s.z⟫ + ⟪gs, s.z - xs⟫ := by
      rw [← inner_add_right]; congr 1; abel
    linarith
  have htp := prox_three_point hyp.setConvex hyp.regConvex hhpos hp hpmin hz
  rw [sub_self, norm_zero, ← hddef] at htp
  have hgzd : ⟪gz, s.z - p⟫ ≤ ‖gz‖ * d := by
    calc ⟪gz, s.z - p⟫ ≤ ‖gz‖ * ‖s.z - p‖ := real_inner_le_norm _ _
      _ = ‖gz‖ * d := by rw [norm_sub_rev]
  have hdsq : d ^ 2 ≤ s.h * ((‖gz‖ + G) * d + Δ) := by
    have e : ⟪gz, p - s.z⟫ = -⟪gz, s.z - p⟫ := by rw [← inner_neg_right]; congr 1; abel
    rw [e] at htp
    have := mul_le_mul_of_nonneg_left (add_le_add hgzd hψ) hhpos.le
    linarith
  have hH0 : 0 ≤ f s.z - f xs - ⟪gs, s.z - xs⟫ := by linarith
  have hHΔ : f s.z - f xs - ⟪gs, s.z - xs⟫ ≤ Δ := by
    have := optimality hyp.convex hyp.grad hyp.cont hyp.setConvex hyp.regConvex hxs hmin hz
    linarith
  set γ := ‖gz - gs‖ with hγ
  have hγ0 : 0 ≤ γ := norm_nonneg _
  have hcoc := shifted_cocoercive hL0 hL1 hyp.convex hyp.grad hyp.cont hyp.smooth xs s.z
  have hgzG : ‖gz‖ ≤ G + γ := by
    calc ‖gz‖ = ‖(gz - gs) + gs‖ := by congr 1; abel
      _ ≤ γ + ‖gs‖ := norm_add_le _ _
      _ ≤ G + γ := by linarith
  set sq := Real.sqrt (2 * Ls * Δ) with hsqdef
  have hs2 : sq ^ 2 = 2 * Ls * Δ := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hγb : γ ≤ 16 * L1 * Δ + 2 * sq := by
    have hq : γ ^ 2 ≤ 8 * (Ls + 2 * L1 * γ) * Δ := by
      have h1 : L0 + L1 * ‖gz‖ + L1 * γ ≤ Ls + 2 * L1 * γ := by
        have := mul_le_mul_of_nonneg_left hgzG hL1
        simp only [Ls]; linarith
      have h2 : 8 * (L0 + L1 * ‖gz‖ + L1 * γ) * (f s.z - f xs - ⟪gs, s.z - xs⟫) ≤
          8 * (Ls + 2 * L1 * γ) * Δ := by
        apply mul_le_mul (by linarith) hHΔ hH0 (by positivity)
      linarith
    by_contra hcon
    push Not at hcon
    have hpos : 0 < γ - 16 * L1 * Δ - 2 * sq := by linarith
    have hγpos : 0 < γ := by nlinarith [mul_nonneg hL1 hΔ.le]
    have hp1 := mul_pos hpos hγpos
    have hp2 := mul_nonneg hpos.le hs0
    have hp3 := mul_nonneg hs0 (mul_nonneg hL1 hΔ.le)
    linarith [hp1, hp2, hs2, hq, hp3]
  have hsqrtb : L1 * sq ≤ Ls / 2 + L1 ^ 2 * Δ := by
    have hX : 0 ≤ Ls / 2 + L1 ^ 2 * Δ := by positivity
    have hprod : (L1 * sq) ^ 2 = 2 * L1 ^ 2 * Ls * Δ := by rw [mul_pow, hs2]; ring
    have hsum : 0 ≤ L1 * sq + (Ls / 2 + L1 ^ 2 * Δ) := by positivity
    nlinarith [sq_nonneg (Ls / 2 - L1 ^ 2 * Δ), hprod, hsum]
  set Mz := L0 + L1 * ‖gz‖ with hMz
  have hMz0 : 0 < Mz := by positivity
  have hMzb : Mz ≤ 2 * Ls + 18 * L1 ^ 2 * Δ := by
    have := mul_le_mul_of_nonneg_left (hgzG.trans (by linarith : G + γ ≤ G + 16 * L1 * Δ + 2 * sq)) hL1
    simp only [Mz, Ls] at this hsqrtb ⊢
    linarith
  have hBb : L1 * (‖gz‖ + G) ≤ 3 * Ls + 18 * L1 ^ 2 * Δ := by
    have := mul_le_mul_of_nonneg_left hgzG hL1
    have h2 := mul_le_mul_of_nonneg_left hγb hL1
    simp only [Ls] at this hsqrtb h2 ⊢
    linarith [mul_nonneg hL1 hG0]
  have hden : 0 < 12 * Ls + 176 * L1 ^ 2 * Δ := by positivity
  have hh' : s.h * (12 * Ls + 176 * L1 ^ 2 * Δ) ≤ 1 := by
    rw [le_div_iff₀ hden] at hh; linarith
  have hhL : 0 ≤ s.h * Ls := mul_nonneg hhpos.le hLs0.le
  have hhΔ : 0 ≤ s.h * (L1 ^ 2 * Δ) := mul_nonneg hhpos.le (mul_nonneg (sq_nonneg L1) hΔ.le)
  have hloc : L1 * d ≤ 1 / 2 := by
    by_cases hcase : d ≤ 2 * s.h * (‖gz‖ + G)
    · have h1 := mul_le_mul_of_nonneg_left hcase hL1
      have h2 : 2 * s.h * (L1 * (‖gz‖ + G)) ≤ 2 * s.h * (3 * Ls + 18 * L1 ^ 2 * Δ) :=
        mul_le_mul_of_nonneg_left hBb (by positivity)
      linarith
    · push Not at hcase
      have hdpos : 0 < d := by
        have : 0 ≤ 2 * s.h * (‖gz‖ + G) := by positivity
        linarith
      have h1 : d ^ 2 ≤ 2 * s.h * Δ := by
        have := mul_lt_mul_of_pos_right hcase hdpos
        nlinarith
      have h2 : L1 ^ 2 * d ^ 2 ≤ 2 * s.h * (L1 ^ 2 * Δ) := by
        have := mul_le_mul_of_nonneg_left h1 (sq_nonneg L1)
        linarith
      have h3 : 2 * s.h * (L1 ^ 2 * Δ) ≤ 1 / 88 := by linarith
      have h5 : (L1 * d) ^ 2 ≤ (1 / 2) ^ 2 := by rw [mul_pow]; linarith
      exact (abs_le_of_sq_le_sq' h5 (by norm_num)).2
  have hlip : ‖g p - gz‖ ≤ 2 * Mz * d := by
    have := ball_lipschitz hL0.le hL1 hyp.cont hyp.smooth (x := s.z) (u := p) (v := s.z) hloc
      le_rfl (by simpa using hd0)
    rw [← hgz, ← hddef, ← hMz] at this
    exact this
  have hin : ⟪g p - gz, p - s.z⟫ ≤ 2 * Mz * d ^ 2 := by
    calc ⟪g p - gz, p - s.z⟫ ≤ ‖g p - gz‖ * ‖p - s.z‖ := real_inner_le_norm _ _
      _ ≤ 2 * Mz * d * d := by gcongr
      _ = 2 * Mz * d ^ 2 := by ring
  have h4 : 4 * Mz * s.h ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hMzb (by positivity : (0:ℝ) ≤ 4 * s.h)
    linarith
  linarith [mul_le_mul_of_nonneg_left hin (by positivity : (0:ℝ) ≤ 2 * s.h),
    mul_le_mul_of_nonneg_right h4 (sq_nonneg d)]

end OracleTemplate.CompositeParameterFree
