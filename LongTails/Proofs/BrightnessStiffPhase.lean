import Mathlib.Tactic
import LongTails.Proofs.BrightnessComparatorProgress
import LongTails.Proofs.BrightnessFirstFitGuard

namespace LongTails.Proofs.BrightnessFastContraction

lemma angular_contraction (x b : ℝ) (hx : |x| ≤ 1) (hb : |b| ≤ 1/2)
    (h : |x| ≤ 1/2 ∨ b*x ≤ 0) :
    max ((1-b^2)*(1-x^2)) ((1+b*x)^2/4) ≤
      (1-b^2)*max (1-x^2) (1/4) := by
  have hb2 : b^2 ≤ 1/4 := by
    nlinarith only [pow_le_pow_left₀ (abs_nonneg _) hb 2,sq_abs b]
  have h0 : 0 ≤ 1-b^2 := by linarith
  have hmax := le_max_right (1-x^2) (1/4 : ℝ)
  apply max_le
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) h0
  · by_cases hs : |x| ≤ 1/2
    · have hx2 : x^2 ≤ 1/4 := by
        nlinarith only [pow_le_pow_left₀ (abs_nonneg _) hs 2,sq_abs x]
      have hbx : |b*x| ≤ 1/4 := by
        rw [abs_mul]
        nlinarith only [mul_le_mul hb hs (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)]
      have hsq : (1+b*x)^2 ≤ (5/4 : ℝ)^2 := by
        exact pow_le_pow_left₀ (by linarith only [(abs_le.mp hbx).1])
          (by linarith only [(abs_le.mp hbx).2]) 2
      have hh : 3/4 ≤ max (1-x^2) (1/4 : ℝ) := by linarith only [hx2,le_max_left (1-x^2) (1/4 : ℝ)]
      nlinarith only [hsq,mul_le_mul (show (3:ℝ)/4 ≤ 1-b^2 by linarith) hh (by norm_num) h0]
    · have hneg := h.resolve_left hs
      have hmag : -(b*x) = |b| * |x| := by rw [← abs_mul,abs_of_nonpos hneg]
      have hh : |b|/2 ≤ -(b*x) := by
        nlinarith only [hmag,mul_le_mul_of_nonneg_left (le_of_not_ge hs) (abs_nonneg b)]
      have hlo : 0 ≤ 1+b*x := by
        have bound := mul_le_mul hb hx (abs_nonneg x) (by norm_num : (0:ℝ) ≤ 1/2)
        nlinarith only [bound,hmag]
      have hsq : (1+b*x)^2 ≤ 1+b*x := by nlinarith only [mul_nonneg hlo (neg_nonneg.mpr hneg)]
      nlinarith only [hsq,hh,mul_le_mul_of_nonneg_left hb (abs_nonneg b),
        sq_abs b,mul_le_mul_of_nonneg_left hmax h0]

noncomputable def potential (p t : ℝ) := max |p^2-t^2| (max (p^2) (t^2)/4)

lemma potential_swap (p t : ℝ) : potential t p = potential p t := by
  simp only [potential,abs_sub_comm (t^2) (p^2),max_comm (t^2) (p^2)]

lemma potential_scale (a p t : ℝ) : potential (a*p) (a*t) = a^2*potential p t := by
  simp only [potential,mul_pow,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg a),
    ← mul_max_of_nonneg _ _ (sq_nonneg a)]
  rw [show a^2*max (p^2) (t^2)/4 = a^2*(max (p^2) (t^2)/4) by ring,
    ← mul_max_of_nonneg _ _ (sq_nonneg a)]

private lemma normalized_contraction (x b : ℝ) (hx : |x| ≤ 1) (hb : |b| ≤ 1/2)
    (hs : |x| ≤ 1/2 ∨ b*x ≤ 0) :
    potential (1+b*x) (x+b) ≤ (1-b^2)*potential 1 x := by
  have hx2 : x^2 ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hb2 : b^2 ≤ 1 := by
    nlinarith only [pow_le_pow_left₀ (abs_nonneg _) hb 2,sq_abs b]
  have he : (1+b*x)^2-(x+b)^2 = (1-b^2)*(1-x^2) := by ring
  have hd := mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hx2)
  simp only [potential,one_pow,he,abs_of_nonneg hd,abs_of_nonneg (sub_nonneg.mpr hx2),
    max_eq_left hx2,max_eq_left (show (x+b)^2 ≤ (1+b*x)^2 by linarith only [he,hd])]
  exact angular_contraction x b hx hb hs

private lemma contraction_of_dominant (p t b : ℝ) (hp : p ≠ 0) (ht : |t| ≤ |p|)
    (hb : |b| ≤ 1/2) (hs : 2*|t| ≤ |p| ∨ b*p*t ≤ 0) :
    potential (p+b*t) (t+b*p) ≤ (1-b^2)*potential p t := by
  let x := t/p
  have he : t = p*x := by dsimp [x]; field_simp
  have hp' := abs_pos.mpr hp
  have hx : |x| ≤ 1 := by simpa [x,abs_div,div_le_iff₀ hp'] using ht
  have hs' : |x| ≤ 1/2 ∨ b*x ≤ 0 := by
    rcases hs with h | h
    · left
      rw [show |x| = |t|/|p| by simp [x,abs_div],div_le_iff₀ hp']
      linarith
    · right
      by_contra! hc
      have hh := mul_pos (sq_pos_of_ne_zero hp) hc
      nth_rw 1 [he] at h
      nlinarith only [h,hh]
  have H := mul_le_mul_of_nonneg_left (normalized_contraction x b hx hb hs') (sq_nonneg p)
  rw [← potential_scale,show p^2*((1-b^2)*potential 1 x) =
    (1-b^2)*(p^2*potential 1 x) by ring,← potential_scale] at H
  rw [he]
  simpa only [mul_one, mul_add, mul_assoc, mul_left_comm, mul_comm] using H

lemma potential_contraction (p t b : ℝ) (hb : |b| ≤ 1/2)
    (hs : 2*min |p| |t| ≤ max |p| |t| ∨ b*p*t ≤ 0) :
    potential (p+b*t) (t+b*p) ≤ (1-b^2)*potential p t := by
  rcases le_total |t| |p| with h | h
  · by_cases hp : p = 0
    · have ht : t = 0 := abs_nonpos_iff.mp (by simpa [hp] using h)
      simp [hp,ht,potential]
    · exact contraction_of_dominant p t b hp h hb (by simpa [min_eq_right h,max_eq_left h] using hs)
  · by_cases ht : t = 0
    · have hp : p = 0 := abs_nonpos_iff.mp (by simpa [ht] using h)
      simp [hp,ht,potential]
    · rw [potential_swap (t+b*p) (p+b*t), potential_swap t p]
      apply contraction_of_dominant t p b ht h hb
      simpa [min_eq_left h,max_eq_right h,mul_right_comm b t p] using hs

lemma potential_perturbation (p t e : ℝ) :
    potential (p+e) t ≤ potential p t + 2*|p| * |e| + e^2 := by
  let err := 2*|p| * |e| + e^2
  have he : 0 ≤ err := by dsimp [err]; positivity
  have hs : |2*p*e+e^2| ≤ err := by
    calc
      _ ≤ |2*p*e| + |e^2| := abs_add_le _ _
      _ = err := by rw [abs_of_nonneg (sq_nonneg e)]; simp [err,abs_mul]
  have hd := abs_add_le (p^2-t^2) (2*p*e+e^2)
  rw [show p^2-t^2+(2*p*e+e^2) = (p+e)^2-t^2 by ring] at hd
  have hp := le_abs_self (2*p*e+e^2)
  unfold potential
  apply max_le
  · linarith only [hs,hd,le_max_left |p^2-t^2| (max (p^2) (t^2)/4)]
  · have hm : max ((p+e)^2) (t^2) ≤ max (p^2) (t^2) + err := by
      apply max_le
      · nlinarith only [hs,hp,le_max_left (p^2) (t^2)]
      · linarith only [he,le_max_right (p^2) (t^2)]
    change _ ≤ _ + 2*|p| * |e| + e^2
    dsimp [err] at hm he
    linarith only [hm,he,le_max_right |p^2-t^2| (max (p^2) (t^2)/4)]

lemma potential_forced (p t b e ρ : ℝ) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (he : |e| ≤ ρ * max |p| |t|) (hb : |b| ≤ 1/2)
    (hs : 2*min |p| |t| ≤ max |p| |t| ∨ b*p*t ≤ 0) :
    potential (p+b*t+e) (t+b*p) ≤ (1-b^2+16*ρ)*potential p t := by
  let m := max |p| |t|
  have hm : 0 ≤ m := (abs_nonneg p).trans (le_max_left _ _)
  have hcap : m^2 ≤ 4*potential p t := by
    have hsq : m^2 = max (p^2) (t^2) := by
      rcases le_total |p| |t| with h | h
      · have hh := pow_le_pow_left₀ (abs_nonneg p) h 2
        simp [m,max_eq_right h,max_eq_right (show p^2 ≤ t^2 by simpa using hh)]
      · have hh := pow_le_pow_left₀ (abs_nonneg t) h 2
        simp [m,max_eq_left h,max_eq_left (show t^2 ≤ p^2 by simpa using hh)]
    unfold potential
    linarith only [hsq,le_max_right |p^2-t^2| (max (p^2) (t^2)/4)]
  have hmix : |p+b*t| ≤ (3/2)*m := by
    have H := abs_add_le p (b*t)
    rw [abs_mul] at H
    nlinarith only [H,mul_le_mul_of_nonneg_right hb (abs_nonneg t),
      show |p| ≤ m from le_max_left _ _,show |t| ≤ m from le_max_right _ _]
  have hsmall : |e| ≤ m := he.trans (by nlinarith only [mul_le_mul_of_nonneg_right hρ' hm])
  have hprod := mul_le_mul hmix he (abs_nonneg e) (by positivity)
  have he2 := mul_le_mul hsmall he (abs_nonneg e) hm
  nlinarith only [potential_perturbation (p+b*t) (t+b*p) e,
    potential_contraction p t b hb hs,hprod,he2,sq_abs e,mul_le_mul_of_nonneg_left hcap hρ]

lemma occupation (V b : ℕ → ℝ) (ρ : ℝ) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < V k)
    (hstep : ∀ k < N, V (k+1) ≤ (1-b k^2+ρ)*V k) :
    ∑ k ∈ Finset.range N, b k^2 ≤ Real.log (V 0) - Real.log (V N) + N*ρ := by
  have hlog (k : ℕ) (hk : k < N) : Real.log (V (k+1)) - Real.log (V k) ≤ ρ-b k^2 := by
    rw [← Real.log_div (hpos _ (by omega)).ne' (hpos _ (by omega)).ne']
    have hr : V (k+1)/V k ≤ 1-b k^2+ρ := (div_le_iff₀ (hpos _ (by omega))).mpr (hstep k hk)
    linarith only [hr,Real.log_le_sub_one_of_pos (div_pos (hpos (k+1) (by omega)) (hpos k (by omega)))]
  induction N with
  | zero => simp
  | succ n ih =>
    have H := ih (fun k hk => hpos k (by omega)) (fun k hk => hstep k (by omega)) (fun k hk => hlog k (by omega))
    rw [Finset.sum_range_succ,Nat.cast_succ]
    linarith [hlog n (by omega)]

lemma count_large (V b : ℕ → ℝ) (N : ℕ) (ρ α upper lower : ℝ)
    (hα : 0 < α) (hl : 0 < lower) (hρ : 0 ≤ ρ) (hbudget : N*ρ ≤ 1)
    (hinit : V 0 ≤ upper) (hu : lower ≤ upper)
    (hfloor : ∀ k < N, lower ≤ V k)
    (hstep : ∀ k, k+1 < N → V (k+1) ≤ (1-b k^2+ρ)*V k) :
    (∑ k ∈ Finset.range N, if α ≤ |b k| then (1:ℝ) else 0) ≤
      1+(1+Real.log (upper/lower))/α^2 := by
  have hlog : 0 ≤ Real.log (upper/lower) := Real.log_nonneg ((one_le_div hl).mpr hu)
  cases N with
  | zero => simp; positivity
  | succ n =>
    have H := occupation V b ρ n (fun k hk => hl.trans_le (hfloor k (by omega)))
      (fun k hk => hstep k (by omega))
    have hi := Real.log_le_log (hl.trans_le (hfloor 0 (by omega))) hinit
    have hj := Real.log_le_log hl (hfloor n (by omega))
    have hh : (∑ k ∈ Finset.range n, (if α ≤ |b k| then (1:ℝ) else 0)*α^2) ≤
        ∑ k ∈ Finset.range n, b k^2 := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs with h
      · simpa using pow_le_pow_left₀ hα.le h 2
      · simpa using sq_nonneg (b k)
    rw [← Finset.sum_mul] at hh
    have hc : (∑ k ∈ Finset.range n, if α ≤ |b k| then (1:ℝ) else 0) ≤
        (1+Real.log (upper/lower))/α^2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hα),Real.log_div (hl.trans_le hu).ne' hl.ne']
      rw [Nat.cast_succ] at hbudget
      nlinarith only [H,hi,hj,hh,hbudget,hρ]
    rw [Finset.sum_range_succ]
    split_ifs <;> linarith only [hc]

end LongTails.Proofs.BrightnessFastContraction

namespace LongTails.Proofs.BrightnessPrefixOccupation

open BrightnessFastContraction

lemma restoring_sector (p t F μ R κ U D : ℝ)
    (hμ : 0 < μ) (hR : 0 < R) (hκ : 0 ≤ κ)
    (hD : 1 ≤ D) (hscale : 2*(1+U) ≤ μ*D)
    (hfloor : D/R ≤ max |p| |t|)
    (hrestore : R^2*p*t*F+|R^2*p*t| * μ ≤ 1+U*D) :
    2*min |p| |t| ≤ max |p| |t| ∨ (κ*F)*p*t ≤ 0 := by
  by_cases h : F*p*t ≤ 0
  · exact Or.inr (by nlinarith only [mul_nonpos_of_nonneg_of_nonpos hκ h])
  push Not at h
  left
  let m := max |p| |t|
  have hm : 0 < m := (div_pos (by linarith only [hD]) hR).trans_le hfloor
  have hR' : D ≤ m*R := (div_le_iff₀ hR).mp hfloor
  have hBig := pow_le_pow_left₀ (by linarith only [hD] : 0 ≤ D) hR' 2
  have htarget : 2*(1+U*D) ≤ μ*(m*R)^2 := by
    nlinarith only [hD,mul_le_mul_of_nonneg_right hscale (by linarith only [hD] : 0 ≤ D),
      mul_le_mul_of_nonneg_left hBig hμ.le]
  have ht' : 0 ≤ R^2*(F*p*t) := mul_nonneg (sq_nonneg R) h.le
  rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg R)] at hrestore
  have he : min |p| |t| * m = |p| * |t| := min_mul_max _ _
  by_contra! hsmall
  have Hs := mul_lt_mul_of_pos_right hsmall hm
  have Hz := mul_lt_mul_of_pos_left Hs (mul_pos hμ (sq_pos_of_pos hR))
  nlinarith only [htarget,hrestore,ht',Hz,
    congrArg (fun y : ℝ => 2*μ*R^2*y) he]

lemma potential_bounds (p t : ℝ) : max |p| |t|^2/4 ≤ potential p t ∧
    potential p t ≤ max |p| |t|^2 := by
  have hs : (max |p| |t|)^2 = max (p^2) (t^2) := by
    rcases le_total |p| |t| with h | h
    · have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
      simp [max_eq_right h,max_eq_right (show p^2 ≤ t^2 by simpa using hh)]
    · have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
      simp [max_eq_left h,max_eq_left (show t^2 ≤ p^2 by simpa using hh)]
  rw [hs]
  refine ⟨le_max_right _ _,max_le ?_ ?_⟩
  · apply abs_le.mpr
    constructor <;> linarith only [sq_nonneg p,sq_nonneg t,le_max_left (p^2) (t^2),le_max_right (p^2) (t^2)]
  · linarith only [sq_nonneg p,le_max_left (p^2) (t^2)]

lemma prefix_count (P T β e : ℕ → ℝ) (N : ℕ) (α R ρ m : ℝ)
    (hα : 0 < α) (hR : 1 ≤ R) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hN : 16*N*ρ ≤ 1)
    (hm : 1 ≤ m) (hinit : max |P 0| |T 0| ≤ m)
    (hn : ∀ k < N, 1/R ≤ max |P k| |T k|)
    (hb : ∀ k < N, |β k| ≤ 1/2) (he : ∀ k < N, |e k| ≤ ρ*max |P k| |T k|)
    (hs : ∀ k < N, 2*min |P k| |T k| ≤ max |P k| |T k| ∨ β k*P k*T k ≤ 0)
    (hp : ∀ k < N, P (k+1) = P k+β k*T k+e k) (ht : ∀ k < N, T (k+1) = T k+β k*P k) :
    (∑ k ∈ Finset.range N, if α ≤ |β k| then (1:ℝ) else 0) ≤
      1+(1+Real.log (4*m^2*R^2))/α^2 := by
  let V k := potential (P k) (T k)
  have hpos : 0 < R := by linarith
  have hlo : 0 < 1/(4*R^2) := by positivity
  have hHi : 1/(4*R^2) ≤ m^2 := by
    rw [div_le_iff₀ (by positivity)]
    calc
      _ ≤ (1:ℝ)^2*(4*1^2) := by norm_num
      _ ≤ _ := by gcongr
  have hh := count_large V β N (16*ρ) α (m^2) (1/(4*R^2)) hα hlo (by positivity)
    (by nlinarith only [hN]) ((potential_bounds _ _).2.trans (pow_le_pow_left₀
      ((abs_nonneg _).trans (le_max_left _ _)) hinit 2)) hHi (by
      intro k hk
      apply le_trans _ (potential_bounds _ _).1
      have H := pow_le_pow_left₀ (by positivity : 0 ≤ 1/R) (hn k hk) 2
      rw [div_pow,one_pow] at H
      calc
        _ = (1/R^2)/4 := by ring
        _ ≤ _ := by linarith only [H]) (by
      intro k hk
      dsimp only [V]
      rw [hp k (by omega),ht k (by omega)]
      exact potential_forced _ _ _ _ ρ hρ hρ₁ (he _ (by omega)) (hb _ (by omega)) (hs _ (by omega)))
  rwa [show m^2/(1/(4*R^2))=4*m^2*R^2 by field_simp] at hh

end LongTails.Proofs.BrightnessPrefixOccupation

namespace LongTails.Proofs.BrightnessStiffPhase

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open BrightnessFirstFitParameters
open BrightnessScaledCoordinates
open BrightnessTrajectoryBounds
open BrightnessFirstFitGuard
open BrightnessFirstFitWork
open BrightnessScaledForces
open BrightnessOrientation

noncomputable def vote (p : Params) (x : Images p) (c : Scales) (k : ℕ) :=
  brightness (meanRow p x (path p x c.κ k))

noncomputable def β (p : Params) (x : Images p) (c : Scales) (k : ℕ) := c.κ*vote p x c k

noncomputable def perturbation (p : Params) (x : Images p) (c : Scales) (k : ℕ) :=
  let s := path p x c.κ k
  kick p c.κ s (meanRow p x s)

noncomputable def ξ (p : Params) (x : Images p) (c : Scales) := reference p.P (β p x c)

noncomputable def pole (p : Params) (x : Images p) (c : Scales) (k : ℕ) :=
  let s := path p x c.κ k
  max |s.P| |s.T|

noncomputable def bad (p : Params) (x : Images p) (c : Scales) (k : ℕ) : Bool :=
  decide (c.κ*c.f ≤ |β p x c k|)

lemma update_P (p : Params) (x : Images p) (c : Scales) (k : ℕ) :
    (path p x c.κ (k+1)).P = (path p x c.κ k).P+
      β p x c k*(path p x c.κ k).T+perturbation p x c k := rfl

lemma update_T (p : Params) (x : Images p) (c : Scales) (k : ℕ) :
    (path p x c.κ (k+1)).T = (path p x c.κ k).T+
      β p x c k*(path p x c.κ k).P := rfl

lemma beta_cap (p : Params) (x : Images p) (c : Scales) (h : Tuning p c) (G : Geometry p x)
    (k : ℕ) : |β p x c k| ≤ 1/2 := by
  have hF := (force_bounds p x G (path p x c.κ k)).1
  have H := (small_tunings h).1
  have hU := h.Upos
  have hκ := h.κpos
  have hc := mul_nonneg hκ.le h.Dpos.le
  rw [β,abs_mul,abs_of_nonneg hκ.le]
  apply le_trans (mul_le_mul_of_nonneg_left hF hκ.le)
  nlinarith only [H,mul_nonneg hc hU.le,h.Γle]

lemma readout_cap (p : Params) (x : Images p) (c : Scales) (h : Tuning p c)
    (env : Envelope p x c) (k : ℕ) (hk : k ≤ c.H) :
    let s := path p x c.κ k
    max |s.Q| |s.P| * p.J ≤ c.U := by
  let s := path p x c.κ k
  obtain ⟨hp,_,hq,_⟩ := env.cap k hk
  have hh := abs_sub_le s.Q p.Q 0
  simp only [sub_zero] at hh
  have hδ := (small_tunings h).2.2.1
  rw [h.Ueq,mul_comm p.J]
  apply mul_le_mul_of_nonneg_right _ h.Jpos.le
  apply max_le
  · linarith only [hh,hq,hδ,abs_nonneg p.P]
  · linarith only [hp,abs_nonneg p.Q]

lemma count (p : Params) (x : Images p) (valid : spec.valid p) (G : Geometry p x) (N : ℕ)
    (hn : N ≤ (scales p).H) (pre : ∀ k < N, let c := scales p
      c.V*c.M/p.R < pole p x c k ∧ ‖(path p x c.κ k).w‖ ≤ c.V*c.M) :
    (∑ k ∈ Finset.range N, if bad p x (scales p) k then (1:ℝ) else 0) ≤ (scales p).B := by
  let c := scales p
  let S := path p x c.κ
  have h : Tuning p c := tuning p valid
  have env : Envelope p x c := envelope p x valid G
  have U := h.Upos
  have κ := h.κpos
  have f := h.fpos
  have J := h.Jpos
  have μ := h.μpos
  have M := h.Mpos
  have V : 0 < c.V := by linarith only [h.Vge]
  have R : 0 < p.R := by linarith only [h.Rlarge]
  have H : (1:ℝ) ≤ c.H := by exact_mod_cast env.horizon
  have nH : (N:ℝ) ≤ c.H := by exact_mod_cast hn
  have size := comparator_size h
  have hB : 0 ≤ c.B := by linarith only [h.Bge]
  have hM : 1 ≤ c.M := by
    nlinarith only [size.1,norm_nonneg p.readout,
      mul_nonneg (mul_nonneg κ.le U.le) hB]
  have hVM : 1 ≤ c.V*c.M := by
    nlinarith only [mul_le_mul (by linarith only [h.Vge] : 1 ≤ c.V) hM (by norm_num) V.le]
  let ρ := error p c*p.R/(c.V*c.M)
  have hW : 0 ≤ radius p c := by unfold radius; positivity
  have hε : 0 ≤ error p c := by unfold error; positivity
  have hg : 0 ≤ growth p c := by unfold growth; positivity
  have ρ₀ : 0 ≤ ρ := by dsimp [ρ]; positivity
  obtain ⟨_,hforce,hsmall⟩ := scale_remainders p valid
  change 16*c.H*error p c*p.R ≤ c.V*c.M at hforce
  have ρH : 16*(c.H:ℝ)*ρ ≤ 1 := by
    dsimp [ρ]
    rw [← mul_div_assoc,div_le_iff₀ (mul_pos V M)]
    nlinarith only [hforce]
  have ρ₁ : ρ ≤ 1 := by nlinarith only [ρH,mul_le_mul_of_nonneg_right H ρ₀,ρ₀]
  have hδ := (small_tunings h).2.2.1
  have hδpos := h.δpos
  have hT : |(initial p).T| ≤ 1 := by
    apply (initial_brightness p).trans
    change (‖p.readout‖/p.R^2)^2 + c.H*growth p c +
      2*(1+c.U*radius p c)/(p.μ*p.R^2)+(c.V*c.M/p.R)^2 ≤ c.δ^2 at hsmall
    nlinarith only [hsmall,mul_nonneg (by positivity : (0:ℝ) ≤ c.H) hg,
      (by positivity : 0 ≤ 2*(1+c.U*radius p c)/(p.μ*p.R^2)),sq_nonneg (c.V*c.M/p.R),
      pow_le_pow_left₀ hδpos.le hδ 2,sq_nonneg (‖p.readout‖/p.R^2-1)]
  have hc := BrightnessPrefixOccupation.prefix_count (fun k => (S k).P) (fun k => (S k).T)
    (β p x c) (perturbation p x c) N (c.κ*c.f) p.R ρ (1+|p.P|)
    (mul_pos κ f) h.Rlarge ρ₀ ρ₁ (by nlinarith only [ρH,mul_le_mul_of_nonneg_right nH ρ₀])
    (by linarith only [abs_nonneg p.P]) (max_le (by change |p.P| ≤ _; linarith)
      (hT.trans (by linarith only [abs_nonneg p.P]))) (fun k hk =>
        (div_le_div_of_nonneg_right hVM R.le).trans (pre k hk).1.le)
    (fun k _ => beta_cap p x c h G k) (by
      intro k hk
      apply (env.growth k (hk.trans_le hn)).2.2.trans
      change error p c ≤ ρ*pole p x c k
      have hh := mul_le_mul_of_nonneg_left (pre k hk).1.le ρ₀
      apply le_trans _ hh
      dsimp [ρ]
      field_simp
      rfl) (by
      intro k hk
      have hw := (pre k hk).2
      have UU := readout_cap p x c h env k (hk.le.trans hn)
      have hrest := restoring_at p x G (S k) R (path_centered p x c.κ k)
      have hv := mul_le_mul_of_nonneg_right (by linarith only [h.Vge] : 1 ≤ c.V) (mul_nonneg μ.le M.le)
      apply BrightnessPrefixOccupation.restoring_sector _ _ (vote p x c k) p.μ p.R c.κ c.U (c.V*c.M) μ R κ.le hVM
        (by nlinarith only [size.2.1,hv,U.le])
        (pre k hk).1.le
      exact hrest.trans (by nlinarith only [mul_le_mul UU hw (norm_nonneg _) U.le]))
    (fun k _ => update_P p x c k) (fun k _ => update_T p x c k)
  change _ ≤ c.B
  rw [h.Beq]
  simpa only [bad,decide_eq_true_eq] using hc

end LongTails.Proofs.BrightnessStiffPhase
