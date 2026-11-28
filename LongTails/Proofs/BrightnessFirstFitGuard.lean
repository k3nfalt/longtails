import Mathlib.Tactic
import LongTails.Proofs.BrightnessDominantEnvelope
import LongTails.Proofs.BrightnessFirstFitParameters

namespace LongTails.Proofs.BrightnessOrientation

noncomputable def reference (P : ℝ) (β : ℕ → ℝ) : ℕ → ℝ
  | 0 => |P|
  | k+1 => Real.sqrt (1-β k^2)*reference P β k

lemma reference_mono (P : ℝ) (β : ℕ → ℝ) : ∀ k,
    0 ≤ reference P β k ∧ reference P β (k+1) ≤ reference P β k := by
  have h0 (k : ℕ) : 0 ≤ reference P β k := by
    induction k with
    | zero => exact abs_nonneg _
    | succ k ih => exact mul_nonneg (Real.sqrt_nonneg _) ih
  intro k
  refine ⟨h0 _,?_⟩
  change Real.sqrt _ * _ ≤ _
  have h : Real.sqrt (1-β k^2) ≤ 1 := (Real.sqrt_le_one).mpr (by linarith [sq_nonneg (β k)])
  nlinarith only [mul_le_mul_of_nonneg_right h (h0 k)]

lemma imbalance_shadow (P T β e : ℕ → ℝ) (N : ℕ) (E : ℝ)
    (hb : ∀ k < N, |β k| ≤ 1) (hp : ∀ k < N, P (k+1) = P k + β k*T k + e k)
    (ht : ∀ k < N, T (k+1) = T k + β k*P k)
    (he : ∀ k < N, |2*(P k+β k*T k)*e k+e k^2| ≤ E) :
    |P N^2-T N^2-reference (P 0) β N^2| ≤ T 0^2 + N*E := by
  induction N with
  | zero => simp [reference,abs_of_nonneg (sq_nonneg (T 0))]
  | succ n ih =>
    have H := ih (fun k hk => hb k (by omega)) (fun k hk => hp k (by omega))
      (fun k hk => ht k (by omega)) (fun k hk => he k (by omega))
    have hβ : β n^2 ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg _) (hb n (by omega)) 2
    rw [hp n (by omega),ht n (by omega),reference,mul_pow,Real.sq_sqrt (sub_nonneg.mpr hβ)]
    rw [show (P n+β n*T n+e n)^2-(T n+β n*P n)^2-
      (1-β n^2)*reference (P 0) β n^2 =
      (1-β n^2)*(P n^2-T n^2-reference (P 0) β n^2) +
      (2*(P n+β n*T n)*e n+e n^2) by ring,Nat.cast_succ]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hβ)]
    nlinarith only [H,he n (by omega),mul_nonneg (sq_nonneg (β n))
      (abs_nonneg (P n^2-T n^2-reference (P 0) β n^2))]

lemma absolute_orientation (P T x a b : ℝ) (hx : 0 ≤ x)
    (hd : |P^2-T^2-x^2| ≤ a) (hs : |P*T| ≤ b) :
    (|P|-x)^2 ≤ a+b := by
  have hb := (abs_nonneg _).trans hs
  have ha := (abs_nonneg _).trans hd
  have lo := (abs_le.mp hd).1
  have hi := (abs_le.mp hd).2
  have hdiff : |P^2-x^2| ≤ a+b := by
    apply abs_le.mpr
    constructor
    · nlinarith only [lo,sq_nonneg T,hb]
    · rw [abs_mul] at hs
      rcases le_total |T| |P| with h | h
      · nlinarith only [hi,mul_le_mul_of_nonneg_right h (abs_nonneg T),hs,sq_abs T]
      · nlinarith only [mul_le_mul_of_nonneg_left h (abs_nonneg P),hs,sq_abs P,ha,sq_nonneg x]
  rcases le_total |P| x with h | h
  · have hp := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hp
    rw [abs_of_nonpos (sub_nonpos.mpr hp)] at hdiff
    nlinarith only [hdiff,mul_le_mul_of_nonneg_left h (abs_nonneg P),sq_abs P]
  · have hp := pow_le_pow_left₀ hx h 2
    rw [sq_abs] at hp
    rw [abs_of_nonneg (sub_nonneg.mpr hp)] at hdiff
    nlinarith only [hdiff,mul_le_mul_of_nonneg_right h hx,sq_abs P]

lemma sign_persistence (P T β e : ℕ → ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hinit : 0 ≤ P 0) (hgap : ∀ k ≤ N, 3*δ^2 ≤ P k^2-T k^2)
    (hb : ∀ k < N, |β k| ≤ 1/2) (he : ∀ k < N, |e k| ≤ δ/4)
    (hp : ∀ k < N, P (k+1) = P k+β k*T k+e k) : 0 ≤ P N := by
  have keep (j : ℕ) (hj : j ≤ N) : 0 ≤ P j := by
    induction j with
    | zero => exact hinit
    | succ k ih =>
      have hk : k < N := by omega
      have hh := ih (by omega)
      have hD := hgap k hk.le
      have hT : |T k| ≤ P k := by nlinarith only [hh,sq_abs (T k),hD,sq_nonneg δ]
      have hP : δ ≤ P k := by nlinarith only [hD,sq_nonneg (T k),sq_nonneg δ,hh,hδ]
      have hx := mul_le_mul (hb k hk) hT (abs_nonneg (T k)) (by norm_num : (0:ℝ) ≤ 1/2)
      have hv := neg_abs_le (β k*T k)
      rw [abs_mul] at hv
      rw [hp k hk]
      linarith only [hδ,hP,hx,hv,(abs_le.mp (he k hk)).1]
  exact keep N le_rfl

lemma close_on_quiet_step (P T β e ξ : ℕ → ℝ) (N : ℕ) (sign δ : ℝ)
    (hsign : |sign| = 1) (hδ : 0 < δ) (hinit : 0 ≤ sign*P 0) (hx : 0 ≤ ξ N)
    (hmono : ∀ k ≤ N, ξ N ≤ ξ k)
    (hd : ∀ k ≤ N, |P k^2-T k^2-ξ k^2| ≤ δ^2)
    (hb : ∀ k < N, |β k| ≤ 1/2) (he : ∀ k < N, |e k| ≤ δ/4)
    (hp : ∀ k < N, P (k+1) = P k+β k*T k+e k) (hprod : |P N*T N| ≤ δ^2) :
    |P N-sign*max δ (ξ N)| ≤ 7*δ := by
  have hs : sign^2 = 1 := by nlinarith only [sq_abs sign,congrArg (fun x : ℝ => x^2) hsign]
  have H := absolute_orientation (P N) (T N) (ξ N) (δ^2) (δ^2) hx (hd _ le_rfl) hprod
  have hh : |(|P N|-ξ N)| ≤ 2*δ := by
    nlinarith only [sq_abs (|P N|-ξ N),H,abs_nonneg (|P N|-ξ N),hδ,sq_pos_of_pos hδ]
  rcases le_total (ξ N) (2*δ) with h | h
  · apply (abs_sub _ _).trans
    rw [abs_mul,hsign,one_mul,abs_of_nonneg (hδ.le.trans (le_max_left _ _))]
    have hm : max δ (ξ N) ≤ 2*δ := max_le (by linarith only [hδ]) h
    linarith only [hm,h,(abs_le.mp hh).2,hδ]
  · have hg (k : ℕ) (hk : k ≤ N) : 3*δ^2 ≤ (sign*P k)^2-(sign*T k)^2 := by
      simp only [mul_pow,hs,one_mul]
      have hxl : 2*δ ≤ ξ k := h.trans (hmono k hk)
      nlinarith only [(abs_le.mp (hd k hk)).1,pow_le_pow_left₀ (by positivity : 0 ≤ 2*δ) hxl 2]
    have hOrient := sign_persistence (fun k => sign*P k) (fun k => sign*T k) β
      (fun k => sign*e k) N δ hδ hinit hg hb (fun k hk => by simpa [abs_mul,hsign] using he k hk)
      (fun k hk => by rw [hp k hk]; ring)
    rw [max_eq_right (show δ ≤ ξ N by linarith only [h,hδ])]
    have hz : sign*P N = |P N| := by
      rw [← abs_of_nonneg hOrient,abs_mul,hsign,one_mul]
    have heq : |P N-sign*ξ N| = |(|P N|-ξ N)| := by
      have alg : sign*P N-ξ N = sign*(P N-sign*ξ N) := by linear_combination ξ N * hs
      rw [← hz,alg,abs_mul,hsign,one_mul]
    linarith only [heq,hh,hδ]

end LongTails.Proofs.BrightnessOrientation

namespace LongTails.Proofs.BrightnessFirstFitGuard

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)
open LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry (axis_norm)
open LongTails.Proofs.BrightnessFirstFitParameters
open LongTails.Proofs.BrightnessScaledCoordinates
open LongTails.Proofs.BrightnessTrajectoryBounds

structure Envelope (p : Params) (x : Images p) (c : Scales) : Prop where
  horizon : 1 ≤ c.H
  cap : ∀ k ≤ c.H, let s := path p x c.κ k
    |s.P| ≤ 2+|p.P| ∧ |s.T| ≤ 2+|p.P| ∧ |s.Q-p.Q| ≤ c.δ/4 ∧ ‖s.w‖ ≤ radius p c
  growth : ∀ k < c.H, let s := path p x c.κ k
    let next := path p x c.κ (k+1)
    let z := meanRow p x s
    let β := c.κ*brightness z
    let e := kick p c.κ s z
    max (next.P^2) (next.T^2) ≤ max (s.P^2) (s.T^2)+BrightnessFirstFitParameters.growth p c ∧
      |2*(s.P+β*s.T)*e+e^2| ≤ BrightnessFirstFitParameters.growth p c ∧ |e| ≤ error p c

lemma initial_norm (p : Params) : ‖(initial p).w‖ ≤ ‖p.readout‖ := by
  have hinner : ⟪axis p.d,centered p.readout⟫ = 0 := centered_orthogonal p.d.property _
  have hh := norm_add_sq_real (⟪axis p.d,p.readout⟫ • axis p.d) (centered p.readout)
  rw [real_inner_smul_left,hinner,mul_zero,mul_zero,add_zero,
    show ⟪axis p.d,p.readout⟫ • axis p.d+centered p.readout = p.readout by unfold centered; abel] at hh
  change ‖centered p.readout‖ ≤ _
  nlinarith only [hh,sq_nonneg ‖⟪axis p.d,p.readout⟫ • axis p.d‖,norm_nonneg p.readout,
    norm_nonneg (centered p.readout)]

lemma initial_brightness (p : Params) : |(initial p).T| ≤ ‖p.readout‖/p.R^2 := by
  change |⟪axis p.d,p.readout⟫/p.R^2| ≤ _
  rw [abs_div,abs_of_nonneg (sq_nonneg p.R)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hn : ‖axis p.d‖ = 1 := axis_norm p.d.property
  simpa only [hn,one_mul] using abs_real_inner_le_norm (axis p.d) p.readout

lemma envelope (p : Params) (x : Images p) (valid : spec.valid p) (G : Geometry p x) :
    Envelope p x (scales p) := by
  let c := scales p
  have h : Tuning p c := tuning p valid
  have κ := h.κpos
  have U := h.Upos
  have Γ := h.Γpos
  have M := h.Mpos
  have J := h.Jpos
  have μ := h.μpos
  have δ := h.δpos
  have V : 0 < c.V := by linarith only [h.Vge]
  have R : 0 < p.R := by linarith only [h.Rlarge]
  have hH : 1 ≤ c.H := by
    have hn : 0 < 32*(p.n:ℝ)*c.V^2*c.M/(c.κ*c.Γ) := by positivity
    exact Nat.one_le_iff_ne_zero.mpr (fun he => by simpa [he] using (hn.trans_le h.budget).ne')
  have H : 1 ≤ (c.H:ℝ) := by exact_mod_cast hH
  have hW : 0 ≤ radius p c := by unfold radius; positivity
  have hε : 0 ≤ error p c := by unfold error; positivity
  have hg : 0 ≤ growth p c := by unfold growth; positivity
  have ⟨hsm,hδJ,hδ,hf⟩ := small_tunings h
  have hc : c.κ*p.D ≤ 1 := by
    nlinarith only [hsm,h.Γle,mul_nonneg (mul_nonneg κ.le h.Dpos.le) U.le]
  obtain ⟨hq,_,ht⟩ := scale_remainders p valid
  change (c.H:ℝ)*error p c ≤ c.δ/4 at hq
  change (‖p.readout‖/p.R^2)^2 + c.H*growth p c +
    2*(1+c.U*radius p c)/(p.μ*p.R^2)+(c.V*c.M/p.R)^2 ≤ c.δ^2 at ht
  have he' : error p c ≤ 1 := by nlinarith only [hq,hδ,mul_le_mul_of_nonneg_right H hε]
  have ho : 0 ≤ 2*(1+c.U*radius p c)/(p.μ*p.R^2) := by positivity
  have hgap : (‖p.readout‖/p.R^2)^2+c.H*growth p c ≤ 1 := by
    nlinarith only [ht,ho,sq_nonneg (c.V*c.M/p.R),pow_le_pow_left₀ δ.le hδ 2]
  have hzero := pow_le_pow_left₀ (abs_nonneg _) (initial_brightness p) 2
  rw [sq_abs] at hzero
  have hinit : max (p.P^2) ((initial p).T^2)+c.H*growth p c ≤ (2+|p.P|)^2 := by
    rcases max_cases (p.P^2) ((initial p).T^2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith only [hgap,hzero,sq_nonneg (‖p.readout‖/p.R^2),sq_abs p.P,
      abs_nonneg p.P,sq_nonneg p.P]
  have hcap : max (|p.Q|+1) (2+|p.P|)*p.J ≤ c.U := by
    rw [h.Ueq,mul_comm p.J]
    apply mul_le_mul_of_nonneg_right _ J.le
    apply max_le <;> linarith only [abs_nonneg p.P,abs_nonneg p.Q]
  have S := guard p x G c.κ c.U (2+|p.P|) (radius p c) (error p c) (growth p c) c.H κ.le R μ.le
    J.le hcap U.le (by positivity) (by unfold radius; nlinarith only [initial_norm p])
    le_rfl hε he' hc le_rfl hg hinit (by linarith only [hq,hδ])
  have caps (k : ℕ) (hk : k ≤ c.H) :
      let s := path p x c.κ k
      |s.P| ≤ 2+|p.P| ∧ |s.T| ≤ 2+|p.P| ∧ |s.Q-p.Q| ≤ c.δ/4 ∧ ‖s.w‖ ≤ radius p c := by
    let s := path p x c.κ k
    obtain ⟨h1,h2,h3⟩ := S k hk
    have hn : (k:ℝ) ≤ c.H := by exact_mod_cast hk
    have hbound : max (s.P^2) (s.T^2) ≤ (2+|p.P|)^2 := by
      nlinarith only [h1,hinit,mul_le_mul_of_nonneg_right hn hg]
    refine ⟨?_,?_,h2.trans ((mul_le_mul_of_nonneg_right hn hε).trans hq),?_⟩
    · nlinarith only [hbound,le_max_left (s.P^2) (s.T^2),sq_abs s.P,abs_nonneg s.P,abs_nonneg p.P]
    · nlinarith only [hbound,le_max_right (s.P^2) (s.T^2),sq_abs s.T,abs_nonneg s.T,abs_nonneg p.P]
    · unfold radius
      nlinarith only [h3,initial_norm p,mul_le_mul_of_nonneg_right hn (mul_nonneg κ.le U.le)]
  refine ⟨hH,caps,?_⟩
  intro k hk
  let s := path p x c.κ k
  obtain ⟨hp,hT,hQ,hw⟩ := caps k hk.le
  have hQa : |s.Q| ≤ |p.Q|+1 := by
    have hh := abs_sub_le s.Q p.Q 0
    simp only [sub_zero] at hh
    linarith only [hh,hQ,hδ]
  have UU := (mul_le_mul_of_nonneg_right (max_le_max hQa hp) J.le).trans hcap
  obtain ⟨h1,h2,_,_,he⟩ := step_bounds p x G s c.κ _ _ _ _ κ.le R μ.le J.le
    (path_centered p x c.κ k) hw hp hT UU hc le_rfl he'
  exact ⟨h1,h2,he⟩

end LongTails.Proofs.BrightnessFirstFitGuard
