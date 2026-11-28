import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import LongTails.Proofs.BrightnessFirstFitForces

namespace LongTails.Proofs.BrightnessImbalanceOccupation

lemma dominant_energy (p t b : ℝ) (hb : b^2 ≤ 1) :
    max ((p+b*t)^2) ((t+b*p)^2) =
      max (p^2) (t^2)+2*b*p*t+b^2*min (p^2) (t^2) := by
  have h : (p+b*t)^2-(t+b*p)^2 = (1-b^2)*(p^2-t^2) := by ring
  rcases le_total (p^2) (t^2) with hpt | htp
  · have H : (p+b*t)^2 ≤ (t+b*p)^2 := by
      nlinarith only [h,mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hb) (sub_nonpos.mpr hpt)]
    rw [max_eq_right H,max_eq_right hpt,min_eq_left hpt]
    ring
  · have H : (t+b*p)^2 ≤ (p+b*t)^2 := by
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr htp)]
    rw [max_eq_left H,max_eq_left htp,min_eq_right htp]
    ring

lemma dominant_energy_forced (p t b u : ℝ) (hb : |b| ≤ 1) :
    max ((p+b*t+u)^2) ((t+b*p)^2) ≤
      max (p^2) (t^2) + 2*b*p*t + |b| * |b*p*t| +
        4*max |p| |t| * |u| + u^2 := by
  have hb2 : b^2 ≤ 1 := by nlinarith only [pow_le_pow_left₀ (abs_nonneg _) hb 2,sq_abs b]
  have hmin : min (p^2) (t^2) ≤ |p| * |t| := by
    rcases le_total |p| |t| with ht | hp
    · apply (min_le_left (p^2) (t^2)).trans
      nlinarith only [sq_abs p, mul_le_mul_of_nonneg_left ht (abs_nonneg p)]
    · apply (min_le_right (p^2) (t^2)).trans
      nlinarith only [sq_abs t, mul_le_mul_of_nonneg_right hp (abs_nonneg t)]
  have hm := dominant_energy p t b hb2
  have hlt : |p+b*t| ≤ 2*max |p| |t| := by
    have hsum := abs_add_le p (b*t)
    rw [abs_mul] at hsum
    nlinarith only [hsum,mul_le_mul_of_nonneg_right hb (abs_nonneg t),
      le_max_left |p| |t|,le_max_right |p| |t|]
  have hcost : 2*(p+b*t)*u ≤ 4*max |p| |t| * |u| := by
    have ha := le_abs_self ((p+b*t)*u)
    rw [abs_mul] at ha
    nlinarith only [ha,mul_le_mul_of_nonneg_right hlt (abs_nonneg u)]
  rw [abs_mul,abs_mul]
  have hprod : b^2*min (p^2) (t^2) ≤ |b| * (|b| * |p| * |t|) := by
    calc
      _ ≤ b^2*(|p| * |t|) := mul_le_mul_of_nonneg_left hmin (sq_nonneg b)
      _ = _ := by rw [← sq_abs b]; ring
  apply max_le
  · nlinarith only [hcost,hprod,hm,le_max_left ((p+b*t)^2) ((t+b*p)^2)]
  · have hn : 0 ≤ max |p| |t| := (abs_nonneg p).trans (le_max_left _ _)
    nlinarith only [mul_nonneg hn (abs_nonneg u),sq_nonneg u,hprod,hm,
      le_max_right ((p+b*t)^2) ((t+b*p)^2)]

end LongTails.Proofs.BrightnessImbalanceOccupation

namespace LongTails.Proofs.BrightnessDominantEnvelope

open BrightnessImbalanceOccupation

lemma one_step (p t b e R K W m ε : ℝ) (hb : |b| ≤ 1)
    (hp : |p| ≤ m) (ht : |t| ≤ m) (he : |e| ≤ ε) (he' : ε ≤ 1) (hR : 0 < R)
    (hwork : R^2*(b*p*t) ≤ K*W) (hKW : 0 ≤ K*W) :
    let step := 3*K*W/R^2 + (4*m+1)*ε
    max ((p+b*t+e)^2) ((t+b*p)^2) ≤ max (p^2) (t^2)+step ∧
      |2*(p+b*t)*e+e^2| ≤ step := by
  dsimp only
  have hε := (abs_nonneg e).trans he
  have hm := (abs_nonneg p).trans hp
  have he2 : e^2 ≤ ε := by
    nlinarith only [mul_le_mul he (he.trans he') (abs_nonneg e) hε,sq_abs e]
  have hm' := max_le hp ht
  have hforce : 4*max |p| |t| * |e| ≤ 4*m*ε := by
    nlinarith only [mul_le_mul hm' he (abs_nonneg e) hm]
  have hcost : 2*b*p*t+|b| * |b*p*t| ≤ 3*K*W/R^2 := by
    have hn := mul_le_mul_of_nonneg_right hb (abs_nonneg (b*p*t))
    have hr : 0 < R^2 := sq_pos_of_pos hR
    rcases le_total 0 (b*p*t) with h | h
    · rw [abs_of_nonneg h] at hn ⊢
      have hh : b*p*t ≤ K*W/R^2 := (le_div_iff₀ hr).mpr (by nlinarith only [hwork])
      rw [show 3*K*W/R^2 = 3*(K*W/R^2) by ring]
      nlinarith only [hn,hh]
    · rw [abs_of_nonpos h] at hn ⊢
      have hh : 0 ≤ 3*K*W/R^2 := div_nonneg (by nlinarith only [hKW]) hr.le
      nlinarith only [hn,h,hh]
  refine ⟨by linarith only [dominant_energy_forced p t b e hb,hforce,he2,hcost],?_⟩
  have hsum := abs_add_le p (b*t)
  rw [abs_mul] at hsum
  have hh : |p+b*t| ≤ 2*m := by
    nlinarith only [hsum,hp,ht,mul_le_mul_of_nonneg_right hb (abs_nonneg t)]
  have H := abs_add_le (2*(p+b*t)*e) (e^2)
  rw [abs_of_nonneg (sq_nonneg e),abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at H
  nlinarith only [H,he2,mul_le_mul hh he (abs_nonneg e) (show 0 ≤ 2*m by linarith),
    div_nonneg (show 0 ≤ 3*K*W by nlinarith only [hKW]) (sq_nonneg R)]

lemma bootstrap (P T Q W : ℕ → ℝ) (N : ℕ) (m ε δ a : ℝ)
    (hm : 0 ≤ m) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hinit : max ((P 0)^2) ((T 0)^2) + N*δ ≤ m^2) (hQ : N*ε ≤ 1)
    (hstep : ∀ k < N, |P k| ≤ m → |T k| ≤ m → |Q k-Q 0| ≤ 1 → W k ≤ W 0+k*a →
      max ((P (k+1))^2) ((T (k+1))^2) ≤ max ((P k)^2) ((T k)^2)+δ ∧
      |Q (k+1)-Q k| ≤ ε ∧ W (k+1) ≤ W k+a) :
    ∀ k ≤ N, max ((P k)^2) ((T k)^2) ≤ max ((P 0)^2) ((T 0)^2)+k*δ ∧
      |Q k-Q 0| ≤ k*ε ∧ W k ≤ W 0+k*a := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ N := by omega
    obtain ⟨hM,hq,hW⟩ := ih hk'
    have leN : (k:ℝ) ≤ N := by exact_mod_cast hk'
    have hcap : max (P k^2) (T k^2) ≤ m^2 := by
      nlinarith only [hM,hinit,mul_le_mul_of_nonneg_right leN hδ]
    have hpc : |P k| ≤ m := by nlinarith only [sq_abs (P k),le_max_left (P k^2) (T k^2),hcap,hm,abs_nonneg (P k)]
    have htc : |T k| ≤ m := by nlinarith only [sq_abs (T k),le_max_right (P k^2) (T k^2),hcap,hm,abs_nonneg (T k)]
    have hqc : |Q k-Q 0| ≤ 1 := hq.trans ((mul_le_mul_of_nonneg_right leN hε).trans hQ)
    obtain ⟨h1,h2,h3⟩ := hstep k (by omega) hpc htc hqc hW
    rw [Nat.cast_succ]
    refine ⟨by linarith only [hM,h1],?_,by linarith only [hW,h3]⟩
    linarith only [abs_sub_le (Q (k+1)) (Q k) (Q 0),h2,hq]

end LongTails.Proofs.BrightnessDominantEnvelope

namespace LongTails.Proofs.BrightnessTrajectoryBounds

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)
open LongTails.Proofs.BrightnessScaledCoordinates
open LongTails.Proofs.BrightnessScaledForces
open LongTails.Proofs.BrightnessFirstFitWork

noncomputable def meanRow (p : Params) (x : Images p) (s : State p.d) := mixture x (votes p x s)

noncomputable def kick (p : Params) (κ : ℝ) (s : State p.d) (z : Setups.TwoSampleQuadraticPerceptron.Features p.d) :=
  κ*⟪smooth z,s.w⟫/p.R^2

lemma step_bounds (p : Params) (x : Images p) (G : Geometry p x) (s : State p.d)
    (κ m U W ε : ℝ) (hκ : 0 ≤ κ) (hR : 0 < p.R) (hμ : 0 ≤ p.μ) (hJ : 0 ≤ p.J)
    (hw : ⟪axis p.d,s.w⟫ = 0) (hW : ‖s.w‖ ≤ W)
    (hp : |s.P| ≤ m) (ht : |s.T| ≤ m) (hU : max |s.Q| |s.P| * p.J ≤ U)
    (hc : κ*p.D ≤ 1) (hε : κ*p.J*W/p.R^2 ≤ ε) (hε' : ε ≤ 1) :
    let z := meanRow p x s
    let b := κ*brightness z
    let e := kick p κ s z
    let next := advance p κ s z
    let step := 3*κ*(1+U*W)/p.R^2+(4*m+1)*ε
    max (next.P^2) (next.T^2) ≤ max (s.P^2) (s.T^2)+step ∧
      |2*(s.P+b*s.T)*e+e^2| ≤ step ∧
      |next.Q-s.Q| ≤ ε ∧ ‖next.w‖ ≤ ‖s.w‖+κ*U ∧ |e| ≤ ε := by
  let z := meanRow p x s
  let g := votes p x s
  have hm := vote_mass p x s
  obtain ⟨hd,hA,hC⟩ := force_bounds p x G s
  change |brightness z| ≤ p.D at hd
  change ‖contrast z‖ ≤ p.J*mass p g at hA
  change ‖smooth z‖ ≤ p.J*mass p g at hC
  have hjg : p.J*mass p g ≤ p.J := by simpa using mul_le_mul_of_nonneg_left hm.2 hJ
  have perturb (y : Setups.TwoSampleQuadraticPerceptron.Features p.d) (hy : ‖y‖ ≤ p.J) :
      |κ*⟪y,s.w⟫/p.R^2| ≤ ε := by
    rw [abs_div,abs_mul,abs_of_nonneg hκ,abs_of_nonneg (sq_nonneg p.R)]
    apply le_trans _ hε
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hh := (abs_real_inner_le_norm y s.w).trans (mul_le_mul hy hW (norm_nonneg _) hJ)
    nlinarith only [mul_le_mul_of_nonneg_left hh hκ]
  have he : |kick p κ s z| ≤ ε := perturb _ (hC.trans hjg)
  have hb : |κ*brightness z| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg hκ]
    exact (mul_le_mul_of_nonneg_left hd hκ).trans hc
  have hU0 : 0 ≤ U := (mul_nonneg ((abs_nonneg s.Q).trans (le_max_left _ _)) hJ).trans hU
  have hW0 := (norm_nonneg _).trans hW
  have H := restoring_at p x G s hR hw
  change p.R^2*s.P*s.T*brightness z + |p.R^2*s.P*s.T| * p.μ ≤ _ at H
  have H' : p.R^2*((κ*brightness z)*s.P*s.T) ≤ κ*(1+U*W) := by
    have hh := mul_le_mul hU hW (norm_nonneg s.w) hU0
    have hz : p.R^2*s.P*s.T*brightness z ≤ 1+U*W := by
      linarith only [hh,H,mul_nonneg (abs_nonneg (p.R^2*s.P*s.T)) hμ]
    nlinarith only [mul_le_mul_of_nonneg_left hz hκ]
  obtain ⟨h1,h2⟩ := BrightnessDominantEnvelope.one_step s.P s.T _ _ p.R κ (1+U*W) m ε
    hb hp ht he hε' hR H' (by positivity)
  refine ⟨h1,h2,?_,?_,he⟩
  · change |s.Q+κ*⟪contrast z,s.w⟫/p.R^2-s.Q| ≤ _
    rw [add_sub_cancel_left]
    exact perturb _ (hA.trans hjg)
  · change ‖s.w+κ • readout s z‖ ≤ _
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hκ]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ hκ
    have Hread := readout_force p x G s g (fun i => Real.sigmoid_nonneg _)
    exact Hread.trans (by nlinarith only [mul_le_mul hU hm.2 hm.1 hU0])

lemma guard (p : Params) (x : Images p) (G : Geometry p x)
    (κ U m W ε cost : ℝ) (N : ℕ) (hκ : 0 ≤ κ) (hR : 0 < p.R)
    (hμ : 0 ≤ p.μ) (hJ : 0 ≤ p.J) (hU : max (|p.Q|+1) m * p.J ≤ U)
    (hU₀ : 0 ≤ U) (hm : 0 ≤ m) (hW : ‖(initial p).w‖+N*(κ*U) ≤ W)
    (hε : κ*p.J*W/p.R^2 ≤ ε) (hε₀ : 0 ≤ ε) (hε' : ε ≤ 1)
    (hc : κ*p.D ≤ 1) (hcost : 3*κ*(1+U*W)/p.R^2+(4*m+1)*ε ≤ cost)
    (hcost₀ : 0 ≤ cost) (hinit : max (p.P^2) ((initial p).T^2) + N*cost ≤ m^2)
    (hq : N*ε ≤ 1) :
    let S := path p x κ
    ∀ k ≤ N, max ((S k).P^2) ((S k).T^2) ≤
        max (p.P^2) ((initial p).T^2)+k*cost ∧
      |(S k).Q-p.Q| ≤ k*ε ∧ ‖(S k).w‖ ≤ ‖(initial p).w‖+k*(κ*U) := by
  let S := path p x κ
  apply BrightnessDominantEnvelope.bootstrap (fun k => (S k).P) (fun k => (S k).T)
    (fun k => (S k).Q) (fun k => ‖(S k).w‖) N m ε cost (κ*U)
    hm hε₀ hcost₀ hinit hq
  intro k hk hp ht hQ hw
  have hQa : |(S k).Q| ≤ |p.Q|+1 := by
    change |(S k).Q-p.Q| ≤ 1 at hQ
    have hh := abs_sub_le ((S k).Q) p.Q 0
    simp only [sub_zero] at hh
    linarith
  have hU' := (mul_le_mul_of_nonneg_right (max_le_max hQa hp) hJ).trans hU
  have hW' : ‖(S k).w‖ ≤ W := by
    change ‖(S k).w‖ ≤ ‖(initial p).w‖+k*(κ*U) at hw
    have hh : (k:ℝ) ≤ N := by exact_mod_cast hk.le
    nlinarith only [hw,hW,mul_le_mul_of_nonneg_right hh (mul_nonneg hκ hU₀)]
  obtain ⟨h1,_,h3,h4,_⟩ := step_bounds p x G (S k) κ m U W ε
    hκ hR hμ hJ (path_centered p x κ k) hW' hp ht hU' hc hε hε'
  exact ⟨h1.trans (by linarith only [hcost]),h3,h4⟩

end LongTails.Proofs.BrightnessTrajectoryBounds
