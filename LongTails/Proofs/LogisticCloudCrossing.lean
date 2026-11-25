import LongTails.Proofs.LogisticCloudTuning
import LongTails.Proofs.LogisticCloudTrajectory
import LongTails.Proofs.LogisticCloudHitting

open scoped RealInnerProductSpace BigOperators
open LongTails.Setups.LogisticDefectCloud
open LongTails.Proofs.LogisticCloudCone
open LongTails.Proofs.LogisticCloudTuning
open LongTails.Proofs.LogisticCloudDrift
open LongTails.Proofs.LogisticCloudHitting
open LongTails.Proofs.LogisticCloudModel
open LongTails.Proofs.LogisticCloudBatch
open LongTails.Proofs.LogisticCloudTrajectory
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudAverages

namespace LongTails.Proofs.LogisticCloudCrossing

variable {p : Params} {D : Data p} (G : Geometry p D)

def Correct (w : Weights p.d) : Prop :=
  0 < score G.e 0 w ∧ ∀ i, score (zcol G i) (ycol G i) w < 0

lemma overshoot {p q P Q η τ D : ℝ} (hp : 0 < p) (hq : q ≤ 0) (hP : 0 < P)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1) (hD : 0 < D) {E : ℝ}
    (hE : E ≤ 2*D) (hE₀ : 0 ≤ E)
    (hQ : Q = q + η/2*(Real.sigmoid (-(p*q))-(1+τ)*Real.sigmoid ((1+τ)*p*q-E))*p)
    (hc : η*p^2 ≤ 1) (hs : η*p*P ≤ 1/4) :
    (1+τ)*P*Q ≤ D/4 := by
  have hz := mul_nonpos_of_nonneg_of_nonpos hp.le hq
  have hneg := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1+τ by linarith) hz
  let b := Real.sigmoid ((1+τ)*p*q-E)
  have hgap := sigmoid_gap (show (1+τ)*p*q-E ≤ -(p*q) by linarith only [hz,hneg,hE₀])
  change Real.sigmoid _ - b ≤ _ at hgap
  have hb : 0 ≤ b := Real.sigmoid_nonneg _
  have hh : Real.sigmoid (-(p*q))-(1+τ)*b ≤ (E-(2+τ)*p*q)/4 := by
    nlinarith only [hgap,mul_nonneg hτ hb]
  have hsmall : η*(2+τ)*p^2 ≤ 8 := by
    nlinarith [mul_le_mul_of_nonneg_right hτ' (mul_nonneg hη (sq_nonneg p))]
  have hbound : Q ≤ η*p*E/8 := by
    rw [hQ]
    change q+η/2*(Real.sigmoid _ -(1+τ)*b)*p ≤ _
    nlinarith only [mul_le_mul_of_nonneg_right hh (mul_nonneg hη hp.le),
      mul_nonneg (neg_nonneg.mpr hq) (sub_nonneg.mpr hsmall)]
  have hw := mul_le_mul_of_nonneg_left hbound (mul_nonneg (show 0 ≤ 1+τ by linarith) hP.le)
  have hcoef : (1+τ)*(η*p*P) ≤ 1/2 := by
    nlinarith [mul_le_mul (show 1+τ ≤ 2 by linarith) hs (by positivity : 0 ≤ η*p*P)
      (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith only [hw,mul_le_mul_of_nonneg_right hcoef hE₀,hE,hD]

set_option maxHeartbeats 1600000 in
lemma next_point (hp : spec.valid p) (s t : ℝ) (hs : s^2=1) (ht : t^2=1) (w : Weights p.d)
    (r : ℝ) (hr : ‖transverse G w‖ ≤ r)
    (hc : Cone p.a (chart G s t w)) (hq : (chart G s t w).q ≤ 0)
    (hH : amplitude (chart G s t w) ≤ 2^16*Real.sqrt p.a)
    (hfloor : 64*r ≤ p.μ*(chart G s t w).p) (vfloor : 64*r ≤ p.μ*(chart G s t w).v) :
    let W := gradientStep G (rate p) w
    let X := chart G s t W
    Progress (scales p hp) (chart G s t w) X ∧ ‖transverse G W‖ ≤ r ∧ (0 < X.q → Correct G W) := by
  let S := scales p hp
  let x := chart G s t w
  let W := gradientStep G (rate p) w
  let X := chart G s t W
  let β := Real.sqrt (1-p.a^2)
  let η := rate p
  let D₀ := p.μ*signal β x
  let τ := p.μ*p.a
  let b := avgWeight G w
  let l := slowCoeff G η w
  let h := hCoeff G η w
  let e := err G w s (p.μ*β) G.z
  let f := err G w t p.μ G.y
  change Cone p.a x at hc
  change x.q ≤ 0 at hq
  change _ ≤ p.μ*x.p at hfloor
  change _ ≤ p.μ*x.v at vfloor
  have hμ : 0 < p.μ := S.hμ
  have ha : 0 < p.a := S.ha
  have ha' : p.a ≤ 1/16 := S.ha'
  have hβ : 4/5 ≤ β := S.hβ
  have hβ' : β ≤ 1 := S.hβ'
  have hβ₀ : 0 < β := by linarith
  have hη : 0 < η := S.hη
  have tune : η*(p.a+p.μ) ≤ 1/2^48 := S.tune
  have hδ : η*p.μ ≤ 1 := by nlinarith [mul_pos hη ha]
  have hH' : (amplitude x)^2 ≤ 2^32*p.a := by
    have HH := pow_le_pow_left₀ (amplitude_bounds hc).1.le hH 2
    nlinarith only [HH,Real.sq_sqrt ha.le]
  have hnorm := norm_nonneg (transverse G w)
  have hr₀ : 0 ≤ r := hnorm.trans hr
  have he₀ := err_bound G s hs w (p.μ*β) (mul_pos hμ hβ₀) G.z G.bound_z (fun i =>
    ⟨(G.orthogonal i _ (by simp : G.e ∈ ({G.e,G.u,G.v} : Set _))).1,
    (G.orthogonal i _ (by simp : G.u ∈ ({G.e,G.u,G.v} : Set _))).1,
    (G.orthogonal i _ (by simp : G.v ∈ ({G.e,G.u,G.v} : Set _))).1⟩)
  have hf₀ := err_bound G t ht w p.μ hμ G.y G.bound_y (fun i =>
    ⟨(G.orthogonal i _ (by simp : G.e ∈ ({G.e,G.u,G.v} : Set _))).2,
    (G.orthogonal i _ (by simp : G.u ∈ ({G.e,G.u,G.v} : Set _))).2,
    (G.orthogonal i _ (by simp : G.v ∈ ({G.e,G.u,G.v} : Set _))).2⟩)
  have he : |e| ≤ x.p/8 := by
    apply he₀.trans
    rw [div_le_iff₀ (mul_pos hμ hβ₀)]
    nlinarith [mul_le_mul_of_nonneg_right hβ (mul_nonneg hμ.le hc.1.le)]
  have hf : |f| ≤ x.v/8 := by
    apply hf₀.trans
    rw [div_le_iff₀ hμ]
    linarith
  have hu := signal_bounds hc hq hβ hβ'
  have hD : 0 < D₀ := mul_pos hμ (by nlinarith [hu.1,sq_pos_of_pos (amplitude_bounds hc).1])
  let d := fun i => D₀-⟪localFeature G w i,transverse G w⟫
  have hd (i) : D₀/2 ≤ d i ∧ d i ≤ 2*D₀ := by
    have H := margin_noise G s t hs ht w hμ hβ hc (by linarith) (by linarith) i
    change |⟪_,_⟫| ≤ D₀/4 at H
    dsimp [d]
    exact ⟨by linarith [(abs_le.mp H).2],by linarith [(abs_le.mp H).1]⟩
  obtain ⟨E,⟨hE,hE'⟩,hB⟩ := effective_deficit ((1+τ)*x.p*x.q) D₀ d hD.le hd
  have hsum (i) : score (zcol G i) (ycol G i) w = (1+τ)*x.p*x.q-d i := by
    rw [(score_components G s t hs ht w i).2]
    dsimp [x,d,D₀,β,τ]; ring
  have hb : Real.sigmoid ((1+τ)*x.p*x.q-E) = b := by
    simpa only [b,avgWeight,bweight,hsum] using hB
  have hh : h = drift S x E := by
    dsimp only [h,hCoeff,drift]
    rw [(score_components G s t hs ht w 0).1]
    change η/2*(_-(1+τ)*b) = η/2*(_-(1+τ)*Real.sigmoid ((1+τ)*x.p*x.q-E))
    rw [hb]
  have hl : l = weight S x E := by
    change η/2*p.μ*b = η/2*p.μ*Real.sigmoid ((1+τ)*x.p*x.q-E)
    rw [hb]
  have hE₀ : 0 ≤ E := by linarith
  have hEs : E ≤ 8*p.μ*(amplitude x)^2 := by
    dsimp [D₀] at hE'
    nlinarith only [hE',mul_le_mul_of_nonneg_left hu.2 hμ.le]
  obtain ⟨hab,hlo,hl₀,hl',hcases⟩ := coefficients S x E hc hq hE₀ hEs hH'
  rw [← hh] at hab hlo hcases
  rw [← hl] at hlo hl₀ hl' hcases
  change -(5/4)*p.a*(β*l) ≤ h at hlo
  change 2*l ≤ η*p.μ at hl'
  have hj₀ := mul_nonneg hβ₀.le hl₀
  have hj' := mul_le_mul_of_nonneg_right hβ' hl₀
  have hstep : X = LogisticCloudCone.step x h (β*l) l e f := chart_update G η s t w hμ hβ₀
  obtain ⟨hC,hM,hP,hV⟩ := advance ha.le ha' hc hq hab hlo hj₀ (by linarith)
    hl₀ (by linarith) he hf
  rw [← hstep] at hC hM hP hV
  have hA := amplitude_step (h := h) (e := e) (f := f) hc hj₀ hl₀
    (show 2*(β*l) ≤ η*p.μ by linarith) hl'
  rw [← hstep] at hA
  have hHη : η*(amplitude x)^2 ≤ 1/2^16 := by
    nlinarith [mul_le_mul_of_nonneg_left hH' hη.le,mul_nonneg hη.le hμ.le]
  have hloc (i) : η/2*‖localFeature G w i‖^2 ≤ 8 := by
    obtain ⟨h₁,h₂⟩ := texture_small G s t hs ht w
    have H := local_norm G w i
    change _ = |x.p| at h₁
    change _ = |x.t| at h₂
    have hT : 0 ≤ x.t := by linarith [hc.2.2.2.2.2.1,hc.2.2.2.2.1]
    rw [h₁,h₂,abs_of_pos hc.1,abs_of_nonneg hT] at H
    obtain ⟨_,H₁,H₂⟩ := amplitude_bounds hc
    have HH := pow_le_pow_left₀ (norm_nonneg _) (show ‖localFeature G w i‖ ≤ 4*amplitude x by linarith) 2
    nlinarith only [mul_le_mul_of_nonneg_left HH hη.le,hHη]
  have hW : ‖transverse G W‖ ≤ r := (transverse_nonexpansive G η hη.le w hloc).trans hr
  change Progress S x X ∧ _ ∧ _
  refine ⟨⟨hC,?_,hV,hA.1,hA.2,?_⟩,hW,?_⟩
  · rw [hstep] at hM ⊢
    exact mass_growth ha' hc hq hj₀ (mul_pos hη hμ).le he hcases hM
  · intro H
    have Hs := pow_le_pow_left₀ (by positivity : 0 ≤ 64*Real.sqrt S.a) H 2
    have HE : 256*(S.μ*S.a) ≤ E := by
      change 64*Real.sqrt p.a ≤ _ at H
      change (64*Real.sqrt p.a)^2 ≤ _ at Hs
      rw [mul_pow,Real.sq_sqrt ha.le] at Hs
      dsimp only [D₀] at hE
      change 256*(p.μ*p.a) ≤ E
      nlinarith only [hE,mul_le_mul_of_nonneg_left hu.1 hμ.le,mul_le_mul_of_nonneg_left Hs hμ.le,mul_nonneg hμ.le ha.le]
    have HI := high_drift S x E hc.1.le hq HE
    rw [← hh] at HI
    rw [hstep]
    dsimp only [LogisticCloudCone.step]
    linarith [mul_le_mul_of_nonneg_right HI hc.1.le]
  · intro hQ
    have hnext := score_components G s t hs ht W
    refine ⟨(hnext 0).1 ▸ mul_pos hC.1 hQ,?_⟩
    intro i
    have htex := margin_noise G s t hs ht W hμ hβ hC
      (by nlinarith [mul_le_mul_of_nonneg_left hP hμ.le])
      (by nlinarith [mul_le_mul_of_nonneg_left hV hμ.le]) i
    change |⟪_,_⟫| ≤ p.μ*signal β X/4 at htex
    have hU : x.u ≤ X.u := by
      rw [hstep]; dsimp [LogisticCloudCone.step]; linarith [mul_nonneg hj₀ hc.1.le]
    have hT : x.t ≤ X.t := by
      rw [hstep]; dsimp [LogisticCloudCone.step]
      nlinarith [mul_nonneg hl₀ (show 0 ≤ x.v+f by linarith [(abs_le.mp hf).1,hc.2.2.2.2.1])]
    have ut : 0 ≤ x.u := by linarith [hc.1,hc.2.2.1]
    have tv : 0 ≤ x.t := by linarith [hc.2.2.2.2.2.1,hc.2.2.2.2.1]
    have hD' : D₀/2 ≤ p.μ*signal β X := by
      have HU := mul_le_mul hP hU ut hC.1.le
      have HT := mul_le_mul hT hV hc.2.2.2.2.1.le (tv.trans hT)
      dsimp [D₀,signal]
      nlinarith only [mul_le_mul_of_nonneg_left HU (mul_nonneg hμ.le hβ₀.le),
        mul_le_mul_of_nonneg_left HT hμ.le,mul_nonneg (mul_nonneg hμ.le tv) hc.2.2.2.2.1.le]
    have HT' : amplitude X ≤ 2*amplitude x := by
      nlinarith [hA.2,mul_le_mul_of_nonneg_right hδ (amplitude_bounds hc).1.le]
    have hpp := (amplitude_bounds hc).2.1
    have hPP := (amplitude_bounds hC).2.1
    have H₁ := mul_le_mul hpp hpp hc.1.le (by linarith : 0 ≤ 2*amplitude x)
    have H₂ := mul_le_mul hpp (show X.p ≤ 4*amplitude x by linarith) hC.1.le
      (by linarith : 0 ≤ 2*amplitude x)
    have hQeq : X.q = x.q+η/2*(Real.sigmoid (-(x.p*x.q))-
        (1+τ)*Real.sigmoid ((1+τ)*x.p*x.q-E))*x.p := by
      rw [hstep]; dsimp only [LogisticCloudCone.step]; rw [hh]; rfl
    have HH := overshoot hc.1 hq hC.1 hη.le (mul_nonneg hμ.le ha.le)
      (by have sm : p.μ ≤ 1/10 := S.hμ'
          nlinarith [mul_le_mul sm ha' ha.le (by norm_num : (0:ℝ) ≤ 1/10)])
      hD hE' hE₀ hQeq (by nlinarith [mul_le_mul_of_nonneg_left H₁ hη.le])
      (by nlinarith [mul_le_mul_of_nonneg_left H₂ hη.le])
    rw [(hnext i).2]
    change (1+τ)*X.p*X.q-p.μ*signal β X+_ < 0
    nlinarith only [HH,hD',hD,(abs_le.mp htex).2]

end LongTails.Proofs.LogisticCloudCrossing
