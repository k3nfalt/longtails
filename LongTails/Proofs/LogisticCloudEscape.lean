import LongTails.Proofs.LogisticCloudEntry

open LongTails.Setups.LogisticDefectCloud
open LongTails.Proofs.LogisticCloudCone
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudAlignment
open LongTails.Proofs.LogisticCloudModel
open LongTails.Proofs.LogisticCloudBatch
open LongTails.Proofs.LogisticCloudTrajectory
open LongTails.Proofs.LogisticCloudWarmup
open LongTails.Proofs.LogisticCloudTuning
open LongTails.Proofs.LogisticCloudEntryBounds
open LongTails.Proofs.LogisticCloudEntry

open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open scoped RealInnerProductSpace

namespace LongTails.Proofs.LogisticCloudEscape

variable {p : Params} {D : Data p} (G : Geometry p D)

noncomputable def orientation (z : ℝ) : ℝ := if 0 ≤ z then 1 else -1

lemma orientation_spec (z : ℝ) : (orientation z)^2 = 1 ∧ orientation z*z = |z| := by
  dsimp [orientation]
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

set_option maxHeartbeats 3000000 in
lemma entry (hp : spec.valid p) (w : Weights p.d) (hw : ‖w‖ = radius p)
    (hP : projectionSize p*radius p ≤ |(projections G w).1|)
    (hT : projectionSize p*radius p ≤ |(projections G w).2|) :
    let W := (gradientStep G (rate p))^[entryTime p] w
    ∃ s t : ℝ, s^2=1 ∧ t^2=1 ∧
      let x := chart G s t W
      Cone p.a x ∧ x.q ≤ 0 ∧ 320*radius p ≤ p.μ*mass x ∧ 64*radius p ≤ p.μ*x.v ∧
        radius p ≤ mass x ∧ amplitude x ≤ 64*Real.sqrt p.a ∧ ‖transverse G W‖ ≤ radius p := by
  let η := rate p
  let g := 1+η*p.μ/4
  let n := entryTime p
  let F := g^n
  let b := small p
  let κ := projectionSize p
  let r := radius p
  let X := fun j => (gradientStep G η)^[j] w
  let Y := fun j : ℕ => g^j • growing (axis G) G.v w
  have ⟨hb,hb',hκ,hκ',hF,_,_,hsize,hK,hgain,hangle⟩ := tuning_facts p hp
  change r*F ≤ 2*b at hsize
  change 256*r^3/p.μ*F^2 ≤ p.a*κ*r/128 at hK
  change 4096 ≤ p.μ*κ*F at hgain
  change 4096 ≤ p.a*κ*F at hangle
  change 1 ≤ F at hF
  change 0 < κ at hκ
  change κ ≤ 1 at hκ'
  have hμ : 0 < p.μ := (scales p hp).hμ
  have hμ' : p.μ ≤ 1/10 := (scales p hp).hμ'
  have ha : 0 < p.a := (scales p hp).ha
  have ha' : p.a ≤ 1/16 := (scales p hp).ha'
  have hη : 0 < η := (scales p hp).hη
  have htune : η*(p.a+p.μ) ≤ 1/2^48 := (scales p hp).tune
  have hr : 0 < r := (tiny p hp).2.2.1
  have hsm : b ≤ p.a/2^20 := (tiny p hp).2.1
  have hδ : η*p.μ/4 ≤ 1 := by nlinarith [mul_pos hη ha]
  have hg : 1 ≤ g := by dsimp [g]; nlinarith [mul_pos hη hμ]
  have hcoef : p.a*κ ≤ 1 := by nlinarith [mul_le_mul ha' hκ' hκ.le (by norm_num : (0:ℝ) ≤ 1/16)]
  let E := 8*r+p.a*κ*r*F/128
  have herr (j : ℕ) (hj : j ≤ n) : ‖X j-Y j‖ ≤ 8*r+p.a*κ*r*g^j/128 := by
    have hpow : g^j ≤ F := pow_le_pow_right₀ hg hj
    have hk := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans hg) _) hpow 2)
      (show 0 ≤ 256*r^3/p.μ by positivity)
    have hc : 256*r^3/p.μ*(g^j)^2 ≤ r := by
      nlinarith only [hk,hK,mul_le_mul_of_nonneg_right hcoef hr.le,hr.le]
    have HE := aligned G η r hη hr.le hμ (by linarith) ha.le (by linarith) w hw.le j hδ hc
    change ‖X j-Y j‖ ≤ _ at HE
    have hh := mul_le_mul_of_nonneg_right (hk.trans hK) (pow_nonneg (zero_le_one.trans hg) j)
    nlinarith only [HE,hh]
  have hnorm (j : ℕ) (hj : j ≤ n) : ‖X j‖ ≤ 36*b := by
    have hpow : g^j ≤ F := pow_le_pow_right₀ hg hj
    have hn := norm_sub_norm_le (X j) (Y j)
    have hy : ‖Y j‖ ≤ 9*r*g^j := by
      rw [show ‖Y j‖ = g^j*‖growing (axis G) G.v w‖ by
        simp [Y,norm_smul,abs_of_nonneg (zero_le_one.trans hg)]]
      have H := growing_bound G hp w
      rw [hw] at H
      nlinarith only [mul_le_mul_of_nonneg_left H (pow_nonneg (zero_le_one.trans hg) j)]
    have hrj := mul_le_mul_of_nonneg_left (one_le_pow₀ hg (n := j)) hr.le
    have hpos := mul_nonneg hr.le (pow_nonneg (zero_le_one.trans hg) j)
    nlinarith only [hpos,hrj,hn,hy,herr j hj,mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg hr.le (pow_nonneg (zero_le_one.trans hg) j)),
      mul_le_mul_of_nonneg_left hpow hr.le,mul_le_mul_of_nonneg_left hF hr.le,hsize]
  have htrans (j : ℕ) (hj : j ≤ n) : ‖transverse G (X j)‖ ≤ r := by
    induction j with
    | zero => exact (norm_transverse_le G w).trans hw.le
    | succ j ih =>
      have HH := hnorm j (by omega)
      have hlocal (i) : η/2*‖localFeature G (X j) i‖^2 ≤ 8 := by
        obtain ⟨h₁,h₂,_⟩ := bounds (X j)
        have hn := local_norm G (X j) i
        have hsq := pow_le_pow_left₀ (norm_nonneg _) (show ‖localFeature G (X j) i‖ ≤ 72*b by linarith) 2
        have hb₂ : b^2 ≤ p.a := by nlinarith [mul_le_mul_of_nonneg_right hb' hb.le]
        nlinarith only [mul_le_mul_of_nonneg_left hsq hη.le,mul_le_mul_of_nonneg_left hb₂ hη.le,
          htune,mul_nonneg hη.le hμ.le]
      exact (transverse_nonexpansive G η hη.le (X j) hlocal).trans (ih (by omega)) |>.trans'
        (by rw [show X (j+1) = gradientStep G η (X j) from Function.iterate_succ_apply' ..])
  let s := orientation ((projections G w).1)
  let t := orientation ((projections G w).2)
  let P := F*|(projections G w).1|
  let T := F*|(projections G w).2|
  have Hs := orientation_spec ((projections G w).1)
  have Ht := orientation_spec ((projections G w).2)
  have hp' : κ*r*F ≤ P := by
    dsimp only [P]; nlinarith only [mul_le_mul_of_nonneg_right hP (zero_le_one.trans hF)]
  have ht' : κ*r*F ≤ T := by
    dsimp only [T]; nlinarith only [mul_le_mul_of_nonneg_right hT (zero_le_one.trans hF)]
  have hP₀ : 0 < P := (mul_pos (mul_pos hκ hr) (zero_lt_one.trans_le hF)).trans_le hp'
  have hT₀ : 0 < T := (mul_pos (mul_pos hκ hr) (zero_lt_one.trans_le hF)).trans_le ht'
  have heP : E ≤ p.a*P/64 := by
    dsimp only [E]
    nlinarith only [mul_le_mul_of_nonneg_right hangle hr.le,mul_le_mul_of_nonneg_left hp' ha.le,
      mul_nonneg (mul_nonneg (mul_nonneg ha.le hκ.le) hr.le) (zero_le_one.trans hF)]
  have heT : E ≤ p.a*T/64 := by
    dsimp only [E]
    nlinarith only [mul_le_mul_of_nonneg_right hangle hr.le,mul_le_mul_of_nonneg_left ht' ha.le,
      mul_nonneg (mul_nonneg (mul_nonneg ha.le hκ.le) hr.le) (zero_le_one.trans hF)]
  have hfp : 4096*r ≤ p.μ*P := by
    nlinarith only [mul_le_mul_of_nonneg_right hgain hr.le,mul_le_mul_of_nonneg_left hp' hμ.le]
  have hft : 4096*r ≤ p.μ*T := by
    nlinarith only [mul_le_mul_of_nonneg_right hgain hr.le,mul_le_mul_of_nonneg_left ht' hμ.le]
  let β := Real.sqrt (1-p.a^2)
  let z := chart G s t (X n)
  have hmode : chart G s t (Y n) = ⟨P,-p.a*P,β*P,T,T⟩ := by
    rw [chart_mode]
    dsimp only [P,T,s,t,F]
    have A (z : ℝ) : orientation z*(g^n*z) = g^n*|z| := by
      rw [mul_left_comm, (orientation_spec z).2]
    simp only [A,β]
  have gaps := coordinate_gap G s t Hs.1 Ht.1 (X n) (Y n)
  rw [hmode] at gaps
  obtain ⟨P₁,Q₁,U₁,T₁,V₁⟩ := gaps
  have HE : ‖X n-Y n‖ ≤ E := herr n le_rfl
  have hQ : |z.q+p.a*P| ≤ E := by simpa [z,sub_neg_eq_add,neg_mul] using Q₁.trans HE
  obtain ⟨hC,hq,hm,hv,hmp⟩ := numerical_entry ha ha' (scales p hp).hβ (scales p hp).hβ'
    hP₀ hT₀ hμ heP heT hfp hft z (P₁.trans HE) hQ (U₁.trans HE) (T₁.trans HE) (V₁.trans HE)
  have Habs (v : Features p.d) (h : ‖v‖=1) :
      |⟪v,readout (X n)⟫| ≤ ‖X n‖ := by
    simpa [h] using (abs_real_inner_le_norm v _).trans
      (mul_le_mul_of_nonneg_left (bounds (X n)).2.2 (norm_nonneg v))
  have hH : amplitude z ≤ 36*b := by
    apply max_le
    · have hsabs : |s| = 1 := by nlinarith [Hs.1,sq_abs s,abs_nonneg s]
      have H := le_abs_self z.u
      change s*_ ≤ |s*_| at H
      rw [abs_mul,hsabs,one_mul] at H
      exact (H.trans (Habs _ G.norm_u)).trans (hnorm n le_rfl)
    · have htabs : |t| = 1 := by nlinarith [Ht.1,sq_abs t,abs_nonneg t]
      have H := le_abs_self z.v
      change t*_ ≤ |t*_| at H
      rw [abs_mul,htabs,one_mul] at H
      exact (H.trans (Habs _ G.norm_v)).trans (hnorm n le_rfl)
  have hsqrt : p.a ≤ Real.sqrt p.a := by
    nlinarith [Real.sq_sqrt ha.le,Real.sqrt_nonneg p.a,
      mul_nonneg (show 0 ≤ 1-Real.sqrt p.a by
        linarith [Real.sqrt_le_one.mpr (show p.a ≤ 1 by linarith)]) (Real.sqrt_nonneg p.a)]
  refine ⟨s,t,Hs.1,Ht.1,hC,hq,hm,hv,?_,by linarith,htrans n le_rfl⟩
  nlinarith [mul_le_mul_of_nonneg_right hμ' hP₀.le]

end LongTails.Proofs.LogisticCloudEscape
