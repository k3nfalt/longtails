import LongTails.Proofs.LogisticCloudEscape
import LongTails.Proofs.LogisticCloudCrossing
import LongTails.Proofs.LogisticCloudHorizon

open scoped RealInnerProductSpace
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudCone
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudModel
open LongTails.Proofs.LogisticCloudExecution
open LongTails.Proofs.LogisticCloudBatch
open LongTails.Proofs.LogisticCloudTrajectory
open LongTails.Proofs.LogisticCloudTuning
open LongTails.Proofs.LogisticCloudEntry
open LongTails.Proofs.LogisticCloudEscape
open LongTails.Proofs.LogisticCloudCrossing
open LongTails.Proofs.LogisticCloudHitting
open LongTails.Proofs.LogisticCloudHorizon
open LongTails.Proofs.LogisticCloudInitialization

namespace LongTails.Proofs.LogisticCloudSeparation

variable {p : Params} {D : Data p} (G : Geometry p D)

lemma physical_correct (hL : 0 < p.L) (w : Weights p.d)
    (hc : Correct G (Real.sqrt p.L • w)) : Separates D w := by
  intro i
  change 0 < margin (input D i) w
  dsimp only [input]
  split_ifs
  · obtain ⟨H,_⟩ := physical_component G.e 0 w p.L hL
    change 0 < score (sumFeature D.reference) (diffFeature D.reference) w
    simp only [smul_zero] at H
    rw [G.reference_sum,G.reference_diff,H]
    exact hc.1
  · let j := Fin.ofNat p.n (i.val-p.n)
    obtain ⟨H,_⟩ := physical_component (zcol G j) (ycol G j) w p.L hL
    obtain ⟨hn,hd⟩ := neg_feature (D.negative j)
    obtain ⟨hz,hy⟩ := actual_columns G j
    change 0 < score (sumFeature (-D.negative j)) (diffFeature (-D.negative j)) w
    rw [hn,hd,hz,hy]
    have he (a b : Features p.d) : score (-a) (-b) w = -score a b w := by
      simp only [score,inner_neg_left]; ring
    rw [he,H]
    exact neg_pos.mpr (hc.2 j)

lemma reaches (hp : spec.valid p) (g : Weights p.d)
    (hg : Good (probes G).1 (probes G).2 p.ρ g) :
    ∃ k ≤ ⌈2^58*(1+p.a/p.μ)*Real.log (1/radius p)⌉₊,
      Separates D ((fullStep D (rate p/p.L))^[k] (start p g).point) := by
  let η := rate p
  let w := Real.sqrt p.L • (start p g).point
  let W := (gradientStep G η)^[entryTime p] w
  let X := fun j : ℕ => (gradientStep G η)^[j] W
  obtain ⟨hr,hP,hT⟩ := seed_projection G hp g hg
  obtain ⟨s,t,hs,ht,hc,hq,hm,hv,hrm,hA,hN⟩ := entry G hp w hr hP hT
  let z := fun j => chart G s t (X j)
  let ok := fun j => ‖transverse G (X j)‖ ≤ radius p
  let hit := fun j => Correct G (X j)
  let S := scales p hp
  have hi : Safe S z ok 0 := ⟨hc,hq,hN,le_rfl,le_rfl⟩
  have step (j : ℕ) (H : Safe S z ok j) (HB : amplitude (z j) ≤ 2^16*Real.sqrt p.a) :
      Progress S (z j) (z (j+1)) ∧ ok (j+1) ∧ (0 < (z (j+1)).q → hit (j+1)) := by
    obtain ⟨hC,hQ,hB,hM,hV⟩ := H
    have hμ : 0 < p.μ := S.hμ
    have hmass := (geometry S.ha' hC hQ).2.2.2
    have h₁ := mul_le_mul_of_nonneg_left hmass hμ.le
    have h₂ := mul_le_mul_of_nonneg_left hM hμ.le
    have h₃ := mul_le_mul_of_nonneg_left hV hμ.le
    change 320*radius p ≤ p.μ*mass (z 0) at hm
    change 64*radius p ≤ p.μ*(z 0).v at hv
    have H' := next_point G hp s t hs ht (X j) (radius p) hB hC hQ HB
      (by change 64*radius p ≤ p.μ*(z j).p; linarith)
      (by change 64*radius p ≤ p.μ*(z j).v; linarith)
    simpa only [z,ok,hit,X,Function.iterate_succ_apply'] using H'
  obtain ⟨hK,hJ,hmax,htime⟩ := horizons p hp
  have hgrowth : 640*Real.sqrt p.a ≤ (1+η*p.μ/80)^lowTime p*mass (z 0) := by
    exact hK.trans (mul_le_mul_of_nonneg_left hrm (pow_nonneg (by
      have h := mul_pos S.hη S.hμ
      change 0 < η*p.μ at h
      linarith) _))
  obtain ⟨k,hk,hgood⟩ := until_crossing S z ok hit hi hA step _ _ hgrowth
    (by change 4 ≤ (highTime p:ℝ)*η*p.μ; rwa [mul_assoc]) hmax
  refine ⟨k+entryTime p,by omega,physical_correct G hp.2.1 _ ?_⟩
  have transport (n : ℕ) : Real.sqrt p.L • (fullStep D (η/p.L))^[n] (start p g).point =
      (gradientStep G η)^[n] w := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply',physical_step G hp.2.1,ih]
  rw [transport,Function.iterate_add_apply]
  exact hgood

end LongTails.Proofs.LogisticCloudSeparation
