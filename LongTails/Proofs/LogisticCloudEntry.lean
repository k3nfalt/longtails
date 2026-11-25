import LongTails.Proofs.LogisticCloudEntryBounds
import LongTails.Proofs.LogisticCloudWarmup
import LongTails.Proofs.LogisticCloudTrajectory
import LongTails.Proofs.LogisticCloudInitialization

open scoped RealInnerProductSpace
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudCone
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudAlignment
open LongTails.Proofs.LogisticCloudModel
open LongTails.Proofs.LogisticCloudBatch
open LongTails.Proofs.LogisticCloudTrajectory
open LongTails.Proofs.LogisticCloudWarmup
open LongTails.Proofs.LogisticCloudTuning
open LongTails.Proofs.LogisticCloudEntryBounds
open LongTails.Proofs.LogisticCloudInitialization

namespace LongTails.Proofs.LogisticCloudEntry

variable {p : Params} {D : Data p} (G : Geometry p D)

noncomputable def projections (w : Weights p.d) : ℝ × ℝ :=
  ((w (.inl 0)+⟪axis G,readout w⟫)/2,(w (.inl 1)+⟪G.v,readout w⟫)/2)

noncomputable def probes : Weights p.d × Weights p.d :=
  ((Real.sqrt 2)⁻¹ • pack 1 0 (axis G),(Real.sqrt 2)⁻¹ • pack 0 1 G.v)

lemma unit_probes (hp : spec.valid p) : ‖(probes G).1‖ = 1 ∧ ‖(probes G).2‖ = 1 := by
  have ha : 0 < p.a := (scales p hp).ha
  have ha' : p.a ≤ 1/16 := (scales p hp).ha'
  have h₁ := norm_pack_sq 1 0 (axis G)
  have h₂ := norm_pack_sq 0 1 G.v
  rw [axis_unit G ha.le (by linarith)] at h₁
  rw [G.norm_v] at h₂
  have h₃ : ‖pack 1 0 (axis G)‖ = Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),norm_nonneg (pack 1 0 (axis G)),
      Real.sqrt_nonneg (2:ℝ)]
  have h₄ : ‖pack 0 1 G.v‖ = Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),norm_nonneg (pack 0 1 G.v),
      Real.sqrt_nonneg (2:ℝ)]
  simp [probes,norm_smul,h₃,h₄,abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))]

lemma seed_projection (hp : spec.valid p) (g : Weights p.d)
    (hg : Good (probes G).1 (probes G).2 p.ρ g) :
    let w := Real.sqrt p.L • (start p g).point
    ‖w‖ = radius p ∧ projectionSize p*radius p ≤ |(projections G w).1| ∧
      projectionSize p*radius p ≤ |(projections G w).2| := by
  intro w
  obtain ⟨_,hL,_,_,_,_,hρ,hρ',hr,_⟩ := hp
  let R := radius p
  have hR : 0 < R := mul_pos hr (Real.sqrt_pos.mpr hL)
  have hstart : w = (R/‖g‖) • g := by
    dsimp [w,R,radius,start]
    rw [smul_smul]; congr 1; ring
  obtain ⟨h₁,h₂,h₃⟩ := projection hρ hρ'.le hR hg
  rw [← hstart] at h₁ h₂ h₃
  refine ⟨h₁,?_,?_⟩
  all_goals
    simp only [probes,real_inner_smul_left,inner_pack,one_mul,zero_mul,add_zero,zero_add,
      abs_mul,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))] at h₂ h₃
    dsimp [projections,projectionSize]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  all_goals
    have hd : 0 < (p.d:ℝ)+2 := by positivity
    dsimp only [R] at h₂ h₃ hR
    field_simp [hd.ne'] at h₂ h₃ ⊢
    nlinarith only [h₂,h₃,mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ Real.sqrt 2 by norm_num)
      (mul_nonneg (sq_nonneg p.ρ) hR.le)]

lemma coordinate_gap (s t : ℝ) (hs : s^2=1) (ht : t^2=1) (w y : Weights p.d) :
    let x := chart G s t w
    let z := chart G s t y
    |x.p-z.p| ≤ ‖w-y‖ ∧ |x.q-z.q| ≤ ‖w-y‖ ∧ |x.u-z.u| ≤ ‖w-y‖ ∧
      |x.t-z.t| ≤ ‖w-y‖ ∧ |x.v-z.v| ≤ ‖w-y‖ := by
  have h₁ : |s| = 1 := by nlinarith [sq_abs s,abs_nonneg s]
  have h₂ : |t| = 1 := by nlinarith [sq_abs t,abs_nonneg t]
  obtain ⟨P,T,V⟩ := bounds (w-y)
  have h (a : Features p.d) (ha : ‖a‖ = 1) :
      |⟪a,readout (w-y)⟫| ≤ ‖w-y‖ := by
    simpa [ha] using (abs_real_inner_le_norm a (readout (w-y))).trans
      (mul_le_mul_of_nonneg_left V (norm_nonneg a))
  dsimp only [chart,coords]
  simp only [← mul_sub,abs_mul,h₁,h₂,one_mul,← inner_sub_right,← readout_sub]
  exact ⟨P,h _ G.norm_e,h _ G.norm_u,T,h _ G.norm_v⟩

lemma chart_mode (s t F : ℝ) (w : Weights p.d) :
    let P := s*(F*(projections G w).1)
    let T := t*(F*(projections G w).2)
    chart G s t (F • growing (axis G) G.v w) =
      ⟨P,-p.a*P,Real.sqrt (1-p.a^2)*P,T,T⟩ := by
  obtain ⟨_,_,_,hue,hve,hvu⟩ := orthonormal_axes G
  simp [chart,coords,growing,mode,projections,axis,real_inner_smul_right,inner_add_right,
    hue,hve,hvu,G.eu,G.uv,G.ev,G.norm_e,G.norm_u,G.norm_v]
  ring_nf
  simp

lemma growing_bound (hp : spec.valid p) (w : Weights p.d) : ‖growing (axis G) G.v w‖ ≤ 9*‖w‖ := by
  have ha : p.a ≤ 1/16 := (scales p hp).ha'
  obtain ⟨hf,hn⟩ := bounded_modes (axis G) G.v
    (axis_unit G (scales p hp).ha.le (by linarith)) G.norm_v (axis_ortho G) w
  have H : growing (axis G) G.v w = w-remainder (axis G) G.v w-falling (axis G) G.v w := by
    rw [eq_sub_iff_add_eq,eq_sub_iff_add_eq]
    exact split _ _ _
  have hh := norm_sub_le (w-remainder (axis G) G.v w) (falling (axis G) G.v w)
  rw [← H] at hh
  linarith [norm_sub_le w (remainder (axis G) G.v w)]

end LongTails.Proofs.LogisticCloudEntry
