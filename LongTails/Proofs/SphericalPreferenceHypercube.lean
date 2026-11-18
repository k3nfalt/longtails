import LongTails.Proofs.SphericalPreferenceGaussian
import LongTails.Proofs.PreferenceTranscriptDistance
import Mathlib.Analysis.Normed.Module.Normalize
import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped RealInnerProductSpace ENNReal NNReal BigOperators

namespace LongTails.Proofs.SphericalPreferenceHypercube

open LongTails.Setups.SphericalRandomUtility LongTails.Proofs.SphericalPreferenceGaussian

abbrev Vertex (d : ℕ) := Fin d → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def vector {d : ℕ} (v : Vertex d) : Point d := WithLp.toLp 2 (fun i => sign (v i))

lemma sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]

lemma norm_vector {d : ℕ} (v : Vertex d) : ‖vector v‖ = Real.sqrt d := by
  rw [← Real.sqrt_sq (norm_nonneg (vector v)), EuclideanSpace.real_norm_sq_eq]
  simp [vector, sign_sq]

noncomputable def unitVector {d : ℕ} (v : Vertex d) : Point d := (Real.sqrt d)⁻¹ • vector v

lemma norm_unitVector {d : ℕ} [NeZero d] (v : Vertex d) : ‖unitVector v‖ = 1 := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  rw [unitVector,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_vector,inv_mul_cancel₀ (by positivity)]

noncomputable def linear (p : Params) (v : Vertex p.d) (x : Point p.d) : ℝ :=
  -(8*p.ε/p.R)*⟪unitVector v,x⟫

noncomputable def optimal (p : Params) [NeZero p.d] (v : Vertex p.d) : Feasible p :=
  ⟨(p.R : ℝ) • unitVector v,by simp [norm_smul,norm_unitVector,abs_of_nonneg p.R.coe_nonneg]⟩

lemma amplitude (p : Params) (hR : 0 < p.R) (he : 0 < p.ε) (hacc : p.ε ≤ p.B*p.R/16) :
    0 < 8*p.ε/p.R ∧ 8*p.ε/p.R ≤ p.B/2 := by
  have hr : 0 < (p.R : ℝ) := hR
  exact ⟨by positivity,(div_le_iff₀ hr).mpr (by linarith only [hacc])⟩

lemma optimality (p : Params) [NeZero p.d] (v : Vertex p.d) (hR : 0 < p.R) (he : 0 < p.ε) :
    IsMinOn (linear p v) (closedBall 0 p.R) (optimal p v).val := by
  intro x hx
  have h := (real_inner_le_norm (unitVector v) x).trans (by
    simpa only [norm_unitVector,one_mul] using mem_closedBall_zero_iff.mp hx)
  have hr : 0 < (p.R : ℝ) := hR
  change -(8*p.ε/p.R)*⟪unitVector v,(p.R:ℝ) • unitVector v⟫ ≤ _
  rw [real_inner_smul_right,real_inner_self_eq_norm_sq,norm_unitVector,one_pow,mul_one]
  exact mul_le_mul_of_nonpos_left h (neg_nonpos.mpr (by positivity))

lemma small_noise (p : Params) [NeZero p.d] (hB : 0 < p.B) :
    1/2 ≤ (mixture p.d p.B).real (closedBall 0 (p.B/2)) := by
  let D := stdGaussian (Point p.d)
  let C : Set (Point p.d) := {z | 16*(p.d : ℝ) < ‖z‖^2}
  have hm : MeasurableSet C := measurableSet_lt measurable_const (by fun_prop)
  have hb := LongTails.Proofs.GatedEscapeGaussian.norm_sq_tail (E := Point p.d) 16 (by norm_num)
  simp only [Point,finrank_euclideanSpace_fin] at hb
  change (∫ z, C.indicator (1 : Point p.d → ℝ) z ∂D) ≤ _ at hb
  rw [integral_indicator_one hm] at hb
  have hC := measureReal_compl (μ := D) hm
  rw [probReal_univ] at hC
  have hd : 0 < (p.d : ℝ) := by exact_mod_cast NeZero.pos p.d
  have hds := Real.sqrt_pos.mpr hd
  have ht : Cᶜ ⊆ (fun z : Point p.d => (p.B/(8*Real.sqrt p.d)) • z) ⁻¹' closedBall 0 (p.B/2) := by
    intro z hz
    have hz' : ‖z‖^2 ≤ 16*(p.d : ℝ) := le_of_not_gt hz
    have hz'' : ‖z‖ ≤ 4*Real.sqrt p.d := by
      nlinarith only [hz',Real.sq_sqrt hd.le,norm_nonneg z,hds.le]
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    apply (mul_le_mul_of_nonneg_left hz'' (by positivity)).trans_eq
    field_simp
    ring
  have hsmall := measureReal_mono (μ := D) ht
  rw [mixture_real]
  have heq : (scaled p.d (p.B/(8*Real.sqrt p.d))).real (closedBall 0 (p.B/2)) =
      D.real ((fun z : Point p.d => (p.B/(8*Real.sqrt p.d)) • z) ⁻¹' closedBall 0 (p.B/2)) := by
    simp only [measureReal_def,scaled,D,Measure.map_apply (show Measurable (fun z : Point p.d => (p.B/(8*Real.sqrt p.d)) • z) by fun_prop) measurableSet_closedBall]
  rw [heq]
  linarith only [hsmall,hC,hb,measureReal_nonneg (μ := scaled p.d (2*p.B)) (s := closedBall 0 (p.B/2))]

lemma radius_good (p : Params) [NeZero p.d] (v : Vertex p.d) {a : ℝ} (ha : 0 ≤ a)
    (hamp : a = 8*p.ε/p.R) (hle : a ≤ p.B/2) :
    closedBall (0 : Point p.d) (p.B/2) ⊆ good p (linear p v) := by
  intro z hz x y
  have he : sampleUtility (linear p v) z x.val - sampleUtility (linear p v) z y.val =
      ⟪(-a) • unitVector v + z,x.val-y.val⟫ := by
    simp only [sampleUtility,linear,inner_sub_right,inner_add_left,real_inner_smul_left,hamp]
  rw [he]
  apply (abs_real_inner_le_norm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hs := norm_add_le ((-a) • unitVector v) z
  rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg ha,norm_unitVector,mul_one] at hs
  linarith only [hs,mem_closedBall_zero_iff.mp hz,hle]

def flip {d : ℕ} (v : Vertex d) (i : Fin d) : Vertex d := Function.update v i (!(v i))

lemma flip_twice {d : ℕ} (v : Vertex d) (i : Fin d) : flip (flip v i) i = v := by
  funext j
  by_cases h : j=i <;> simp [flip,h,Function.update_of_ne]

def flipEquiv {d : ℕ} (i : Fin d) : Vertex d ≃ Vertex d where
  toFun v := flip v i
  invFun v := flip v i
  left_inv v := flip_twice v i
  right_inv v := flip_twice v i

lemma flip_projection {d : ℕ} (v : Vertex d) (i : Fin d) (u : Point d) :
    |⟪unitVector v,u⟫-⟪unitVector (flip v i),u⟫| = 2*(Real.sqrt d)⁻¹*|u i| := by
  have hv : vector v - vector (flip v i) = EuclideanSpace.single i (2*sign (v i)) := by
    ext j
    by_cases h : j=i
    · subst j
      cases hb : v i <;> norm_num [vector,flip,sign,hb]
    · simp [vector,flip,h]
  rw [unitVector,unitVector,real_inner_smul_left,real_inner_smul_left,← mul_sub,← inner_sub_left,hv,
    EuclideanSpace.inner_single_left]
  simp only [RCLike.conj_to_real,abs_mul,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
  cases v i <;> simp [sign] <;> ring

noncomputable def oracle (p : Params) (v : Vertex p.d) :
    OracleTemplate.Oracle (Feasible p × Feasible p) Bool where
  Seed := fun _ => Point p.d
  law := ⟨Measure.infinitePi fun _ : ℕ => mixture p.d p.B,inferInstance⟩
  answer := fun _ (_,q) z => comparePair (linear p v) q z

lemma admissible (p : Params) [NeZero p.d] (v : Vertex p.d) (hR : 0 < p.R) (hB : 0 < p.B)
    (he : 0 < p.ε) (hacc : p.ε ≤ p.B*p.R/16) : spec.admissible p (linear p v) (oracle p v) := by
  obtain ⟨ha,hamp⟩ := amplitude p hR he hacc
  refine ⟨?_, ?_, ⟨mixture p.d p.B,inferInstance⟩, (oracle p v).law, mixture_spherical p.B, ?_,
    OracleTemplate.StochasticGeneralized.infinitePi_iid (mixture p.d p.B), rfl⟩
  · refine ⟨convex_closedBall _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    simp [linear,inner_add_right,real_inner_smul_right,smul_eq_mul]
    linarith
  · unfold Function.uncurry comparePair sampleUtility linear
    apply measurable_to_bool
    simp only [Set.preimage,Set.mem_singleton_iff,decide_eq_true_eq]
    apply measurableSet_le <;> fun_prop
  · change (1/2 : ℝ≥0∞) ≤ mixture p.d p.B (good p (linear p v))
    apply (ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top _ _)).mp
    have h := (small_noise p hB).trans (measureReal_mono (radius_good p v ha.le rfl hamp))
    norm_num [measureReal_def] at h ⊢
    exact h

noncomputable def queryUnit {p : Params} (q : Feasible p × Feasible p) : Point p.d :=
  NormedSpace.normalize (q.1.val-q.2.val)

noncomputable def yes (p : Params) (v : Vertex p.d) (q : Feasible p × Feasible p) : ℝ :=
  (mixture p.d p.B).real {z | comparePair (linear p v) q z = true}

lemma yes_mem (p : Params) (v : Vertex p.d) (q : Feasible p × Feasible p) :
    yes p v q ∈ Icc 0 1 := ⟨measureReal_nonneg,measureReal_le_one⟩

lemma yes_eq (p : Params) [NeZero p.d] (hB : 0 < p.B) (v : Vertex p.d) (q : Feasible p × Feasible p) :
    yes p v q = if q.1.val = q.2.val then 1 else link p.d p.B ((8*p.ε/p.R)*⟪unitVector v,queryUnit q⟫) := by
  by_cases he : q.1.val=q.2.val
  · simp [yes,comparePair,sampleUtility,he]
  rw [ite_eq_right he,← link_eq hB (queryUnit q) (NormedSpace.norm_normalize (sub_ne_zero.mpr he))]
  unfold yes
  congr 1
  ext z
  change decide (_ ≤ _) = true ↔ _
  rw [decide_eq_true_eq]
  simp only [Set.mem_ofPred_eq,sampleUtility,linear]
  have hp := inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr he))
  rw [queryUnit,NormedSpace.normalize,real_inner_smul_right,real_inner_smul_left,
    inner_sub_right,real_inner_comm z,inner_sub_right]
  rw [show 8*p.ε/p.R*(‖q.1.val-q.2.val‖⁻¹* (⟪unitVector v,q.1.val⟫-⟪unitVector v,q.2.val⟫)) =
    ‖q.1.val-q.2.val‖⁻¹*(8*p.ε/p.R*(⟪unitVector v,q.1.val⟫-⟪unitVector v,q.2.val⟫)) by ring,
    mul_le_mul_iff_right₀ hp]
  constructor <;> intro H <;> linarith only [H]

noncomputable def energy (p : Params) (q : Feasible p × Feasible p) (i : Fin p.d) : ℝ :=
  256*(8*p.ε/p.R/p.B)^2*(queryUnit q i)^2

lemma energy_sum (p : Params) (q : Feasible p × Feasible p) :
    ∑ i, energy p q i ≤ 256*(8*p.ε/p.R/p.B)^2 := by
  unfold energy
  rw [← Finset.mul_sum,← EuclideanSpace.real_norm_sq_eq]
  by_cases hq : q.1.val = q.2.val
  · simp [queryUnit,hq]; positivity
  · simp [queryUnit,NormedSpace.norm_normalize (sub_ne_zero.mpr hq)]

lemma yes_distance (p : Params) [NeZero p.d] (hB : 0 < p.B) (hR : 0 < p.R)
    (he : 0 < p.ε) (hacc : p.ε ≤ p.B*p.R/16) (v : Vertex p.d) (i : Fin p.d)
    (q : Feasible p × Feasible p) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let p₀ := yes p v q
    let p₁ := yes p (flip v i) q
    PreferenceTranscriptDistance.squareDistance (a*p₀) (b*p₁) +
      PreferenceTranscriptDistance.squareDistance (a*(1-p₀)) (b*(1-p₁)) ≤
      PreferenceTranscriptDistance.squareDistance a b + (a+b)*energy p q i := by
  let A := 8*p.ε/p.R
  let u := queryUnit q
  obtain ⟨hA,hAB⟩ := amplitude p hR he hacc
  dsimp only
  rw [yes_eq p hB,yes_eq p hB]
  by_cases heq : q.1.val = q.2.val
  · simp [heq,energy,queryUnit,PreferenceTranscriptDistance.squareDistance]
  simp only [ite_eq_right heq]
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize (sub_ne_zero.mpr heq)
  have hdom (v : Vertex p.d) : |A*⟪unitVector v,u⟫| ≤ p.B/2 := by
    rw [abs_mul,abs_of_pos hA]
    have h := abs_real_inner_le_norm (unitVector v) u
    rw [hu,norm_unitVector,mul_one] at h
    exact (mul_le_mul_of_nonneg_left h hA.le).trans (by simpa using hAB)
  have h := PreferenceTranscriptDistance.split_distance_le ha hb (by norm_num : (0:ℝ)<1/16)
    (link_interior p.d hB (hdom v)) (link_interior p.d hB (hdom (flip v i)))
  apply h.trans (add_le_add le_rfl _)
  have hdiff := link_modulus (d := p.d) hB (A*⟪unitVector v,u⟫) (A*⟪unitVector (flip v i),u⟫)
  rw [← mul_sub,abs_mul,abs_of_pos hA,flip_projection] at hdiff
  have hd : 0 < Real.sqrt p.d := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos p.d)
  have hcancel : 4*Real.sqrt p.d/p.B*(A*(2*(Real.sqrt p.d)⁻¹*|u i|)) = 8*A/p.B*|u i| := by field_simp; ring
  rw [hcancel] at hdiff
  have hh := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  rw [sq_abs, mul_pow, sq_abs] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*(a+b) by positivity)
  dsimp only [energy]
  change _ ≤ (a+b)*(256*(A/p.B)^2*(u i)^2)
  ring_nf at hh' ⊢
  exact hh'

end LongTails.Proofs.SphericalPreferenceHypercube
