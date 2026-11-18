import LongTails.Proofs.SphericalPreferenceTranscriptLaw
import LongTails.TemplateLowerBound

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SphericalPreferenceRisk

open LongTails.Setups.SphericalRandomUtility LongTails.Proofs.SphericalPreferenceGaussian
open LongTails.Proofs.SphericalPreferenceHypercube LongTails.Proofs.SphericalPreferenceTranscript
open LongTails.Proofs.SphericalPreferenceTranscriptLaw OracleTemplate

noncomputable def decode {d : ℕ} (x : Point d) : Vertex d := fun i => decide (0 ≤ x i)

lemma coordinate_error (p : Params) [NeZero p.d] (v : Vertex p.d) (x : Feasible p) (i : Fin p.d) :
    ((p.R : ℝ)*(Real.sqrt p.d)⁻¹)^2 * mistake (decode x.val i) (v i) ≤
      (x.val i - ((optimal p v).val i))^2 := by
  let t := (p.R : ℝ)*(Real.sqrt p.d)⁻¹
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have he : (optimal p v).val i = t * sign (v i) := by
    simp [optimal,t,unitVector,vector,mul_assoc]
  rw [he]
  change t^2 * mistake (decode x.val i) (v i) ≤ _
  by_cases h : 0 ≤ x.val i
  · cases hb : v i <;> simp [decode,h,mistake,sign]
    all_goals nlinarith only [mul_nonneg ht h,sq_nonneg (x.val i),sq_nonneg (x.val i - t)]
  · cases hb : v i <;> simp [decode,h,mistake,sign]
    all_goals nlinarith only [mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_ge h),sq_nonneg (x.val i),sq_nonneg (x.val i + t)]

lemma hamming_loss (p : Params) [NeZero p.d] (hR : 0 < p.R) (he : 0 < p.ε)
    (v : Vertex p.d) (x : Feasible p) :
    4*p.ε * (∑ i, mistake (decode x.val i) (v i)) ≤
      (p.d : ℝ)*(linear p v x.val-linear p v (optimal p v).val) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => coordinate_error p v x i)
  rw [← Finset.mul_sum] at h
  change _ ≤ ∑ i, ((x.val-(optimal p v).val) i)^2 at h
  rw [← EuclideanSpace.real_norm_sq_eq, norm_sub_sq_real] at h
  have hRn : ‖(optimal p v).val‖ = (p.R : ℝ) := by simp [optimal,norm_smul,norm_unitVector,abs_of_nonneg p.R.coe_nonneg]
  have hinner : ⟪x.val,(optimal p v).val⟫ = (p.R : ℝ)*⟪unitVector v,x.val⟫ := by
    simp [optimal,real_inner_smul_right,real_inner_comm x.val]
  rw [hRn,hinner] at h
  have hx := pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp x.property) 2
  have hr : 0 < (p.R : ℝ) := hR
  have hd : 0 < (p.d : ℝ) := by exact_mod_cast NeZero.pos p.d
  have hds := Real.sq_sqrt hd.le
  rw [mul_pow,inv_pow,hds] at h
  have hgap : linear p v x.val-linear p v (optimal p v).val =
      (8*p.ε/p.R)*(p.R-⟪unitVector v,x.val⟫) := by
    simp [linear,optimal,real_inner_smul_right,norm_unitVector]
    ring
  rw [hgap]
  have hh : (p.R : ℝ)^2*(∑ i, mistake (decode x.val i) (v i)) ≤
      (2*(p.R:ℝ)^2-2*p.R*⟪unitVector v,x.val⟫)*p.d := by
    field_simp [hd.ne'] at h
    nlinarith only [h,mul_le_mul_of_nonneg_right hx hd.le]
  field_simp [hr.ne']
  apply le_of_mul_le_mul_left _ hr
  nlinarith only [hh]

lemma history_risk (p : Params) [NeZero p.d] (hR : 0 < p.R) (hB : 0 < p.B)
    (he : 0 < p.ε) (hacc : p.ε ≤ p.B*p.R/16) {k : ℕ}
    (hk : (k : ℝ) ≤ p.d*(p.B*p.R/p.ε)^2/524288)
    {S : Type} (s : S) (step : S → Bool → S) (query : S → Feasible p × Feasible p)
    (output : S → Feasible p) :
    let t := state s step k
    let m := fun v => weight s step (fun x => yes p v (query x)) k
    5/4*(Fintype.card (Vertex p.d) : ℝ)*p.ε ≤ ∑ v, ∑ w : Words k,
      m v w*(linear p v (output (t w)).val-linear p v (optimal p v).val) := by
  let t := state s step k
  let m := fun v => weight s step (fun x => yes p v (query x)) k
  let V : ℝ := Fintype.card (Vertex p.d)
  let C : ℝ := 256*(8*p.ε/p.R/p.B)^2
  have hm (v w) : 0 ≤ m v w := weight_nonneg s step _ (fun x => yes_mem p v (query x)) k w
  have hp := transcript_distance s step (fun v x => yes p v (query x)) (fun i x => energy p (query x) i)
    (fun v x => yes_mem p v (query x)) (fun x => energy_sum p (query x)) (fun v i x a b ha hb => by
      simpa only [Fintype.sum_bool,factor,Bool.false_eq_true,ite_false,ite_true,add_comm] using
        yes_distance p hB hR he hacc v i (query x) a b ha hb) k
  have hr := paired_loss m hm (fun v => mass_one s step _ k) (fun w => decode (output (t w)).val)
  have hR' : 0 < (p.R : ℝ) := hR
  have hV : 0 ≤ V := Nat.cast_nonneg _
  have hdist : (k : ℝ)*(2*V*C) ≤ V*p.d/16 :=
    (mul_le_mul_of_nonneg_right hk (show 0 ≤ 2*V*C by dsimp [C]; positivity)).trans_eq (by
      dsimp only [C]
      field_simp
      ring)
  let err := ∑ v, ∑ i, ∑ w, m v w * mistake (decode (output (t w)).val i) (v i)
  have herr : 5*V*p.d ≤ 16*err := by
    change _ ≤ (k : ℝ)*(2*V*C) at hp
    change 6*V*p.d ≤ 16*err + 16*_ at hr
    linarith only [hr,hp.trans hdist]
  let losses := ∑ v, ∑ w : Words k, m v w*(linear p v (output (t w)).val-linear p v (optimal p v).val)
  have hpoint := Finset.sum_le_sum (s := Finset.univ) fun (v : Vertex p.d) _ =>
    Finset.sum_le_sum (s := Finset.univ) fun (w : Words k) _ =>
      mul_le_mul_of_nonneg_left (hamming_loss p hR he v (output (t w))) (hm v w)
  have hg : 4*p.ε*err ≤ p.d*losses := by
    dsimp only [err,losses]
    simp only [Finset.mul_sum]
    conv_lhs => arg 2; intro v; rw [Finset.sum_comm]
    simpa only [Finset.mul_sum,mul_left_comm,mul_assoc,mul_comm] using hpoint
  change 5/4*V*p.ε ≤ losses
  have hd : 0 < (p.d : ℝ) := by exact_mod_cast NeZero.pos p.d
  apply le_of_mul_le_mul_left _ hd
  nlinarith only [hg,mul_le_mul_of_nonneg_left herr he.le]

end LongTails.Proofs.SphericalPreferenceRisk
