import LongTails.Proofs.LogisticCloudAlignment
import LongTails.Proofs.LogisticCloudAverages
import LongTails.Proofs.LogisticCloudExecution
import LongTails.Proofs.PairedOracleExecution

open scoped RealInnerProductSpace BigOperators
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift)
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudAlignment
open LongTails.Proofs.LogisticCloudExecution (increment fullStep)

namespace LongTails.Proofs.LogisticCloudModel

variable {d : ℕ}

noncomputable def score (a b : Features d) (w : Weights d) : ℝ :=
  w (.inl 0)*⟪a,readout w⟫+w (.inl 1)*⟪b,readout w⟫

lemma score_inner (a b : Features d) (w : Weights d) : score a b w = ⟪action a b w,w⟫/2 := by
  rw [action,inner_pack,inner_add_left,real_inner_smul_left,real_inner_smul_left,score]
  ring

lemma action_columns (w : Weights d) :
    ∃ L : (Features d × Features d) →ₗ[ℝ] Weights d, ∀ a b, L (a,b) = action a b w := by
  let F : (Features d × Features d) → Weights d := fun ab => action ab.1 ab.2 w
  refine ⟨{ toFun := F, map_add' := ?_, map_smul' := ?_ },fun _ _ => rfl⟩
  · intro x y
    apply pack_ext <;> simp [F,action,inner_add_left,smul_add]
    abel
  · intro c x
    apply pack_ext <;> simp [F,action,real_inner_smul_left,smul_smul,smul_add,mul_comm]

variable {p : Params} {D : Data p} (G : Geometry p D)

noncomputable def axis := (-p.a) • G.e + Real.sqrt (1-p.a^2) • G.u

lemma axis_unit (ha : 0 ≤ p.a) (ha' : p.a ≤ 1) : ‖axis G‖ = 1 := by
  have h := ortho_sum_norm G.e G.u G.norm_e G.norm_u G.eu (-p.a) (Real.sqrt (1-p.a^2))
  have hh : 0 ≤ 1-p.a^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha') (show 0 ≤ 1+p.a by linarith)]
  change ‖(-p.a) • G.e + _ • G.u‖ = 1
  rw [Real.sq_sqrt hh] at h
  nlinarith [norm_nonneg ((-p.a) • G.e + Real.sqrt (1-p.a^2) • G.u)]

lemma axis_ortho : ⟪axis G,G.v⟫ = 0 := by
  simp [axis,inner_add_left,real_inner_smul_left,G.ev,G.uv]

noncomputable def zcol (i : Fin p.n) := G.e - p.μ • axis G + G.z i
noncomputable def ycol (i : Fin p.n) := -(p.μ • G.v) + G.y i

lemma actual_columns (i : Fin p.n) :
    sumFeature (D.negative i) = p.L • zcol G i ∧ diffFeature (D.negative i) = p.L • ycol G i := by
  refine ⟨?_,G.negative_diff _⟩
  rw [G.negative_sum,zcol,axis]
  module

noncomputable def bweight (w : Weights p.d) (i : Fin p.n) :=
  Real.sigmoid (score (zcol G i) (ycol G i) w)

noncomputable def gradientStep (η : ℝ) (w : Weights p.d) :=
  w + (η/2) • (Real.sigmoid (-score G.e 0 w) • action G.e 0 w -
    (p.n : ℝ)⁻¹ • ∑ i, bweight G w i • action (zcol G i) (ycol G i) w)

lemma neg_feature (b : Features d) :
    sumFeature (-b) = -sumFeature b ∧ diffFeature (-b) = -diffFeature b := by
  have hs : shift (-b) = -shift b := rfl
  unfold sumFeature diffFeature
  rw [hs]
  constructor <;> module

lemma physical_component (a b : Features d) (w : Weights d) (L : ℝ) (hL : 0 < L) :
    score (L • a) (L • b) w = score a b (Real.sqrt L • w) ∧
    action (L • a) (L • b) w = Real.sqrt L • action a b (Real.sqrt L • w) := by
  have hs := Real.sq_sqrt hL.le
  obtain ⟨C,hC⟩ := action_columns w
  constructor
  · simp only [score,readout_smul,PiLp.smul_apply,smul_eq_mul,real_inner_smul_left,
      real_inner_smul_right]
    ring_nf
    rw [hs]
    ring
  · rw [action_smul,smul_smul,← sq,hs,← hC,← hC]
    exact C.map_smul L (a,b)

lemma signed_batch {M : Type*} [AddCommMonoid M] (f : Features p.d → M) :
    (∑ i : Index p, f (input D i)) = (p.n : ℕ) • f D.reference + ∑ i, f (-D.negative i) := by
  let n : ℕ := p.n
  let g := fun j : ℕ => f (-D.negative (Fin.ofNat p.n (j-n)))
  have hh := LongTails.Proofs.PairedOracleExecution.doubled_batch_sum n (fun _ => f D.reference) g
  have he (i : Index p) : f (input D i) = if i.val < n then f D.reference else g i.val := by
    dsimp [input,n,g]
    split <;> rfl
  simp_rw [he]
  simpa [g,n] using hh

lemma physical_step (hL : 0 < p.L) (η : ℝ) (w : Weights p.d) :
    Real.sqrt p.L • fullStep D (η/p.L) w = gradientStep G η (Real.sqrt p.L • w) := by
  let X := Real.sqrt p.L • w
  let F := fun b : Features p.d => Real.sigmoid (-margin b w) • direction b w
  have hs := Real.sq_sqrt hL.le
  have pos : F D.reference = Real.sqrt p.L •
      (Real.sigmoid (-score G.e 0 X) • action G.e 0 X) := by
    obtain ⟨hm,hg⟩ := physical_component G.e 0 w p.L hL
    simp only [smul_zero] at hm hg
    change Real.sigmoid (-score (sumFeature _) (diffFeature _) w) • action _ _ w = _
    rw [G.reference_sum,G.reference_diff,hm,hg,smul_comm]
  have neg (i : Fin p.n) : F (-D.negative i) = Real.sqrt p.L •
      (-(bweight G X i • action (zcol G i) (ycol G i) X)) := by
    obtain ⟨hm,hg⟩ := physical_component (zcol G i) (ycol G i) w p.L hL
    obtain ⟨hn,hd⟩ := neg_feature (D.negative i)
    obtain ⟨hz,hy⟩ := actual_columns G i
    obtain ⟨C,hC⟩ := action_columns w
    have hsneg (a b : Features p.d) : score (-a) (-b) w = -score a b w := by
      simp only [score,inner_neg_left]; ring
    have haneg (a b : Features p.d) : action (-a) (-b) w = -action a b w := by
      rw [← hC,← hC]; exact C.map_neg (a,b)
    change Real.sigmoid (-score (sumFeature _) (diffFeature _) w) • action _ _ w = _
    rw [hn,hd,hz,hy,hsneg,haneg,neg_neg,hm,hg,smul_neg,smul_neg,smul_comm]
    rfl
  change Real.sqrt p.L • (w+((η/p.L)/(2*p.n)) • ∑ i, F (input D i)) = _
  rw [signed_batch F,pos]
  simp_rw [neg,smul_neg,Finset.sum_neg_distrib,← Finset.smul_sum]
  dsimp only [gradientStep]
  rw [smul_add]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
  match_scalars <;> field_simp [hL.ne',hn] <;> ring_nf <;> simp [hs]
  all_goals try dsimp [X]
  all_goals ring

end LongTails.Proofs.LogisticCloudModel
