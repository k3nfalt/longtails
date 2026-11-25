import LongTails.Setups.LogisticDefectCloud
import LongTails.Proofs.LogisticCloudCone
import Mathlib.Tactic

open scoped RealInnerProductSpace
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudCone (Point)

namespace LongTails.Proofs.LogisticCloudCoordinates

variable {d : ℕ}

@[simp] lemma pack_first (s t : ℝ) (v : Features d) : pack s t v (.inl 0) = s := rfl
@[simp] lemma pack_second (s t : ℝ) (v : Features d) : pack s t v (.inl 1) = t := rfl
@[simp] lemma readout_pack (s t : ℝ) (v : Features d) : readout (pack s t v) = v := rfl

lemma pack_ext {x y : Weights d} (hp : x (.inl 0) = y (.inl 0))
    (ht : x (.inl 1) = y (.inl 1)) (hv : readout x = readout y) : x = y := by
  ext (i | i)
  · fin_cases i <;> assumption
  · exact congrArg (fun w : Features d => w i) hv

@[simp] lemma pack_readout (w : Weights d) : pack (w (.inl 0)) (w (.inl 1)) (readout w) = w :=
  pack_ext rfl rfl rfl

@[simp] lemma readout_zero : readout (0 : Weights d) = 0 := rfl
@[simp] lemma readout_neg (x : Weights d) : readout (-x) = -readout x := rfl
@[simp] lemma readout_add (x y : Weights d) : readout (x+y) = readout x+readout y := rfl
@[simp] lemma readout_sub (x y : Weights d) : readout (x-y) = readout x-readout y := rfl
@[simp] lemma readout_smul (a : ℝ) (x : Weights d) : readout (a • x) = a • readout x := rfl

lemma inner_pack (s t : ℝ) (z : Features d) (w : Weights d) :
    ⟪pack s t z, w⟫ = s*w (.inl 0) + t*w (.inl 1) + ⟪z,readout w⟫ := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_two, pack, readout, mul_comm]

lemma norm_pack_sq (s t : ℝ) (z : Features d) :
    ‖pack s t z‖ ^ 2 = s^2+t^2+‖z‖^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_pack, pack_first, pack_second, readout_pack,
    real_inner_self_eq_norm_sq]
  ring

lemma bounds (w : Weights d) :
    |w (.inl 0)| ≤ ‖w‖ ∧ |w (.inl 1)| ≤ ‖w‖ ∧ ‖readout w‖ ≤ ‖w‖ := by
  have h := norm_pack_sq (w (.inl 0)) (w (.inl 1)) (readout w)
  rw [pack_readout] at h
  have hp := sq_nonneg (w (.inl 0))
  have ht := sq_nonneg (w (.inl 1))
  have hv := sq_nonneg ‖readout w‖
  refine ⟨le_of_sq_le_sq ?_ (norm_nonneg _), le_of_sq_le_sq ?_ (norm_nonneg _),
    le_of_sq_le_sq ?_ (norm_nonneg _)⟩ <;> try rw [sq_abs]
  all_goals linarith

variable {p : Params} {D : Data p}

noncomputable def coords (G : Geometry p D) (w : Weights p.d) : Point :=
  ⟨w (.inl 0), ⟪G.e,readout w⟫, ⟪G.u,readout w⟫, w (.inl 1), ⟪G.v,readout w⟫⟩

noncomputable def transverse (G : Geometry p D) (x : Weights p.d) : Features p.d :=
  readout x - (⟪G.e,readout x⟫ • G.e + ⟪G.u,readout x⟫ • G.u + ⟪G.v,readout x⟫ • G.v)

lemma decomposition (G : Geometry p D) (w : Weights p.d) :
    let x := coords G w
    readout w = x.q • G.e + x.u • G.u + x.v • G.v + transverse G w := by
  dsimp [coords,transverse]
  abel

lemma orthonormal_axes (G : Geometry p D) :
    ⟪G.e,G.e⟫ = 1 ∧ ⟪G.u,G.u⟫ = 1 ∧ ⟪G.v,G.v⟫ = 1 ∧
    ⟪G.u,G.e⟫ = 0 ∧ ⟪G.v,G.e⟫ = 0 ∧ ⟪G.v,G.u⟫ = 0 := by
  exact ⟨by simp [G.norm_e], by simp [G.norm_u], by simp [G.norm_v],
    (real_inner_comm _ _).trans G.eu, (real_inner_comm _ _).trans G.ev,
    (real_inner_comm _ _).trans G.uv⟩

lemma transverse_ortho (G : Geometry p D) (w : Weights p.d) :
    ⟪G.e,transverse G w⟫ = 0 ∧ ⟪G.u,transverse G w⟫ = 0 ∧ ⟪G.v,transverse G w⟫ = 0 := by
  obtain ⟨he,hu,hv,hue,hve,hvu⟩ := orthonormal_axes G
  simp [transverse,inner_sub_right,inner_add_right,real_inner_smul_right,
    G.norm_e,G.norm_u,G.norm_v,hue,hve,hvu,G.eu,G.ev,G.uv]

lemma norm_transverse_le (G : Geometry p D) (w : Weights p.d) : ‖transverse G w‖ ≤ ‖w‖ := by
  obtain ⟨he,hu,hv⟩ := transverse_ortho G w
  have h := decomposition G w
  let x := coords G w
  let a := x.q • G.e+x.u • G.u+x.v • G.v
  have hz : ⟪a,transverse G w⟫ = 0 := by
    simp [a,inner_add_left,real_inner_smul_left,he,hu,hv]
  have hh := norm_add_sq_real a (transverse G w)
  change readout w = a+transverse G w at h
  rw [← h,hz] at hh
  exact (le_of_sq_le_sq (by linarith [sq_nonneg ‖a‖]) (norm_nonneg _)).trans (bounds w).2.2

end LongTails.Proofs.LogisticCloudCoordinates
