import LongTails.Proofs.IidVectorConcentration
import LongTails.Algorithms.ClippedTwoPoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.WeightedOracleBlocks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma block_inner {N : ℕ} (v : PiLp 2 (fun _ : Fin N => E)) (i : Fin N) (x : E) :
    ⟪v, PiLp.single 2 i x⟫ = ⟪v i, x⟫ := by
  simp [PiLp.inner_apply, PiLp.single_apply, apply_ite]

lemma weighted_block_norm {N : ℕ} (i : Fin N) (w : ℝ) (x : E) :
    ‖w • (PiLp.single 2 i x : PiLp 2 (fun _ : Fin N => E))‖ = |w| * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single]

lemma weighted_block_inner {N : ℕ} (v : PiLp 2 (fun _ : Fin N => E))
    (i : Fin N) (w : ℝ) (x : E) :
    ⟪v, w • PiLp.single 2 i x⟫ = ⟪w • v i, x⟫ := by
  rw [real_inner_smul_right, block_inner, real_inner_smul_left]

lemma block_direction_norm {N : ℕ} (v : PiLp 2 (fun _ : Fin N => E))
    (i : Fin N) (w : ℝ) : ‖w • v i‖ ≤ |w| * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v i) (abs_nonneg w)

omit [InnerProductSpace ℝ E] in
lemma block_energy {N : ℕ} (v : PiLp 2 (fun _ : Fin N => E)) :
    ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => E) v

omit [InnerProductSpace ℝ E] in
lemma block_isometry {N : ℕ} (i : Fin N) :
    Isometry (fun x : E => (PiLp.single 2 i x : PiLp 2 (fun _ : Fin N => E))) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [dist_eq_norm, ← PiLp.single_sub, PiLp.norm_single]

lemma weighted_block_measurable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Y : Ω → E} (hY : Measurable Y)
    {N : ℕ} (i : Fin N) (w : ℝ) :
    Measurable (fun z => w • (PiLp.single 2 i (Y z) : PiLp 2 (fun _ : Fin N => E))) :=
  (((block_isometry i).continuous.measurable).comp hY).const_smul w

lemma weighted_block_trace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → E} (hY : Integrable (fun z => ‖Y z‖ ^ 2) P)
    {V : ℝ} (hV : (∫ z, ‖Y z‖ ^ 2 ∂P) ≤ V) {N : ℕ} (i : Fin N) (w : ℝ) :
    Integrable (fun z => ‖w • (PiLp.single 2 i (Y z) : PiLp 2 (fun _ : Fin N => E))‖ ^ 2) P ∧
      (∫ z, ‖w • (PiLp.single 2 i (Y z) : PiLp 2 (fun _ : Fin N => E))‖ ^ 2 ∂P) ≤ w ^ 2 * V := by
  simp_rw [weighted_block_norm, mul_pow, sq_abs]
  refine ⟨hY.const_mul _, ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hV (sq_nonneg w)

lemma weighted_block_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → E} {C b θ R : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hmgf : ∀ q : E, b * |θ| * ‖q‖ < 1 →
      Integrable (fun z => Real.exp (θ * ⟪q, Y z⟫)) P ∧
        (∫ z, Real.exp (θ * ⟪q, Y z⟫) ∂P) ≤
          Real.exp (C * ‖q‖ ^ 2 * θ ^ 2 / (1 - b * |θ| * ‖q‖)))
    {N : ℕ} (i : Fin N) (w : ℝ) (v : PiLp 2 (fun _ : Fin N => E))
    (hv : ‖v‖ ≤ R) (hsmall : b * |θ| * (|w| * R) ≤ 1 / 3) :
    Integrable (fun z => Real.exp (θ * ⟪v, w • PiLp.single 2 i (Y z)⟫)) P ∧
      (∫ z, Real.exp (θ * ⟪v, w • PiLp.single 2 i (Y z)⟫) ∂P) ≤
        Real.exp ((3 / 2) * C * w ^ 2 * R ^ 2 * θ ^ 2) := by
  have hq : ‖w • v i‖ ≤ |w| * R := (block_direction_norm v i w).trans
    (mul_le_mul_of_nonneg_left hv (abs_nonneg w))
  have hscale := mul_le_mul_of_nonneg_left hq (mul_nonneg hb (abs_nonneg θ))
  have hhalf : b * |θ| * ‖w • v i‖ ≤ 1 / 3 := hscale.trans hsmall
  have hm := hmgf (w • v i) (by linarith)
  have hden : 0 < 1 - b * |θ| * ‖w • v i‖ := by linarith
  have hsq : ‖w • v i‖ ^ 2 ≤ w ^ 2 * R ^ 2 := by
    have ht := pow_le_pow_left₀ (norm_nonneg _) hq 2
    simpa only [mul_pow, sq_abs] using ht
  have hnum := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC) (sq_nonneg θ)
  have htarget : 0 ≤ C * w ^ 2 * R ^ 2 * θ ^ 2 := by positivity
  have hfrac : C * ‖w • v i‖ ^ 2 * θ ^ 2 / (1 - b * |θ| * ‖w • v i‖) ≤
      (3 / 2) * C * w ^ 2 * R ^ 2 * θ ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhalf htarget]
  simp_rw [weighted_block_inner]
  exact ⟨hm.1, hm.2.trans (Real.exp_le_exp.mpr hfrac)⟩

lemma iid_weighted_block_tail {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {Y : (n : ℕ) → (Fin n → Z) × Z → E} (hY : ∀ n, Measurable (Y n))
    {N : ℕ} (block : ℕ → Fin N) (w : ℕ → ℝ)
    {R cap θe θc energy cross ell C b : ℝ}
    (hR : 0 ≤ R) (hθe : 0 ≤ θe) (hθc : 0 ≤ θc) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hsmall : θe * cap ≤ 1) (variance : ℕ → ℝ)
    (hcap : ∀ i a z, w i ^ 2 * ‖Y i (a, z)‖ ^ 2 ≤ cap)
    (hvariance : ∀ i a, Integrable (fun z => ‖Y i (a, z)‖ ^ 2) p ∧
      (∫ z, ‖Y i (a, z)‖ ^ 2 ∂p) ≤ variance i)
    (hdirection : ∀ i a q, b * |θc| * ‖q‖ < 1 →
      Integrable (fun z => Real.exp (θc * ⟪q, Y i (a, z)⟫)) p ∧
        (∫ z, Real.exp (θc * ⟪q, Y i (a, z)⟫) ∂p) ≤
          Real.exp (C * ‖q‖ ^ 2 * θc ^ 2 / (1 - b * |θc| * ‖q‖)))
    (hscale : ∀ i, b * |θc| * (|w i| * R) ≤ 1 / 3)
    (n : ℕ)
    (hebudget : 2 * θe * (∑ i ∈ Finset.range n, w i ^ 2 * variance i) - θe * energy ≤ -ell)
    (hcbudget : (∑ i ∈ Finset.range n, (3 / 2) * C * w i ^ 2 * R ^ 2 * θc ^ 2) - θc * cross ≤ -ell)
    (hrbudget : energy + 2 * cross ≤ R ^ 2) :
    P.real {ω | R < ‖∑ i ∈ Finset.range n,
      w i • (PiLp.single 2 (block i) (Y i ((fun j => ξ j ω), ξ i ω)) : PiLp 2 (fun _ : Fin N => E))‖} ≤
        2 * Real.exp (-ell) := by
  let W := fun i az => w i • (PiLp.single 2 (block i) (Y i az) : PiLp 2 (fun _ : Fin N => E))
  have hW : ∀ i, Measurable (W i) := fun i => weighted_block_measurable (hY i) (block i) (w i)
  have hc : ∀ i a z, ‖W i (a, z)‖ ^ 2 ≤ cap := by
    intro i a z
    simpa only [W, weighted_block_norm, mul_pow, sq_abs] using hcap i a z
  have hv : ∀ i a, (∫ z, ‖W i (a, z)‖ ^ 2 ∂p) ≤ w i ^ 2 * variance i := by
    intro i a
    exact (weighted_block_trace (hvariance i a).1 (hvariance i a).2 (block i) (w i)).2
  have hm : ∀ i a v, ‖v‖ ≤ R →
      Integrable (fun z => Real.exp (θc * ⟪v, W i (a, z)⟫)) p ∧
        (∫ z, Real.exp (θc * ⟪v, W i (a, z)⟫) ∂p) ≤
          Real.exp ((3 / 2) * C * w i ^ 2 * R ^ 2 * θc ^ 2) := by
    intro i a v hvr
    exact weighted_block_mgf hC hb (hdirection i a) (block i) (w i) v hvr (hscale i)
  exact IidVectorConcentration.iid_vector_tail hξ hind hlaw hW hR hθe hθc hsmall
    (fun i => w i ^ 2 * variance i) (fun i => (3 / 2) * C * w i ^ 2 * R ^ 2 * θc ^ 2)
    hc hv hm n hebudget hcbudget hrbudget

open LongTails.Algorithms.ClippedTwoPoint

lemma batch_size_bounds {T A α : ℝ} (hT : 0 < T) (hA : 0 < A) (hα : 0 < α) :
    0 < batchSize T A α ∧ T * α / A ≤ (batchSize T A α : ℝ) ∧
      (batchSize T A α : ℝ) ≤ T * α / A + 1 := by
  have hp : 0 < T * α / A := by positivity
  exact ⟨Nat.ceil_pos.mpr hp, Nat.le_ceil _, (Nat.ceil_lt_add_one hp.le).le⟩

lemma batch_weight_bounds {T A α : ℝ} (hT : 0 < T) (hA : 0 < A) (hα : 0 < α) :
    0 < batchWeight T A α ∧ batchWeight T A α ≤ A / T := by
  have hb := batch_size_bounds hT hA hα
  have hbR : (0 : ℝ) < batchSize T A α := by exact_mod_cast hb.1
  refine ⟨div_pos hα hbR, ?_⟩
  apply (div_le_div_iff₀ hbR hT).mpr
  have hlo := (div_le_iff₀ hA).mp hb.2.1
  nlinarith only [hlo]

lemma batch_weight_square {T A α : ℝ} (hT : 0 < T) (hA : 0 < A) (hα : 0 < α) :
    (batchSize T A α : ℝ) * (batchWeight T A α) ^ 2 ≤ α * A / T := by
  have hb := batch_size_bounds hT hA hα
  have hbR : (batchSize T A α : ℝ) ≠ 0 := by exact_mod_cast hb.1.ne'
  have he : (batchSize T A α : ℝ) * (batchWeight T A α) ^ 2 = α * batchWeight T A α := by
    dsimp [batchWeight]
    field_simp
  rw [he, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (batch_weight_bounds hT hA hα).2 hα.le

lemma batch_total_size {N : ℕ} {T A : ℝ} {α : Fin N → ℝ}
    (hT : 0 < T) (hA : 0 < A) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = A) :
    (∑ i, (batchSize T A (α i) : ℝ)) ≤ T + N := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (batch_size_bounds hT hA (hα i)).2.2)
  calc
    _ ≤ ∑ i, (T * α i / A + 1) := hh
    _ = T + N := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hsum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp

lemma batch_total_weight_square {N : ℕ} {T A : ℝ} {α : Fin N → ℝ}
    (hT : 0 < T) (hA : 0 < A) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = A) :
    (∑ i, (batchSize T A (α i) : ℝ) * (batchWeight T A (α i)) ^ 2) ≤ A ^ 2 / T := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => batch_weight_square hT hA (hα i))
  calc
    _ ≤ ∑ i, α i * A / T := hh
    _ = A ^ 2 / T := by rw [← Finset.sum_div, ← Finset.sum_mul, hsum, pow_two]

lemma batch_total_size_nat {N T : ℕ} {A : ℝ} {α : Fin N → ℝ}
    (hT : 0 < T) (hA : 0 < A) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = A) :
    (∑ i, batchSize T A (α i)) ≤ T + N := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hh := batch_total_size hTR hA hα hsum
  exact_mod_cast hh

lemma batch_two_branch_value_cost {N T : ℕ} {A : ℝ} {α : Fin N → ℝ}
    (hT : 0 < T) (hA : 0 < A) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = A) :
    2 * (2 * (∑ i, batchSize T A (α i)) + T) ≤ 6 * T + 4 * N := by
  have hh := batch_total_size_nat hT hA hα hsum
  omega

lemma batch_record_sum {N : ℕ} (B : Fin N → ℕ) {M : Type*} [AddCommMonoid M]
    (f : ((i : Fin N) × Fin (B i)) → M) :
    (∑ j : Fin (∑ i, B i), f (batchRecord B j)) = ∑ i, ∑ j, f ⟨i, j⟩ := by
  exact (finSigmaFinEquiv.symm.sum_comp f).trans (Fintype.sum_sigma f)

lemma batch_record_weight_square {N : ℕ} (B : Fin N → ℕ) (w : Fin N → ℝ) :
    (∑ j : Fin (∑ i, B i), w (batchRecord B j).1 ^ 2) = ∑ i, (B i : ℝ) * w i ^ 2 := by
  rw [batch_record_sum B (fun ij => w ij.1 ^ 2)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma batch_record_index {N : ℕ} (B : Fin N → ℕ) (j : Fin (∑ i, B i)) :
    (j : ℕ) = (∑ i : Fin (batchRecord B j).1,
      B (Fin.castLE (batchRecord B j).1.2.le i)) + (batchRecord B j).2 := by
  have hh := finSigmaFinEquiv_apply (batchRecord B j)
  simpa only [batchRecord, Equiv.apply_symm_apply] using hh

lemma batch_record_block_energy {N : ℕ} (B : Fin N → ℕ) (w : Fin N → ℝ)
    (Y : ((i : Fin N) × Fin (B i)) → E) :
    ‖∑ j : Fin (∑ i, B i), w (batchRecord B j).1 •
      (PiLp.single 2 (batchRecord B j).1 (Y (batchRecord B j)) : PiLp 2 (fun _ : Fin N => E))‖ ^ 2 =
      ∑ i, w i ^ 2 * ‖∑ j, Y ⟨i, j⟩‖ ^ 2 := by
  rw [batch_record_sum B (fun ij => w ij.1 •
    (PiLp.single 2 ij.1 (Y ij) : PiLp 2 (fun _ : Fin N => E))), block_energy]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ t, ∑ j, w t • (PiLp.single 2 t (Y ⟨t, j⟩) : PiLp 2 (fun _ : Fin N => E))) i =
      w i • ∑ j, Y ⟨i, j⟩ := by
    change (WithLp.ofLp (∑ t, ∑ j, w t •
      (PiLp.single 2 t (Y ⟨t, j⟩) : PiLp 2 (fun _ : Fin N => E)))) i = _
    simp [WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply, Finset.smul_sum, smul_ite]
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

lemma iid_weighted_block_confidence {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {Y : (n : ℕ) → (Fin n → Z) × Z → E} (hY : ∀ n, Measurable (Y n))
    {N : ℕ} (block : ℕ → Fin N) (w variance : ℕ → ℝ) (n : ℕ)
    {K d ell C b : ℝ} (hK : 0 < K) (hd : 0 < d) (hell : 0 < ell) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hcap : ∀ i a z, w i ^ 2 * ‖Y i (a, z)‖ ^ 2 ≤ 4 * d * K / ell)
    (hvariance : ∀ i a, Integrable (fun z => ‖Y i (a, z)‖ ^ 2) p ∧
      (∫ z, ‖Y i (a, z)‖ ^ 2 ∂p) ≤ variance i)
    (hvsum : (∑ i ∈ Finset.range n, w i ^ 2 * variance i) ≤ 20 * d * K)
    (hcsum : C * (∑ i ∈ Finset.range n, w i ^ 2) ≤ 262144 * K)
    (hscale : ∀ i, b * |w i| ≤ 256 * Real.sqrt K / Real.sqrt ell)
    (hdirection : ∀ i a θ q, b * |θ| * ‖q‖ < 1 →
      Integrable (fun z => Real.exp (θ * ⟪q, Y i (a, z)⟫)) p ∧
        (∫ z, Real.exp (θ * ⟪q, Y i (a, z)⟫) ∂p) ≤
          Real.exp (C * ‖q‖ ^ 2 * θ ^ 2 / (1 - b * |θ| * ‖q‖))) :
    P.real {ω | 8192 * Real.sqrt (K * (d + ell)) < ‖∑ i ∈ Finset.range n,
      w i • (PiLp.single 2 (block i) (Y i ((fun j => ξ j ω), ξ i ω)) : PiLp 2 (fun _ : Fin N => E))‖} ≤
        2 * Real.exp (-ell) := by
  let R := 8192 * Real.sqrt (K * (d + ell))
  let q := R * Real.sqrt K
  let θc := Real.sqrt ell / (768 * q)
  let θe := ell / (4 * (d * K))
  have hR : 0 < R := by dsimp [R]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hc := StoppedVectorConcentration.cross_chernoff_parameters hq hell
  have he := StoppedVectorConcentration.energy_chernoff_parameters (mul_pos hd hK) hell
  have hθc : 0 < θc := hc.1
  have hθe : 0 < θe := he.1
  have hecap : θe * (4 * d * K / ell) ≤ 1 := by
    simpa only [θe, mul_assoc] using he.2.1.le
  have hebudget : 2 * θe * (∑ i ∈ Finset.range n, w i ^ 2 * variance i) - θe * (44 * d * K) ≤ -ell := by
    have hh := mul_le_mul_of_nonneg_left hvsum (show 0 ≤ 2 * θe by positivity)
    have heq := he.2.2
    change 40 * (d * K) * θe - θe * (44 * (d * K)) = -ell at heq
    nlinarith only [hh, heq]
  have hscale' (i : ℕ) : b * |θc| * (|w i| * R) ≤ 1 / 3 := by
    rw [abs_of_pos hθc]
    have hh := mul_le_mul_of_nonneg_right (hscale i) (mul_nonneg hθc.le hR.le)
    have heq := hc.2.1
    change (256 * q / Real.sqrt ell) * θc = 1 / 3 at heq
    have hid : (256 * Real.sqrt K / Real.sqrt ell) * (θc * R) =
        (256 * q / Real.sqrt ell) * θc := by dsimp [q]; ring
    rw [hid] at hh
    nlinarith only [hh, heq]
  have hq2 : q ^ 2 = R ^ 2 * K := by dsimp [q]; rw [mul_pow, Real.sq_sqrt hK.le]
  have hcost : (∑ i ∈ Finset.range n, (3 / 2) * C * w i ^ 2 * R ^ 2 * θc ^ 2) ≤
      (3 / 2) * 262144 * q ^ 2 * θc ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hcsum (show 0 ≤ (3 / 2) * R ^ 2 * θc ^ 2 by positivity)
    have hs : (∑ i ∈ Finset.range n, (3 / 2) * C * w i ^ 2 * R ^ 2 * θc ^ 2) =
        (3 / 2) * R ^ 2 * θc ^ 2 * (C * ∑ i ∈ Finset.range n, w i ^ 2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hs, hq2]
    nlinarith only [hh]
  have hceq : (3 / 2) * 262144 * q ^ 2 * θc ^ 2 - θc * (1280 * q * Real.sqrt ell) = -ell := by
    have hh := hc.2.2
    rw [hc.2.1] at hh
    change 262144 * q ^ 2 * θc ^ 2 / (1 - 1 / 3) - θc * (1280 * q * Real.sqrt ell) = -ell at hh
    convert hh using 1; ring
  have hcbudget : (∑ i ∈ Finset.range n, (3 / 2) * C * w i ^ 2 * R ^ 2 * θc ^ 2) -
      θc * (1280 * q * Real.sqrt ell) ≤ -ell := by linarith only [hcost, hceq]
  have hrbudget : 44 * d * K + 2 * (1280 * q * Real.sqrt ell) ≤ R ^ 2 := by
    simpa only [R, q, mul_assoc] using StoppedVectorConcentration.stopped_radius_budget hK.le hd.le hell.le
  exact iid_weighted_block_tail hξ hind hlaw hY block w hR.le hθe.le hθc.le hC hb hecap variance
    hcap hvariance (fun i a => hdirection i a θc) hscale' n hebudget hcbudget hrbudget

lemma clipping_schedule_scales {M A T d ell : ℝ}
    (hM : 0 < M) (hA : 0 < A) (hT : 0 < T) (hd : 0 < d) (hell : 0 < ell) :
    let τ := M * Real.sqrt (T / (d * ell))
    let K := M ^ 2 * A ^ 2 / T
    0 < K ∧ 0 < τ ∧
      (A / T) ^ 2 * (2 * d * τ) ^ 2 = 4 * d * K / ell ∧
      256 * Real.sqrt d * τ * (A / T) = 256 * Real.sqrt K / Real.sqrt ell := by
  dsimp only
  have ht : 0 ≤ T / (d * ell) := by positivity
  have hk : 0 ≤ M ^ 2 * A ^ 2 / T := by positivity
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · simp only [mul_pow, div_pow, Real.sq_sqrt ht]
    field_simp
    ring
  · apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow, div_pow, Real.sq_sqrt hd.le, Real.sq_sqrt ht,
      Real.sq_sqrt hk, Real.sq_sqrt hell.le]
    field_simp

lemma clipping_weighted_parameters {M A T d ell B : ℝ}
    (hM : 0 < M) (hA : 0 < A) (hT : 0 < T) (hd : 0 < d) (hell : 0 < ell)
    (hB : 0 ≤ B) (hBM : B ≤ 2 * M ^ 2) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i, |w i| ≤ A / T) (hs : (∑ i ∈ Finset.range n, w i ^ 2) ≤ A ^ 2 / T) :
    let τ := M * Real.sqrt (T / (d * ell))
    let K := M ^ 2 * A ^ 2 / T
    (∀ i, w i ^ 2 * (2 * d * τ) ^ 2 ≤ 4 * d * K / ell) ∧
      (∑ i ∈ Finset.range n, w i ^ 2 * (10 * d * B)) ≤ 20 * d * K ∧
      (131072 * B) * (∑ i ∈ Finset.range n, w i ^ 2) ≤ 262144 * K ∧
      (∀ i, (256 * Real.sqrt d * τ) * |w i| ≤ 256 * Real.sqrt K / Real.sqrt ell) := by
  have hp := clipping_schedule_scales hM hA hT hd hell
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hw2 : w i ^ 2 ≤ (A / T) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (w i)) (hw i) 2
    exact (mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)).trans_eq hp.2.2.1
  · have he : (∑ i ∈ Finset.range n, w i ^ 2 * (10 * d * B)) =
        (10 * d * B) * ∑ i ∈ Finset.range n, w i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he]
    calc
      _ ≤ (10 * d * B) * (A ^ 2 / T) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 20 * d * (M ^ 2 * A ^ 2 / T) := by
        have hh := mul_le_mul_of_nonneg_left hBM (show 0 ≤ 10 * d * A ^ 2 / T by positivity)
        convert hh using 1 <;> ring
  · calc
      _ ≤ (131072 * B) * (A ^ 2 / T) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 262144 * (M ^ 2 * A ^ 2 / T) := by
        have hh := mul_le_mul_of_nonneg_left hBM (show 0 ≤ 131072 * A ^ 2 / T by positivity)
        convert hh using 1 <;> ring
  · intro i
    exact (mul_le_mul_of_nonneg_left (hw i) (by positivity)).trans_eq hp.2.2.2

lemma weighted_direction_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → E} {C b θ R : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hmgf : ∀ q : E, b * |θ| * ‖q‖ < 1 →
      Integrable (fun z => Real.exp (θ * ⟪q, Y z⟫)) P ∧
        (∫ z, Real.exp (θ * ⟪q, Y z⟫) ∂P) ≤
          Real.exp (C * ‖q‖ ^ 2 * θ ^ 2 / (1 - b * |θ| * ‖q‖)))
    (w : ℝ) (v : E)
    (hv : ‖v‖ ≤ R) (hsmall : b * |θ| * (|w| * R) ≤ 1 / 3) :
    Integrable (fun z => Real.exp (θ * (w * ⟪v, Y z⟫))) P ∧
      (∫ z, Real.exp (θ * (w * ⟪v, Y z⟫)) ∂P) ≤
        Real.exp ((3 / 2) * C * w ^ 2 * R ^ 2 * θ ^ 2) := by
  have hq : ‖w • v‖ ≤ |w| * R := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hv (abs_nonneg w)
  have hscale := mul_le_mul_of_nonneg_left hq (mul_nonneg hb (abs_nonneg θ))
  have hhalf : b * |θ| * ‖w • v‖ ≤ 1 / 3 := hscale.trans hsmall
  have hm := hmgf (w • v) (by linarith)
  have hden : 0 < 1 - b * |θ| * ‖w • v‖ := by linarith
  have hsq : ‖w • v‖ ^ 2 ≤ w ^ 2 * R ^ 2 := by
    have ht := pow_le_pow_left₀ (norm_nonneg _) hq 2
    simpa only [mul_pow, sq_abs] using ht
  have hnum := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC) (sq_nonneg θ)
  have htarget : 0 ≤ C * w ^ 2 * R ^ 2 * θ ^ 2 := by positivity
  have hfrac : C * ‖w • v‖ ^ 2 * θ ^ 2 / (1 - b * |θ| * ‖w • v‖) ≤
      (3 / 2) * C * w ^ 2 * R ^ 2 * θ ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhalf htarget]
  simp only [real_inner_smul_left] at hm
  exact ⟨hm.1, hm.2.trans (Real.exp_le_exp.mpr hfrac)⟩


lemma iid_weighted_direction_confidence {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {Y : (n : ℕ) → (Fin n → Z) × Z → E} (hY : ∀ n, Measurable (Y n))
    {v : (n : ℕ) → (Fin n → Z) → E} (hv : ∀ n, Measurable (v n))
    (w : ℕ → ℝ) (n : ℕ) {K D ell C b : ℝ}
    (hK : 0 < K) (hD : 0 < D) (hell : 0 < ell) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hvb : ∀ i a, ‖v i a‖ ≤ D)
    (hcsum : C * (∑ i ∈ Finset.range n, w i ^ 2) ≤ 262144 * K)
    (hscale : ∀ i, b * |w i| ≤ 256 * Real.sqrt K / Real.sqrt ell)
    (hdirection : ∀ i a θ q, b * |θ| * ‖q‖ < 1 →
      Integrable (fun z => Real.exp (θ * ⟪q, Y i (a, z)⟫)) p ∧
        (∫ z, Real.exp (θ * ⟪q, Y i (a, z)⟫) ∂p) ≤
          Real.exp (C * ‖q‖ ^ 2 * θ ^ 2 / (1 - b * |θ| * ‖q‖))) :
    P.real {ω | 1280 * (D * Real.sqrt K) * Real.sqrt ell ≤
      ∑ i ∈ Finset.range n, w i * ⟪v i (fun j => ξ j ω), Y i ((fun j => ξ j ω), ξ i ω)⟫} ≤
        Real.exp (-ell) := by
  let q := D * Real.sqrt K
  let θ := Real.sqrt ell / (768 * q)
  have hq : 0 < q := by dsimp [q]; positivity
  have hc := StoppedVectorConcentration.cross_chernoff_parameters hq hell
  have hθ : 0 < θ := hc.1
  have hscale' (i : ℕ) : b * |θ| * (|w i| * D) ≤ 1 / 3 := by
    rw [abs_of_pos hθ]
    have hh := mul_le_mul_of_nonneg_right (hscale i) (mul_nonneg hθ.le hD.le)
    have heq := hc.2.1
    change (256 * q / Real.sqrt ell) * θ = 1 / 3 at heq
    have hid : (256 * Real.sqrt K / Real.sqrt ell) * (θ * D) =
        (256 * q / Real.sqrt ell) * θ := by dsimp [q]; ring
    rw [hid] at hh
    nlinarith only [hh, heq]
  have hq2 : q ^ 2 = D ^ 2 * K := by dsimp [q]; rw [mul_pow, Real.sq_sqrt hK.le]
  have hcost : (∑ i ∈ Finset.range n, (3 / 2) * C * w i ^ 2 * D ^ 2 * θ ^ 2) ≤
      (3 / 2) * 262144 * q ^ 2 * θ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hcsum (show 0 ≤ (3 / 2) * D ^ 2 * θ ^ 2 by positivity)
    have hs : (∑ i ∈ Finset.range n, (3 / 2) * C * w i ^ 2 * D ^ 2 * θ ^ 2) =
        (3 / 2) * D ^ 2 * θ ^ 2 * (C * ∑ i ∈ Finset.range n, w i ^ 2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hs, hq2]
    nlinarith only [hh]
  have heq : (3 / 2) * 262144 * q ^ 2 * θ ^ 2 - θ * (1280 * q * Real.sqrt ell) = -ell := by
    have hh := hc.2.2
    rw [hc.2.1] at hh
    change 262144 * q ^ 2 * θ ^ 2 / (1 - 1 / 3) - θ * (1280 * q * Real.sqrt ell) = -ell at hh
    convert hh using 1
    ring
  let inc := fun i (az : (Fin i → Z) × Z) => w i * ⟪v i az.1, Y i az⟫
  have hi : ∀ i, Measurable (inc i) := fun i =>
    (((hv i).comp measurable_fst).inner (hY i)).const_mul (w i)
  have hm (i : ℕ) (a : Fin i → Z) :=
    weighted_direction_mgf hC hb (hdirection i a θ) (w i) (v i a) (hvb i a) (hscale' i)
  have hh := AdaptiveOracleConcentration.iid_predictable_sum_exponential_bound hξ hind hlaw
    (fun i => (3 / 2) * C * w i ^ 2 * D ^ 2 * θ ^ 2) θ hi
    (fun i a => (hm i a).1) (fun i a => (hm i a).2) n
  have ht := StoppedVectorConcentration.exponential_tail_of_bound hθ.le hh.1 hh.2
    (1280 * q * Real.sqrt ell)
  exact ht.trans (Real.exp_le_exp.mpr (by linarith only [hcost, heq]))

lemma biased_block_energy {N : ℕ} (a : Fin N → ℝ) (noise bias : Fin N → E)
    {R β : ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, ‖bias i‖ ≤ β)
    (hn : ‖∑ i, a i • (PiLp.single 2 i (noise i) : PiLp 2 (fun _ : Fin N => E))‖ ≤ R) :
    (∑ i, a i ^ 2 * ‖noise i + bias i‖ ^ 2) ≤ (R + (∑ i, a i) * β) ^ 2 := by
  let V := PiLp 2 (fun _ : Fin N => E)
  have hb' : ‖∑ i, a i • (PiLp.single 2 i (bias i) : V)‖ ≤ (∑ i, a i) * β := by
    calc
      _ ≤ ∑ i, ‖a i • (PiLp.single 2 i (bias i) : V)‖ := norm_sum_le _ _
      _ ≤ ∑ i, a i * β := Finset.sum_le_sum fun i _ => by
        rw [weighted_block_norm, abs_of_nonneg (ha i)]
        exact mul_le_mul_of_nonneg_left (hb i) (ha i)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hnorm : ‖∑ i, a i • (PiLp.single 2 i (noise i + bias i) : V)‖ ≤
      R + (∑ i, a i) * β := by
    simp only [PiLp.single_add, smul_add, Finset.sum_add_distrib]
    exact (norm_add_le _ _).trans (add_le_add hn hb')
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [block_energy] at hs
  convert hs using 1
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ j, a j • (PiLp.single 2 j (noise j + bias j) : V)) i =
      a i • (noise i + bias i) := by
    change (WithLp.ofLp (∑ j, a j • (PiLp.single 2 j (noise j + bias j) : V))) i = _
    simp [WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply, smul_ite]
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

lemma biased_comparator {N : ℕ} (a : Fin N → ℝ) (noise bias direction : Fin N → E)
    {C D β : ℝ} (ha : ∀ i, 0 ≤ a i) (hβ : 0 ≤ β)
    (hb : ∀ i, ‖bias i‖ ≤ β) (hd : ∀ i, ‖direction i‖ ≤ D)
    (hn : (∑ i, a i * ⟪noise i, direction i⟫) ≤ C) :
    (∑ i, a i * ⟪noise i + bias i, direction i⟫) ≤ C + (∑ i, a i) * β * D := by
  simp only [inner_add_left, mul_add, Finset.sum_add_distrib]
  have hb' : (∑ i, a i * ⟪bias i, direction i⟫) ≤ (∑ i, a i) * β * D := by
    calc
      _ ≤ ∑ i, a i * (β * D) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left ((real_inner_le_norm _ _).trans
          (mul_le_mul (hb i) (hd i) (norm_nonneg _) hβ)) (ha i)
      _ = _ := by rw [← Finset.sum_mul]; ring
  exact add_le_add hn hb'

end LongTails.Proofs.WeightedOracleBlocks
