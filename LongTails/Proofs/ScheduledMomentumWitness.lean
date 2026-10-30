import LongTails.Proofs.ScheduledMomentumExecution
import LongTails.Proofs.SeparationSuccess
import LongTails.Proofs.NsgdProcess
import LongTails.Proofs.SeparationLower

namespace LongTails.Proofs.ScheduledMomentumWitness

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar
open LongTails.Setups.ScheduledMomentumComparison
open LongTails.Proofs.DiagonalSpectral LongTails.Proofs.SeparationInstance
open LongTails.Proofs.SeparationModel LongTails.Proofs.GaussianBlocks
open LongTails.Proofs.SeparationTrajectory LongTails.Proofs.ScheduledMomentumExecution

variable {m n : ℕ}

noncomputable def scalarDirection (r : ℕ) (normalize : Bool) (a b : ℝ) : ℝ × ℝ :=
  if normalize then
    ((Real.sqrt (a ^ 2 + (r - 1 : ℕ) * b ^ 2))⁻¹ * a,
      (Real.sqrt (a ^ 2 + (r - 1 : ℕ) * b ^ 2))⁻¹ * b)
  else (a, b)

noncomputable def matrixDirection (normalize : Bool) : Space m n → Space m n :=
  if normalize then nsgdDirection else sgdDirection

noncomputable def scalarState (r : ℕ) (normalize : Bool) (ℓ c s β : ℝ) (η : ℕ → ℝ)
    (φ : FlatShape) (B : ℕ) (ξ : ℕ → ℝ) : ℕ → (ℝ × ℝ) × (ℝ × ℝ)
  | 0 => ((0, 0), (0, 0))
  | t + 1 =>
      let S := scalarState r normalize ℓ c s β η φ B ξ t
      let a := β * S.2.1 + (1 - β) * (ℓ * S.1.1 + s * blockMean B t ξ)
      let b := β * S.2.2 + (1 - β) * (c * φ.slope S.1.2)
      ((S.1.1 - η t * (scalarDirection r normalize a b).1,
        S.1.2 - η t * (scalarDirection r normalize a b).2), (a, b))

noncomputable def splitVec (a b : ℝ) : Fin (min m n) → ℝ := fun i => if stiff i then a else b

lemma splitVec_add (a b a' b' : ℝ) :
    splitVec (m := m) (n := n) a b + splitVec a' b' = splitVec (a + a') (b + b') := by
  funext i
  by_cases hi : stiff i <;> simp [splitVec, hi]

lemma splitVec_smul (k a b : ℝ) :
    k • splitVec (m := m) (n := n) a b = splitVec (k * a) (k * b) := by
  funext i
  by_cases hi : stiff i <;> simp [splitVec, hi]

lemma norm_diagMat_split (hr : 0 < min m n) (a b : ℝ) :
    ‖diagMat (splitVec (m := m) (n := n) a b)‖ =
      Real.sqrt (a ^ 2 + (min m n - 1 : ℕ) * b ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_diagMat]
  congr 1
  rw [← sum_stiff_split hr]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : stiff j <;> simp [splitVec, stiff] at * <;> simp_all

lemma matrixDirection_split (hr : 0 < min m n) (normalize : Bool) (a b : ℝ) :
    matrixDirection normalize (diagMat (splitVec (m := m) (n := n) a b)) =
      diagMat (splitVec (scalarDirection (min m n) normalize a b).1
        (scalarDirection (min m n) normalize a b).2) := by
  cases normalize
  · simp [matrixDirection, sgdDirection, scalarDirection]
  · simp only [matrixDirection, nsgdDirection, scalarDirection, ↓reduceIte]
    rw [norm_diagMat_split hr, ← diagMat_smul, splitVec_smul]

lemma reduction (hr : 0 < min m n) (normalize : Bool) (ℓ c s β : ℝ) (η : ℕ → ℝ) (φ : FlatShape)
    (x0 : Space m n) {B : ℕ} (hB : 0 < B) (ξ : ℕ → ℝ) (t : ℕ) :
    (∀ i, offset x0 (sampledMomentum (matrixDirection normalize) β η B x0
        (sample ℓ c s φ x0) ξ t).1 i =
      if stiff i then (scalarState (min m n) normalize ℓ c s β η φ B ξ t).1.1
      else (scalarState (min m n) normalize ℓ c s β η φ B ξ t).1.2) ∧
    (sampledMomentum (matrixDirection normalize) β η B x0 (sample ℓ c s φ x0) ξ t).2 =
      diagMat (splitVec (scalarState (min m n) normalize ℓ c s β η φ B ξ t).2.1
        (scalarState (min m n) normalize ℓ c s β η φ B ξ t).2.2) := by
  induction t with
  | zero =>
      refine ⟨fun i => ?_, ?_⟩
      · simp [sampledMomentum, offset, scalarState]
      · have h0 : splitVec (m := m) (n := n) 0 0 = 0 := by
          funext i
          simp [splitVec]
        have h00 : diagMat (0 : Fin (min m n) → ℝ) = (0 : Space m n) := by
          simpa using diagMat_smul (m := m) (n := n) 0 0
        show (0 : Space m n) = diagMat (splitVec 0 0)
        rw [h0, h00]
  | succ t ih =>
      obtain ⟨hx, hM⟩ := ih
      have hcoef : coefficients ℓ c φ (offset x0 (sampledMomentum (matrixDirection normalize) β η
            B x0 (sample ℓ c s φ x0) ξ t).1) + noiseVec (s * blockMean B t ξ) =
          splitVec (ℓ * (scalarState (min m n) normalize ℓ c s β η φ B ξ t).1.1 +
            s * blockMean B t ξ)
            (c * φ.slope (scalarState (min m n) normalize ℓ c s β η φ B ξ t).1.2) := by
        funext j
        simp only [Pi.add_apply, coefficients, noiseVec, hx j, splitVec]
        by_cases hj : stiff j <;> simp [hj]
      have hMnew : β • (sampledMomentum (matrixDirection normalize) β η B x0
            (sample ℓ c s φ x0) ξ t).2 + (1 - β) • ((1 / (B : ℝ)) •
            ∑ j ∈ Finset.range B, sample ℓ c s φ x0 (sampledMomentum (matrixDirection normalize)
              β η B x0 (sample ℓ c s φ x0) ξ t).1 (ξ (B * t + j))) =
          diagMat (splitVec (m := m) (n := n)
            (scalarState (min m n) normalize ℓ c s β η φ B ξ (t + 1)).2.1
            (scalarState (min m n) normalize ℓ c s β η φ B ξ (t + 1)).2.2) := by
        rw [batch_mean_sample ℓ c s φ x0 _ hB, hM, hcoef, ← diagMat_smul, ← diagMat_smul,
          ← diagMat_add, splitVec_smul, splitVec_smul, splitVec_add]
        try rfl
      refine ⟨fun i => ?_, ?_⟩
      · simp only [sampledMomentum]
        rw [hMnew, matrixDirection_split hr, offset_sub_smul, hx i]
        by_cases hi : stiff i
        · simp only [hi, ↓reduceIte, splitVec]
          try rfl
        · simp only [hi, ↓reduceIte, splitVec]
          try rfl
      · simp only [sampledMomentum]
        rw [hMnew]

lemma measurable_scalarDirection (r : ℕ) (normalize : Bool) :
    Measurable (fun q : ℝ × ℝ => scalarDirection r normalize q.1 q.2) := by
  cases normalize
  · simp only [scalarDirection, Bool.false_eq_true, ↓reduceIte]
    exact measurable_fst.prodMk measurable_snd
  · simp only [scalarDirection, ↓reduceIte]
    fun_prop

lemma measurable_scalarState (r : ℕ) (normalize : Bool) (ℓ c s β : ℝ) (η : ℕ → ℝ)
    (φ : FlatShape) (B t : ℕ) :
    Measurable (fun ξ => scalarState r normalize ℓ c s β η φ B ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hz := measurable_blockMean B t
      have hsl : Measurable φ.slope := φ.continuous_slope.measurable
      have ha : Measurable (fun ξ => β * (scalarState r normalize ℓ c s β η φ B ξ t).2.1 +
          (1 - β) * (ℓ * (scalarState r normalize ℓ c s β η φ B ξ t).1.1 +
            s * blockMean B t ξ)) :=
        (measurable_const.mul ih.snd.fst).add
          (measurable_const.mul ((measurable_const.mul ih.fst.fst).add (measurable_const.mul hz)))
      have hb : Measurable (fun ξ => β * (scalarState r normalize ℓ c s β η φ B ξ t).2.2 +
          (1 - β) * (c * φ.slope (scalarState r normalize ℓ c s β η φ B ξ t).1.2)) :=
        (measurable_const.mul ih.snd.snd).add
          (measurable_const.mul (measurable_const.mul (hsl.comp ih.fst.snd)))
      have hd := (measurable_scalarDirection r normalize).comp (ha.prodMk hb)
      exact ((ih.fst.fst.sub (measurable_const.mul hd.fst)).prodMk
        (ih.fst.snd.sub (measurable_const.mul hd.snd))).prodMk (ha.prodMk hb)

lemma scalarState_local (r : ℕ) (normalize : Bool) (ℓ c s β : ℝ) (η : ℕ → ℝ) (φ : FlatShape)
    (B : ℕ) (ξ ξ' : ℕ → ℝ) (t : ℕ) (h : ∀ k < B * t, ξ k = ξ' k) :
    scalarState r normalize ℓ c s β η φ B ξ t = scalarState r normalize ℓ c s β η φ B ξ' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have h' : ∀ k < B * t, ξ k = ξ' k := fun k hk =>
        h k (lt_of_lt_of_le hk (Nat.mul_le_mul_left B (Nat.le_succ t)))
      have hm : blockMean B t ξ = blockMean B t ξ' := by
        unfold blockMean
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        apply h
        have := Finset.mem_range.mp hj
        rw [Nat.mul_succ]
        omega
      simp only [scalarState, ih h', hm]

lemma flat_momentum_le (r : ℕ) (normalize : Bool) {ℓ c s β : ℝ} (η : ℕ → ℝ) (φ : FlatShape)
    (B : ℕ) (ξ : ℕ → ℝ) (hc : 0 ≤ c) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (t : ℕ) :
    |(scalarState r normalize ℓ c s β η φ B ξ t).2.2| ≤ c := by
  induction t with
  | zero => simpa [scalarState] using hc
  | succ t ih =>
      simp only [scalarState]
      have hsl := φ.bounded (scalarState r normalize ℓ c s β η φ B ξ t).1.2
      calc |β * (scalarState r normalize ℓ c s β η φ B ξ t).2.2 +
            (1 - β) * (c * φ.slope (scalarState r normalize ℓ c s β η φ B ξ t).1.2)|
          ≤ β * |(scalarState r normalize ℓ c s β η φ B ξ t).2.2| +
            (1 - β) * (c * |φ.slope (scalarState r normalize ℓ c s β η φ B ξ t).1.2|) := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hβ0, abs_of_nonneg (by linarith : 0 ≤ 1 - β),
              abs_of_nonneg hc]
        _ ≤ β * c + (1 - β) * (c * 1) := by
            gcongr
        _ = c := by ring

lemma nuclear_momentum (hr : 0 < min m n) (normalize : Bool) (ℓ c s β : ℝ) (η : ℕ → ℝ)
    (φ : FlatShape) (x0 : Space m n) {B : ℕ} (hB : 0 < B) (ξ : ℕ → ℝ) (t : ℕ) :
    nuclearNorm (gradient (objective ℓ c φ x0) (sampledMomentum (matrixDirection normalize) β η B x0
        (sample ℓ c s φ x0) ξ t).1) =
      |ℓ * (scalarState (min m n) normalize ℓ c s β η φ B ξ t).1.1| +
        (min m n - 1 : ℕ) * |c * φ.slope (scalarState (min m n) normalize ℓ c s β η φ B ξ t).1.2| :=
  nuclear_scalar ℓ c φ x0 _ hr _ _ (reduction hr normalize ℓ c s β η φ x0 hB ξ t).1

lemma telescope_le (y : ℕ → ℝ) (hy0 : y 0 = 0) {t T : ℕ} (ht : t ≤ T) :
    y t ≤ ∑ u ∈ Finset.range T, |y (u + 1) - y u| := by
  have h1 : y t = ∑ u ∈ Finset.range t, (y (u + 1) - y u) := by
    rw [Finset.sum_range_sub, hy0, sub_zero]
  rw [h1]
  calc (∑ u ∈ Finset.range t, (y (u + 1) - y u)) ≤ ∑ u ∈ Finset.range t, |y (u + 1) - y u| :=
        Finset.sum_le_sum fun u _ => le_abs_self _
    _ ≤ ∑ u ∈ Finset.range T, |y (u + 1) - y u| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr ht)
          (fun _ _ _ => abs_nonneg _)

lemma flat_penalty {R c ε w D : ℝ} (hRc : R * c = 3 * ε) (hc : 0 ≤ c) (hR : 0 ≤ R) (hw : 0 < w)
    (hDw : 0 < D - w) (hε : 0 ≤ ε) (y : ℕ → ℝ) (hy0 : y 0 = 0) {t T : ℕ} (ht : t ≤ T) :
    3 * ε / 2 * (1 - (∑ u ∈ Finset.range T, |y (u + 1) - y u|) / (D - w)) ≤
      R * |c * valleySlope w D (y t)| := by
  set V := ∑ u ∈ Finset.range T, |y (u + 1) - y u|
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hyt := telescope_le y hy0 ht
  by_cases hfar : y t ≤ D - w
  · have hsl := valleySlope_far hw hfar
    have habs : 1 / 2 ≤ |valleySlope w D (y t)| := by
      rw [abs_of_neg (by linarith)]
      linarith
    have h1 : R * (c * (1 / 2)) ≤ R * |c * valleySlope w D (y t)| := by
      rw [abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hc) hR
    have h2 : 0 ≤ V / (D - w) := div_nonneg hV hDw.le
    have h3 : R * (c * (1 / 2)) = 3 * ε / 2 := by
      rw [show R * (c * (1 / 2)) = (R * c) / 2 by ring, hRc]
    nlinarith
  · have h1 : 1 < V / (D - w) := by
      rw [lt_div_iff₀ hDw]
      linarith
    have h2 : 3 * ε / 2 * (1 - V / (D - w)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact h2.trans (mul_nonneg hR (abs_nonneg _))

lemma condition_scalar {B : ℕ} (hB : 0 < B) (t : ℕ) {G : (ℕ → ℝ) → ℝ}
    (hloc : LongTails.Proofs.NsgdProcess.Local (B * t) G) (hGm : Measurable G)
    {Φ : ℝ → ℝ → ℝ} (hΦm : Measurable (Function.uncurry Φ)) {C : ℝ}
    (hΦb : ∀ p z, |Φ p z| ≤ C) :
    (∫ ξ, Φ (G ξ) (blockMean B t ξ) ∂stdStream) =
      ∫ ξ, ∫ z, Φ (G ξ) z ∂gaussianReal 0 (1 / (B : NNReal)) ∂stdStream := by
  set k := B * t
  set ν := gaussianReal 0 (1 / (B : NNReal))
  set π := Measure.pi fun _ : Fin k => gaussianReal 0 1
  let Gp := fun q : Fin k → ℝ => G (LongTails.Proofs.NsgdProcess.ext k q)
  have hGp : Measurable Gp := hGm.comp (LongTails.Proofs.NsgdProcess.measurable_ext k)
  have hagree (ξ : ℕ → ℝ) : Gp (fun i : Fin k => ξ i) = G ξ :=
    hloc _ _ (LongTails.Proofs.NsgdProcess.ext_agree k ξ)
  let F := fun q : (Fin k → ℝ) × ℝ => Φ (Gp q.1) q.2
  have hFm : Measurable F := hΦm.comp ((hGp.comp measurable_fst).prodMk measurable_snd)
  have hFi : Integrable F (π.prod ν) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      exact hΦb _ _
  let Ψ := fun q : ℝ => ∫ z, Φ q z ∂ν
  have hΨm : Measurable Ψ := hΦm.stronglyMeasurable.integral_prod_right'.measurable
  have hΨb (q : ℝ) : |Ψ q| ≤ C := by
    have h := norm_integral_le_of_norm_le_const (μ := ν) (C := C)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hΦb q z)
    simpa [Real.norm_eq_abs, Ψ] using h
  let F' := fun q : (Fin k → ℝ) × ℝ => Ψ (Gp q.1)
  have hF'm : Measurable F' := hΨm.comp (hGp.comp measurable_fst)
  have hF'i : Integrable F' (π.prod ν) := by
    apply Integrable.of_bound hF'm.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      exact hΨb _
  have h1 := freeze hB t hFi
  have h2 := freeze hB t hF'i
  have hl : (∫ ξ, Φ (G ξ) (blockMean B t ξ) ∂stdStream) =
      ∫ ξ, F ((fun i : Fin k => ξ i), blockMean B t ξ) ∂stdStream := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by simp only [F, hagree]
  have hr : (∫ ξ, ∫ z, Φ (G ξ) z ∂ν ∂stdStream) =
      ∫ ξ, F' ((fun i : Fin k => ξ i), blockMean B t ξ) ∂stdStream := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by simp only [F', Ψ, hagree]
  rw [hl, hr, h1, h2]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => by
    simp only [F, F', Ψ]
    rw [integral_const, probReal_univ, one_smul]

lemma witness_admissible (p : LongTails.Setups.BatchedSpectralSmooth.Public)
    (hr : 2 ≤ min p.m p.n) (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hs : 0 ≤ p.s) (hε : 0 < p.ε)
    {R c w D : ℝ} (hR : R = ((min p.m p.n - 1 : ℕ) : ℝ)) (hc : c = 3 * p.ε / R) (hw : 0 < w)
    (hwd : w = 6 * p.ε / p.L) (hD : D = p.Δ / (3 * p.ε)) :
    LongTails.Setups.BatchedSpectralSmooth.spec.admissible p
      (objective (p.L / 2) c (valleyShape hw D) p.x0)
      (LongTails.Proofs.SeparationSuccess.gaussianOracle
        (sample (p.L / 2) c p.s (valleyShape hw D) p.x0)) := by
  have hr0 : 0 < min p.m p.n := by omega
  have hm : 0 < p.m := lt_of_lt_of_le hr0 (min_le_left _ _)
  have hR1 : 1 ≤ R := by
    rw [hR]
    exact_mod_cast (show 1 ≤ min p.m p.n - 1 by omega)
  have hRc : R * c = 3 * p.ε := by rw [hc]; field_simp
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg (by linarith) (by linarith)
  have hD0 : 0 ≤ D := by rw [hD]; exact div_nonneg hΔ (by linarith)
  refine LongTails.Proofs.SeparationSuccess.separation_admissible hm (by linarith) hc0 hs le_rfl
    (valleyShape hw D) ?_ hr0 (((min p.m p.n - 1 : ℕ) : ℝ) * (c * w))
    (LongTails.Proofs.SeparationLower.objective_ge (by linarith) hc0 (valleyShape hw D)
      (LongTails.Proofs.SeparationLower.valley_ge_width hw.le D) hr0 p.x0) ?_
  · change p.L / 2 + ((min p.m p.n - 1 : ℕ) : ℝ) * (c * (1 / w)) ≤ p.L
    rw [← hR, show R * (c * (1 / w)) = (R * c) / w by ring, hRc, hwd]
    have : 3 * p.ε / (6 * p.ε / p.L) = p.L / 2 := by field_simp; ring
    linarith
  · rw [LongTails.Proofs.SeparationLower.objective_start_eq _ c _ hr0 p.x0, ← hR]
    have hv : valley w D 0 ≤ w + D := by
      have := LongTails.Proofs.NsgdLattice.valley_le w D 0 hw.le
      rwa [zero_sub, abs_neg, abs_of_nonneg hD0] at this
    have hv' : R * (c * (valleyShape hw D).value 0) ≤ R * (c * (w + D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hc0) (by linarith)
    have : R * (c * (w + D)) - R * (c * w) = p.Δ := by
      rw [show R * (c * (w + D)) - R * (c * w) = (R * c) * D by ring, hRc, hD]
      field_simp
    linarith

lemma success_sum_momentum {p : LongTails.Setups.BatchedSpectralSmooth.Public}
    {f : Space p.m p.n → ℝ} {g : Space p.m p.n → ℝ → Space p.m p.n}
    (hg : Measurable (Function.uncurry g)) {direction : Space p.m p.n → Space p.m p.n}
    (hdir : Measurable direction) {β : ℝ} {η : ℕ → ℝ} {B T : ℕ}
    {A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)}
    (hA : FollowsScheduledMomentum direction β η B T p.x0 A)
    (hi : ∀ t, Integrable (fun ξ => nuclearNorm (gradient f
      (sampledMomentum direction β η B p.x0 g ξ t).1)) stdStream)
    (hsucc : LongTails.Setups.BatchedSpectralSmooth.spec.successful p f
      (fun z : A.Seed × (ℕ → ℝ) => execute (LongTails.Proofs.SeparationSuccess.gaussianOracle g)
        A (fun _ => B * (T + 1)) z.1 z.2)
      (⟨(A.law : Measure _).prod stdStream, inferInstance⟩ :
        ProbabilityMeasure (A.Seed × (ℕ → ℝ)))) :
    (∑ t ∈ Finset.range (T + 1), ∫ ξ, nuclearNorm (gradient f
      (sampledMomentum direction β η B p.x0 g ξ t).1) ∂stdStream) ≤ (T + 1) * p.ε := by
  have hF : Measurable (fun X : Space p.m p.n => nuclearNorm (gradient f X)) :=
    (LongTails.Proofs.MatrixCovariance.continuous_nuclearNorm _ _).measurable.comp
      (LongTails.Proofs.MuonProcess.measurable_gradient f)
  have hout := uniform_output (⟨stdStream, inferInstance⟩ : ProbabilityMeasure (ℕ → ℝ)) g hg hdir
    hA (fun X => nuclearNorm (gradient f X)) hF hi
  obtain ⟨_, _, hle⟩ := hsucc
  simp only at hout
  have h2 : (∑ t ∈ Finset.range (T + 1), ∫ ξ, nuclearNorm (gradient f
      (sampledMomentum direction β η B p.x0 g ξ t).1) ∂stdStream) / (T + 1) ≤ p.ε :=
    (hout.2.2).symm.trans_le hle
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

lemma travel_bound {ℓ R c ε w D : ℝ} (hRc : R * c = 3 * ε) (hc : 0 ≤ c) (hR : 0 ≤ R) (hw : 0 < w)
    (hDw : 0 < D - w) (hε : 0 ≤ ε) {T : ℕ} (x y : (ℕ → ℝ) → ℕ → ℝ) (hy0 : ∀ ξ, y ξ 0 = 0)
    (hx : ∀ t, Integrable (fun ξ => |ℓ * x ξ t|) stdStream)
    (hyi : ∀ t, Integrable (fun ξ => R * |c * valleySlope w D (y ξ t)|) stdStream)
    (hV : Integrable (fun ξ => ∑ u ∈ Finset.range T, |y ξ (u + 1) - y ξ u|) stdStream)
    (hsum : (∑ t ∈ Finset.range (T + 1), ∫ ξ, (|ℓ * x ξ t| +
      R * |c * valleySlope w D (y ξ t)|) ∂stdStream) ≤ (T + 1) * ε) :
    (∑ t ∈ Finset.range (T + 1), ∫ ξ, |ℓ * x ξ t| ∂stdStream) + (T + 1) * ε / 2 ≤
      3 * ε / 2 * (T + 1) * (∫ ξ, ∑ u ∈ Finset.range T, |y ξ (u + 1) - y ξ u| ∂stdStream) /
        (D - w) := by
  set EV := ∫ ξ, ∑ u ∈ Finset.range T, |y ξ (u + 1) - y ξ u| ∂stdStream
  have hgi : Integrable (fun ξ => 3 * ε / 2 *
      (1 - (∑ u ∈ Finset.range T, |y ξ (u + 1) - y ξ u|) / (D - w))) stdStream :=
    ((integrable_const 1).sub (hV.div_const _)).const_mul _
  have hgint : (∫ ξ, 3 * ε / 2 *
      (1 - (∑ u ∈ Finset.range T, |y ξ (u + 1) - y ξ u|) / (D - w)) ∂stdStream) =
      3 * ε / 2 * (1 - EV / (D - w)) := by
    rw [integral_const_mul, integral_sub (integrable_const 1) (hV.div_const _), integral_const,
      integral_div, probReal_univ, one_smul]
  have hlow : ∀ t ∈ Finset.range (T + 1), 3 * ε / 2 * (1 - EV / (D - w)) ≤
      ∫ ξ, R * |c * valleySlope w D (y ξ t)| ∂stdStream := by
    intro t ht
    rw [← hgint]
    exact integral_mono hgi (hyi t) fun ξ =>
      flat_penalty hRc hc hR hw hDw hε (y ξ) (hy0 ξ) (Finset.mem_range_succ_iff.mp ht)
  have hsplit : ∀ t ∈ Finset.range (T + 1), (∫ ξ, (|ℓ * x ξ t| +
      R * |c * valleySlope w D (y ξ t)|) ∂stdStream) =
      (∫ ξ, |ℓ * x ξ t| ∂stdStream) + ∫ ξ, R * |c * valleySlope w D (y ξ t)| ∂stdStream :=
    fun t _ => integral_add (hx t) (hyi t)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib] at hsum
  have hsum2 := Finset.sum_le_sum hlow
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum2
  push_cast at hsum2
  have e : ((T : ℝ) + 1) * (3 * ε / 2 * (1 - EV / (D - w))) =
      3 * ε / 2 * (T + 1) - 3 * ε / 2 * (T + 1) * EV / (D - w) := by ring
  linarith

end LongTails.Proofs.ScheduledMomentumWitness
