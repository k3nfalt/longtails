import LongTails.Proofs.MomentumSeparationModel

namespace LongTails.Proofs.MomentumSeparationBridge

open MeasureTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar
open LongTails.Proofs.DiagonalSpectral
open LongTails.Proofs.MomentumSeparationInstance LongTails.Proofs.MomentumSeparationModel
open LongTails.Proofs.MomentumSeparationCore LongTails.Proofs.MomentumDirectionExecution

variable {m n : ℕ}

lemma dg_row (k : Fin (min m n)) : (dg k).1.val = k.val := rfl

lemma dg_col (k : Fin (min m n)) : (dg k).2.val = k.val := rfl

lemma not_stiff_dg {k : Fin (min m n)} (hk : k.val ≠ 0) : ¬ stiffEntry (dg k : Fin m × Fin n) := by
  intro h; exact hk h.1

lemma diagMat_stiff {a : Fin (min m n) → ℝ} (ha : ∀ k : Fin (min m n), k.val = 0 → a k = 0)
    {p : Fin m × Fin n} (hp : stiffEntry p) : diagMat a p = 0 := by
  simp only [diagMat, PiLp.toLp_apply]
  split_ifs with h
  · exact ha _ (by simp; exact hp.1)
  · rfl

lemma coefficients_zero (c : ℝ) (φ : SeparationInstance.FlatShape) (u : Fin (min m n) → ℝ) (k : Fin (min m n))
    (hk : k.val = 0) : SeparationInstance.coefficients 0 c φ u k = 0 := by
  simp [SeparationInstance.coefficients, SeparationInstance.stiff, hk]

lemma gradient_stiff (ℓ c : ℝ) (φ : SeparationInstance.FlatShape) (x0 X : Space m n) {p : Fin m × Fin n}
    (hp : stiffEntry p) : gradient (MomentumSeparationInstance.objective ℓ c φ x0) X p = ℓ * (X p - x0 p) := by
  rw [MomentumSeparationInstance.gradient_objective, PiLp.add_apply, diagMat_stiff (coefficients_zero c φ _) hp]
  simp [stiffVec, hp]

lemma gradient_flat (ℓ c : ℝ) (φ : SeparationInstance.FlatShape) (x0 X : Space m n) {k : Fin (min m n)}
    (hk : k.val ≠ 0) :
    gradient (MomentumSeparationInstance.objective ℓ c φ x0) X (dg k) = c * φ.slope (X (dg k) - x0 (dg k)) := by
  rw [MomentumSeparationInstance.gradient_objective, PiLp.add_apply, diagMat_apply_dg]
  simp [stiffVec, not_stiff_dg hk, SeparationInstance.coefficients, SeparationInstance.stiff, hk,
    SeparationInstance.offset]

lemma gradient_other (ℓ c : ℝ) (φ : SeparationInstance.FlatShape) (x0 X : Space m n) {p : Fin m × Fin n}
    (hp : ¬ stiffEntry p) (hd : ∀ k : Fin (min m n), k.val ≠ 0 → dg k ≠ p) :
    gradient (MomentumSeparationInstance.objective ℓ c φ x0) X p = 0 := by
  rw [MomentumSeparationInstance.gradient_objective, PiLp.add_apply]
  have h1 : stiffVec x0 X p = 0 := by simp [stiffVec, hp]
  have h2 : diagMat (SeparationInstance.coefficients 0 c φ (SeparationInstance.offset x0 X)) p = 0 := by
    apply diagMat_apply_of_ne
    intro k hk
    by_cases h0 : k.val = 0
    · apply hp
      rw [← hk]
      exact ⟨h0, Or.inl h0⟩
    · exact hd k h0 hk
  simp [h1, h2]

lemma noise_stiff (hr : 0 < min m n) (s : ℝ) (ω : Col m n × Bool) (i : Col m n) :
    noise hr s ω ((row0 hr, colOf hr i) : Fin m × Fin n) =
      if ω.1 = i then s * AdamSeparationModel.sign ω.2 else 0 := by
  rw [noise_apply]
  by_cases h : ω.1 = i
  · rw [ite_eq_left (by rw [h]), ite_eq_left h]
  · rw [ite_eq_right (fun he => h (colOf_injective hr (congrArg Prod.snd he).symm)),
      ite_eq_right h]

lemma noise_nonstiff (hr : 0 < min m n) (s : ℝ) (ω : Col m n × Bool) {p : Fin m × Fin n}
    (hp : ¬ stiffEntry p) : noise hr s ω p = 0 := by
  rw [noise_apply, ite_eq_right]
  intro he
  exact hp (he ▸ stiffEntry_colOf hr ω.1)

noncomputable def batchNoise (hr : 0 < min m n) (s : ℝ) (B : ℕ) (ξ : ℕ → Col m n × Bool)
    (t : ℕ) : Space m n :=
  (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, noise hr s (ξ (B * t + j))

noncomputable def inputAt (s : ℝ) (B : ℕ) (ξ : ℕ → Col m n × Bool) (i : Col m n) (u : ℕ) : ℝ :=
  (1 / (B : ℝ)) * ∑ j ∈ Finset.range B,
    if (ξ (B * u + j)).1 = i then s * AdamSeparationModel.sign (ξ (B * u + j)).2 else 0

lemma batchNoise_stiff (hr : 0 < min m n) (s : ℝ) (B : ℕ) (ξ : ℕ → Col m n × Bool) (t : ℕ)
    (i : Col m n) :
    batchNoise hr s B ξ t ((row0 hr, colOf hr i) : Fin m × Fin n) = inputAt s B ξ i t := by
  simp only [batchNoise, inputAt, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
    Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact noise_stiff hr s _ i

lemma batchNoise_nonstiff (hr : 0 < min m n) (s : ℝ) (B : ℕ) (ξ : ℕ → Col m n × Bool) (t : ℕ)
    {p : Fin m × Fin n} (hp : ¬ stiffEntry p) : batchNoise hr s B ξ t p = 0 := by
  simp only [batchNoise, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_zero (fun j _ => noise_nonstiff hr s _ hp), mul_zero]

lemma batch_mean_split (hr : 0 < min m n) (f : Space m n → ℝ) (s : ℝ) {B : ℕ} (hB : 0 < B)
    (ξ : ℕ → Col m n × Bool) (t : ℕ) (X : Space m n) :
    (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, MomentumSeparationModel.sample hr f s X (ξ (B * t + j)) =
      gradient f X + batchNoise hr s B ξ t := by
  simp only [MomentumSeparationModel.sample, batchNoise, Finset.sum_add_distrib, smul_add,
    Finset.sum_const, Finset.card_range]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [one_div_mul_cancel hBr, one_smul]

section Iterates

variable (hr : 0 < min m n) (ℓ c s β η : ℝ) (φ : SeparationInstance.FlatShape) (B : ℕ)
  (x0 : Space m n) (direction : Space m n → Space m n) (κ : Space m n → ℝ)

noncomputable def iter (ξ : ℕ → Col m n × Bool) : ℕ → Space m n × Space m n :=
  sampledMomentum direction β η B x0
    (MomentumSeparationModel.sample hr (MomentumSeparationInstance.objective ℓ c φ x0) s) ξ

noncomputable def gain (ξ : ℕ → Col m n × Bool) (t : ℕ) : ℝ :=
  η * κ (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2

variable {hr ℓ c s β η φ B x0 direction κ}

lemma iter_succ_entry (hB : 0 < B) (hdir : ∀ M, direction M = κ M • M)
    (ξ : ℕ → Col m n × Bool) (t : ℕ) (p : Fin m × Fin n) :
    (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2 p =
        β * (iter hr ℓ c s β η φ B x0 direction ξ t).2 p + (1 - β) *
          (gradient (MomentumSeparationInstance.objective ℓ c φ x0)
            (iter hr ℓ c s β η φ B x0 direction ξ t).1 p + batchNoise hr s B ξ t p) ∧
      (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).1 p =
        (iter hr ℓ c s β η φ B x0 direction ξ t).1 p -
          gain hr ℓ c s β η φ B x0 direction κ ξ t *
            (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2 p := by
  have hM : (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2 =
      β • (iter hr ℓ c s β η φ B x0 direction ξ t).2 + (1 - β) •
        (gradient (MomentumSeparationInstance.objective ℓ c φ x0)
          (iter hr ℓ c s β η φ B x0 direction ξ t).1 + batchNoise hr s B ξ t) := by
    change β • (iter hr ℓ c s β η φ B x0 direction ξ t).2 + (1 - β) • ((1 / (B : ℝ)) •
      ∑ j ∈ Finset.range B, MomentumSeparationModel.sample hr
        (MomentumSeparationInstance.objective ℓ c φ x0) s
          (iter hr ℓ c s β η φ B x0 direction ξ t).1 (ξ (B * t + j))) = _
    rw [batch_mean_split hr _ s hB ξ t]
  constructor
  · rw [hM]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  · change ((iter hr ℓ c s β η φ B x0 direction ξ t).1 - η • direction
      (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2) p = _
    rw [hdir]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, gain]
    ring

lemma flat_entries (hB : 0 < B) (hdir : ∀ M, direction M = κ M • M) {w D : ℝ} (hw : 0 < w)
    (hφ : φ = SeparationInstance.valleyShape hw D) (ξ : ℕ → Col m n × Bool) {k : Fin (min m n)} (hk : k.val ≠ 0)
    (t : ℕ) :
    (iter hr ℓ c s β η φ B x0 direction ξ t).1 (dg k) - x0 (dg k) =
        (flat β c w D (gain hr ℓ c s β η φ B x0 direction κ ξ) t).1 ∧
      (iter hr ℓ c s β η φ B x0 direction ξ t).2 (dg k) =
        (flat β c w D (gain hr ℓ c s β η φ B x0 direction κ ξ) t).2 := by
  induction t with
  | zero => simp [iter, sampledMomentum, flat]
  | succ t ih =>
      obtain ⟨h1, h2⟩ := iter_succ_entry hB hdir ξ t (dg k)
      have hg := gradient_flat ℓ c φ x0 (iter hr ℓ c s β η φ B x0 direction ξ t).1 hk
      have hn := batchNoise_nonstiff hr s B ξ t (not_stiff_dg hk)
      rw [hg, hn, add_zero] at h1
      have hslope : φ.slope = SeparationInstance.valleySlope w D := by rw [hφ]; rfl
      have hM : (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2 (dg k) =
          (flat β c w D (gain hr ℓ c s β η φ B x0 direction κ ξ) (t + 1)).2 := by
        rw [h1, ih.2, show (iter hr ℓ c s β η φ B x0 direction ξ t).1 (dg k) - x0 (dg k) =
          (flat β c w D (gain hr ℓ c s β η φ B x0 direction κ ξ) t).1 from ih.1, hslope]
        rfl
      refine ⟨?_, hM⟩
      rw [h2, hM]
      change _ = (flat β c w D (gain hr ℓ c s β η φ B x0 direction κ ξ) t).1 -
        gain hr ℓ c s β η φ B x0 direction κ ξ t *
          (flat β c w D (gain hr ℓ c s β η φ B x0 direction κ ξ) (t + 1)).2
      rw [← ih.1]
      ring

lemma stiff_entries (hB : 0 < B) (hdir : ∀ M, direction M = κ M • M)
    (ξ : ℕ → Col m n × Bool) (i : Col m n) (t : ℕ) :
    (iter hr ℓ c s β η φ B x0 direction ξ t).1 ((row0 hr, colOf hr i) : Fin m × Fin n) -
        x0 ((row0 hr, colOf hr i) : Fin m × Fin n) =
        ∑ u ∈ Finset.range t, inputAt s B ξ i u *
          (impulse β ℓ (gain hr ℓ c s β η φ B x0 direction κ ξ) u t).1 ∧
      (iter hr ℓ c s β η φ B x0 direction ξ t).2 ((row0 hr, colOf hr i) : Fin m × Fin n) =
        ∑ u ∈ Finset.range t, inputAt s B ξ i u *
          (impulse β ℓ (gain hr ℓ c s β η φ B x0 direction κ ξ) u t).2 := by
  set α := gain hr ℓ c s β η φ B x0 direction κ ξ
  set p : Fin m × Fin n := (row0 hr, colOf hr i)
  induction t with
  | zero => simp [iter, sampledMomentum]
  | succ t ih =>
      obtain ⟨h1, h2⟩ := iter_succ_entry hB hdir ξ t p
      have hg := gradient_stiff ℓ c φ x0 (iter hr ℓ c s β η φ B x0 direction ξ t).1
        (stiffEntry_colOf hr i)
      have hn := batchNoise_stiff hr s B ξ t i
      rw [hg, hn] at h1
      have hz : impulse β ℓ α t t = (0, 0) := impulse_before β ℓ α t t le_rfl
      have hWt : (impulse β ℓ α t (t + 1)).2 = 1 - β := impulse_fresh_momentum β ℓ α t
      have hrest : ∀ u ∈ Finset.range t, inputAt s B ξ i u * (impulse β ℓ α u (t + 1)).2 =
          β * (inputAt s B ξ i u * (impulse β ℓ α u t).2) +
            (1 - β) * ℓ * (inputAt s B ξ i u * (impulse β ℓ α u t).1) := by
        intro u hu
        have hne : t ≠ u := (Nat.ne_of_lt (Finset.mem_range.mp hu)).symm
        change inputAt s B ξ i u * (β * (impulse β ℓ α u t).2 + (1 - β) *
          (ℓ * (impulse β ℓ α u t).1 + if t = u then 1 else 0)) = _
        rw [ite_eq_right hne]
        ring
      have hM : (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2 p =
          ∑ u ∈ Finset.range (t + 1), inputAt s B ξ i u * (impulse β ℓ α u (t + 1)).2 := by
        rw [h1, ih.2, ih.1, Finset.sum_range_succ, hWt, Finset.sum_congr rfl hrest,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
      refine ⟨?_, hM⟩
      have hR : ∑ u ∈ Finset.range (t + 1), inputAt s B ξ i u * (impulse β ℓ α u (t + 1)).1 =
          ∑ u ∈ Finset.range (t + 1), inputAt s B ξ i u * (impulse β ℓ α u t).1 -
            α t * ∑ u ∈ Finset.range (t + 1), inputAt s B ξ i u * (impulse β ℓ α u (t + 1)).2 := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro u _
        change inputAt s B ξ i u * ((impulse β ℓ α u t).1 - α t * (impulse β ℓ α u (t + 1)).2) = _
        ring
      rw [h2, hR, ← hM, Finset.sum_range_succ (fun u => inputAt s B ξ i u * (impulse β ℓ α u t).1),
        hz]
      have hg : gain hr ℓ c s β η φ B x0 direction κ ξ t = α t := rfl
      rw [hg]
      simp only [mul_zero, add_zero]
      linarith [ih.1]

end Iterates

lemma other_entries {hr : 0 < min m n} {ℓ c s β η : ℝ} {φ : SeparationInstance.FlatShape} {B : ℕ}
    {x0 : Space m n} {direction : Space m n → Space m n} {κ : Space m n → ℝ}
    (hB : 0 < B) (hdir : ∀ M, direction M = κ M • M) (ξ : ℕ → Col m n × Bool)
    {p : Fin m × Fin n} (hp : ¬ stiffEntry p) (hd : ∀ k : Fin (min m n), k.val ≠ 0 → dg k ≠ p)
    (t : ℕ) :
    (iter hr ℓ c s β η φ B x0 direction ξ t).1 p = x0 p ∧
      (iter hr ℓ c s β η φ B x0 direction ξ t).2 p = 0 := by
  induction t with
  | zero => simp [iter, sampledMomentum]
  | succ t ih =>
      obtain ⟨h1, h2⟩ := iter_succ_entry (κ := κ) hB hdir ξ t p
      rw [gradient_other ℓ c φ x0 _ hp hd, batchNoise_nonstiff hr s B ξ t hp, ih.2] at h1
      simp only [mul_zero, add_zero] at h1
      exact ⟨by rw [h2, h1, ih.1]; ring, h1⟩

lemma norm_sq_split (hr : 0 < min m n) (Y : Space m n)
    (hY : ∀ p : Fin m × Fin n, ¬ stiffEntry p → (∀ k : Fin (min m n), k.val ≠ 0 → dg k ≠ p) →
      Y p = 0) :
    ‖Y‖ ^ 2 = ∑ i : Col m n, Y ((row0 hr, colOf hr i) : Fin m × Fin n) ^ 2 +
      ∑ k ∈ (Finset.univ : Finset (Fin (min m n))).filter (fun k => k.val ≠ 0), Y (dg k) ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  set A := (Finset.univ : Finset (Col m n)).image
    (fun i => ((row0 hr, colOf hr i) : Fin m × Fin n)) with hA
  set Fl := ((Finset.univ : Finset (Fin (min m n))).filter (fun k => k.val ≠ 0)).image
    (dg (m := m) (n := n)) with hFl
  have hinjA : Set.InjOn (fun i => ((row0 hr, colOf hr i) : Fin m × Fin n))
      (Finset.univ : Finset (Col m n)) := fun a _ b _ h =>
    colOf_injective hr (congrArg Prod.snd h)
  have hdisj : Disjoint A Fl := by
    rw [Finset.disjoint_left]
    intro p hpA hpF
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hpA
    obtain ⟨k, hk, hkp⟩ := Finset.mem_image.mp hpF
    have hk0 := (Finset.mem_filter.mp hk).2
    exact not_stiff_dg hk0 (hkp ▸ stiffEntry_colOf hr i)
  have hsub : A ∪ Fl ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub, Finset.sum_union hdisj, Finset.sum_image (fun a ha b hb h => hinjA ha hb h),
    Finset.sum_image (fun a _ b _ h => dg_injective h)]
  intro p _ hp
  have hns : ¬ stiffEntry p := by
    intro hs
    obtain ⟨i, rfl⟩ := (stiffEntry_iff hr p).mp hs
    exact hp (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hnd : ∀ k : Fin (min m n), k.val ≠ 0 → dg k ≠ p := by
    intro k hk hkp
    exact hp (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, hkp⟩))
  rw [hY p hns hnd]
  ring

lemma stiffVec_norm_sq (hr : 0 < min m n) (x0 X : Space m n) :
    ‖stiffVec x0 X‖ ^ 2 = ∑ i : Col m n, (X ((row0 hr, colOf hr i) : Fin m × Fin n) -
      x0 ((row0 hr, colOf hr i) : Fin m × Fin n)) ^ 2 := by
  rw [norm_sq_split hr (stiffVec x0 X) (fun p hp _ => by simp [stiffVec, hp])]
  have h0 : ∑ k ∈ (Finset.univ : Finset (Fin (min m n))).filter (fun k => k.val ≠ 0),
      stiffVec x0 X (dg k) ^ 2 = 0 := Finset.sum_eq_zero fun k hk => by
    simp [stiffVec, not_stiff_dg (Finset.mem_filter.mp hk).2]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp [stiffVec, stiffEntry_colOf hr i]

def Distinct (B T : ℕ) (ξ : ℕ → Col m n × Bool) : Prop :=
  ∀ a b, a < B * T → b < B * T → a ≠ b → (ξ a).1 ≠ (ξ b).1

lemma inputAt_ne_zero {s : ℝ} {B : ℕ} {ξ : ℕ → Col m n × Bool} {i : Col m n} {u : ℕ}
    (h : inputAt s B ξ i u ≠ 0) : ∃ j < B, (ξ (B * u + j)).1 = i := by
  by_contra hcon
  push Not at hcon
  apply h
  unfold inputAt
  rw [Finset.sum_eq_zero (fun j hj => ite_eq_right (hcon j (Finset.mem_range.mp hj))), mul_zero]

lemma inputAt_orth {s : ℝ} {B T : ℕ} {ξ : ℕ → Col m n × Bool} (hd : Distinct B T ξ)
    (i : Col m n) {u v : ℕ} (hu : u < T) (hv : v < T) (huv : u ≠ v) :
    inputAt s B ξ i u * inputAt s B ξ i v = 0 := by
  by_contra hne
  obtain ⟨j, hj, hji⟩ := inputAt_ne_zero (left_ne_zero_of_mul hne)
  obtain ⟨j', hj', hji'⟩ := inputAt_ne_zero (right_ne_zero_of_mul hne)
  have h1 : B * u + j < B * T := by nlinarith
  have h2 : B * v + j' < B * T := by nlinarith
  have h3 : B * u + j ≠ B * v + j' := by
    intro he
    apply huv
    have := congrArg (· / B) he
    rwa [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj,
      Nat.div_eq_of_lt hj', Nat.add_zero, Nat.add_zero] at this
  exact hd _ _ h1 h2 h3 (hji.trans hji'.symm)

lemma sq_sum_orth {s : ℝ} {B T : ℕ} {ξ : ℕ → Col m n × Bool} (hd : Distinct B T ξ)
    (i : Col m n) (z : ℕ → ℝ) {t : ℕ} (ht : t ≤ T) :
    (∑ u ∈ Finset.range t, inputAt s B ξ i u * z u) ^ 2 =
      ∑ u ∈ Finset.range t, inputAt s B ξ i u ^ 2 * z u ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_eq_single u]
  · ring
  · intro v hv hvu
    have h := inputAt_orth (s := s) hd i (by have := Finset.mem_range.mp hu; omega)
      (by have := Finset.mem_range.mp hv; omega) (Ne.symm hvu)
    calc inputAt s B ξ i u * z u * (inputAt s B ξ i v * z v) =
          (inputAt s B ξ i u * inputAt s B ξ i v) * (z u * z v) := by ring
      _ = 0 := by rw [h, zero_mul]
  · intro h; exact absurd hu h

lemma inputAt_sq_sum {s : ℝ} {B T : ℕ} (hB : 0 < B) {ξ : ℕ → Col m n × Bool}
    (hd : Distinct B T ξ) {u : ℕ} (hu : u < T) :
    ∑ i : Col m n, inputAt s B ξ i u ^ 2 = s ^ 2 / B := by
  classical
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hinner : ∀ i : Col m n, (∑ j ∈ Finset.range B,
      if (ξ (B * u + j)).1 = i then s * AdamSeparationModel.sign (ξ (B * u + j)).2 else 0) ^ 2 =
      ∑ j ∈ Finset.range B, if (ξ (B * u + j)).1 = i then s ^ 2 else 0 := by
    intro i
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single j]
    · split_ifs
      · have hs1 : AdamSeparationModel.sign (ξ (B * u + j)).2 ^ 2 = 1 := by
          cases (ξ (B * u + j)).2 <;> simp [AdamSeparationModel.sign]
        calc s * AdamSeparationModel.sign (ξ (B * u + j)).2 *
              (s * AdamSeparationModel.sign (ξ (B * u + j)).2) =
              s ^ 2 * AdamSeparationModel.sign (ξ (B * u + j)).2 ^ 2 := by ring
          _ = s ^ 2 := by rw [hs1, mul_one]
      · ring
    · intro j' hj' hne
      by_cases h1 : (ξ (B * u + j)).1 = i
      · by_cases h2 : (ξ (B * u + j')).1 = i
        · exfalso
          have hj1 := Finset.mem_range.mp hj
          have hj2 := Finset.mem_range.mp hj'
          exact hd (B * u + j) (B * u + j') (by nlinarith) (by nlinarith) (by omega)
            (h1.trans h2.symm)
        · rw [ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    · intro h; exact absurd hj h
  have hcount : ∀ j : ℕ, (∑ i : Col m n, if (ξ (B * u + j)).1 = i then s ^ 2 else 0) = s ^ 2 := by
    intro j
    rw [Finset.sum_ite_eq]
    simp
  calc ∑ i : Col m n, inputAt s B ξ i u ^ 2 =
        ∑ i : Col m n, (1 / (B : ℝ)) ^ 2 * ∑ j ∈ Finset.range B,
          (if (ξ (B * u + j)).1 = i then s ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [inputAt, mul_pow, hinner]
    _ = (1 / (B : ℝ)) ^ 2 * ∑ j ∈ Finset.range B, s ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun j _ => hcount j
    _ = s ^ 2 / B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

section Path

variable {hr : 0 < min m n} {ℓ c s β η : ℝ} {φ : SeparationInstance.FlatShape} {B T : ℕ}
  {x0 : Space m n} {direction : Space m n → Space m n} {κ : Space m n → ℝ}

lemma range_extend_zero {β ℓ : ℝ} (α : ℕ → ℝ) (F : ℝ → ℝ) (hF : F 0 = 0) {t T : ℕ}
    (ht : t ≤ T) (sel : ℝ × ℝ → ℝ) (hsel : sel (0, 0) = 0) :
    ∑ u ∈ Finset.range t, F (sel (impulse β ℓ α u t)) =
      ∑ u ∈ Finset.range T, F (sel (impulse β ℓ α u t)) := by
  apply Finset.sum_subset (Finset.range_subset_range.mpr ht)
  intro u hu hut
  have : t ≤ u := by
    by_contra h
    exact hut (Finset.mem_range.mpr (by omega))
  rw [impulse_before β ℓ α u t this, hsel, hF]

lemma stiff_norm_good (hB : 0 < B) (hdir : ∀ M, direction M = κ M • M)
    (hs : 0 ≤ s) {ξ : ℕ → Col m n × Bool} (hd : Distinct B T ξ) {t : ℕ} (ht : t ≤ T) :
    ‖stiffVec x0 (iter hr ℓ c s β η φ B x0 direction ξ t).1‖ =
      s / Real.sqrt B * Real.sqrt (∑ u ∈ Finset.range T,
        ((impulse β ℓ (gain hr ℓ c s β η φ B x0 direction κ ξ) u t).1) ^ 2) := by
  set α := gain hr ℓ c s β η φ B x0 direction κ ξ
  have hsq : ‖stiffVec x0 (iter hr ℓ c s β η φ B x0 direction ξ t).1‖ ^ 2 =
      s ^ 2 / B * ∑ u ∈ Finset.range T, ((impulse β ℓ α u t).1) ^ 2 := by
    rw [stiffVec_norm_sq hr]
    simp_rw [(stiff_entries (κ := κ) hB hdir ξ _ t).1]
    simp_rw [sq_sum_orth (s := s) hd _ _ ht]
    rw [Finset.sum_comm]
    have hin : ∀ u ∈ Finset.range t, ∑ i : Col m n, inputAt s B ξ i u ^ 2 *
        (impulse β ℓ α u t).1 ^ 2 = s ^ 2 / B * (impulse β ℓ α u t).1 ^ 2 := by
      intro u hu
      rw [← Finset.sum_mul, inputAt_sq_sum hB hd (by have := Finset.mem_range.mp hu; omega)]
    rw [Finset.sum_congr rfl hin, ← Finset.mul_sum]
    congr 1
    exact range_extend_zero α (fun x => x ^ 2) (by ring) ht Prod.fst rfl
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_mul (by positivity), Real.sqrt_div' _ hB'.le,
    Real.sqrt_sq hs]

lemma momentum_norm_good (hB : 0 < B) (hdir : ∀ M, direction M = κ M • M) {w D : ℝ}
    (hw : 0 < w) (hφ : φ = SeparationInstance.valleyShape hw D)
    {ξ : ℕ → Col m n × Bool} (hd : Distinct B T ξ) {t : ℕ} (ht : t < T) :
    ‖(iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2‖ ^ 2 =
      s ^ 2 / B * ∑ u ∈ Finset.range T,
        ((impulse β ℓ (gain hr ℓ c s β η φ B x0 direction κ ξ) u (t + 1)).2) ^ 2 +
      ((min m n - 1 : ℕ) : ℝ) *
        ((flat β c w D (gain hr ℓ c s β η φ B x0 direction κ ξ) (t + 1)).2) ^ 2 := by
  set α := gain hr ℓ c s β η φ B x0 direction κ ξ
  rw [norm_sq_split hr _ (fun p hp hpd => (other_entries (κ := κ) hB hdir ξ hp hpd (t + 1)).2)]
  congr 1
  · simp_rw [(stiff_entries (κ := κ) hB hdir ξ _ (t + 1)).2]
    simp_rw [sq_sum_orth (s := s) hd _ _ (Nat.succ_le_of_lt ht)]
    rw [Finset.sum_comm]
    have hin : ∀ u ∈ Finset.range (t + 1), ∑ i : Col m n, inputAt s B ξ i u ^ 2 *
        (impulse β ℓ α u (t + 1)).2 ^ 2 = s ^ 2 / B * (impulse β ℓ α u (t + 1)).2 ^ 2 := by
      intro u hu
      rw [← Finset.sum_mul, inputAt_sq_sum hB hd (by have := Finset.mem_range.mp hu; omega)]
    rw [Finset.sum_congr rfl hin, ← Finset.mul_sum]
    congr 1
    exact range_extend_zero α (fun x => x ^ 2) (by ring) (Nat.succ_le_of_lt ht) Prod.snd rfl
  · have hfl : ∀ k ∈ (Finset.univ : Finset (Fin (min m n))).filter (fun k => k.val ≠ 0),
        (iter hr ℓ c s β η φ B x0 direction ξ (t + 1)).2 (dg k) ^ 2 =
          ((flat β c w D α (t + 1)).2) ^ 2 := by
      intro k hk
      rw [(flat_entries (κ := κ) hB hdir hw hφ ξ (Finset.mem_filter.mp hk).2 (t + 1)).2]
    rw [Finset.sum_congr rfl hfl, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (min m n))))
      (fun k => k.val ≠ 0)
    have hone : ((Finset.univ : Finset (Fin (min m n))).filter (fun k => ¬ k.val ≠ 0)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨⟨0, hr⟩, ?_⟩
      ext k
      simp [Fin.ext_iff]
    rw [hone, Finset.card_univ, Fintype.card_fin] at hc
    have : ((Finset.univ : Finset (Fin (min m n))).filter (fun k => k.val ≠ 0)).card =
        min m n - 1 := by omega
    rw [this]

end Path

end LongTails.Proofs.MomentumSeparationBridge
