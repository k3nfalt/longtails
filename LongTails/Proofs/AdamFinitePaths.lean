import LongTails.Proofs.AdamScalarProcess
import LongTails.Proofs.AdamTravelBound

namespace LongTails.Proofs.AdamFinitePaths

noncomputable def swapCoordinate {I Ω : Type*} [DecidableEq I] (i : I) :
    ((I → Ω) × Ω) ≃ ((I → Ω) × Ω) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv z := by simp
  right_inv z := by simp

lemma sum_coordinate_updates {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I]
    (i : I) (F : (I → Ω) → ℝ) :
    ∑ ω : I → Ω, ∑ v : Ω, F (Function.update ω i v) =
      (Fintype.card Ω : ℝ) * ∑ ω : I → Ω, F ω := by
  have h := (swapCoordinate (Ω := Ω) i).sum_comp (fun z => F z.1)
  simp only [Fintype.sum_prod_type, swapCoordinate, Equiv.coe_fn_mk,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at h
  exact h

lemma sum_conditional_le {I Ω : Type*} [Fintype I] [Fintype Ω] [Nonempty Ω]
    [DecidableEq I] (i : I) (F G : (I → Ω) → ℝ) (C : ℝ)
    (h : ∀ ω, ∑ v : Ω, F (Function.update ω i v) ≤
      C * ∑ v : Ω, G (Function.update ω i v)) :
    ∑ ω, F ω ≤ C * ∑ ω, G ω := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => h ω)
  rw [← Finset.mul_sum, sum_coordinate_updates, sum_coordinate_updates] at hh
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  nlinarith

open LongTails.Proofs.AdamRademacher

noncomputable def pathNoise (s : ℝ) (B H : ℕ) (ω : Fin H → Fin B → Bool) (j : ℕ) : ℝ :=
  if hj : j < H then batchNoise s B (ω ⟨j, hj⟩) else 0

lemma pathNoise_update (s : ℝ) (B H : ℕ) (ω : Fin H → Fin B → Bool)
    (t : Fin H) (v : Fin B → Bool) :
    pathNoise s B H (Function.update ω t v) =
      Function.update (pathNoise s B H ω) t.val (batchNoise s B v) := by
  funext j
  by_cases hj : j = t.val
  · subst j
    simp [pathNoise, t.isLt]
  · by_cases hjH : j < H
    · have hne : (⟨j, hjH⟩ : Fin H) ≠ t := by intro he; exact hj (congrArg Fin.val he)
      simp [pathNoise, hjH, Function.update_of_ne hj, Function.update_of_ne hne]
    · simp [pathNoise, hjH, Function.update_of_ne hj]

lemma batchNoise_scale {r : ℝ} (hr : r ≠ 0) (s : ℝ) (B : ℕ) (v : Fin B → Bool) :
    r * batchNoise (s / r) B v = batchNoise s B v := by
  unfold batchNoise
  field_simp

open LongTails.Setups.SpectralSmoothAdamComparison
open LongTails.Proofs.AdamScalarProcess

lemma path_coupling (a : AdamTuning) (ha : a.Valid) {r : ℝ} (hr : 0 < r)
    (ℓ c w D s : ℝ) (hs : 0 < s) (hcs : s / r ≤ c)
    {B H : ℕ} (hB : 0 < B) (t : Fin H) :
    ∑ ω : Fin H → Fin B → Bool,
      |diagDirection a r ℓ c w D (pathNoise s B H ω) t.val -
        offDirection a r ℓ c w D (pathNoise s B H ω) t.val| ≤
      (8 * c * B * (t.val + 1 : ℕ) ^ 2 / (s / r)) *
        ∑ ω : Fin H → Fin B → Bool, |offDirection a r ℓ c w D (pathNoise s B H ω) t.val| := by
  apply sum_conditional_le t
  intro ω
  have h := conditional_coupling a ha hr ℓ c w D (pathNoise s B H ω) t.val
    (flip B) (batchNoise (s / r) B) B (s / r)
    (batchNoise_flip (s / r) B) (batchNoise_bound (by positivity) hB)
    (batchNoise_absolute_lower (by positivity) hB) (by positivity) (by positivity) hcs
  simpa only [pathNoise_update, batchNoise_scale hr.ne'] using h

lemma path_step_bound (a : AdamTuning) (ha : a.Valid) {r : ℝ} (hr : 0 < r)
    (ℓ c w D s : ℝ) (hs : 0 < s) (hcs : s / r ≤ c)
    {B H T : ℕ} (hB : 0 < B) (t : Fin H) (ht : t.val < T) :
    let ξ := pathNoise s B H
    a.η * (∑ ω, |diagDirection a r ℓ c w D (ξ ω) t.val - offDirection a r ℓ c w D (ξ ω) t.val|) ≤
      (8 * c * B * T ^ 2 / s) *
        ((∑ ω, |(trajectory a r ℓ c w D (ξ ω) t.val).stiff|) +
          (∑ ω, |(trajectory a r ℓ c w D (ξ ω) (t.val + 1)).stiff|) +
          a.η * ∑ ω, |diagDirection a r ℓ c w D (ξ ω) t.val - offDirection a r ℓ c w D (ξ ω) t.val|) := by
  dsimp only
  have hc : 0 ≤ c := (div_pos hs hr).le.trans hcs
  have hcouple := path_coupling a ha hr ℓ c w D s hs hcs hB t
  have hpow : ((t.val + 1 : ℕ) : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by
    gcongr
    exact_mod_cast (show t.val + 1 ≤ T by omega)
  have hcoef : 8 * c * B * (t.val + 1 : ℕ) ^ 2 / (s / r) ≤
      (8 * c * B * T ^ 2 / s) * r := by
    rw [div_div_eq_mul_div]
    have := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 8 * c * B * r / s by positivity)
    convert this using 1 <;> ring
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    stiff_direction_bound a ha.1.le hr.le ℓ c w D (pathNoise s B H ω) t.val)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hbound
  have hcouple' := hcouple.trans (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  have hm := mul_le_mul_of_nonneg_left hcouple' ha.1.le
  have hn := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 8 * c * B * T ^ 2 / s by positivity)
  nlinarith

lemma path_travel_bound (a : AdamTuning) (ha : a.Valid) {r : ℝ} (hr : 0 < r)
    (ℓ c w D s : ℝ) (hs : 0 < s) (hcs : s / r ≤ c)
    {B T : ℕ} (hB : 0 < B) (hk : 8 * c * B * T ^ 2 / s ≤ (1 / 2 : ℝ)) :
    let ξ := pathNoise s B (T + 1)
    a.η * (∑ j ∈ Finset.range T, ∑ ω,
      |diagDirection a r ℓ c w D (ξ ω) j - offDirection a r ℓ c w D (ξ ω) j|) ≤
      4 * (8 * c * B * T ^ 2 / s) *
        ∑ j ∈ Finset.range (T + 1), ∑ ω, |(trajectory a r ℓ c w D (ξ ω) j).stiff| := by
  dsimp only
  rw [Finset.mul_sum]
  apply AdamTravelBound.absorbed_travel
  · have hc : 0 ≤ c := (div_pos hs hr).le.trans hcs
    positivity
  · exact hk
  · intro j
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · intro j hj
    exact path_step_bound a ha hr ℓ c w D s hs hcs hB ⟨j, by omega⟩ hj

lemma path_success_travel (a : AdamTuning) (hη : 0 ≤ a.η) (r ℓ R c w D ε : ℝ)
    (hR : 0 ≤ R) (hc : 0 ≤ c) (hw : 0 < w) (hD : 0 < D) (hε : 0 < ε)
    (hRc : R * c = 4 * ε) (hDw : 2 * w ≤ D) (B T : ℕ)
    (hsuccess : (∑ j : Fin (T + 1), ∑ ω : Fin (T + 1) → Fin B → Bool,
      R * |c * SeparationInstance.valleySlope w D
        (trajectory a r ℓ c w D (pathNoise ε B (T + 1) ω) j).quiet|) ≤
      (T + 1 : ℕ) * (Fintype.card (Fin (T + 1) → Fin B → Bool) : ℝ) * ε) :
    (Fintype.card (Fin (T + 1) → Fin B → Bool) : ℝ) * D / 4 ≤
      a.η * ∑ j ∈ Finset.range T, ∑ ω : Fin (T + 1) → Fin B → Bool,
        |diagDirection a r ℓ c w D (pathNoise ε B (T + 1) ω) j -
          offDirection a r ℓ c w D (pathNoise ε B (T + 1) ω) j| := by
  have h := AdamTravelBound.finite_barrier
    (fun (j : Fin (T + 1)) (ω : Fin (T + 1) → Fin B → Bool) =>
      R * |c * SeparationInstance.valleySlope w D
        (trajectory a r ℓ c w D (pathNoise ε B (T + 1) ω) j).quiet|)
    (fun ω => a.η * ∑ k ∈ Finset.range T,
      |diagDirection a r ℓ c w D (pathNoise ε B (T + 1) ω) k -
        offDirection a r ℓ c w D (pathNoise ε B (T + 1) ω) k|)
    hε hD.le (by simpa only [Fintype.card_fin] using hsuccess)
    (fun j ω => AdamSeparationInstance.quiet_cost_barrier hR hc hw hD hε.le hRc hDw
      (quiet_travel a hη r ℓ c w D (pathNoise ε B (T + 1) ω) T j (by omega)))
  rw [← Finset.mul_sum, Finset.sum_comm] at h
  exact h

end LongTails.Proofs.AdamFinitePaths
