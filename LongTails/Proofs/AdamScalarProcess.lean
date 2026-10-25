import LongTails.Proofs.AdamNoiseHistory
import LongTails.Proofs.AdamRademacher

namespace LongTails.Proofs.AdamScalarProcess

open LongTails.Setups.SpectralSmoothAdamComparison
open LongTails.Proofs.SeparationInstance

structure State where
  stiff : ℝ
  quiet : ℝ
  firstDiag : ℝ
  firstOff : ℝ
  secondDiag : ℝ
  secondOff : ℝ

noncomputable def quietGradient (c w D : ℝ) (z : State) : ℝ :=
  c * valleySlope w D z.quiet

noncomputable def offGradient (r ℓ c w D noise : ℝ) (z : State) : ℝ :=
  (ℓ * z.stiff + noise - quietGradient c w D z) / r

noncomputable def diagGradient (r ℓ c w D noise : ℝ) (z : State) : ℝ :=
  offGradient r ℓ c w D noise z + quietGradient c w D z

noncomputable def normalize (a : AdamTuning) (t : ℕ) (m v : ℝ) : ℝ :=
  (m / (1 - a.β₁ ^ (t + 1))) /
    (Real.sqrt (v / (1 - a.β₂ ^ (t + 1))) + a.τ)

noncomputable def step (a : AdamTuning) (r ℓ c w D : ℝ) (t : ℕ)
    (noise : ℝ) (z : State) : State :=
  let gd := diagGradient r ℓ c w D noise z
  let go := offGradient r ℓ c w D noise z
  let md := a.β₁ * z.firstDiag + (1 - a.β₁) * gd
  let mo := a.β₁ * z.firstOff + (1 - a.β₁) * go
  let vd := a.β₂ * z.secondDiag + (1 - a.β₂) * gd ^ 2
  let vo := a.β₂ * z.secondOff + (1 - a.β₂) * go ^ 2
  let dd := normalize a t md vd
  let doff := normalize a t mo vo
  ⟨z.stiff - a.η * (r * doff + (dd - doff)),
    z.quiet - a.η * (dd - doff), md, mo, vd, vo⟩

noncomputable def trajectory (a : AdamTuning) (r ℓ c w D : ℝ) (noise : ℕ → ℝ) : ℕ → State
  | 0 => ⟨0, 0, 0, 0, 0, 0⟩
  | t + 1 => step a r ℓ c w D t (noise t) (trajectory a r ℓ c w D noise t)

lemma gradient_difference {c : ℝ} (hc : 0 ≤ c) (r ℓ w D noise : ℝ) (z : State) :
    |diagGradient r ℓ c w D noise z - offGradient r ℓ c w D noise z| ≤ c := by
  simp only [diagGradient, add_sub_cancel_left, quietGradient, abs_mul, abs_of_nonneg hc]
  simpa using mul_le_mul_of_nonneg_left (abs_valleySlope_le w D z.quiet) hc

lemma trajectory_moments (a : AdamTuning) (r ℓ c w D : ℝ) (noise : ℕ → ℝ) (t : ℕ) :
    let z := trajectory a r ℓ c w D noise
    let gd := fun j => diagGradient r ℓ c w D (noise j) (z j)
    let go := fun j => offGradient r ℓ c w D (noise j) (z j)
    (z t).firstDiag = AdamHistory.ema a.β₁ gd t ∧
    (z t).firstOff = AdamHistory.ema a.β₁ go t ∧
    (z t).secondDiag = AdamHistory.ema a.β₂ (fun j => gd j ^ 2) t ∧
    (z t).secondOff = AdamHistory.ema a.β₂ (fun j => go j ^ 2) t := by
  induction t with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    dsimp only at ih ⊢
    rcases ih with ⟨hd, ho, hvd, hvo⟩
    simp only [trajectory, step, AdamHistory.ema, hd, ho, hvd, hvo, and_self]

lemma trajectory_prefix (a : AdamTuning) (r ℓ c w D : ℝ) (noise noise' : ℕ → ℝ)
    (t : ℕ) (h : ∀ j < t, noise j = noise' j) :
    trajectory a r ℓ c w D noise t = trajectory a r ℓ c w D noise' t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [trajectory, trajectory, ih (fun j hj => h j (by omega)), h t (by omega)]

noncomputable def diagHistory (a : AdamTuning) (r ℓ c w D : ℝ) (noise : ℕ → ℝ) (t : ℕ) : ℝ :=
  diagGradient r ℓ c w D (noise t) (trajectory a r ℓ c w D noise t)

noncomputable def offHistory (a : AdamTuning) (r ℓ c w D : ℝ) (noise : ℕ → ℝ) (t : ℕ) : ℝ :=
  offGradient r ℓ c w D (noise t) (trajectory a r ℓ c w D noise t)

noncomputable def diagDirection (a : AdamTuning) (r ℓ c w D : ℝ) (noise : ℕ → ℝ) (t : ℕ) : ℝ :=
  AdamHistory.direction a (diagHistory a r ℓ c w D noise) (t + 1)

noncomputable def offDirection (a : AdamTuning) (r ℓ c w D : ℝ) (noise : ℕ → ℝ) (t : ℕ) : ℝ :=
  AdamHistory.direction a (offHistory a r ℓ c w D noise) (t + 1)

lemma trajectory_step_coordinates (a : AdamTuning) (r ℓ c w D : ℝ) (noise : ℕ → ℝ) (t : ℕ) :
    let z := trajectory a r ℓ c w D noise
    let dd := diagDirection a r ℓ c w D noise t
    let doff := offDirection a r ℓ c w D noise t
    (z (t + 1)).stiff = (z t).stiff - a.η * (r * doff + (dd - doff)) ∧
    (z (t + 1)).quiet = (z t).quiet - a.η * (dd - doff) := by
  have hm := trajectory_moments a r ℓ c w D noise (t + 1)
  dsimp only at hm
  rcases hm with ⟨hd, ho, hvd, hvo⟩
  dsimp only [trajectory, step] at hd ho hvd hvo
  simp only [trajectory, step, normalize, diagDirection, offDirection, AdamHistory.direction,
    diagHistory, offHistory, hd, ho, hvd, hvo]
  exact ⟨rfl, rfl⟩

lemma trajectory_update_prefix (a : AdamTuning) (r ℓ c w D : ℝ) (noise : ℕ → ℝ)
    (t : ℕ) (v : ℝ) :
    trajectory a r ℓ c w D (Function.update noise t v) t = trajectory a r ℓ c w D noise t := by
  apply trajectory_prefix
  intro j hj
  exact Function.update_of_ne (by omega) _ _

lemma offHistory_update_prefix (a : AdamTuning) (r ℓ c w D : ℝ) (noise : ℕ → ℝ)
    (t j : ℕ) (hj : j < t) (v : ℝ) :
    offHistory a r ℓ c w D (Function.update noise t v) j = offHistory a r ℓ c w D noise j := by
  unfold offHistory
  rw [Function.update_of_ne (by omega : j ≠ t)]
  congr 1
  apply trajectory_prefix
  intro i hi
  exact Function.update_of_ne (by omega) _ _

lemma conditional_coupling {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (a : AdamTuning) (ha : a.Valid) {r : ℝ} (hr : 0 < r) (ℓ c w D : ℝ)
    (noise : ℕ → ℝ) (t : ℕ) (e : Ω ≃ Ω) (N : Ω → ℝ) (B s : ℝ)
    (hNsym : ∀ ω, N (e ω) = -N ω) (hNbound : ∀ ω, |N ω| ≤ s)
    (hnoise : (Fintype.card Ω : ℝ) * s ≤ B * ∑ ω, |N ω|)
    (hB : 0 < B) (hs : 0 < s) (hcs : s ≤ c) :
    let ξ := fun ω => Function.update noise t (r * N ω)
    ∑ ω, |diagDirection a r ℓ c w D (ξ ω) t - offDirection a r ℓ c w D (ξ ω) t| ≤
      (8 * c * B * (t + 1 : ℕ) ^ 2 / s) * ∑ ω, |offDirection a r ℓ c w D (ξ ω) t| := by
  dsimp only
  apply AdamNoiseHistory.history_coupling a ha t e N
    (fun ω => diagHistory a r ℓ c w D (Function.update noise t (r * N ω)))
    (fun ω => offHistory a r ℓ c w D (Function.update noise t (r * N ω)))
    (offHistory a r ℓ c w D noise)
    ((ℓ * (trajectory a r ℓ c w D noise t).stiff -
      quietGradient c w D (trajectory a r ℓ c w D noise t)) / r) c B s
  · intro ω j hj
    exact offHistory_update_prefix a r ℓ c w D noise t j hj _
  · intro ω
    simp only [offHistory, Function.update_self, trajectory_update_prefix, offGradient]
    field_simp
    ring
  · intro ω j _
    exact gradient_difference (hs.le.trans hcs) r ℓ w D _ _
  · exact hNsym
  · exact hNbound
  · exact hnoise
  · exact hB
  · exact hs
  · exact hcs

lemma quiet_travel (a : AdamTuning) (hη : 0 ≤ a.η) (r ℓ c w D : ℝ)
    (noise : ℕ → ℝ) (T j : ℕ) (hj : j ≤ T) :
    |(trajectory a r ℓ c w D noise j).quiet| ≤ a.η *
      ∑ k ∈ Finset.range T, |diagDirection a r ℓ c w D noise k - offDirection a r ℓ c w D noise k| := by
  have hbase (j : ℕ) : |(trajectory a r ℓ c w D noise j).quiet| ≤ a.η *
      ∑ k ∈ Finset.range j, |diagDirection a r ℓ c w D noise k - offDirection a r ℓ c w D noise k| := by
    induction j with
    | zero => simp [trajectory]
    | succ j ih =>
      rw [(trajectory_step_coordinates a r ℓ c w D noise j).2, Finset.sum_range_succ]
      have habs := abs_add_le (trajectory a r ℓ c w D noise j).quiet
        (-(a.η * (diagDirection a r ℓ c w D noise j - offDirection a r ℓ c w D noise j)))
      simp only [abs_neg, abs_mul, abs_of_nonneg hη] at habs
      rw [sub_eq_add_neg]
      nlinarith
  refine (hbase j).trans (mul_le_mul_of_nonneg_left ?_ hη)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj) (fun k _ _ => abs_nonneg _)

lemma stiff_direction_bound (a : AdamTuning) (hη : 0 ≤ a.η) {r : ℝ} (hr : 0 ≤ r)
    (ℓ c w D : ℝ) (noise : ℕ → ℝ) (j : ℕ) :
    a.η * r * |offDirection a r ℓ c w D noise j| ≤
      |(trajectory a r ℓ c w D noise j).stiff| +
      |(trajectory a r ℓ c w D noise (j + 1)).stiff| +
      a.η * |diagDirection a r ℓ c w D noise j - offDirection a r ℓ c w D noise j| := by
  have heq : a.η * r * offDirection a r ℓ c w D noise j =
      (trajectory a r ℓ c w D noise j).stiff -
        (trajectory a r ℓ c w D noise (j + 1)).stiff -
        a.η * (diagDirection a r ℓ c w D noise j - offDirection a r ℓ c w D noise j) := by
    rw [(trajectory_step_coordinates a r ℓ c w D noise j).1]
    ring
  have h := abs_add_le
    ((trajectory a r ℓ c w D noise j).stiff - (trajectory a r ℓ c w D noise (j + 1)).stiff)
    (-(a.η * (diagDirection a r ℓ c w D noise j - offDirection a r ℓ c w D noise j)))
  have h' := abs_add_le (trajectory a r ℓ c w D noise j).stiff
    (-(trajectory a r ℓ c w D noise (j + 1)).stiff)
  simp only [← sub_eq_add_neg, ← heq, abs_neg, abs_mul, abs_of_nonneg hη, abs_of_nonneg hr] at h h'
  linarith

end LongTails.Proofs.AdamScalarProcess
