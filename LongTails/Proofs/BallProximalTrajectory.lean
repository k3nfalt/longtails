import LongTails.Proofs.BallProximalEnergy
import LongTails.Proofs.BallProximalSupport
import LongTails.Proofs.BallProximalProfile

open scoped RealInnerProductSpace

namespace OracleTemplate.BallProximal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialProfile (t : ℝ) (c : ℕ → ℝ) : ℕ → List (ℝ × ℝ)
  | 0 => []
  | N + 1 => (t, c 0 * t) :: radialProfile t (fun i => c (i + 1)) N

lemma radialProfile_time (t : ℝ) (c : ℕ → ℝ) (N : ℕ) :
    profileTime (radialProfile t c N) = N * t := by
  induction N generalizing c with
  | zero => simp [radialProfile, profileTime]
  | succ N ih => simp [radialProfile, profileTime, ih, Nat.cast_add]; ring

lemma radialProfile_mem {t : ℝ} {c : ℕ → ℝ} {N : ℕ} {q : ℝ × ℝ}
    (hq : q ∈ radialProfile t c N) : ∃ i < N, q = (t, c i * t) := by
  induction N generalizing c with
  | zero => simp [radialProfile] at hq
  | succ N ih =>
      simp only [radialProfile, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨0, by omega, rfl⟩
      · obtain ⟨i, hi, he⟩ := ih hq
        exact ⟨i + 1, by omega, he⟩

lemma radialProfile_mass {C : Set E} {f : E → ℝ} {x : ℕ → E}
    {c : ℕ → ℝ} {t : ℝ} {N : ℕ}
    (hx : ∀ i ≤ N, x i ∈ C)
    (hs : ∀ i < N, ‖x i - x (i + 1)‖ = t ∧
      ∀ w ∈ C, f (x (i + 1)) + ⟪c i • (x i - x (i + 1)), w - x (i + 1)⟫ ≤ f w) :
    profileMass (radialProfile t c N) ≤ f (x 0) - f (x N) := by
  induction N generalizing x c with
  | zero => simp [radialProfile, profileMass]
  | succ N ih =>
      have h0 := hs 0 (by omega)
      have hp := radial_progress (h0.2 (x 0) (hx 0 (by omega))) h0.1
      have hh := ih (x := fun i => x (i + 1)) (c := fun i => c (i + 1))
        (fun i hi => hx (i + 1) (by omega)) (fun i hi => hs (i + 1) (by omega))
      simp only [radialProfile, profileMass]
      simpa only [zero_add] using (show t * (c 0 * t) +
        profileMass (radialProfile t (fun i => c (i + 1)) N) ≤
        f (x 0) - f (x (N + 1)) by nlinarith [hp, hh])

lemma radialProfile_energy {C : Set E} {f : E → ℝ} {x : ℕ → E}
    {c : ℕ → ℝ} {t : ℝ} {N : ℕ} {z : E} (ht : 0 < t) (hz : z ∈ C)
    (hx : ∀ i ≤ N, x i ∈ C) (hc : ∀ i < N, 0 < c i)
    (hs : ∀ i < N, ‖x i - x (i + 1)‖ = t ∧
      ∀ w ∈ C, f (x (i + 1)) + ⟪c i • (x i - x (i + 1)), w - x (i + 1)⟫ ≤ f w) :
    profileWork (f (x N) - f z) (radialProfile t c N) + ‖x N - z‖ ^ 2 ≤
      ‖x 0 - z‖ ^ 2 := by
  induction N generalizing x c with
  | zero => simp [radialProfile, profileWork]
  | succ N ih =>
      have h0 := hs 0 (by omega)
      have hc0 := hc 0 (by omega)
      have hx' : ∀ i ≤ N, x (i + 1) ∈ C := fun i hi => hx (i + 1) (by omega)
      have hs' := fun i (hi : i < N) => hs (i + 1) (by omega)
      have hh := ih hx' (fun i hi => hc (i + 1) (by omega)) hs'
      have hm := radialProfile_mass hx' hs'
      have hd := radial_distance (h0.2 z hz) h0.1
      have he : 2 * t * (f (x (N + 1)) - f z +
          profileMass (radialProfile t (fun i => c (i + 1)) N)) / (c 0 * t) =
          2 * (f (x (N + 1)) - f z +
          profileMass (radialProfile t (fun i => c (i + 1)) N)) / c 0 := by field_simp
      simp only [radialProfile, profileWork, he]
      have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 / c 0 by positivity)
      have hd' : ‖x 1 - z‖ ^ 2 + t ^ 2 + 2 * (f (x 1) - f z) / c 0 ≤
          ‖x 0 - z‖ ^ 2 := by
        apply (mul_le_mul_iff_left₀ hc0).mp
        field_simp
        nlinarith [hd]
      simp only [zero_add] at hh hm'
      simp only [div_eq_mul_inv] at hm' hd' ⊢
      nlinarith [hh]


lemma radial_slopes_antitone {C : Set E} {f : E → ℝ} {x : ℕ → E}
    {c : ℕ → ℝ} {t : ℝ} {N : ℕ} (ht : 0 < t)
    (hx : ∀ i ≤ N, x i ∈ C) (hc : ∀ i < N, 0 < c i)
    (hs : ∀ i < N, ‖x i - x (i + 1)‖ = t ∧
      ∀ w ∈ C, f (x (i + 1)) + ⟪c i • (x i - x (i + 1)), w - x (i + 1)⟫ ≤ f w)
    {i j : ℕ} (hij : i ≤ j) (hj : j < N) : c j * t ≤ c i * t := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
      have hjN : j < N := by omega
      have h0 := hs j hjN
      have h1 := hs (j + 1) hj
      have hstep := radial_norm_antitone (hc j hjN).le ht h0.1 h1.1
        (h0.2 (x (j + 1 + 1)) (hx _ (by omega))) (h1.2 (x (j + 1)) (hx _ (by omega)))
      exact le_trans hstep (ih hjN)

lemma radialProfile_terminal_energy {C : Set E} {f : E → ℝ} {x : ℕ → E}
    {c : ℕ → ℝ} {t : ℝ} {N : ℕ} {z : E} (ht : 0 < t) (hz : z ∈ C)
    (hx : ∀ i ≤ N + 1, x i ∈ C) (hc : ∀ i < N + 1, 0 < c i)
    (hs : ∀ i < N + 1, ‖x i - x (i + 1)‖ = t ∧
      ∀ w ∈ C, f (x (i + 1)) + ⟪c i • (x i - x (i + 1)), w - x (i + 1)⟫ ≤ f w)
    (hg : 0 ≤ f (x (N + 1)) - f z) :
    profileWork (f (x (N + 1)) - f z) (radialProfile t c (N + 1)) +
      ((f (x (N + 1)) - f z) / (c N * t)) ^ 2 ≤ ‖x 0 - z‖ ^ 2 := by
  have hl := hs N (by omega)
  have ht' := radial_terminal (hc N (by omega)).le (hl.2 z hz) hl.1
  have hd : 0 < c N * t := mul_pos (hc N (by omega)) ht
  have hb : (f (x (N + 1)) - f z) / (c N * t) ≤ ‖x (N + 1) - z‖ :=
    (div_le_iff₀ hd).mpr (by nlinarith [ht'])
  have hb2 := pow_le_pow_left₀ (div_nonneg hg hd.le) hb 2
  linarith [radialProfile_energy ht hz hx hc hs]

lemma radialProfile_mass_pos {t : ℝ} {c : ℕ → ℝ} {N : ℕ} (ht : 0 < t)
    (hc : ∀ i < N + 1, 0 < c i) : 0 < profileMass (radialProfile t c (N + 1)) := by
  have hv : ∀ q ∈ radialProfile t (fun i => c (i + 1)) N, 0 ≤ q.1 ∧ 0 < q.2 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
    exact ⟨ht.le, mul_pos (hc _ (by omega)) ht⟩
  have hn := (profile_nonneg (fun q hq => (hv q hq).1) (fun q hq => (hv q hq).2)).2.1
  have hfirst : 0 < t * (c 0 * t) := mul_pos ht (mul_pos (hc 0 (by omega)) ht)
  simp only [radialProfile, profileMass]
  linarith


lemma radialProfile_mass_eq {t : ℝ} {c F : ℕ → ℝ} {N : ℕ}
    (hF : ∀ i < N, F i = F (i + 1) + c i * t ^ 2) :
    profileMass (radialProfile t c N) = F 0 - F N := by
  induction N generalizing c F with
  | zero => simp [radialProfile, profileMass]
  | succ N ih =>
      have hh := ih (c := fun i => c (i + 1)) (F := fun i => F (i + 1))
        (fun i hi => hF (i + 1) (by omega))
      simp only [radialProfile, profileMass, hh]
      have h0 := hF 0 (by omega)
      simp only [zero_add] at h0 ⊢
      nlinarith

lemma radialProfile_energy_eq {t : ℝ} {c F D : ℕ → ℝ} {N : ℕ} (ht : 0 < t)
    (hF : ∀ i < N, F i = F (i + 1) + c i * t ^ 2)
    (hD : ∀ i < N, D i = t ^ 2 + 2 * F (i + 1) / c i + D (i + 1)) :
    profileWork (F N) (radialProfile t c N) + D N = D 0 := by
  induction N generalizing c F D with
  | zero => simp [radialProfile, profileWork]
  | succ N ih =>
      have hF' := fun i (hi : i < N) => hF (i + 1) (by omega)
      have hh := ih hF' (fun i hi => hD (i + 1) (by omega))
      have hm := radialProfile_mass_eq hF'
      have h0 := hD 0 (by omega)
      simp only [radialProfile, profileWork, hm, zero_add]
      rw [show F (N + 1) + (F 1 - F (N + 1)) = F 1 by ring]
      have he : 2 * t * F 1 / (c 0 * t) = 2 * F 1 / c 0 := by
        by_cases hc : c 0 = 0
        · simp [hc]
        · field_simp
      rw [he]
      simp only [zero_add] at hh h0
      linarith


lemma radialProfile_scale_mass (t : ℝ) (c : ℕ → ℝ) (N : ℕ) (b : ℝ) :
    profileMass (radialProfile t (fun i => b * c i) N) = b * profileMass (radialProfile t c N) := by
  induction N generalizing c with
  | zero => simp [radialProfile, profileMass]
  | succ N ih => simp only [radialProfile, profileMass, ih]; ring

lemma radialProfile_scale_work (t : ℝ) (c : ℕ → ℝ) (N : ℕ) (r : ℝ) {b : ℝ} (hb : b ≠ 0) :
    profileWork r (radialProfile t (fun i => b * c i) N) =
      profileWork (r / b) (radialProfile t c N) := by
  induction N generalizing c with
  | zero => simp [radialProfile, profileWork]
  | succ N ih =>
      simp only [radialProfile, profileWork, ih, radialProfile_scale_mass]
      by_cases hc : c 0 = 0
      · simp [hc]
      · by_cases ht : t = 0
        · simp [ht]
        · field_simp

lemma radialProfile_scale_energy_le {t r b : ℝ} {c : ℕ → ℝ} {N : ℕ}
    (ht : 0 ≤ t) (hr : 0 ≤ r) (hb : 1 ≤ b) (hc : ∀ i < N, 0 < c i * t)
    {j : ℕ} (hj : j < N) :
    profileWork r (radialProfile t (fun i => b * c i) N) + (r / (b * (c j * t))) ^ 2 ≤
      profileWork r (radialProfile t c N) + (r / (c j * t)) ^ 2 := by
  have hb0 : 0 < b := by linarith
  rw [radialProfile_scale_work t c N r (ne_of_gt hb0)]
  have hv : ∀ q ∈ radialProfile t c N, 0 ≤ q.1 ∧ 0 < q.2 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
    exact ⟨ht, hc i hi⟩
  have hn := (profile_nonneg (fun q hq => (hv q hq).1) (fun q hq => (hv q hq).2)).2.2
  have hratio : r / b ≤ r := (div_le_iff₀ hb0).mpr (by nlinarith)
  have hw : profileWork (r / b) (radialProfile t c N) ≤ profileWork r (radialProfile t c N) := by
    rw [profile_work_affine _ (r / b), profile_work_affine _ r]
    nlinarith
  have hd : c j * t ≤ b * (c j * t) := by nlinarith [hc j hj]
  have hres := div_le_div_of_nonneg_left hr (hc j hj) hd
  have hres2 := pow_le_pow_left₀ (div_nonneg hr (mul_pos hb0 (hc j hj)).le) hres 2
  linarith


lemma normalize_profile {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ} {r : ℝ}
    (hap : ∀ i < N, 0 < a i) (ham : ∀ i j, i ≤ j → j < N → a j ≤ a i)
    (hr : 0 ≤ r) (hA : profileMass (radialProfile 1 a N) ≤ 1 - r) :
    ∃ b : ℕ → ℝ, (∀ i < N, 0 < b i) ∧
      (∀ i j, i ≤ j → j < N → b j ≤ b i) ∧
      profileMass (radialProfile 1 b N) = 1 - r ∧
      profileWork r (radialProfile 1 b N) + (r / b (N - 1)) ^ 2 ≤
        profileWork r (radialProfile 1 a N) + (r / a (N - 1)) ^ 2 := by
  have hmass : 0 < profileMass (radialProfile 1 a N) := by
    cases N with
    | zero => omega
    | succ N => exact radialProfile_mass_pos (by norm_num) hap
  let scale := (1 - r) / profileMass (radialProfile 1 a N)
  have hscale : 1 ≤ scale := (one_le_div hmass).mpr hA
  have hscale0 : 0 < scale := by linarith
  refine ⟨fun i => scale * a i, fun i hi => mul_pos hscale0 (hap i hi),
    fun i j hij hj => mul_le_mul_of_nonneg_left (ham i j hij hj) hscale0.le, ?_, ?_⟩
  · rw [radialProfile_scale_mass]
    exact div_mul_cancel₀ _ (ne_of_gt hmass)
  · simpa using radialProfile_scale_energy_le (t := 1) (c := a) (N := N)
      (by norm_num) hr hscale (by simpa using hap) (j := N - 1) (by omega)

lemma radialProfile_work_lower {t r : ℝ} {c : ℕ → ℝ} {N : ℕ}
    (ht : 0 ≤ t) (hr : 0 ≤ r) (hc : ∀ i < N, 0 < c i * t) :
    (N : ℝ) * t ^ 2 ≤ profileWork r (radialProfile t c N) := by
  induction N generalizing c with
  | zero => simp [radialProfile, profileWork]
  | succ N ih =>
      have hc' : ∀ i < N, 0 < c (i + 1) * t := fun i hi => hc (i + 1) (by omega)
      have hv : ∀ q ∈ radialProfile t (fun i => c (i + 1)) N, 0 ≤ q.1 ∧ 0 < q.2 := by
        intro q hq
        obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
        exact ⟨ht, hc' i hi⟩
      have hn := (profile_nonneg (fun q hq => (hv q hq).1) (fun q hq => (hv q hq).2)).2.1
      have hp : 0 ≤ 2 * t * (r + profileMass (radialProfile t (fun i => c (i + 1)) N)) /
          (c 0 * t) := div_nonneg (by positivity) (hc 0 (by omega)).le
      have hh := ih hc'
      simp only [radialProfile, profileWork, Nat.cast_add, Nat.cast_one]
      nlinarith

end

end OracleTemplate.BallProximal
