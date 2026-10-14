import LongTails.Proofs.BallProximalScalar

namespace OracleTemplate.BallProximal

noncomputable section

def profileTime : List (ℝ × ℝ) → ℝ
  | [] => 0
  | q :: qs => q.1 + profileTime qs

def profileMass : List (ℝ × ℝ) → ℝ
  | [] => 0
  | q :: qs => q.1 * q.2 + profileMass qs

def profileInverse : List (ℝ × ℝ) → ℝ
  | [] => 0
  | q :: qs => q.1 / q.2 + profileInverse qs

def profileWork (r : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | q :: qs => q.1 ^ 2 + 2 * q.1 * (r + profileMass qs) / q.2 + profileWork r qs

lemma profile_nonneg {qs : List (ℝ × ℝ)}
    (ht : ∀ q ∈ qs, 0 ≤ q.1) (ha : ∀ q ∈ qs, 0 < q.2) :
    0 ≤ profileTime qs ∧ 0 ≤ profileMass qs ∧ 0 ≤ profileInverse qs := by
  induction qs with
  | nil => simp [profileTime, profileMass, profileInverse]
  | cons q qs ih =>
      have htq := ht q (by simp)
      have haq := ha q (by simp)
      have htail := ih (fun z hz => ht z (by simp [hz])) (fun z hz => ha z (by simp [hz]))
      simp only [profileTime, profileMass, profileInverse]
      exact ⟨add_nonneg htq htail.1, add_nonneg (mul_nonneg htq haq.le) htail.2.1,
        add_nonneg (div_nonneg htq haq.le) htail.2.2⟩

lemma profile_mass_lower {qs : List (ℝ × ℝ)} {m : ℝ}
    (ht : ∀ q ∈ qs, 0 ≤ q.1) (ha : ∀ q ∈ qs, m ≤ q.2) :
    m * profileTime qs ≤ profileMass qs := by
  induction qs with
  | nil => simp [profileTime, profileMass]
  | cons q qs ih =>
      have hq := mul_le_mul_of_nonneg_left (ha q (by simp)) (ht q (by simp))
      have htail := ih (fun z hz => ht z (by simp [hz])) (fun z hz => ha z (by simp [hz]))
      simp only [profileTime, profileMass]
      nlinarith

lemma profile_cauchy {qs : List (ℝ × ℝ)}
    (ht : ∀ q ∈ qs, 0 ≤ q.1) (ha : ∀ q ∈ qs, 0 < q.2) :
    (profileTime qs) ^ 2 ≤ profileMass qs * profileInverse qs := by
  induction qs with
  | nil => simp [profileTime, profileMass, profileInverse]
  | cons q qs ih =>
      have htq := ht q (by simp)
      have haq := ha q (by simp)
      have ht' : ∀ z ∈ qs, 0 ≤ z.1 := fun z hz => ht z (by simp [hz])
      have ha' : ∀ z ∈ qs, 0 < z.2 := fun z hz => ha z (by simp [hz])
      have hn := profile_nonneg ht' ha'
      have hq : q.1 ^ 2 ≤ (q.1 * q.2) * (q.1 / q.2) := by field_simp; rfl
      exact cauchy_combine (mul_nonneg htq haq.le) (div_nonneg htq haq.le)
        hn.2.1 hn.2.2 hq (ih ht' ha')

lemma profile_work_affine (qs : List (ℝ × ℝ)) (r : ℝ) :
    profileWork r qs = profileWork 0 qs + 2 * r * profileInverse qs := by
  induction qs with
  | nil => simp [profileWork, profileInverse]
  | cons q qs ih => simp only [profileWork, profileInverse, ih]; ring

lemma aggregate_cross_lower {a m H A : ℝ} (hm : 0 < m) (ha : m ≤ a)
    (hH : 0 ≤ H) (hA : m * H ≤ A) :
    3 * m * H - a * H - A ≤ m * A / a := by
  apply (le_div_iff₀ (lt_of_lt_of_le hm ha)).mpr
  have h1 := mul_nonneg (show 0 ≤ m + a by linarith) (sub_nonneg.mpr hA)
  have h2 := mul_nonneg (sq_nonneg (a - m)) hH
  nlinarith

lemma profile_pair_lower {qs : List (ℝ × ℝ)} {m : ℝ} (hm : 0 < m)
    (ht : ∀ q ∈ qs, 0 ≤ q.1) (ha : ∀ q ∈ qs, m ≤ q.2) :
    m * (profileTime qs) ^ 2 -
      2 * profileTime qs * (profileMass qs - m * profileTime qs) ≤
      m * profileWork 0 qs := by
  induction qs with
  | nil => simp [profileTime, profileMass, profileWork]
  | cons q qs ih =>
      have htq := ht q (by simp)
      have haq := ha q (by simp)
      have ht' : ∀ z ∈ qs, 0 ≤ z.1 := fun z hz => ht z (by simp [hz])
      have ha' : ∀ z ∈ qs, m ≤ z.2 := fun z hz => ha z (by simp [hz])
      have hn := profile_nonneg ht' (fun z hz => lt_of_lt_of_le hm (ha' z hz))
      have hcross := aggregate_cross_lower hm haq hn.1 (profile_mass_lower ht' ha')
      have hmul := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 2 * q.1 by positivity)
      have htail := ih ht' ha'
      have hdiag := mul_nonneg (sq_nonneg q.1) (sub_nonneg.mpr haq)
      simp only [profileTime, profileMass, profileWork, zero_add]
      simp only [div_eq_mul_inv] at hmul ⊢
      nlinarith


lemma profile_work_nonneg {qs : List (ℝ × ℝ)} {r : ℝ} (hr : 0 ≤ r)
    (ht : ∀ q ∈ qs, 0 ≤ q.1) (ha : ∀ q ∈ qs, 0 < q.2) :
    0 ≤ profileWork r qs := by
  induction qs with
  | nil => simp [profileWork]
  | cons q qs ih =>
      have htq := ht q (by simp)
      have haq := ha q (by simp)
      have ht' : ∀ z ∈ qs, 0 ≤ z.1 := fun z hz => ht z (by simp [hz])
      have ha' : ∀ z ∈ qs, 0 < z.2 := fun z hz => ha z (by simp [hz])
      have hn := profile_nonneg ht' ha'
      have hi := ih ht' ha'
      have hmass := hn.2.1
      simp only [profileWork]
      positivity

lemma profile_high_gap {qs : List (ℝ × ℝ)} {m r : ℝ} (hm : 0 < m)
    (ht : ∀ q ∈ qs, 0 ≤ q.1) (ha : ∀ q ∈ qs, m ≤ q.2)
    (hA : 0 < profileMass qs) (hr : profileMass qs ≤ r) :
    (profileTime qs) ^ 2 * (profileMass qs + r) ^ 2 ≤
      (profileMass qs) ^ 2 * (profileWork r qs + (r / m) ^ 2) := by
  have hap : ∀ q ∈ qs, 0 < q.2 := fun q hq => lt_of_lt_of_le hm (ha q hq)
  have hn := profile_nonneg ht hap
  have hz : profileTime qs ≤ profileMass qs / m :=
    (le_div_iff₀ hm).mpr (by simpa [mul_comm] using profile_mass_lower ht ha)
  have hp := profile_pair_lower hm ht ha
  have hp' : (profileTime qs) ^ 2 -
      2 * profileTime qs * (profileMass qs / m - profileTime qs) ≤ profileWork 0 qs := by
    apply (mul_le_mul_iff_left₀ hm).mp
    field_simp at *
    nlinarith [hp]
  have hh := high_gap_algebra hn.1 hA hr hz (profile_cauchy ht hap) hp'
  rw [profile_work_affine qs r]
  convert hh using 1
  ring

lemma profile_logarithmic {qs : List (ℝ × ℝ)} {r : ℝ} (hr : 0 < r)
    (ht : ∀ q ∈ qs, 0 ≤ q.1) (ha : ∀ q ∈ qs, 0 < q.2) :
    2 * (profileTime qs) ^ 2 ≤
      (Real.log (r + profileMass qs) - Real.log r) * profileWork r qs := by
  induction qs with
  | nil => simp [profileTime, profileMass, profileWork]
  | cons q qs ih =>
      have htq := ht q (by simp)
      have haq := ha q (by simp)
      have ht' : ∀ z ∈ qs, 0 ≤ z.1 := fun z hz => ht z (by simp [hz])
      have ha' : ∀ z ∈ qs, 0 < z.2 := fun z hz => ha z (by simp [hz])
      have hn := profile_nonneg ht' ha'
      have hr' : 0 < r + profileMass qs := by linarith
      have hq := one_piece_logarithmic htq haq hr'
      have hi := ih ht' ha'
      have hl1 : 0 ≤ Real.log (r + profileMass qs + q.1 * q.2) -
          Real.log (r + profileMass qs) := sub_nonneg.mpr
        (Real.log_le_log hr' (by nlinarith [mul_nonneg htq haq.le]))
      have hl2 : 0 ≤ Real.log (r + profileMass qs) - Real.log r :=
        sub_nonneg.mpr (Real.log_le_log hr (by linarith))
      have hw : 0 ≤ q.1 ^ 2 + 2 * q.1 * (r + profileMass qs) / q.2 := by positivity
      have hh := cauchy_combine (x := q.1) (y := profileTime qs) (show 0 ≤ (Real.log (r + profileMass qs + q.1 * q.2) -
          Real.log (r + profileMass qs)) / 2 by positivity) hw
        (show 0 ≤ (Real.log (r + profileMass qs) - Real.log r) / 2 by positivity)
        (profile_work_nonneg hr.le ht' ha') (by nlinarith [hq]) (by nlinarith [hi])
      simp only [profileTime, profileMass, profileWork]
      have he : r + (q.1 * q.2 + profileMass qs) = r + profileMass qs + q.1 * q.2 := by ring
      rw [he]
      nlinarith [hh]


lemma profile_time_append (ps qs : List (ℝ × ℝ)) :
    profileTime (ps ++ qs) = profileTime ps + profileTime qs := by
  induction ps with
  | nil => simp [profileTime]
  | cons p ps ih => simp [profileTime, ih, add_assoc]

lemma profile_mass_append (ps qs : List (ℝ × ℝ)) :
    profileMass (ps ++ qs) = profileMass ps + profileMass qs := by
  induction ps with
  | nil => simp [profileMass]
  | cons p ps ih => simp [profileMass, ih, add_assoc]

lemma profile_work_append (ps qs : List (ℝ × ℝ)) (r : ℝ) :
    profileWork r (ps ++ qs) = profileWork (r + profileMass qs) ps + profileWork r qs := by
  induction ps with
  | nil => simp [profileWork]
  | cons p ps ih => simp only [List.cons_append, profileWork, profile_mass_append, ih]; ring

lemma profile_split {qs : List (ℝ × ℝ)} {m B : ℝ} (hm : 0 < m)
    (hv : ∀ q ∈ qs, 0 ≤ q.1 ∧ m ≤ q.2) (hB : 0 ≤ B) (hBA : B ≤ profileMass qs) :
    ∃ ps ss : List (ℝ × ℝ),
      (∀ q ∈ ps ++ ss, 0 ≤ q.1 ∧ m ≤ q.2) ∧
      profileMass ss = B ∧ profileMass ps + B = profileMass qs ∧
      profileTime ps + profileTime ss = profileTime qs ∧
      ∀ r, profileWork r qs = profileWork (r + B) ps + profileWork r ss := by
  induction qs with
  | nil =>
      have hzero : B = 0 := by simpa [profileMass] using le_antisymm hBA hB
      subst B
      exact ⟨[], [], by simp [profileMass, profileTime, profileWork]⟩
  | cons q qs ih =>
      have hq := hv q (by simp)
      have hv' : ∀ z ∈ qs, 0 ≤ z.1 ∧ m ≤ z.2 := fun z hz => hv z (by simp [hz])
      have ha : 0 < q.2 := lt_of_lt_of_le hm hq.2
      by_cases hb : B ≤ profileMass qs
      · obtain ⟨ps, ss, hpv, hss, hps, htime, hwork⟩ := ih hv' hb
        refine ⟨q :: ps, ss, ?_, hss, ?_, ?_, ?_⟩
        · intro z hz
          simp only [List.cons_append, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hq
          · exact hpv z hz
        · simp only [profileMass]; linarith
        · simp only [profileTime]; linarith
        · intro r
          simp only [profileWork]
          rw [hwork r]
          rw [← hps]
          ring
      · let u := (B - profileMass qs) / q.2
        have hu : 0 ≤ u := div_nonneg (by linarith) ha.le
        have hua : u * q.2 = B - profileMass qs := by dsimp [u]; field_simp
        have hut : u ≤ q.1 := by
          apply (div_le_iff₀ ha).mpr
          simp only [profileMass] at hBA
          linarith
        refine ⟨[(q.1 - u, q.2)], (u, q.2) :: qs, ?_, ?_, ?_, ?_, ?_⟩
        · intro z hz
          simp only [List.singleton_append, List.mem_cons] at hz
          rcases hz with rfl | rfl | hz
          · exact ⟨sub_nonneg.mpr hut, hq.2⟩
          · exact ⟨hu, hq.2⟩
          · exact hv' z hz
        · simp only [profileMass]; linarith
        · simp only [profileMass]; nlinarith
        · simp only [profileTime]; ring
        · intro r
          simp only [profileWork, profileMass]
          rw [show B = u * q.2 + profileMass qs by linarith]
          have hn := ne_of_gt ha
          field_simp
          ring


lemma profile_low_gap {qs : List (ℝ × ℝ)} {m r : ℝ} (hm : 0 < m)
    (ht : ∀ q ∈ qs, 0 ≤ q.1) (ha : ∀ q ∈ qs, m ≤ q.2)
    (hr : 0 < r) (hrA : r < profileMass qs) :
    4 * (profileTime qs) ^ 2 ≤
      (1 + 2 * Real.log ((profileMass qs + r) / (2 * r))) *
        (profileWork r qs + (r / m) ^ 2) := by
  obtain ⟨ps, ss, hv, hss, hps, htime, hwork⟩ :=
    profile_split hm (fun q hq => ⟨ht q hq, ha q hq⟩) hr.le hrA.le
  have hpt : ∀ q ∈ ps, 0 ≤ q.1 := fun q hq => (hv q (List.mem_append_left ss hq)).1
  have hpa : ∀ q ∈ ps, m ≤ q.2 := fun q hq => (hv q (List.mem_append_left ss hq)).2
  have hst : ∀ q ∈ ss, 0 ≤ q.1 := fun q hq => (hv q (List.mem_append_right ps hq)).1
  have hsa : ∀ q ∈ ss, m ≤ q.2 := fun q hq => (hv q (List.mem_append_right ps hq)).2
  have htail := profile_high_gap hm hst hsa (by rwa [hss]) (by rw [hss])
  rw [hss] at htail
  have htail' : 4 * (profileTime ss) ^ 2 ≤ profileWork r ss + (r / m) ^ 2 := by
    nlinarith [sq_pos_of_pos hr]
  have hhead := profile_logarithmic (show 0 < r + r by linarith) hpt
    (fun q hq => lt_of_lt_of_le hm (hpa q hq))
  have hlog : Real.log (r + r + profileMass ps) - Real.log (r + r) =
      Real.log ((profileMass qs + r) / (2 * r)) := by
    rw [Real.log_div (ne_of_gt (show 0 < profileMass qs + r by linarith)) (by positivity)]
    congr 1 <;> congr 1 <;> linarith
  rw [hlog] at hhead
  have hh : 0 < Real.log ((profileMass qs + r) / (2 * r)) :=
    Real.log_pos ((lt_div_iff₀ (by positivity)).mpr (by linarith))
  have hhead' : 2 * (profileTime ps) ^ 2 /
      Real.log ((profileMass qs + r) / (2 * r)) ≤ profileWork (r + r) ps :=
    (div_le_iff₀ hh).mpr (by nlinarith [hhead])
  have he := hwork r
  have hs := split_energy_algebra hh (D := profileWork r qs + (r / m) ^ 2)
    (s := profileTime ps) (q := profileTime ss) (by linarith)
  rwa [htime] at hs

end

end OracleTemplate.BallProximal
