import LongTails.Proofs.BallProximalExecution

namespace OracleTemplate.BallProximal

open LongTails.Setups.ConvexBallProximal

lemma execution_log_energy (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (hv : spec.valid p) (h : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k)
    {z : p.E} (hz : z ∈ I.C) (hR : ‖p.x0 - z‖ ≤ p.R)
    (hΔ : I.f p.x0 - I.f z ≤ p.Δ) {N : ℕ}
    (hg : 0 < I.f (oracleIterate p.x0 O ξ N) - I.f z) :
    2 * ((N : ℝ) * p.t) ^ 2 ≤
      (Real.log p.Δ - Real.log
        (I.f (oracleIterate p.x0 O ξ N) - I.f z)) * p.R ^ 2 := by
  let x := oracleIterate p.x0 O ξ
  let g := I.f (x N) - I.f z
  obtain ⟨c, hc⟩ := iterate_radial_certificates p I O hv h ξ hz (by linarith)
  have hx : ∀ i ≤ N, x i ∈ I.C := fun i _ => iterate_feasible p I O h ξ i
  have hcp : ∀ i < N, 0 < c i := fun i hi => (hc i hi).1
  have hs := fun i (hi : i < N) => (hc i hi).2
  let qs := radialProfile p.t c N
  have hqt : ∀ q ∈ qs, 0 ≤ q.1 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
    exact hv.1.le
  have hqa : ∀ q ∈ qs, 0 < q.2 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
    exact mul_pos (hcp i hi) hv.1
  have hm := radialProfile_mass hx hs
  have hmass : g + profileMass qs ≤ p.Δ := by
    change profileMass qs ≤ I.f p.x0 - I.f (x N) at hm
    dsimp [g]
    linarith
  have hn := profile_nonneg hqt hqa
  have hg0 : 0 < g := hg
  have hl := profile_logarithmic hg0 hqt hqa
  have he := radialProfile_energy hv.1 hz hx hcp hs
  change profileWork g qs + ‖x N - z‖ ^ 2 ≤ ‖p.x0 - z‖ ^ 2 at he
  have hR2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hw : profileWork g qs ≤ p.R ^ 2 := by
    have := sq_nonneg ‖x N - z‖
    linarith
  have hlog0 : 0 ≤ Real.log (g + profileMass qs) - Real.log g :=
    sub_nonneg.mpr (Real.log_le_log hg0 (by linarith [hn.2.1]))
  have hlog : Real.log (g + profileMass qs) - Real.log g ≤
      Real.log p.Δ - Real.log g :=
    sub_le_sub_right (Real.log_le_log (by linarith [hn.2.1]) hmass) _
  have hb := mul_le_mul hlog hw (profile_work_nonneg hg0.le hqt hqa) (by linarith)
  have ht := radialProfile_time p.t c N
  change 2 * ((N : ℝ) * p.t) ^ 2 ≤ (Real.log p.Δ - Real.log g) * p.R ^ 2
  rw [← ht]
  exact hl.trans hb

lemma execution_gaussian (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (hv : spec.valid p) (h : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k)
    {z : p.E} (hz : z ∈ I.C) (hR : ‖p.x0 - z‖ ≤ p.R)
    (hΔ : I.f p.x0 - I.f z ≤ p.Δ) (hRp : 0 < p.R) (K : ℕ) :
    I.f (oracleIterate p.x0 O ξ K) - I.f z ≤
      p.Δ * Real.exp (-2 * (K : ℝ) ^ 2 * p.t ^ 2 / p.R ^ 2) := by
  let g := I.f (oracleIterate p.x0 O ξ K) - I.f z
  by_cases hg : 0 < g
  · have he := execution_log_energy p I O hv h ξ hz hR hΔ hg
    have hlog : Real.log g ≤ Real.log p.Δ + (-2 * (K : ℝ) ^ 2 * p.t ^ 2 / p.R ^ 2) := by
      have hd := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr he
      change 2 * ((K : ℝ) * p.t) ^ 2 / p.R ^ 2 ≤ Real.log p.Δ - Real.log g at hd
      have ha : -2 * (K : ℝ) ^ 2 * p.t ^ 2 / p.R ^ 2 =
          -(2 * ((K : ℝ) * p.t) ^ 2 / p.R ^ 2) := by ring
      rw [ha]
      linarith
    have hh := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log hg, Real.exp_add, Real.exp_log hv.2.2.1] at hh
  · exact le_trans (le_of_not_gt hg) (mul_nonneg hv.2.2.1.le (Real.exp_pos _).le)

lemma execute_gaussian (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (hv : spec.valid p) (h : spec.admissible p I O)
    (seed : (algorithm p.x0).Seed) (ξ : (k : ℕ) → O.Seed k)
    {z : p.E} (hz : z ∈ I.C) (hR : ‖p.x0 - z‖ ≤ p.R)
    (hΔ : I.f p.x0 - I.f z ≤ p.Δ) (hRp : 0 < p.R) (K : ℕ) :
    I.f (execute O (algorithm p.x0) (fun _ => K) seed ξ) - I.f z ≤
      p.Δ * Real.exp (-2 * (K : ℝ) ^ 2 * p.t ^ 2 / p.R ^ 2) := by
  rw [execute_algorithm]
  exact execution_gaussian p I O hv h ξ hz hR hΔ hRp K

lemma iterate_optimal_persists (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (hv : spec.valid p) (h : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k)
    {z : p.E} (hmin : IsMinOn I.f I.C z) {j K : ℕ} (hj : j ≤ K)
    (hopt : I.f (oracleIterate p.x0 O ξ j) = I.f z) :
    I.f (oracleIterate p.x0 O ξ K) = I.f z := by
  apply le_antisymm
  · simpa [hopt] using iterate_objective_antitone p I O hv h ξ hj
  · exact hmin (iterate_feasible p I O h ξ K)

lemma gaussian_budget_accuracy (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (hv : spec.valid p) (h : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k)
    {z : p.E} (hz : z ∈ I.C) (hR : ‖p.x0 - z‖ ≤ p.R)
    (hΔ : I.f p.x0 - I.f z ≤ p.Δ) {K : ℕ}
    (hK : ⌈min ((p.R / p.t) ^ 2)
      ((p.R / p.t) * Real.sqrt (max 0 (Real.log (p.Δ / p.ε)) / 2))⌉₊ ≤ K) :
    I.f (oracleIterate p.x0 O ξ K) - I.f z ≤ p.ε := by
  by_contra hbad
  have hg := lt_of_not_ge hbad
  let g := I.f (oracleIterate p.x0 O ξ K) - I.f z
  have hm := iterate_objective_antitone p I O hv h ξ (Nat.zero_le K)
  have hinit : p.ε < I.f p.x0 - I.f z := by
    change I.f (oracleIterate p.x0 O ξ K) ≤ I.f p.x0 at hm
    linarith
  have heΔ : p.ε < p.Δ := lt_of_lt_of_le hinit hΔ
  have hxz : p.x0 ≠ z := by
    intro he
    rw [he, sub_self] at hinit
    linarith [hv.2.2.2]
  have hRp : 0 < p.R := lt_of_lt_of_le (norm_pos_iff.mpr (sub_ne_zero.mpr hxz)) hR
  have hlog : 0 < Real.log (p.Δ / p.ε) :=
    Real.log_pos ((one_lt_div hv.2.2.2).mpr heΔ)
  have hKp : 0 < K := lt_of_lt_of_le (Nat.ceil_pos.mpr
    (lt_min (sq_pos_of_pos (div_pos hRp hv.1))
      (mul_pos (div_pos hRp hv.1) (Real.sqrt_pos.mpr (by positivity))))) hK
  have hcap := (positive_execution_bounds p I O hv h ξ hz hR hΔ hKp hg).2
  have hg0 : 0 < g := lt_trans hv.2.2.2 hg
  have he := execution_log_energy p I O hv h ξ hz hR hΔ hg0
  have hlg : Real.log p.Δ - Real.log g < Real.log (p.Δ / p.ε) := by
    rw [Real.log_div (ne_of_gt hv.2.2.1) (ne_of_gt hv.2.2.2)]
    have := Real.log_lt_log hv.2.2.2 hg
    linarith
  have hstrict : 2 * ((K : ℝ) * p.t) ^ 2 < Real.log (p.Δ / p.ε) * p.R ^ 2 :=
    lt_of_le_of_lt he (mul_lt_mul_of_pos_right hlg (sq_pos_of_pos hRp))
  have hk := Nat.ceil_le.mp hK
  rcases le_total ((p.R / p.t) ^ 2)
      ((p.R / p.t) * Real.sqrt (max 0 (Real.log (p.Δ / p.ε)) / 2)) with hh | hh
  · rw [min_eq_left hh] at hk
    have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg p.t)
    have heq : (p.R / p.t) ^ 2 * p.t ^ 2 = p.R ^ 2 := by field_simp [ne_of_gt hv.1]
    rw [heq] at hm
    linarith
  · rw [min_eq_right hh] at hk
    have hm := mul_le_mul_of_nonneg_right hk hv.1.le
    have heq : (p.R / p.t) * Real.sqrt (max 0 (Real.log (p.Δ / p.ε)) / 2) * p.t =
        p.R * Real.sqrt (max 0 (Real.log (p.Δ / p.ε)) / 2) := by field_simp [ne_of_gt hv.1]
    rw [heq] at hm
    have hp := pow_le_pow_left₀ (mul_nonneg hv.2.1 (Real.sqrt_nonneg _)) hm 2
    rw [mul_pow, Real.sq_sqrt (by positivity), max_eq_right hlog.le] at hp
    nlinarith

end OracleTemplate.BallProximal
