import LongTails.Proofs.BirchResourceMatchingLower
import LongTails.Theorems.BirchRoutedTime
import LongTails.Theorems.BirchPowerTime

namespace LongTails.Proofs.BirchResourceComplexity

open Set Finset MeasureTheory OracleTemplate
open OracleTemplate.Rennala (Point)
open OracleTemplate.BirchSgd (gradientOracle)
open LongTails.Setups
open LongTails.Proofs.BirchResourceHardInstance
open LongTails.Proofs.BirchResourceLowerWindow
open LongTails.Proofs.BirchResourceChain (scaledOracle)

lemma chance_inverse (p : BirchNonEuclidean.Params) (hε : 0 < p.ε) :
    1 / chance p = 1 + p.σ ^ 2 / (4096 * p.ε) := by
  have hs : 0 < amplitude p := amplitude_pos p hε
  have he : amplitude p ^ 2 = 4096 * p.ε := by
    unfold amplitude
    rw [mul_pow, Real.sq_sqrt hε.le]
    ring
  unfold chance
  rw [he]
  field_simp

lemma gap_width (p : BirchNonEuclidean.Params) (hL : 0 < p.L) (hε : 0 < p.ε)
    (hD : (p.d : ℝ) ≤ p.L * p.Δ / (491520 * p.ε)) :
    width p * amplitude p * (4 * p.d) ≤ p.Δ := by
  have he : amplitude p ^ 2 = 4096 * p.ε := by
    unfold amplitude
    rw [mul_pow, Real.sq_sqrt hε.le]
    ring
  have hb := (le_div_iff₀ (by positivity : 0 < 491520 * p.ε)).1 hD
  have hc : width p * amplitude p * (4 * p.d) = (491520 * p.ε * (p.d : ℝ)) / p.L := by
    unfold width
    rw [show 30 * amplitude p / p.L * amplitude p * (4 * (p.d : ℝ)) =
      (120 * amplitude p ^ 2 * (p.d : ℝ)) / p.L by ring, he]
    ring
  rw [hc]
  exact (div_le_iff₀ hL).2 (by linarith only [hb])

lemma hard_admissible (p : BirchNonEuclidean.Params) (hn : Distortion p.N)
    (hL : 0 < p.L) (hε : 0 < p.ε) (hD : 0 < p.d) (hx : p.x0 = 0)
    (hgap : (p.d : ℝ) ≤ p.L * p.Δ / (491520 * p.ε)) :
    BirchNonEuclidean.spec.admissible p (objectiveInstance p)
      (gradientOracle (streamLaw p hε) (scaledOracle (width p) (amplitude p) (chance p))) :=
  ⟨hard_objective p hn hL hε hD hx (gap_width p hL hε hgap), Bool, inferInstance,
    sampleLaw p hε, streamLaw p hε, _, stream_iid p hε, oracle_valid p hn hL hε, rfl⟩

lemma inf_scale {S T : Set ℝ} (c : ℝ) (hc : 0 < c) (hS : S.Nonempty) (hT : BddBelow T)
    (hmap : ∀ x ∈ S, ∃ y ∈ T, y ≤ c * x) : sInf T ≤ c * sInf S := by
  have h := le_csInf hS (fun x hx => by
    obtain ⟨y, hy, hyx⟩ := hmap x hx
    exact (div_le_iff₀ hc).2 ((csInf_le hT hy).trans (by simpa only [mul_comm c x] using hyx)))
  simpa only [mul_comm (sInf S) c] using (div_le_iff₀ hc).1 h

lemma routed_scale {Route Device : Type*} [Fintype Route] [DecidableEq Device]
    (p : BirchRoutedTime.Profile Route Device) (a b c : ℝ)
    (ha : 0 ≤ a) (hc : 1 ≤ c) (hab : a ≤ c * b) (h : (routedPrices p b).Nonempty) :
    sInf (routedPrices p a) ≤ c * sInf (routedPrices p b) := by
  apply inf_scale c (by linarith) h (routed_price_lower p a ha)
  rintro x ⟨t, ht, r, hfeas, hr, rfl⟩
  refine ⟨t + a / (∑ i, r i), ⟨t, ht, r, hfeas, hr, rfl⟩, ?_⟩
  have h₁ := (div_le_div_of_nonneg_right hab hr.le)
  have h₂ : t ≤ c * t := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) ht.le]
  rw [mul_add]
  nlinarith only [h₁, h₂, mul_div_assoc c b (∑ i, r i)]

lemma power_scale {Mode Device : Type*} [Fintype Mode]
    (p : BirchPowerTime.Profile Mode Device) (u : ℕ) (a b c : ℝ)
    (ha : 0 ≤ a) (hc : 1 ≤ c) (hab : a ≤ c * b) (h : (powerPrices p u b).Nonempty) :
    sInf (powerPrices p u a) ≤ c * sInf (powerPrices p u b) := by
  apply inf_scale c (by linarith) h (power_price_lower p u a ha)
  rintro x ⟨t, ht, hr, rfl⟩
  let r := BirchPowerTime.envelope p t u
  refine ⟨t + a / r, ⟨t, ht, hr, rfl⟩, ?_⟩
  have h₁ := div_le_div_of_nonneg_right hab hr.le
  have h₂ : t ≤ c * t := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) ht.le]
  change t + a / r ≤ c * (t + b / r)
  rw [mul_add]
  nlinarith only [h₁, h₂, mul_div_assoc c b r]

lemma nonempty_route_prices {Route Device : Type*} [Fintype Route] [DecidableEq Device]
    (p : BirchRoutedTime.Profile Route Device) (a b : ℝ) (h : (routedPrices p a).Nonempty) :
    (routedPrices p b).Nonempty := by
  obtain ⟨_, t, ht, x, hx, hr, _⟩ := h
  exact ⟨_, t, ht, x, hx, hr, rfl⟩

lemma nonempty_power_prices {Mode Device : Type*} [Fintype Mode]
    (p : BirchPowerTime.Profile Mode Device) (u : ℕ) (a b : ℝ) (h : (powerPrices p u a).Nonempty) :
    (powerPrices p u b).Nonempty := by
  obtain ⟨_, t, ht, hr, _⟩ := h
  exact ⟨_, t, ht, hr, rfl⟩

lemma budget_scale (p : BirchNonEuclidean.Params) (hε : 0 < p.ε) :
    1 + p.σ ^ 2 / p.ε ≤ 4096 * (1 / chance p) := by
  rw [chance_inverse p hε]
  have he : 4096 * (1 + p.σ ^ 2 / (4096 * p.ε)) = 4096 + p.σ ^ 2 / p.ε := by
    field_simp
  rw [he]
  linarith

lemma finite_positive_lower {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ δ > 0, ∀ i, δ ≤ f i := by
  classical
  have h (s : Finset ι) : ∃ δ > 0, ∀ i ∈ s, δ ≤ f i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨δ, hδ, hbound⟩ := ih
      refine ⟨min δ (f i), lt_min hδ (hf i), ?_⟩
      intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound j hj)
  obtain ⟨δ, hδ, hl⟩ := h univ
  exact ⟨δ, hδ, fun i => hl i (mem_univ _)⟩

lemma routed_price_positive {Route Device : Type*} [Fintype Route] [DecidableEq Device]
    (p : BirchRoutedTime.Profile Route Device) (J : ℕ) (hp : p.Valid J) (b : ℝ) (hb : 0 ≤ b)
    (hne : (routedPrices p b).Nonempty) : 0 < sInf (routedPrices p b) := by
  have hlat (r : Route) : 0 < BirchRoutedTime.latency p r := by
    unfold BirchRoutedTime.latency
    cases he : p.path r with
    | nil => have h := (hp.2 r).2.1; simp [he] at h
    | cons v l =>
      simp only [List.map_cons, List.sum_cons]
      exact add_pos_of_pos_of_nonneg (hp.1 v) (List.sum_nonneg fun x hx => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact (hp.1 i).le)
  obtain ⟨δ, hδ, hmin⟩ := finite_positive_lower _ hlat
  apply hδ.trans_le (le_csInf hne ?_)
  rintro c ⟨t, ht, x, hx, hr, rfl⟩
  have h : ∃ r, 0 < x r := by
    by_contra! hn
    exact (not_le_of_gt hr) (sum_nonpos fun r _ => hn r)
  obtain ⟨r, hr'⟩ := h
  have hlat' : BirchRoutedTime.latency p r ≤ t := le_of_not_gt
    (fun hh => (ne_of_gt hr') (hx.2.1 r hh))
  exact (hmin r).trans (hlat'.trans (le_add_of_nonneg_right (div_nonneg hb hr.le)))

lemma power_price_positive {Mode Device : Type*} [Fintype Mode]
    (p : BirchPowerTime.Profile Mode Device) (hp : p.Valid) (u : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hne : (powerPrices p u b).Nonempty) : 0 < sInf (powerPrices p u b) := by
  obtain ⟨δ, hδ, hmin⟩ := finite_positive_lower p.duration (fun i => (hp.1 i).1)
  apply hδ.trans_le (le_csInf hne ?_)
  rintro c ⟨t, ht, hr, rfl⟩
  obtain ⟨modes, hm, hrate⟩ := LongTails.Proofs.BirchPowerTime.envelope_attained p hp t u
  have hm' : modes.Nonempty := by
    by_contra! he
    rw [he, BirchPowerTime.rate, sum_empty] at hrate
    linarith
  obtain ⟨i, hi⟩ := hm'
  exact (hmin i).trans ((hm.2.2 i hi).1.trans
    (le_add_of_nonneg_right (div_nonneg hb hr.le)))

lemma near_inf (S : Set ℝ) (hne : S.Nonempty) (hpos : 0 < sInf S) :
    ∃ t ∈ S, t ≤ 2 * sInf S := by
  obtain ⟨t, ht, hlt⟩ := exists_lt_of_csInf_lt hne (show sInf S < 2 * sInf S by linarith)
  exact ⟨t, ht, hlt.le⟩

lemma ceiling_factor (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    ((1 + ⌈c * a⌉₊ : ℕ) : ℝ) ≤ (c + 2) * (1 + a) := by
  have h := Nat.ceil_lt_add_one (mul_nonneg hc ha)
  push_cast
  nlinarith only [h, hc, ha]

lemma hard_dimension (A : ℝ) (hA : 983040 ≤ A) :
    0 < ⌊A / 491520⌋₊ ∧ A / 983040 ≤ (⌊A / 491520⌋₊ : ℝ) ∧
      (⌊A / 491520⌋₊ : ℝ) ≤ A / 491520 := by
  have h := Nat.lt_floor_add_one (A / 491520)
  have hfloor := Nat.floor_le (show 0 ≤ A / 491520 by linarith)
  have hp : 0 < (⌊A / 491520⌋₊ : ℝ) := by linarith
  exact ⟨Nat.cast_pos.mp hp, by linarith, hfloor⟩

lemma routed_tuning (p : BirchRoutedTime.Params) (hp : BirchRoutedTime.Valid p)
    (hpos : 0 < sInf (routedPrices p.hardware (BirchRoutedTime.block p))) :
    ∃ (t : ℝ) (x : Fin p.routes → ℝ),
      let q := {p with cutoff := t, fractionalRate := x}
      BirchRoutedTime.Valid q ∧ BirchRoutedTime.window q ≤
        2 * (2 * (p.depth : ℝ) ^ 2 + 4 * p.depth + 2) *
          sInf (routedPrices p.hardware (BirchRoutedTime.block p)) := by
  obtain ⟨hg, hd, hv, ht, hfeas, hr⟩ := hp
  let B := BirchRoutedTime.block p
  have hne : (routedPrices p.hardware B).Nonempty :=
    ⟨_, p.cutoff, ht, p.fractionalRate, hfeas, hr, rfl⟩
  obtain ⟨_, ⟨t, ht', x, hx, hr', rfl⟩, htune⟩ := near_inf _ hne hpos
  let q := {p with cutoff := t, fractionalRate := x}
  refine ⟨t, x, ⟨hg, hd, hv, ht', hx, hr'⟩, ?_⟩
  let C := 2 * (p.depth : ℝ) ^ 2 + 4 * p.depth + 2
  have hC : 0 ≤ C := by unfold C; positivity
  have h₁ : BirchRoutedTime.window q ≤ C * (t + (B : ℝ) / (∑ r, x r)) := by
    change 2 * (p.depth : ℝ) * ((p.depth : ℝ) * B / (∑ r, x r)) + (4 * p.depth + 2) * t ≤ _
    have hdiff : C * (t + (B : ℝ) / (∑ r, x r)) -
        (2 * (p.depth : ℝ) * ((p.depth : ℝ) * B / (∑ r, x r)) + (4 * p.depth + 2) * t) =
          (2 * (p.depth : ℝ) ^ 2) * t + (4 * p.depth + 2) * ((B : ℝ) / (∑ r, x r)) := by
      unfold C
      ring
    exact sub_nonneg.mp (hdiff.symm ▸ (by positivity :
      0 ≤ (2 * (p.depth : ℝ) ^ 2) * t + (4 * p.depth + 2) * ((B : ℝ) / (∑ r, x r))))
  refine h₁.trans ?_
  have hh := mul_le_mul_of_nonneg_left htune hC
  dsimp only [C] at hh
  linarith only [hh]

lemma power_tuning (p : BirchPowerTime.Params) (hp : BirchPowerTime.Valid p)
    (hpos : 0 < sInf (powerPrices p.hardware p.packetLimit (BirchPowerTime.block p))) :
    ∃ t : ℝ, let q := {p with cutoff := t}
      BirchPowerTime.Valid q ∧ BirchPowerTime.window q ≤ 2 * sInf (powerPrices p.hardware p.packetLimit (BirchPowerTime.block p)) := by
  obtain ⟨hg, hv, ht, hr⟩ := hp
  let B := BirchPowerTime.block p
  have hne : (powerPrices p.hardware p.packetLimit B).Nonempty := ⟨_, p.cutoff, ht, hr, rfl⟩
  obtain ⟨_, ⟨t, ht', hr', rfl⟩, htune⟩ := near_inf _ hne hpos
  exact ⟨t, ⟨hg, hv, ht', hr'⟩, htune⟩

noncomputable def A (p : BirchCollections.Params) : ℝ := p.L * p.Δ / p.ε

noncomputable def b₀ (p : BirchCollections.Params) : ℝ := 1 + p.σ ^ 2 / p.ε

open LongTails.Algorithms.BirchResourceNative

lemma rounds_bound (p : BirchCollections.Params) (hA : 1 ≤ A p) :
    (BirchCollections.horizon (tuned p) : ℝ) ≤ 1922 * A p := by
  have he : 240 * p.L * p.Δ / (1 / 8 * p.ε) = 1920 * A p := by unfold A; ring
  change ((1 + ⌈240 * p.L * p.Δ / (1 / 8 * p.ε)⌉₊ : ℕ) : ℝ) ≤ _
  rw [he]
  have hn : 0 ≤ 1920 * A p := by linarith
  have h := Nat.ceil_lt_add_one hn
  push_cast
  linarith

lemma block_bound (p : BirchCollections.Params) (hε : 0 < p.ε) (hκ : 0 ≤ p.κ) :
    (BirchCollections.batchSize (tuned p) : ℝ) ≤ (32 * p.κ + 2) * b₀ p := by
  change ((1 + ⌈32 * 1 * p.κ * p.σ ^ 2 / p.ε⌉₊ : ℕ) : ℝ) ≤ _
  rw [mul_one, mul_div_assoc]
  exact ceiling_factor (32 * p.κ) (p.σ ^ 2 / p.ε) (by positivity) (by positivity)

lemma routed_optimized (p : BirchRoutedTime.Params) (hp : BirchRoutedTime.Valid p)
    (hA : 1 ≤ A p.geometry)
    (hpos : 0 < sInf (routedPrices p.hardware (BirchRoutedTime.block p))) :
    ∃ (t : ℝ) (x : Fin p.routes → ℝ), let q := {p with cutoff := t, fractionalRate := x}
      BirchRoutedTime.Valid q ∧
      BirchRoutedTime.rounds q * BirchRoutedTime.window q ≤
        (1922 * A p.geometry) * (2 * (2 * (p.depth : ℝ)^2 + 4 * p.depth + 2)) *
          (32 * p.geometry.κ + 2) * sInf (routedPrices p.hardware (b₀ p.geometry)) := by
  have hκ : 0 ≤ p.geometry.κ := by
    obtain ⟨reg⟩ := hp.1.regular
    linarith [reg.smoothness_lower, reg.smoothness_upper]
  have hC : 1 ≤ 32 * p.geometry.κ + 2 := by linarith
  obtain ⟨t, x, hvalid, hwindow⟩ := routed_tuning p hp hpos
  let q := {p with cutoff := t, fractionalRate := x}
  have hne₀ : (routedPrices p.hardware (BirchRoutedTime.block p)).Nonempty :=
    ⟨_, p.cutoff, hp.2.2.2.1, p.fractionalRate, hp.2.2.2.2.1, hp.2.2.2.2.2, rfl⟩
  have hne := nonempty_route_prices p.hardware _ (b₀ p.geometry) hne₀
  have hscale := routed_scale p.hardware (BirchRoutedTime.block p) (b₀ p.geometry)
    (32 * p.geometry.κ + 2) (by positivity) hC (block_bound _ hp.1.εpos hκ) hne
  have hn : 0 ≤ BirchRoutedTime.window q := by
    unfold BirchRoutedTime.window
    have ht := hvalid.2.2.2.1
    have hr := hvalid.2.2.2.2.2
    positivity
  have hh := rounds_bound p.geometry hA
  let C := 2 * (2 * (p.depth : ℝ)^2 + 4 * p.depth + 2)
  have hc : 0 ≤ C := by unfold C; positivity
  have hA₀ : 0 ≤ 1922 * A p.geometry := by linarith
  refine ⟨t, x, hvalid, ?_⟩
  change (BirchRoutedTime.rounds p : ℝ) * BirchRoutedTime.window q ≤
    (1922 * A p.geometry) * C * (32 * p.geometry.κ + 2) * sInf (routedPrices p.hardware (b₀ p.geometry))
  calc
    _ ≤ (1922 * A p.geometry) * BirchRoutedTime.window q :=
      mul_le_mul_of_nonneg_right hh hn
    _ ≤ (1922 * A p.geometry) * (C * ((32 * p.geometry.κ + 2) *
        sInf (routedPrices p.hardware (b₀ p.geometry)))) :=
      mul_le_mul_of_nonneg_left (hwindow.trans (mul_le_mul_of_nonneg_left hscale hc)) hA₀
    _ = _ := by ring

lemma power_optimized (p : BirchPowerTime.Params) (hp : BirchPowerTime.Valid p)
    (hA : 1 ≤ A p.geometry)
    (hpos : 0 < sInf (powerPrices p.hardware p.packetLimit (BirchPowerTime.block p))) :
    ∃ t : ℝ, let q := {p with cutoff := t}
      BirchPowerTime.Valid q ∧ BirchPowerTime.rounds q * BirchPowerTime.window q ≤
        (3844 * A p.geometry) * (32 * p.geometry.κ + 2) *
          sInf (powerPrices p.hardware p.packetLimit (b₀ p.geometry)) := by
  have hκ : 0 ≤ p.geometry.κ := by
    obtain ⟨reg⟩ := hp.1.regular
    linarith [reg.smoothness_lower, reg.smoothness_upper]
  have hC : 1 ≤ 32 * p.geometry.κ + 2 := by linarith
  obtain ⟨t, hvalid, hwindow⟩ := power_tuning p hp hpos
  let q := {p with cutoff := t}
  have hne₀ : (powerPrices p.hardware p.packetLimit (BirchPowerTime.block p)).Nonempty :=
    ⟨_, p.cutoff, hp.2.2.1, hp.2.2.2, rfl⟩
  have hne := nonempty_power_prices p.hardware p.packetLimit _ (b₀ p.geometry) hne₀
  have hscale := power_scale p.hardware p.packetLimit (BirchPowerTime.block p) (b₀ p.geometry)
    (32 * p.geometry.κ + 2) (by positivity) hC (block_bound _ hp.1.εpos hκ) hne
  have hn : 0 ≤ BirchPowerTime.window q := by
    unfold BirchPowerTime.window
    have ht := hvalid.2.2.1
    have hr := hvalid.2.2.2
    positivity
  have hh := rounds_bound p.geometry hA
  have hA₀ : 0 ≤ 1922 * A p.geometry := by linarith
  refine ⟨t, hvalid, ?_⟩
  change (BirchPowerTime.rounds p : ℝ) * BirchPowerTime.window q ≤ _
  calc
    _ ≤ (1922 * A p.geometry) * BirchPowerTime.window q :=
      mul_le_mul_of_nonneg_right hh hn
    _ ≤ (1922 * A p.geometry) * (2 * ((32 * p.geometry.κ + 2) *
        sInf (powerPrices p.hardware p.packetLimit (b₀ p.geometry)))) :=
      mul_le_mul_of_nonneg_left (hwindow.trans (mul_le_mul_of_nonneg_left hscale (by norm_num))) hA₀
    _ = _ := by ring

lemma lower_rate_scale {A D Φ Ψ elapsed : ℝ} (hΦ : 0 ≤ Φ) (hD : 0 ≤ D)
    (hd : A / 983040 ≤ D) (hprice : Φ ≤ 4096 * Ψ) (ht : D * Ψ / 72 ≤ elapsed) :
    A * Φ / (983040 * 4096 * 72) ≤ elapsed := by
  have hp : Φ / 4096 ≤ Ψ := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4096)).2
    (by rw [mul_comm Ψ 4096]; exact hprice)
  have hs := mul_le_mul hd hp (div_nonneg hΦ (by norm_num)) hD
  have h := div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 72)
  exact (by convert h using 1; ring :
    A * Φ / (983040 * 4096 * 72) ≤ D * Ψ / 72).trans ht

end LongTails.Proofs.BirchResourceComplexity
