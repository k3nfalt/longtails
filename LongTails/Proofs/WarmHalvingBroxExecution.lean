import LongTails.Proofs.WarmHalvingBroxSteps

open Set

namespace OracleTemplate.WarmHalvingBrox

open LongTails.Setups.BroxGeneralNormConstrainedPL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {C : Set E} {L μ : ℝ}

noncomputable def floorRadius (r L μ ε : ℝ) : ℝ :=
  min r (Real.sqrt (ε / (2 * L ^ 2 / μ + 3 * L / 2)) / 2)

def Phase (f : E → ℝ) (C : Set E) (L μ r Δ : ℝ) (s : State E) (c : ℤ) : Prop :=
  (c = s.updates ∧ gap f C s.center + L * r ^ 2 / 2 * ((4 : ℝ) ^ s.updates - 1) / 3 ≤ Δ) ∨
  (∃ ρ : ℝ, ∃ k : ℕ, 0 < ρ ∧ k ≤ s.updates ∧ (4 : ℝ) ^ k ≤ 1 + 6 * Δ / (L * r ^ 2) ∧
    2 * ρ ≤ radius r c ∧ gap f C s.center ≤ 25 * L ^ 2 * ρ ^ 2 / (2 * μ) ∧
    gap f C s.center * (1 + μ / (25 * L)) ^ (s.updates - k) ≤ Δ)

structure Good (f : E → ℝ) (C : Set E) (L μ r Δ ε : ℝ) (s : State E) : Prop where
  mem : s.center ∈ C
  slope : ∀ φ, s.slope = some φ → φ = fderiv ℝ f s.center
  bound : gap f C s.center ≤ Δ
  floor : gap f C s.center ≤ ε ∨ floorRadius r L μ ε ≤ radius r s.trial
  cap : ∃ c : ℤ, s.trial ≤ c ∧ (s.slope = none → s.trial = c) ∧
    (s.trial < c → ∀ u ∈ C, ‖u - s.center‖ ≤ radius r (s.trial + 1) →
      -fderiv ℝ f s.center (u - s.center) < L * radius r (s.trial + 1) ^ 2) ∧
    Phase f C L μ r Δ s c

def gradCount (s : State E) : ℤ := s.updates + if s.slope.isSome then 1 else 0

def lmoCount (s : State E) : ℤ := 2 * s.updates - s.trial

lemma good_initial {r Δ ε : ℝ} {x0 : E} (hx0 : x0 ∈ C)
    (hΔ : gap f C x0 ≤ Δ) :
    Good f C L μ r Δ ε (⟨0, x0, 0, none, false⟩ : State E) := by
  refine ⟨hx0, by simp, hΔ, Or.inr ?_, ⟨0, le_rfl, fun _ => rfl, by simp, Or.inl ⟨by simp, ?_⟩⟩⟩
  · simp [floorRadius, radius]
  · simpa using hΔ

lemma good_fetch {r Δ ε : ℝ} {s : State E} (hs : Good f C L μ r Δ ε s) :
    Good f C L μ r Δ ε { s with slope := some (fderiv ℝ f s.center) } := by
  obtain ⟨c, hc, -, hrej, hph⟩ := hs.cap
  refine ⟨hs.mem, ?_, hs.bound, hs.floor, ⟨c, hc, by simp, hrej, hph⟩⟩
  intro φ hφ
  simp only [Option.some.injEq] at hφ
  exact hφ.symm

lemma good_reject (H : Hyp f C L μ) {r Δ ε : ℝ} (hr : 0 < r) {s : State E}
    (hs : Good f C L μ r Δ ε s) (hsl : s.slope ≠ none) {v : E}
    (hv : IsOutput f C s.center v (radius r s.trial))
    (hd : -fderiv ℝ f s.center (v - s.center) < L * radius r s.trial ^ 2) :
    Good f C L μ r Δ ε { s with trial := s.trial - 1 } := by
  obtain ⟨c, hc, -, -, hph⟩ := hs.cap
  have hrad := radius_pos hr s.trial
  refine ⟨hs.mem, hs.slope, hs.bound, ?_, ⟨c, by simp; omega, fun h => absurd h hsl, ?_, hph⟩⟩
  · rcases hs.floor with h | _
    · exact Or.inl h
    · rcases le_or_gt (gap f C s.center) ε with h | h
      · exact Or.inl h
      right
      have hg := reject_gap H hs.mem hrad hv hd
      set Cr := 2 * L ^ 2 / μ + 3 * L / 2
      have hC : 0 < Cr := by have := H.L_pos; have := H.μ_pos; positivity
      have hlt : ε / Cr < radius r s.trial ^ 2 := by
        rw [div_lt_iff₀ hC]
        nlinarith
      have hsq : Real.sqrt (ε / Cr) < radius r s.trial := by
        rw [Real.sqrt_lt' hrad]
        exact hlt
      change min r (Real.sqrt (ε / Cr) / 2) ≤ radius r (s.trial - 1)
      rw [radius_pred]
      exact (min_le_right _ _).trans (by linarith)
  · intro _ u hu hux
    simp only [sub_add_cancel] at hux ⊢
    have := hv.opt u hu hux
    have h1 : -fderiv ℝ f s.center (u - s.center) ≤ -fderiv ℝ f s.center (v - s.center) := by
      rw [map_sub, map_sub]
      linarith
    linarith

lemma contraction_capped {gx gv t ρ L μ rad : ℝ} (hL : 0 < L) (hμ : 0 < μ) (ht : t = μ / (25 * L))
    (hgx : 0 ≤ gx) (hρ : 2 * ρ ≤ rad) (hρ0 : 0 < ρ) (hb : gx ≤ 25 * L ^ 2 * ρ ^ 2 / (2 * μ))
    (hdesc : gv ≤ gx - L / 2 * rad ^ 2) : gv * (1 + t) ≤ gx := by
  have h1 : 2 * μ * gx ≤ 25 * L ^ 2 * ρ ^ 2 := by
    rw [le_div_iff₀ (by positivity)] at hb
    linarith
  have hrad : 4 * ρ ^ 2 ≤ rad ^ 2 := by nlinarith
  have h2 : 4 * t * gx ≤ L / 2 * rad ^ 2 := by
    rw [ht]
    have : 4 * (μ / (25 * L)) * gx = 4 * μ * gx / (25 * L) := by ring
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have h3 : gv ≤ gx - 4 * t * gx := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ 1 + t), mul_nonneg ht0 hgx,
    mul_nonneg (mul_nonneg ht0 ht0) hgx]

lemma contraction_uncapped {gx gv t L μ rad : ℝ} (hL : 0 < L) (hμ : 0 < μ)
    (ht : t = μ / (25 * L)) (hb : gv < 25 * L ^ 2 * rad ^ 2 / (2 * μ))
    (hdesc : gv ≤ gx - L / 2 * rad ^ 2) : gv * (1 + t) ≤ gx := by
  have h1 : 2 * μ * gv < 25 * L ^ 2 * rad ^ 2 := by
    rw [lt_div_iff₀ (by positivity)] at hb
    linarith
  have h2 : t * gv ≤ L / 2 * rad ^ 2 := by
    rw [ht]
    have : μ / (25 * L) * gv = μ * gv / (25 * L) := by ring
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

lemma good_accept (H : Hyp f C L μ) {r Δ ε : ℝ} (hr : 0 < r) {s : State E}
    (hs : Good f C L μ r Δ ε s) {v : E} (hv : IsOutput f C s.center v (radius r s.trial))
    (hd : L * radius r s.trial ^ 2 ≤ -fderiv ℝ f s.center (v - s.center)) :
    Good f C L μ r Δ ε (⟨s.updates + 1, v, s.trial + 1, none, false⟩ : State E) := by
  obtain ⟨c, hc, -, hrej, hph⟩ := hs.cap
  have hL := H.L_pos
  have hμ := H.μ_pos
  set rad := radius r s.trial with hrad_def
  have hrad := radius_pos hr s.trial
  have hdesc0 := descent H hs.mem hv
  have hdesc : gap f C v ≤ gap f C s.center - L / 2 * rad ^ 2 := by linarith
  have hgx := gap_nonneg H hs.mem
  have hgv := gap_nonneg H hv.mem
  have hmono : gap f C v ≤ gap f C s.center := by nlinarith
  have h2 : radius r (s.trial + 1) = 2 * rad := radius_succ r s.trial
  refine ⟨hv.mem, by simp, hmono.trans hs.bound, ?_, ⟨s.trial + 1, le_rfl, fun _ => rfl,
    fun h => absurd h (lt_irrefl _), ?_⟩⟩
  · rcases hs.floor with h | h
    · exact Or.inl (hmono.trans h)
    · right
      change floorRadius r L μ ε ≤ radius r (s.trial + 1)
      rw [h2]
      linarith
  · set t := μ / (25 * L) with ht
    rcases eq_or_lt_of_le hc with heq | hlt
    · rcases hph with ⟨hcu, hA⟩ | ⟨ρ, k, hρ, hk, h4k, hρc, hgb, hgk⟩
      · left
        refine ⟨by simp [heq, hcu], ?_⟩
        have hsq : rad ^ 2 = r ^ 2 * 4 ^ s.updates := by
          rw [hrad_def, heq, hcu]
          exact radius_natCast_sq r s.updates
        rw [hsq] at hdesc
        change gap f C v + L * r ^ 2 / 2 * ((4 : ℝ) ^ (s.updates + 1) - 1) / 3 ≤ Δ
        rw [pow_succ (4 : ℝ) s.updates]
        linarith
      · right
        refine ⟨ρ, k, hρ, by change k ≤ s.updates + 1; omega, h4k, ?_, ?_, ?_⟩
        · change 2 * ρ ≤ radius r (s.trial + 1)
          rw [h2]
          rw [← heq] at hρc
          linarith
        · exact hmono.trans hgb
        · change gap f C v * (1 + t) ^ (s.updates + 1 - k) ≤ Δ
          rw [← heq] at hρc
          have hcon := contraction_capped hL hμ ht hgx hρc hρ hgb hdesc
          have hexp : s.updates + 1 - k = (s.updates - k) + 1 := by omega
          rw [hexp, pow_succ]
          have hpow : 0 ≤ (1 + t) ^ (s.updates - k) := by positivity
          calc gap f C v * ((1 + t) ^ (s.updates - k) * (1 + t))
              = gap f C v * (1 + t) * (1 + t) ^ (s.updates - k) := by ring
            _ ≤ gap f C s.center * (1 + t) ^ (s.updates - k) :=
              mul_le_mul_of_nonneg_right hcon hpow
            _ ≤ Δ := hgk
    · have hvx : ‖v - s.center‖ ≤ radius r (s.trial + 1) := by rw [h2]; linarith [hv.dist]
      have hd4 := hrej hlt v hv.mem hvx
      rw [h2] at hd4
      have hd4' : -fderiv ℝ f s.center (v - s.center) < 4 * L * rad ^ 2 := by nlinarith
      have hunc := uncapped_gap H hs.mem hrad hv hd4'
      have hcon := contraction_uncapped hL hμ ht hunc hdesc
      right
      rcases hph with ⟨hcu, hA⟩ | ⟨ρ, k, hρ, hk, h4k, hρc, hgb, hgk⟩
      · refine ⟨rad, s.updates, hrad, by change s.updates ≤ s.updates + 1; omega, ?_, ?_,
          hunc.le, ?_⟩
        · have hX : (4 : ℝ) ^ s.updates - 1 ≤ 6 * Δ / (L * r ^ 2) := by
            rw [le_div_iff₀ (by positivity)]
            linarith
          linarith
        · change 2 * rad ≤ radius r (s.trial + 1)
          rw [h2]
        · change gap f C v * (1 + t) ^ (s.updates + 1 - s.updates) ≤ Δ
          rw [show s.updates + 1 - s.updates = 1 by omega, pow_one]
          exact hcon.trans hs.bound
      · refine ⟨rad, k, hrad, by change k ≤ s.updates + 1; omega, h4k, ?_, hunc.le, ?_⟩
        · change 2 * rad ≤ radius r (s.trial + 1)
          rw [h2]
        · change gap f C v * (1 + t) ^ (s.updates + 1 - k) ≤ Δ
          have hexp : s.updates + 1 - k = (s.updates - k) + 1 := by omega
          rw [hexp, pow_succ]
          have hpow : 0 ≤ (1 + t) ^ (s.updates - k) := by positivity
          calc gap f C v * ((1 + t) ^ (s.updates - k) * (1 + t))
              = gap f C v * (1 + t) * (1 + t) ^ (s.updates - k) := by ring
            _ ≤ gap f C s.center * (1 + t) ^ (s.updates - k) :=
              mul_le_mul_of_nonneg_right hcon hpow
            _ ≤ Δ := hgk

noncomputable def iterBound (L μ r Δ ε : ℝ) : ℕ :=
  ⌊Real.logb 4 (1 + 6 * Δ / (L * r ^ 2))⌋₊ +
    ⌈Real.log (Δ / ε) / Real.log (1 + μ / (25 * L))⌉₊

noncomputable def searchBound (L μ r ε : ℝ) : ℕ :=
  ⌈Real.logb 4 (r ^ 2 * (8 * L ^ 2 / μ + 6 * L) / ε)⌉₊

def Inv (f : E → ℝ) (C : Set E) (L μ r Δ ε : ℝ) (Tg Tl : ℕ) (s : State E)
    (rem : Fin 2 → ℕ) : Prop :=
  (s.stopped = true → s.center ∈ C ∧ gap f C s.center ≤ 0) ∧
  (s.stopped = false → Good f C L μ r Δ ε s ∧ (rem 0 : ℤ) + gradCount s = Tg ∧
    (rem 1 : ℤ) + lmoCount s = Tl)

lemma inv_step (H : Hyp f C L μ) {r Δ ε : ℝ} (hr : 0 < r) {Tg Tl : ℕ}
    (O : Oracle (BroxQuery E) (BroxReply E) 2)
    (hgradO : ∀ history seed x, x ∈ C →
      O.answer history (0, .inl x) seed = .inl (fderiv ℝ f x))
    (hlmoO : ∀ history seed x r g, x ∈ C → 0 ≤ r →
      ∃ v ∈ C, ‖v - x‖ ≤ r ∧ (∀ z ∈ C, ‖z - x‖ ≤ r → g v ≤ g z) ∧
        O.answer history (1, .inr (x, r, g)) seed = .inr v)
    (history : List ((Fin 2 × BroxQuery E) × BroxReply E)) (seed : O.Seed history.length)
    (s : State E) (rem : Fin 2 → ℕ) (hs : Inv f C L μ r Δ ε Tg Tl s rem)
    (hpos : 0 < rem (query r s).1) :
    Inv f C L μ r Δ ε Tg Tl (update L r s (O.answer history (query r s) seed))
      (Function.update rem (query r s).1 (rem (query r s).1 - 1)) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  obtain ⟨u, x, e, sl, st⟩ := s
  cases st with
  | true =>
    have hu : ∀ reply, update L r (⟨u, x, e, sl, true⟩ : State E) reply = ⟨u, x, e, sl, true⟩ := by
      intro reply
      cases sl <;> cases reply <;> rfl
    rw [hu]
    exact ⟨hs.1, fun h => absurd h (by simp)⟩
  | false =>
    obtain ⟨hgood, hg, hl⟩ := hs.2 rfl
    cases sl with
    | none =>
      have hq : query r (⟨u, x, e, none, false⟩ : State E) = (0, .inl x) := rfl
      rw [hq] at hpos ⊢
      dsimp only at hpos ⊢
      rw [hgradO history seed x hgood.mem]
      refine ⟨fun h => absurd h (by simp [update]), fun _ => ⟨good_fetch hgood, ?_, ?_⟩⟩
      · simp only [update, gradCount, Function.update_self, Option.isSome_some, ite_true] at hg ⊢
        simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at hg
        omega
      · simp only [update, lmoCount, Function.update_of_ne h10] at hl ⊢
        exact hl
    | some φ =>
      have hφ : φ = fderiv ℝ f x := hgood.slope φ rfl
      have hq : query r (⟨u, x, e, some φ, false⟩ : State E) = (1, .inr (x, radius r e, φ)) :=
        rfl
      rw [hq] at hpos ⊢
      dsimp only at hpos ⊢
      obtain ⟨v, hv, hvx, hopt, hans⟩ :=
        hlmoO history seed x (radius r e) φ hgood.mem (radius_pos hr e).le
      rw [hans]
      subst hφ
      have hout : IsOutput f C x v (radius r e) := ⟨hv, hvx, hopt⟩
      dsimp only [update]
      split_ifs with h0 h1
      · exact ⟨fun _ => ⟨hgood.mem, stop_gap H hgood.mem (radius_pos hr e) hout h0⟩,
          fun h => absurd h (by simp)⟩
      · refine ⟨fun h => absurd h (by simp), fun _ => ⟨good_accept H hr hgood hout h1, ?_, ?_⟩⟩
        · simp only [gradCount, Function.update_of_ne h10.symm, Option.isSome_none,
            Option.isSome_some, Bool.false_eq_true, ite_false, ite_true] at hg ⊢
          push_cast
          omega
        · simp only [lmoCount, Function.update_self] at hl ⊢
          push_cast
          omega
      · refine ⟨fun h => absurd h (by simp), fun _ => ⟨good_reject H hr hgood (by simp) hout
          (lt_of_not_ge h1), ?_, ?_⟩⟩
        · simp only [gradCount, Function.update_of_ne h10.symm] at hg ⊢
          exact hg
        · simp only [lmoCount, Function.update_self] at hl ⊢
          omega

lemma updates_lt (H : Hyp f C L μ) {r Δ ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {s : State E}
    (hs : Good f C L μ r Δ ε s) (hgap : ε < gap f C s.center) :
    s.updates < iterBound L μ r Δ ε := by
  have hL := H.L_pos
  have hμ := H.μ_pos
  have hq : 1 < 1 + μ / (25 * L) := lt_add_of_pos_right _ (by positivity)
  have hΔ : ε < Δ := hgap.trans_le hs.bound
  obtain ⟨c, -, -, -, hph⟩ := hs.cap
  unfold iterBound
  rcases hph with ⟨-, hA⟩ | ⟨ρ, k, -, hk, h4k, -, -, hgk⟩
  · have hX : (4 : ℝ) ^ s.updates - 1 ≤ 6 * Δ / (L * r ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hkb := le_floor_logb (show (4 : ℝ) ^ s.updates ≤ 1 + 6 * Δ / (L * r ^ 2) by linarith)
    have hn : 0 < ⌈Real.log (Δ / ε) / Real.log (1 + μ / (25 * L))⌉₊ :=
      lt_ceil_log hq (by rw [pow_zero, one_lt_div hε]; exact hΔ)
    omega
  · have hkb := le_floor_logb h4k
    have hpow : 0 < (1 + μ / (25 * L)) ^ (s.updates - k) := by positivity
    have hn : s.updates - k < ⌈Real.log (Δ / ε) / Real.log (1 + μ / (25 * L))⌉₊ := by
      apply lt_ceil_log hq
      rw [lt_div_iff₀ hε]
      nlinarith
    omega

lemma inv_stop (H : Hyp f C L μ) {r Δ ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (s : State E)
    (rem : Fin 2 → ℕ)
    (hs : Inv f C L μ r Δ ε (iterBound L μ r Δ ε)
      (2 * iterBound L μ r Δ ε + searchBound L μ r ε) s rem)
    (h0 : rem (query r s).1 = 0) : s.center ∈ C ∧ gap f C s.center ≤ ε := by
  obtain ⟨u, x, e, sl, st⟩ := s
  cases st with
  | true =>
    obtain ⟨hm, hg⟩ := hs.1 rfl
    exact ⟨hm, hg.trans hε.le⟩
  | false =>
    obtain ⟨hgood, hg, hl⟩ := hs.2 rfl
    refine ⟨hgood.mem, ?_⟩
    by_contra hgap
    have hgap' := lt_of_not_ge hgap
    have hu := updates_lt H hr hε hgood hgap'
    cases sl with
    | none =>
      have hq : query r (⟨u, x, e, none, false⟩ : State E) = (0, .inl x) := rfl
      rw [hq] at h0
      simp only [gradCount, Option.isSome_none, Bool.false_eq_true, ite_false, h0] at hg
      simp only at hu
      omega
    | some φ =>
      have hq : query r (⟨u, x, e, some φ, false⟩ : State E) =
          (1, .inr (x, radius r e, φ)) := rfl
      rw [hq] at h0
      have hfl := hgood.floor.resolve_left hgap
      have he := trial_bound hr H.L_pos H.μ_pos hε hfl
      simp only [lmoCount, h0] at hl
      dsimp only at hl hu he
      unfold searchBound at hl
      omega

theorem execute_success (H : Hyp f C L μ) {r Δ ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {x0 : E}
    (hx0 : x0 ∈ C) (hΔ : gap f C x0 ≤ Δ) (O : Oracle (BroxQuery E) (BroxReply E) 2)
    (hgradO : ∀ history seed x, x ∈ C →
      O.answer history (0, .inl x) seed = .inl (fderiv ℝ f x))
    (hlmoO : ∀ history seed x r g, x ∈ C → 0 ≤ r →
      ∃ v ∈ C, ‖v - x‖ ≤ r ∧ (∀ z ∈ C, ‖z - x‖ ≤ r → g v ≤ g z) ∧
        O.answer history (1, .inr (x, r, g)) seed = .inr v)
    (b : Fin 2 → ℕ) (hb0 : b 0 = iterBound L μ r Δ ε)
    (hb1 : b 1 = 2 * iterBound L μ r Δ ε + searchBound L μ r ε)
    (seed : (algorithm L r x0).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm L r x0) b seed ξ ∈ C ∧
      gap f C (execute O (algorithm L r x0) b seed ξ) ≤ ε := by
  apply execute_of_invariant O (algorithm L r x0) b seed ξ
    (Inv f C L μ r Δ ε (iterBound L μ r Δ ε) (2 * iterBound L μ r Δ ε + searchBound L μ r ε))
    (fun y => y ∈ C ∧ gap f C y ≤ ε)
  · refine ⟨fun h => absurd h (by simp [algorithm]), fun _ => ⟨good_initial hx0 hΔ, ?_, ?_⟩⟩
    · simp [algorithm, gradCount, hb0]
    · simp [algorithm, lmoCount, hb1]
  · intro history s rem hs hpos
    exact inv_step H hr O hgradO hlmoO history (ξ history.length) s rem hs hpos
  · intro s rem hs h0
    exact inv_stop H hr hε s rem hs h0

end OracleTemplate.WarmHalvingBrox
