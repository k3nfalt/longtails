import LongTails.Proofs.RestartedChebyshevRun
import LongTails.Proofs.ScheduleBlockEstimates

namespace OracleTemplate.RestartedScheduleGD

open OracleTemplate.ScheduleBlock
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → ℝ} {L ρ ε G1 R K Δ : ℝ} {steps : List ℝ} {x0 : E}

lemma overshoot (hL : 0 ≤ L) (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (η : ℕ → ℝ) (y : E) {j : ℕ} {h : ℝ} (hη0 : 0 ≤ η j) (hη : η j ≤ h)
    (hG : ‖gradient f y‖ ≤ G1) (hin : ‖gdTraj f η y j - y‖ ≤ R) :
    ‖gdTraj f η y (j + 1) - y‖ ≤ R + h * (G1 + L * R) := by
  have hgr : ‖gradient f (gdTraj f η y j)‖ ≤ G1 + L * R := by
    have := hlip (gdTraj f η y j) y
    calc ‖gradient f (gdTraj f η y j)‖
        ≤ ‖gradient f (gdTraj f η y j) - gradient f y‖ + ‖gradient f y‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ L * ‖gdTraj f η y j - y‖ + G1 := add_le_add this hG
      _ ≤ G1 + L * R := by nlinarith
  have e : gdTraj f η y (j + 1) - y =
      (gdTraj f η y j - y) - η j • gradient f (gdTraj f η y j) := by
    simp only [gdTraj]; abel
  rw [e]
  calc _ ≤ ‖gdTraj f η y j - y‖ + ‖η j • gradient f (gdTraj f η y j)‖ := norm_sub_le _ _
    _ ≤ R + h * (G1 + L * R) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0]
        have : η j * ‖gradient f (gdTraj f η y j)‖ ≤ h * (G1 + L * R) :=
          mul_le_mul hη hgr (norm_nonneg _) (hη0.trans hη)
        linarith

noncomputable def runS (steps : List ℝ) : ℝ := ssum (fun j => steps.getD j 0) steps.length

noncomputable def runQ (steps : List ℝ) (ε : ℝ) : ℝ := runS steps * ε ^ 2 / 16

noncomputable def runA (steps : List ℝ) (ε : ℝ) : ℝ := runQ steps ε / (2 * steps.length)

structure RunHyp (f : E → ℝ) (L ρ ε G1 R K : ℝ) (steps : List ℝ) : Prop where
  hf : ContDiff ℝ 2 f
  hρ : 0 ≤ ρ
  hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖
  hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  F : ScheduleFacts (fun j => steps.getD j 0) steps.length L K
  hn : 1 ≤ steps.length
  hR0 : 0 ≤ R
  hG1 : 0 ≤ G1
  hε : 0 < ε
  hplain : runQ steps ε + runA steps ε ≤ G1 ^ 2 / (2 * L)
  hC : (K ^ 2 / 2 + 1181) * runS steps * (ρ * R ^ 2) ^ 2 +
      (L * K ^ 2 / 2 + 16 * L) * runS steps ^ 2 * (ρ * R ^ 2) ^ 2 +
      2 * runS steps * K ^ 2 * (steps.length : ℝ) ^ 2 * (ρ * R ^ 2) ^ 2 + ρ * R ^ 3 ≤
    runQ steps ε / 4
  hP : K * (2 * G1) * (runS steps * (ρ * (2 * R) ^ 2)) +
      L * K ^ 2 / 2 * runS steps ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 +
      1188 * runS steps * (ρ * (2 * R) ^ 2) ^ 2 +
      15 * L * runS steps ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 +
      15 * L ^ 2 * runS steps ^ 3 * (ρ * (2 * R) ^ 2) ^ 2 + 9 * ρ * R ^ 3 ≤ runQ steps ε / 4
  hEx1 : 42 * ρ * runS steps * (R + K / L * (G1 + L * R)) ≤ 1
  hEx2 : K * G1 * (runS steps * (ρ * R ^ 2)) + 2 * runS steps * G1 ^ 2 / 21 +
      (2 * K ^ 2 / 21 + 1181) * runS steps * (ρ * R ^ 2) ^ 2 +
      (L * K ^ 2 / 2 + 16 * L) * runS steps ^ 2 * (ρ * R ^ 2) ^ 2 + 2 * runQ steps ε ≤
    R ^ 2 / (42 * runS steps)
  hεe : ρ * R ^ 2 ≤ ε / 10

def Good (hf : ContDiff ℝ 2 f) (ε R : ℝ) (steps : List ℝ) (x0 : E) (τ : ℕ)
    (s : State E) : Prop :=
  s.index = 0 ∧ s.done = false ∧ ∃ P, 0 ≤ P ∧
    f s.point + P ≤ f x0 + runQ steps ε - runA steps ε * τ ∧
    (P = runQ steps ε ∨ (‖s.point - s.centre‖ ≤ R ∧
      P = runS steps / 8 * posPart
        (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf s.centre)
        (gradient f s.centre + fderiv ℝ (gradient f) s.centre (s.point - s.centre))))

lemma runQ_pos (H : RunHyp f L ρ ε G1 R K steps) : 0 < runQ steps ε := by
  have := ssum_pos H.F H.hn le_rfl
  unfold runQ runS
  have := H.hε
  positivity

lemma runA_mul_le (H : RunHyp f L ρ ε G1 R K steps) {ℓ : ℕ} (hℓ : ℓ ≤ steps.length) :
    runA steps ε * ℓ ≤ runQ steps ε / 2 := by
  have hQ := runQ_pos H
  have hn : (1 : ℝ) ≤ steps.length := by exact_mod_cast H.hn
  unfold runA
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (ℓ : ℝ) ≤ steps.length := by exact_mod_cast hℓ
  nlinarith

theorem segment_step (H : RunHyp f L ρ ε G1 R K steps) {τ : ℕ} {s : State E}
    (hs : Good H.hf ε R steps x0 τ s)
    (hgr : ∀ j < steps.length,
      ε < ‖gradient f ((stepS f L ε G1 R steps x0)^[j] s).point‖) :
    ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ steps.length ∧
      Good H.hf ε R steps x0 (τ + ℓ) ((stepS f L ε G1 R steps x0)^[ℓ] s) := by
  obtain ⟨x, c, i, d⟩ := s
  obtain ⟨hi, hd, P, hP0, hPbound, hPalt⟩ := hs
  simp only at hi hd hPbound hPalt
  subst hi; subst hd
  have hQ := runQ_pos H
  have hn := H.hn
  set n := steps.length with hn_def
  set S := runS steps
  set Q := runQ steps ε
  set a := runA steps ε
  have hg0 : ε < ‖gradient f x‖ := hgr 0 hn
  have hL := H.F.hL
  by_cases hbig : G1 < ‖gradient f x‖
  · refine ⟨1, le_rfl, hn, ?_⟩
    rw [Function.iterate_one, stepS_plain x c hg0 hbig]
    refine ⟨rfl, rfl, Q, hQ.le, ?_, Or.inl rfl⟩
    have hdes := plain_descent H.hf hL H.hlip x
    have hsq : G1 ^ 2 ≤ ‖gradient f x‖ ^ 2 := pow_le_pow_left₀ H.hG1 hbig.le 2
    have : G1 ^ 2 / (2 * L) ≤ ‖gradient f x‖ ^ 2 / (2 * L) :=
      div_le_div_of_nonneg_right hsq (by linarith)
    have hp := H.hplain
    push_cast
    linarith
  · push Not at hbig
    set η : ℕ → ℝ := fun j => steps.getD j 0
    set X := gdTraj f η x
    classical
    have hex := exists_exit (f := f) (R := R) (steps := steps) hn x
    set ℓ := Nat.find hex
    have hspec := Nat.find_spec hex
    have hℓ1 : 1 ≤ ℓ := hspec.1
    have hℓn : ℓ ≤ n := Nat.find_min' hex ⟨hn, Or.inl le_rfl⟩
    have hmin : ∀ j, 1 ≤ j → j < ℓ → j < n ∧ ‖X j - x‖ ≤ R := by
      intro j hj1 hjℓ
      have := Nat.find_min hex hjℓ
      push Not at this
      exact (this hj1)
    have hstates := block_states (f := f) (L := L) (ε := ε) (x0 := x0) rfl x c ℓ hℓ1
      hspec.2 hmin hbig (fun j hj => hgr j (by omega))
    have hinside := block_inside H.hR0 x ℓ hmin
    have hend := hstates ℓ hℓ1 le_rfl
    simp only [lt_irrefl, ite_false] at hend
    refine ⟨ℓ, hℓ1, hℓn, ?_⟩
    rw [hend]
    have hX : ∀ s, X (s + 1) = X s - η s • gradient f (X s) := fun s => rfl
    have hX0 : X 0 = x := rfl
    by_cases hexit : R < ‖X ℓ - x‖
    · refine ⟨rfl, rfl, Q, hQ.le, ?_, Or.inl rfl⟩
      simp only
      have hbe := block_exit H.hf H.hρ H.hH H.hlip H.F X x hX hX0 hℓ1 hℓn
        (fun s hs => hinside s hs) hbig
      have hov : ‖X ℓ - x‖ ≤ R + K / L * (G1 + L * R) := by
        obtain ⟨j, hj⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
        rw [hj]
        exact overshoot hL.le H.hlip η x (H.F.eta_nonneg j) (H.F.eta_le j (by omega)) hbig
          (hinside j (by omega))
      set D := ‖X ℓ - x‖
      have hS : 0 < S := ssum_pos H.F hn le_rfl
      have hD0 : 0 ≤ D := norm_nonneg _
      have hcube : ρ * D ^ 3 ≤ D ^ 2 / (42 * S) := by
        have h1 : 42 * ρ * S * D ≤ 1 := by
          have := H.hEx1
          have : 42 * ρ * S * D ≤ 42 * ρ * S * (R + K / L * (G1 + L * R)) := by
            apply mul_le_mul_of_nonneg_left hov
            have := H.hρ; positivity
          linarith
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg D]
      have hRD : R ^ 2 / (42 * S) ≤ D ^ 2 / (42 * S) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ H.hR0 hexit.le 2
      have hsplit : D ^ 2 / (21 * S) = 2 * (D ^ 2 / (42 * S)) := by field_simp; ring
      have hE2 := H.hEx2
      have hA := runA_mul_le H hℓn
      rw [show ssum η n = S from rfl] at hbe
      push_cast
      linarith
    · push Not at hexit
      have hℓeq : ℓ = n := le_antisymm hℓn (by
        rcases hspec.2 with h | h
        · exact h
        · linarith)
      have hinR : ∀ s ≤ n, ‖X s - x‖ ≤ R := by
        intro s hs
        rcases lt_or_eq_of_le hs with h | h
        · exact hinside s (by omega)
        · rw [h, ← hℓeq]; exact hexit
      have hS : 0 < S := ssum_pos H.F hn le_rfl
      have hbc := block_completed H.hf H.hρ H.hH H.hlip H.F hn X x hX hX0 hinR
      rw [show ssum η n = S from rfl] at hbc
      set A' := posPart (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric H.hf x)
        (gradient f x + fderiv ℝ (gradient f) x (X n - x))
      have hA'0 : 0 ≤ A' := posPart_nonneg _ _
      refine ⟨rfl, rfl, S / 8 * A', by positivity, ?_, Or.inr ⟨hexit, by rw [hℓeq]⟩⟩
      simp only
      rw [hℓeq]
      have hC := H.hC
      have hAn := runA_mul_le H (le_refl n)
      rcases hPalt with hPQ | ⟨hxc, hPA⟩
      · rw [hPQ] at hPbound
        push_cast at hPbound ⊢
        have : 0 ≤ S / 8 * A' := by positivity
        linarith
      · have hcR : ‖x - c‖ ≤ R := hxc
        have hγ0 := frame_err H.hf H.hρ H.hH c x hcR
        set γ := gradient f c + fderiv ℝ (gradient f) c (x - c)
        have hγx : ‖gradient f x - γ‖ ≤ ρ * R ^ 2 := by
          have e : gradient f x - γ =
              gradient f x - gradient f c - fderiv ℝ (gradient f) c (x - c) := by
            simp only [γ]; abel
          rw [e]; exact hγ0
        have hεe := H.hεe
        have hε0 := H.hε
        have hγup : ‖γ‖ ≤ 2 * G1 := by
          have := norm_le_norm_sub_add γ (gradient f x)
          rw [norm_sub_rev] at this
          linarith
        have hγlo : 9 * ε / 10 ≤ ‖γ‖ := by
          have := norm_le_norm_sub_add (gradient f x) γ
          linarith
        have hbp := block_pred H.hf H.hρ H.hH H.hlip H.F hn X c x hX hX0 hcR hinR hγup
        rw [show ssum η n = S from rfl] at hbp
        have hPP := H.hP
        set B := negPart (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric H.hf c) γ
        have hsum := posPart_add_negPart
          (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric H.hf c) γ
        have hγsq : (9 * ε / 10) ^ 2 ≤ ‖γ‖ ^ 2 :=
          pow_le_pow_left₀ (by have := H.hε; positivity) hγlo 2
        have hQdef : Q = S * ε ^ 2 / 16 := rfl
        rw [hPA] at hPbound
        push_cast at hPbound ⊢
        have hB0 : 0 ≤ B := negPart_nonneg _ _
        have p1 : S * (9 * ε / 10) ^ 2 ≤ S * ‖γ‖ ^ 2 := mul_le_mul_of_nonneg_left hγsq hS.le
        have p2 : 0 ≤ S * B := mul_nonneg hS.le hB0
        set Ac := posPart (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric H.hf c) γ
        have p3 : S * Ac + S * B = S * ‖γ‖ ^ 2 := by rw [← mul_add, hsum]
        have p4 : S * (9 * ε / 10) ^ 2 = 81 / 100 * (S * ε ^ 2) := by ring
        linarith

theorem reach (H : RunHyp f L ρ ε G1 R K steps) (N : ℕ)
    (hgr : ∀ t < N, ε < ‖gradient f
      ((stepS f L ε G1 R steps x0)^[t] ⟨x0, x0, 0, false⟩).point‖) :
    ∀ m, ∃ τ ≤ N, (N < τ + steps.length ∨ m ≤ τ) ∧
      Good H.hf ε R steps x0 τ ((stepS f L ε G1 R steps x0)^[τ] ⟨x0, x0, 0, false⟩) := by
  intro m
  induction m with
  | zero =>
    refine ⟨0, Nat.zero_le _, Or.inr le_rfl, rfl, rfl, runQ steps ε, (runQ_pos H).le, ?_,
      Or.inl rfl⟩
    simp
  | succ m ih =>
    obtain ⟨τ, hτN, hτ, hgood⟩ := ih
    by_cases hfar : N < τ + steps.length
    · exact ⟨τ, hτN, Or.inl hfar, hgood⟩
    · push Not at hfar
      have hmτ : m ≤ τ := by
        rcases hτ with h | h
        · omega
        · exact h
      obtain ⟨ℓ, hℓ1, hℓn, hg'⟩ := segment_step H hgood (fun j hj => by
        rw [← Function.iterate_add_apply]
        exact hgr (j + τ) (by omega))
      rw [← Function.iterate_add_apply, add_comm ℓ τ] at hg'
      exact ⟨τ + ℓ, by omega, Or.inr (by omega), hg'⟩

theorem count_bound (H : RunHyp f L ρ ε G1 R K steps) (hΔ : ∀ x, f x0 - f x ≤ Δ) (N : ℕ)
    (hgr : ∀ t < N, ε < ‖gradient f
      ((stepS f L ε G1 R steps x0)^[t] ⟨x0, x0, 0, false⟩).point‖) :
    (N : ℝ) < (Δ + runQ steps ε) / runA steps ε + steps.length := by
  obtain ⟨τ, hτN, hτ, hgood⟩ := reach H N hgr (N + 1)
  have hfar : N < τ + steps.length := by
    rcases hτ with h | h
    · exact h
    · omega
  obtain ⟨-, -, P, hP0, hPb, -⟩ := hgood
  have hd := hΔ ((stepS f L ε G1 R steps x0)^[τ] ⟨x0, x0, 0, false⟩).point
  have hQ := runQ_pos H
  have ha : 0 < runA steps ε := by
    unfold runA
    have : (0:ℝ) < steps.length := by exact_mod_cast H.hn
    positivity
  have hτa : runA steps ε * τ ≤ Δ + runQ steps ε := by linarith
  have hτle : (τ : ℝ) ≤ (Δ + runQ steps ε) / runA steps ε := by
    rw [le_div_iff₀ ha]; linarith
  have : (N : ℝ) < τ + steps.length := by exact_mod_cast hfar
  linarith

theorem gd_bound (hf : ContDiff ℝ 2 f) (hL : 0 < L) (hε : 0 < ε)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hΔ : ∀ x, f x0 - f x ≤ Δ)
    (N : ℕ) (hgr : ∀ t < N, ε < ‖gradient f
      ((stepS f L ε 0 R [] x0)^[t] ⟨x0, x0, 0, false⟩).point‖) :
    (N : ℝ) * ε ^ 2 ≤ 2 * L * Δ := by
  have key : ∀ t ≤ N, ∃ x, (stepS f L ε 0 R [] x0)^[t] ⟨x0, x0, 0, false⟩ = ⟨x, x0, 0, false⟩ ∧
      f x ≤ f x0 - t * (ε ^ 2 / (2 * L)) := by
    intro t ht
    induction t with
    | zero => exact ⟨x0, rfl, by simp⟩
    | succ t ih =>
      obtain ⟨x, hx, hfx⟩ := ih (by omega)
      have hg := hgr t (by omega)
      rw [hx] at hg
      have hg' : ε < ‖gradient f x‖ := hg
      refine ⟨x - L⁻¹ • gradient f x, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hx]
        exact stepS_plain x x0 hg' (by linarith)
      · have hd := plain_descent hf hL hlip x
        have h2 : ε ^ 2 / (2 * L) ≤ ‖gradient f x‖ ^ 2 / (2 * L) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hε.le hg'.le 2) (by linarith)
        push_cast
        linarith
  obtain ⟨x, -, hfx⟩ := key N le_rfl
  have := hΔ x
  have h2 : (N : ℝ) * (ε ^ 2 / (2 * L)) ≤ Δ := by linarith
  have e : (N : ℝ) * ε ^ 2 = 2 * L * ((N : ℝ) * (ε ^ 2 / (2 * L))) := by field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 2 * L)
  linarith

end OracleTemplate.RestartedScheduleGD
