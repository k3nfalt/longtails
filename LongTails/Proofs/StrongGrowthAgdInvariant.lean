import LongTails.Proofs.StrongGrowthAgdProcess
import LongTails.Proofs.StrongGrowthAgdWeights
import LongTails.Proofs.StrongGrowthAgdEpochEnd

namespace LongTails.Proofs.StrongGrowthAgdInvariant

open LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdProcess
  LongTails.Proofs.StrongGrowthAgdWeights LongTails.Proofs.StrongGrowthAgdModel
  LongTails.Proofs.StrongGrowthAgdEpochEnd
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {Ω : Type}
variable (cfg : Config) (x0 : E) (g : E → Ω → E)

lemma Eb_gt (hK : 1 ≤ cfg.K) : 1 < cfg.Eb := by unfold Config.Eb; omega

lemma K_lt_Eb : cfg.K < cfg.Eb := by unfold Config.Eb; omega

lemma pos_lt_Eb (hEb : 0 < cfg.Eb) (t : ℕ) : cfg.pos t < cfg.Eb := Nat.mod_lt _ hEb

lemma pos_succ_of_lt (hEb : 1 < cfg.Eb) {t : ℕ} (h : cfg.pos t + 1 < cfg.Eb) :
    cfg.pos (t + 1) = cfg.pos t + 1 := by
  unfold Config.pos at *
  rw [Nat.add_mod, Nat.mod_eq_of_lt hEb, Nat.mod_eq_of_lt h]

lemma pos_succ_of_eq (hEb : 1 < cfg.Eb) {t : ℕ} (h : cfg.pos t + 1 = cfg.Eb) :
    cfg.pos (t + 1) = 0 := by
  unfold Config.pos at *
  rw [Nat.add_mod, Nat.mod_eq_of_lt hEb, h, Nat.mod_self]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma blockStep_of_done {s : State E} (hd : s.done = true) (ω : Fin cfg.b → Ω) :
    blockStep cfg x0 g s ω = s := by
  simp [blockStep, hd]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma blockStep_frozen {s : State E} (hd : s.done = false) (hk : cfg.pos s.t < cfg.K)
    (htr : s.trig = true) (ω : Fin cfg.b → Ω) :
    blockStep cfg x0 g s ω = { s with t := s.t + 1 } := by
  simp only [blockStep, batchUpdate, hd, Bool.false_eq_true, ↓reduceIte, hk, htr]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma blockStep_agd {s : State E} (hd : s.done = false) (hk : cfg.pos s.t < cfg.K)
    (htr : s.trig = false) (ω : Fin cfg.b → Ω) :
    blockStep cfg x0 g s ω =
      { s with
        t := s.t + 1
        xPrev := s.x
        x := ypoint cfg s - cfg.η • bmean cfg g (ypoint cfg s) ω
        glast := bmean cfg g (ypoint cfg s) ω
        S := s.S + ‖ypoint cfg s - cfg.η • bmean cfg g (ypoint cfg s) ω - s.x‖ ^ 2
        ybar := s.ybar + pw cfg.K (cfg.pos s.t) • ypoint cfg s
        trig := decide (cfg.B ^ 2 < ((cfg.pos s.t + 1 : ℕ) : ℝ) *
          (s.S + ‖ypoint cfg s - cfg.η • bmean cfg g (ypoint cfg s) ω - s.x‖ ^ 2)) } := by
  simp only [blockStep, batchUpdate, queryPoint, hd, Bool.false_eq_true, ↓reduceIte, hk, htr]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma blockStep_gd {s : State E} (hd : s.done = false) (hk : cfg.pos s.t = cfg.K)
    (ω : Fin cfg.b → Ω) :
    blockStep cfg x0 g s ω =
      { s with
        t := s.t + 1
        xPrev := s.x - cfg.ηf • bmean cfg g s.x ω
        x := s.x - cfg.ηf • bmean cfg g s.x ω } := by
  simp only [blockStep, batchUpdate, queryPoint, hd, Bool.false_eq_true, ↓reduceIte, hk,
    lt_self_iff_false]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma blockStep_val {s : State E} (hd : s.done = false) (hk : cfg.K < cfg.pos s.t)
    (hlt : cfg.pos s.t + 1 < cfg.Eb) (ω : Fin cfg.b → Ω) :
    blockStep cfg x0 g s ω =
      { s with
        t := s.t + 1
        vCount := if s.trig = true then s.vCount
          else s.vCount + (if ‖bmean cfg g s.ybar ω‖ ≤ cfg.thr then 1 else 0) } := by
  have h1 : ¬ cfg.pos s.t < cfg.K := by omega
  have h2 : ¬ cfg.pos s.t = cfg.K := by omega
  simp only [blockStep, batchUpdate, queryPoint, hd, Bool.false_eq_true, ↓reduceIte, h1, h2, hlt]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma blockStep_last {s : State E} (hd : s.done = false) (hk : cfg.K < cfg.pos s.t)
    (heq : cfg.pos s.t + 1 = cfg.Eb) (ω : Fin cfg.b → Ω) :
    blockStep cfg x0 g s ω =
      (if ¬ s.trig = true ∧ 2 * (if s.trig = true then s.vCount
          else s.vCount + (if ‖bmean cfg g s.ybar ω‖ ≤ cfg.thr then 1 else 0)) > cfg.m
        then { s with t := s.t + 1, done := true, out := s.ybar }
        else restart cfg x0 s) := by
  have h1 : ¬ cfg.pos s.t < cfg.K := by omega
  have h2 : ¬ cfg.pos s.t = cfg.K := by omega
  have h3 : ¬ cfg.pos s.t + 1 < cfg.Eb := by omega
  simp only [blockStep, batchUpdate, queryPoint, hd, Bool.false_eq_true, ↓reduceIte, h1, h2, h3]

variable (f : E → ℝ) (ρ : ℝ)

noncomputable def Dm : ℝ := 4 * ρ * cfg.B ^ 2

noncomputable def cw : ℝ := 7 / (cfg.K : ℝ) ^ 2 + 2 * cfg.θ / cfg.K

noncomputable def wsum (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, pw cfg.K i

noncomputable def Avec (xS ybar : E) (k : ℕ) : E :=
  wsum cfg k • gradient f xS + fderiv ℝ (gradient f) xS (ybar - wsum cfg k • xS)

noncomputable def Zvec (sN : State E × E) : E :=
  cfg.η • (Avec cfg f sN.1.xStart sN.1.ybar (cfg.pos sN.1.t) + sN.2) +
    ((1 - cfg.θ) * pw cfg.K (cfg.pos sN.1.t)) • (sN.1.x - sN.1.xPrev)

noncomputable def nextN (sN : State E × E) (ω : Fin cfg.b → Ω) : E :=
  if sN.1.done = false ∧ cfg.pos sN.1.t < cfg.K ∧ sN.1.trig = false then
    (if cfg.pos sN.1.t = 0 then 0 else sN.2) +
      pw cfg.K (cfg.pos sN.1.t) • (bmean cfg g (ypoint cfg sN.1) ω - gradient f (ypoint cfg sN.1))
  else sN.2

noncomputable def astep (sN : State E × E) (ω : Fin cfg.b → Ω) : State E × E :=
  (blockStep cfg x0 g sN.1 ω, nextN cfg g f sN ω)

structure InvAgd (sN : State E × E) : Prop where
  hx : ‖sN.1.x - sN.1.xStart‖ ≤ Real.sqrt (cfg.pos sN.1.t * sN.1.S)
  hd : ‖sN.1.x - sN.1.xPrev‖ ^ 2 ≤ sN.1.S
  hS : (cfg.pos sN.1.t : ℝ) * sN.1.S ≤ cfg.B ^ 2
  hS0 : 0 ≤ sN.1.S
  hyb : ‖sN.1.ybar - wsum cfg (cfg.pos sN.1.t) • sN.1.xStart‖ ≤ 2 * cfg.B * wsum cfg (cfg.pos sN.1.t)
  hZ : 1 ≤ cfg.pos sN.1.t → ‖Zvec cfg f sN‖ ≤
    cw cfg * Real.sqrt (cfg.pos sN.1.t * sN.1.S) + cfg.η * Dm cfg ρ * wsum cfg (cfg.pos sN.1.t)
  hstart : cfg.pos sN.1.t = 0 →
    sN.1.xPrev = sN.1.x ∧ sN.1.x = sN.1.xStart ∧ sN.1.glast = 0 ∧ sN.1.S = 0 ∧ sN.1.ybar = 0

structure Inv (cfg : Config) (x0 : E) (f : E → ℝ) (ρ : ℝ) (sN : State E × E) : Prop where
  hi : sN.1.i = 0
  hacc : sN.1.acc = 0
  hvc : sN.1.vCount ≤ cfg.m
  hfresh : sN.1.done = false → cfg.pos sN.1.t = 0 → sN.1.trig = false
  hx0 : sN.1.done = false → sN.1.t % (cfg.N1 * cfg.Eb) = 0 → sN.1.x = x0
  hlast : sN.1.done = false → cfg.pos sN.1.t ≤ cfg.K →
    ‖sN.1.x + cfg.η • sN.1.glast - sN.1.xStart‖ ≤ 2 * cfg.B
  hagd : sN.1.done = false → cfg.pos sN.1.t ≤ cfg.K → sN.1.trig = false → InvAgd cfg f ρ sN
  hval : sN.1.done = false → cfg.K < cfg.pos sN.1.t → sN.1.trig = false →
    ‖sN.1.ybar - sN.1.xStart‖ ≤ 2 * cfg.B
  hvc2 : sN.1.done = false → cfg.K < cfg.pos sN.1.t → sN.1.vCount + cfg.K + 1 ≤ cfg.pos sN.1.t
  hvc0 : sN.1.done = false → cfg.pos sN.1.t ≤ cfg.K → sN.1.vCount = 0

structure CfgHyp : Prop where
  hK : 3 ≤ cfg.K
  hθ0 : 0 < cfg.θ
  hθ1 : cfg.θ ≤ 1
  hη : 0 < cfg.η
  hB : 0 < cfg.B
  hm : 1 ≤ cfg.m

variable {cfg f ρ}

omit [FiniteDimensional ℝ E] in
lemma InvAgd.S_le (_hc : CfgHyp cfg) {sN : State E × E} (h : InvAgd cfg f ρ sN) : sN.1.S ≤ cfg.B ^ 2 := by
  rcases Nat.eq_zero_or_pos (cfg.pos sN.1.t) with h0 | hpos
  · rw [(h.hstart h0).2.2.2.1]; positivity
  · have h1 : (1 : ℝ) ≤ cfg.pos sN.1.t := by exact_mod_cast hpos
    nlinarith [h.hS, h.hS0]

omit [FiniteDimensional ℝ E] in
lemma InvAgd.x_le (hc : CfgHyp cfg) {sN : State E × E} (h : InvAgd cfg f ρ sN) :
    ‖sN.1.x - sN.1.xStart‖ ≤ cfg.B := by
  refine h.hx.trans ?_
  rw [Real.sqrt_le_left hc.hB.le]
  exact h.hS

omit [FiniteDimensional ℝ E] in
lemma InvAgd.d_le (hc : CfgHyp cfg) {sN : State E × E} (h : InvAgd cfg f ρ sN) :
    ‖sN.1.x - sN.1.xPrev‖ ≤ cfg.B := by
  have := h.hd.trans (h.S_le hc)
  nlinarith [norm_nonneg (sN.1.x - sN.1.xPrev), hc.hB]

omit [FiniteDimensional ℝ E] in
lemma InvAgd.y_le (hc : CfgHyp cfg) {sN : State E × E} (h : InvAgd cfg f ρ sN) :
    ‖ypoint cfg sN.1 - sN.1.xStart‖ ≤ 2 * cfg.B := by
  unfold ypoint
  have e : sN.1.x + (1 - cfg.θ) • (sN.1.x - sN.1.xPrev) - sN.1.xStart =
      (sN.1.x - sN.1.xStart) + (1 - cfg.θ) • (sN.1.x - sN.1.xPrev) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hc.hθ1])]
  have h1 := h.x_le hc
  have h2 := h.d_le hc
  nlinarith [hc.hθ0, norm_nonneg (sN.1.x - sN.1.xPrev)]

lemma cw_nonneg (hc : CfgHyp cfg) : 0 ≤ cw cfg := by
  unfold cw
  have : (0 : ℝ) < cfg.K := by exact_mod_cast (show 0 < cfg.K by have := hc.hK; omega)
  have := hc.hθ0
  positivity

lemma coef_le (hc : CfgHyp cfg) (k : ℕ) (hk : k + 1 ≤ cfg.K) :
    |(1 - cfg.θ) * pw cfg.K (k + 1) - pw cfg.K k| ≤ cw cfg := by
  have hK : 3 ≤ cfg.K := hc.hK
  have h1 := pw_succ_sub (K := cfg.K) (k := k) hK hk
  have h2 := pw_le (K := cfg.K) (k := k + 1) (by omega)
  have hKpos : (0 : ℝ) < cfg.K := by exact_mod_cast (show 0 < cfg.K by omega)
  have e : (1 - cfg.θ) * pw cfg.K (k + 1) - pw cfg.K k =
      (pw cfg.K (k + 1) - pw cfg.K k) - cfg.θ * pw cfg.K (k + 1) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  unfold cw
  rw [abs_mul, abs_of_pos hc.hθ0]
  have h3 : |pw cfg.K (k + 1)| ≤ 2 / cfg.K := by
    rw [abs_le]
    constructor
    · have := pw_nonneg (K := cfg.K) (k := k + 1) (by omega) hk
      linarith [show (0:ℝ) ≤ 2 / cfg.K by positivity]
    · exact h2
  calc |pw cfg.K (k + 1) - pw cfg.K k| + cfg.θ * |pw cfg.K (k + 1)|
      ≤ 7 / (cfg.K : ℝ) ^ 2 + cfg.θ * (2 / cfg.K) := by
        have := mul_le_mul_of_nonneg_left h3 hc.hθ0.le
        linarith
    _ = 7 / (cfg.K : ℝ) ^ 2 + 2 * cfg.θ / cfg.K := by ring

lemma sqrt_step {k S v : ℝ} (hk : 0 ≤ k) (hS : 0 ≤ S) (hv : 0 ≤ v) :
    Real.sqrt (k * S) + v ≤ Real.sqrt ((k + 1) * (S + v ^ 2)) := by
  rw [Real.sqrt_mul hk]
  have ha := Real.sqrt_nonneg k
  have hb := Real.sqrt_nonneg S
  have ha2 : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk
  have hb2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS
  rw [Real.le_sqrt (by positivity) (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt S - Real.sqrt k * v), mul_nonneg ha hb]

omit [FiniteDimensional ℝ E] in
lemma Avec_succ (xS ybar y : E) (k : ℕ) :
    Avec cfg f xS (ybar + pw cfg.K k • y) (k + 1) =
      Avec cfg f xS ybar k + pw cfg.K k • gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) y := by
  unfold Avec wsum gradModel
  rw [Finset.sum_range_succ]
  simp only [add_smul, map_add, map_sub, map_smul, smul_sub, smul_add]
  abel

omit [FiniteDimensional ℝ E] in
lemma Avec_zero_one (xS : E) : Avec cfg f xS (0 + pw cfg.K 0 • (0 : E)) 1 = 0 := by
  simp [Avec, wsum, pw_zero]

omit [FiniteDimensional ℝ E] in
variable (cfg f) in
lemma nextN_of_not {s : State E} {N : E} (ω : Fin cfg.b → Ω)
    (h : ¬ (s.done = false ∧ cfg.pos s.t < cfg.K ∧ s.trig = false)) :
    nextN cfg g f (s, N) ω = N := by
  simp only [nextN, h, ↓reduceIte]

omit [FiniteDimensional ℝ E] in
variable (cfg f) in
lemma nextN_agd {s : State E} {N : E} (ω : Fin cfg.b → Ω) (hd : s.done = false)
    (hk : cfg.pos s.t < cfg.K) (htr : s.trig = false) :
    nextN cfg g f (s, N) ω = (if cfg.pos s.t = 0 then 0 else N) +
      pw cfg.K (cfg.pos s.t) • (bmean cfg g (ypoint cfg s) ω - gradient f (ypoint cfg s)) := by
  simp only [nextN, hd, hk, htr, and_self, ↓reduceIte]

omit [FiniteDimensional ℝ E] in
lemma Zvec_succ_eq (_hc : CfgHyp cfg) {s : State E} {N : E} (y x' ghat : E) (k : ℕ)
    (hy : y = s.x + (1 - cfg.θ) • (s.x - s.xPrev)) (hx' : x' = y - cfg.η • ghat) (hk : cfg.pos s.t = k) :
    cfg.η • (Avec cfg f s.xStart (s.ybar + pw cfg.K k • y) (k + 1) +
        (N + pw cfg.K k • (ghat - gradient f y))) +
      ((1 - cfg.θ) * pw cfg.K (k + 1)) • (x' - s.x) =
      Zvec cfg f (s, N) + ((1 - cfg.θ) * pw cfg.K (k + 1) - pw cfg.K k) • (x' - s.x) -
        (cfg.η * pw cfg.K k) • (gradient f y - gradModel (fderiv ℝ (gradient f) s.xStart) s.xStart
          (gradient f s.xStart) y) := by
  unfold Zvec
  rw [Avec_succ, hk]
  subst hx' hy
  module

variable (cfg) in
lemma pos_zero_of_trial (t : ℕ) (h : t % (cfg.N1 * cfg.Eb) = 0) : cfg.pos t = 0 := by
  unfold Config.pos
  rw [← Nat.mod_mul_right_mod t cfg.Eb cfg.N1, mul_comm, h, Nat.zero_mod]

variable (cfg f ρ) in
theorem inv_preserved (hc : CfgHyp cfg) (h : Hyp f L ρ) {sN : State E × E} (hinv : Inv cfg x0 f ρ sN)
    (ω : Fin cfg.b → Ω) : Inv cfg x0 f ρ (astep cfg x0 g f sN ω) := by
  obtain ⟨s, N⟩ := sN
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := hc.hK; omega)
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  have hposE : cfg.pos s.t < cfg.Eb := pos_lt_Eb cfg (by omega) s.t
  have hDm : 0 ≤ Dm cfg ρ := by unfold Dm; have := h.hρ; positivity
  unfold astep
  by_cases hd : s.done = true
  · rw [blockStep_of_done cfg x0 g hd, nextN_of_not cfg g f ω (by simp [hd])]
    exact hinv
  have hd' : s.done = false := by simpa using hd
  by_cases hkK : cfg.pos s.t < cfg.K
  · have hp : cfg.pos (s.t + 1) = cfg.pos s.t + 1 := pos_succ_of_lt cfg hEb (by omega)
    have hnt : ¬ (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 := by
      intro h0; have := pos_zero_of_trial cfg (s.t + 1) h0; omega
    by_cases htr : s.trig = true
    ·
      rw [blockStep_frozen cfg x0 g hd' hkK htr, nextN_of_not cfg g f ω (by simp [htr])]
      refine ⟨hinv.hi, hinv.hacc, hinv.hvc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ h0; simp only [hp] at h0; omega
      · intro _ h0; exact absurd h0 hnt
      · intro _ _; exact hinv.hlast hd' hkK.le
      · intro _ _ h'; simp [htr] at h'
      · intro _ h' _; simp only [hp] at h'; omega
      · intro _ h'; simp only [hp] at h'; omega
      · intro _ _; exact hinv.hvc0 hd' hkK.le
    · have htr' : s.trig = false := by simpa using htr
      have hA := hinv.hagd hd' hkK.le htr'
      rw [blockStep_agd cfg x0 g hd' hkK htr', nextN_agd cfg g f ω hd' hkK htr']
      set y := ypoint cfg s with hy
      set ghat := bmean cfg g y ω with hghat
      set x' := y - cfg.η • ghat with hx'
      set k := cfg.pos s.t with hk
      have hyS : ‖y - s.xStart‖ ≤ 2 * cfg.B := hA.y_le hc
      have hxS := hA.x_le hc
      have hdd := hA.d_le hc
      have hyx : y = s.x + (1 - cfg.θ) • (s.x - s.xPrev) := rfl
      have hδ : ‖gradient f y - gradModel (fderiv ℝ (gradient f) s.xStart) s.xStart (gradient f s.xStart) y‖
          ≤ Dm cfg ρ := by
        refine (h.gradModel_err s.xStart y).trans ?_
        unfold Dm
        have hsq : ‖y - s.xStart‖ ^ 2 ≤ (2 * cfg.B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyS 2
        have := mul_le_mul_of_nonneg_left hsq h.hρ
        nlinarith [this]
      have hw0 : 0 ≤ pw cfg.K k := pw_nonneg (by have := hc.hK; omega) hkK.le
      have hws : wsum cfg (k + 1) = wsum cfg k + pw cfg.K k := Finset.sum_range_succ _ _
      refine ⟨hinv.hi, hinv.hacc, hinv.hvc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ h0; simp only [hp] at h0; omega
      · intro _ h0; exact absurd h0 hnt
      · intro _ _
        show ‖x' + cfg.η • ghat - s.xStart‖ ≤ 2 * cfg.B
        rw [hx', sub_add_cancel]
        exact hyS
      · intro _ _ hfire
        have hfire' : ((k + 1 : ℕ) : ℝ) * (s.S + ‖x' - s.x‖ ^ 2) ≤ cfg.B ^ 2 := by
          have := of_decide_eq_false hfire
          exact not_lt.mp this
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show ‖x' - s.xStart‖ ≤ Real.sqrt (cfg.pos (s.t + 1) * (s.S + ‖x' - s.x‖ ^ 2))
          rw [hp]
          push_cast
          calc ‖x' - s.xStart‖ = ‖(s.x - s.xStart) + (x' - s.x)‖ := by congr 1; abel
            _ ≤ ‖s.x - s.xStart‖ + ‖x' - s.x‖ := norm_add_le _ _
            _ ≤ Real.sqrt (k * s.S) + ‖x' - s.x‖ := by linarith [hA.hx]
            _ ≤ _ := sqrt_step (Nat.cast_nonneg _) hA.hS0 (norm_nonneg _)
        · show ‖x' - s.x‖ ^ 2 ≤ s.S + ‖x' - s.x‖ ^ 2
          linarith [hA.hS0]
        · show (cfg.pos (s.t + 1) : ℝ) * (s.S + ‖x' - s.x‖ ^ 2) ≤ cfg.B ^ 2
          rw [hp]; exact_mod_cast hfire'
        · show 0 ≤ s.S + ‖x' - s.x‖ ^ 2
          have := hA.hS0; positivity
        · show ‖s.ybar + pw cfg.K k • y - wsum cfg (cfg.pos (s.t + 1)) • s.xStart‖ ≤
            2 * cfg.B * wsum cfg (cfg.pos (s.t + 1))
          rw [hp, hws]
          calc ‖s.ybar + pw cfg.K k • y - (wsum cfg k + pw cfg.K k) • s.xStart‖
              = ‖(s.ybar - wsum cfg k • s.xStart) + pw cfg.K k • (y - s.xStart)‖ := by
                congr 1; simp only [add_smul, smul_sub]; abel
            _ ≤ ‖s.ybar - wsum cfg k • s.xStart‖ + pw cfg.K k * ‖y - s.xStart‖ := by
                refine (norm_add_le _ _).trans ?_
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
            _ ≤ 2 * cfg.B * wsum cfg k + pw cfg.K k * (2 * cfg.B) := by
                have := mul_le_mul_of_nonneg_left hyS hw0
                linarith [hA.hyb]
            _ = 2 * cfg.B * (wsum cfg k + pw cfg.K k) := by ring
        · intro _
          show ‖cfg.η • (Avec cfg f s.xStart (s.ybar + pw cfg.K k • y) (cfg.pos (s.t + 1)) +
              ((if k = 0 then 0 else N) + pw cfg.K k • (ghat - gradient f y))) +
              ((1 - cfg.θ) * pw cfg.K (cfg.pos (s.t + 1))) • (x' - s.x)‖ ≤
            cw cfg * Real.sqrt (cfg.pos (s.t + 1) * (s.S + ‖x' - s.x‖ ^ 2)) +
              cfg.η * Dm cfg ρ * wsum cfg (cfg.pos (s.t + 1))
          rw [hp, hws]
          push_cast
          have hcw := cw_nonneg hc
          have hcoef := coef_le hc k (by omega)
          by_cases hk0 : k = 0
          · obtain ⟨h1, h2, h3, h4, h5⟩ := hA.hstart hk0
            have h4' : s.S = 0 := h4
            have h5' : s.ybar = 0 := h5
            have hw0' : wsum cfg 0 = 0 := by simp [wsum]
            have hA1 : Avec cfg f s.xStart 0 1 = 0 := by simp [Avec, wsum, pw_zero]
            have hc0 := coef_le hc 0 (by omega)
            simp only [pw_zero, sub_zero, zero_add] at hc0
            simp only [hk0, ↓reduceIte, h4', h5', pw_zero, zero_smul, add_zero, zero_add, hw0', hA1,
              smul_zero, mul_zero, Nat.cast_zero, one_mul, norm_smul, Real.norm_eq_abs,
              Real.sqrt_sq_eq_abs, abs_norm]
            exact mul_le_mul_of_nonneg_right hc0 (norm_nonneg _)
          · simp only [hk0, ↓reduceIte]
            rw [Zvec_succ_eq hc y x' ghat k hyx hx' hk.symm]
            have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            have hZ := hA.hZ hk1
            calc ‖Zvec cfg f (s, N) + ((1 - cfg.θ) * pw cfg.K (k + 1) - pw cfg.K k) • (x' - s.x) -
                  (cfg.η * pw cfg.K k) • (gradient f y - gradModel (fderiv ℝ (gradient f) s.xStart)
                    s.xStart (gradient f s.xStart) y)‖
                ≤ ‖Zvec cfg f (s, N)‖ + |(1 - cfg.θ) * pw cfg.K (k + 1) - pw cfg.K k| * ‖x' - s.x‖ +
                  (cfg.η * pw cfg.K k) * Dm cfg ρ := by
                  refine (norm_sub_le _ _).trans ?_
                  have h1 := norm_add_le (Zvec cfg f (s, N))
                    (((1 - cfg.θ) * pw cfg.K (k + 1) - pw cfg.K k) • (x' - s.x))
                  rw [norm_smul, Real.norm_eq_abs] at h1
                  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.hη.le hw0)]
                  have h2 := mul_le_mul_of_nonneg_left hδ (mul_nonneg hc.hη.le hw0)
                  linarith
              _ ≤ (cw cfg * Real.sqrt (k * s.S) + cfg.η * Dm cfg ρ * wsum cfg k) +
                  cw cfg * ‖x' - s.x‖ + cfg.η * pw cfg.K k * Dm cfg ρ := by
                  have := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (x' - s.x))
                  linarith
              _ = cw cfg * (Real.sqrt (k * s.S) + ‖x' - s.x‖) +
                  cfg.η * Dm cfg ρ * (wsum cfg k + pw cfg.K k) := by ring
              _ ≤ cw cfg * Real.sqrt ((k + 1) * (s.S + ‖x' - s.x‖ ^ 2)) +
                  cfg.η * Dm cfg ρ * (wsum cfg k + pw cfg.K k) := by
                  have := sqrt_step (k := (k : ℝ)) (Nat.cast_nonneg _) hA.hS0 (norm_nonneg (x' - s.x))
                  nlinarith [mul_le_mul_of_nonneg_left this hcw]
        · intro h0; rw [hp] at h0; omega
      · intro _ h' _; simp only [hp] at h'; omega
      · intro _ h'; simp only [hp] at h'; omega
      · intro _ _; exact hinv.hvc0 hd' hkK.le
  · by_cases hkE : cfg.pos s.t = cfg.K
    ·
      have hp : cfg.pos (s.t + 1) = cfg.pos s.t + 1 := pos_succ_of_lt cfg hEb (t := s.t) (by have := hc.hm; unfold Config.Eb; omega)
      have hnt : ¬ (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 := by
        intro h0; have := pos_zero_of_trial cfg (s.t + 1) h0; omega
      rw [blockStep_gd cfg x0 g hd' hkE, nextN_of_not cfg g f ω (by omega)]
      refine ⟨hinv.hi, hinv.hacc, hinv.hvc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ h0; simp only [hp] at h0; omega
      · intro _ h0; exact absurd h0 hnt
      · intro _ h'; simp only [hp] at h'; omega
      · intro _ h' _; simp only [hp] at h'; omega
      · intro _ _ htr
        show ‖s.ybar - s.xStart‖ ≤ 2 * cfg.B
        have hA := hinv.hagd hd' hkE.le htr
        have hyb := hA.hyb
        rw [hkE] at hyb
        have hsum : wsum cfg cfg.K = 1 := sum_pw (by have := hc.hK; omega)
        rw [hsum, one_smul, mul_one] at hyb
        exact hyb
      · intro _ _
        show s.vCount + cfg.K + 1 ≤ cfg.pos (s.t + 1)
        rw [hp, hinv.hvc0 hd' hkE.le]; omega
      · intro _ h'; simp only [hp] at h'; omega
    · have hkK' : cfg.K < cfg.pos s.t := by omega
      by_cases hlt : cfg.pos s.t + 1 < cfg.Eb
      · have hp : cfg.pos (s.t + 1) = cfg.pos s.t + 1 := pos_succ_of_lt cfg hEb hlt
        rw [blockStep_val cfg x0 g hd' hkK' hlt, nextN_of_not cfg g f ω (by omega)]
        have hvc' : (if s.trig = true then s.vCount
            else s.vCount + (if ‖bmean cfg g s.ybar ω‖ ≤ cfg.thr then 1 else 0)) ≤ s.vCount + 1 := by
          split_ifs <;> omega
        have hvc2 : s.vCount + cfg.K + 1 ≤ cfg.pos s.t := hinv.hvc2 hd' hkK'
        have hnt : ¬ (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 := by
          intro h0; have := pos_zero_of_trial cfg (s.t + 1) h0; omega
        refine ⟨hinv.hi, hinv.hacc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show (if s.trig = true then s.vCount
            else s.vCount + (if ‖bmean cfg g s.ybar ω‖ ≤ cfg.thr then 1 else 0)) ≤ cfg.m
          have : cfg.pos s.t + 1 < cfg.K + 1 + cfg.m := hlt
          omega
        · intro _ h0; simp only [hp] at h0; omega
        · intro _ h0; exact absurd h0 hnt
        · intro _ h'; simp only [hp] at h'; omega
        · intro _ h' _; simp only [hp] at h'; omega
        · intro _ _ htr; exact hinv.hval hd' hkK' htr
        · intro _ _
          show (if s.trig = true then s.vCount
            else s.vCount + (if ‖bmean cfg g s.ybar ω‖ ≤ cfg.thr then 1 else 0)) + cfg.K + 1 ≤
            cfg.pos (s.t + 1)
          rw [hp]; omega
        · intro _ h'; simp only [hp] at h'; omega
      · have heq : cfg.pos s.t + 1 = cfg.Eb := by omega
        have hp : cfg.pos (s.t + 1) = 0 := pos_succ_of_eq cfg hEb heq
        rw [blockStep_last cfg x0 g hd' hkK' heq, nextN_of_not cfg g f ω (by omega)]
        by_cases hacc : ¬ s.trig = true ∧ 2 * (if s.trig = true then s.vCount
            else s.vCount + (if ‖bmean cfg g s.ybar ω‖ ≤ cfg.thr then 1 else 0)) > cfg.m
        · rw [ite_eq_left hacc]
          refine ⟨hinv.hi, hinv.hacc, hinv.hvc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h' <;> simp at h'
        · rw [ite_eq_right hacc]
          simp only [restart]
          · refine ⟨hinv.hi, hinv.hacc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · show 0 ≤ cfg.m; omega
            · intro _ _; rfl
            · intro _ h0
              show (if (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else s.x) = x0
              rw [ite_eq_left h0]
            · intro _ _
              show ‖(if (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else s.x) + cfg.η • (0 : E) -
                (if (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else s.x)‖ ≤ 2 * cfg.B
              rw [smul_zero, add_zero, sub_self, norm_zero]
              linarith [hc.hB]
            · intro _ _ _
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · show ‖(if (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else s.x) -
                  (if (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else s.x)‖ ≤
                  Real.sqrt (cfg.pos (s.t + 1) * (0 : ℝ))
                rw [sub_self, norm_zero, mul_zero, Real.sqrt_zero]
              · show ‖(if (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else s.x) -
                  (if (s.t + 1) % (cfg.N1 * cfg.Eb) = 0 then x0 else s.x)‖ ^ 2 ≤ (0 : ℝ)
                rw [sub_self, norm_zero]; norm_num
              · show (cfg.pos (s.t + 1) : ℝ) * (0 : ℝ) ≤ cfg.B ^ 2
                rw [mul_zero]; positivity
              · exact le_rfl
              · show ‖(0 : E) - wsum cfg (cfg.pos (s.t + 1)) • (if (s.t + 1) % (cfg.N1 * cfg.Eb) = 0
                  then x0 else s.x)‖ ≤ 2 * cfg.B * wsum cfg (cfg.pos (s.t + 1))
                rw [hp]
                simp [wsum]
              · intro h1; rw [hp] at h1; omega
              · intro _; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
            · intro _ h'; rw [hp] at h'; omega
            · intro _ h'; rw [hp] at h'; omega
            · intro _ _; rfl

omit [FiniteDimensional ℝ E] in
variable (cfg f ρ) in
theorem inv_init (hc : CfgHyp cfg) (N : E) : Inv cfg x0 f ρ (initState x0, N) := by
  have hp : cfg.pos 0 = 0 := by simp [Config.pos]
  refine ⟨rfl, rfl, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _
    show ‖x0 + cfg.η • (0 : E) - x0‖ ≤ 2 * cfg.B
    rw [smul_zero, add_zero, sub_self, norm_zero]; linarith [hc.hB]
  · intro _ _ _
    refine ⟨?_, ?_, ?_, le_rfl, ?_, ?_, ?_⟩
    · show ‖x0 - x0‖ ≤ Real.sqrt (cfg.pos 0 * (0 : ℝ)); rw [sub_self, norm_zero, mul_zero, Real.sqrt_zero]
    · show ‖x0 - x0‖ ^ 2 ≤ (0 : ℝ); rw [sub_self, norm_zero]; norm_num
    · show (cfg.pos 0 : ℝ) * (0 : ℝ) ≤ cfg.B ^ 2; rw [mul_zero]; positivity
    · show ‖(0 : E) - wsum cfg (cfg.pos 0) • x0‖ ≤ 2 * cfg.B * wsum cfg (cfg.pos 0)
      rw [hp]; simp [wsum]
    · intro h1; have h1' : 1 ≤ cfg.pos 0 := h1; rw [hp] at h1'; omega
    · intro _; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro _ h'; have h'' : cfg.K < cfg.pos 0 := h'; rw [hp] at h''; omega
  · intro _ h'; have h'' : cfg.K < cfg.pos 0 := h'; rw [hp] at h''; omega
  · intro _ _; rfl

end LongTails.Proofs.StrongGrowthAgdInvariant
