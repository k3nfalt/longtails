import LongTails.Proofs.GatedEscapeSaddle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.GatedEscapeBudget

open LongTails.Algorithms.GatedPerturbedEscape LongTails.Proofs.GatedEscapeSaddle
  LongTails.Proofs.GatedEscapeEscape

noncomputable def Kc (d : ℕ) : ℝ := Real.log (20480 * d)
noncomputable def γc (ρ ε : ℝ) : ℝ := Real.sqrt (ρ * ε)
noncomputable def θc (ρ ε : ℝ) (d : ℕ) : ℝ := γc ρ ε / (240 * Kc d)
noncomputable def rc (ρ ε : ℝ) (d : ℕ) : ℝ := θc ρ ε d / ρ
noncomputable def Tc (L ρ ε : ℝ) (d : ℕ) : ℕ := ⌈4 * Kc d * L / γc ρ ε⌉₊ + 1
noncomputable def Wc (ρ Δ ε : ℝ) (d : ℕ) : ℝ :=
  2 ^ 27 * Kc d ^ 3 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε)
noncomputable def κc (L ρ ε : ℝ) : ℝ := L / γc ρ ε
noncomputable def Dc (ρ Δ ε : ℝ) : ℝ := Real.sqrt ρ * Δ / (ε * Real.sqrt ε)
noncomputable def lgc (L ρ Δ ε δ : ℝ) (d : ℕ) : ℝ :=
  Real.log (4096 * Kc d * κc L ρ ε * (1 + Dc ρ Δ ε) / δ)
noncomputable def Mc (L ρ Δ ε δ : ℝ) (d : ℕ) : ℕ := ⌈30 * lgc L ρ Δ ε δ d⌉₊
noncomputable def bc (L ρ σ ε : ℝ) (d : ℕ) : ℕ :=
  ⌈2 ^ 54 * Kc d ^ 4 * (1 + d * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε) + σ ^ 2 / ε ^ 2)⌉₊ + 1
noncomputable def Nc (L ρ Δ ε δ : ℝ) (d : ℕ) : ℕ :=
  ⌈2 ^ 40 * lgc L ρ Δ ε δ d ^ 2 * Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε)⌉₊

noncomputable def cfgOf (L ρ σ Δ ε δ : ℝ) (d : ℕ) : Config where
  η := 1 / L
  r := rc ρ ε d
  s0 := rc ρ ε d / 256
  gth := ε / 2
  θ := θc ρ ε d
  τg := ε / 24
  τ0 := rc ρ ε d * θc ρ ε d / 24
  τq := θc ρ ε d / 8
  M := Mc L ρ Δ ε δ d
  T := Tc L ρ ε d
  k := Mc L ρ Δ ε δ d
  b := bc L ρ σ ε d

section facts

variable {L ρ σ Δ ε δ : ℝ} {d : ℕ}

lemma Kc_ge (hd : 0 < d) : 1 ≤ Kc d := by
  unfold Kc
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.le_log_iff_exp_le (by positivity)]
  have : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  nlinarith

lemma exp_Kc (hd : 0 < d) : Real.exp (Kc d) = 20480 * d := by
  unfold Kc
  exact Real.exp_log (by have : (0 : ℝ) < d := (by exact_mod_cast hd); positivity)

end facts

section facts2

variable {L ρ σ Δ ε δ : ℝ} {d : ℕ}

structure Valid (L ρ σ Δ ε δ : ℝ) (d : ℕ) : Prop where
  hL : 0 < L
  hρ : 0 < ρ
  hσ : 0 ≤ σ
  hΔ : 0 ≤ Δ
  hε : 0 < ε
  hδ : 0 < δ
  hδ1 : δ < 1
  hρε : ρ * ε ≤ L ^ 2
  hd : 0 < d

variable (V : Valid L ρ σ Δ ε δ d)
include V

lemma γ_pos : 0 < γc ρ ε := Real.sqrt_pos.mpr (mul_pos V.hρ V.hε)

lemma γ_sq : γc ρ ε ^ 2 = ρ * ε := Real.sq_sqrt (mul_pos V.hρ V.hε).le

lemma γ_le : γc ρ ε ≤ L := by
  have h := γ_sq V
  have h0 := γ_pos V
  nlinarith [V.hρε, V.hL]

lemma γ_split : γc ρ ε = Real.sqrt ρ * Real.sqrt ε := Real.sqrt_mul V.hρ.le ε

lemma K_pos : 0 < Kc d := lt_of_lt_of_le one_pos (Kc_ge V.hd)

lemma θ_pos : 0 < θc ρ ε d := div_pos (γ_pos V) (by have := K_pos V; positivity)

lemma r_pos : 0 < rc ρ ε d := div_pos (θ_pos V) V.hρ

omit V in
lemma T_ge : 4 * Kc d * L / γc ρ ε + 1 ≤ (Tc L ρ ε d : ℝ) := by
  unfold Tc; push_cast; linarith [Nat.le_ceil (4 * Kc d * L / γc ρ ε)]

lemma T_le : (Tc L ρ ε d : ℝ) ≤ 4 * Kc d * L / γc ρ ε + 2 := by
  unfold Tc; push_cast
  have := Nat.ceil_lt_add_one (show 0 ≤ 4 * Kc d * L / γc ρ ε by
    have := K_pos V; have := γ_pos V; have := V.hL; positivity)
  linarith

lemma KLγ : 1 ≤ 4 * Kc d * L / γc ρ ε := by
  rw [le_div_iff₀ (γ_pos V)]
  have := Kc_ge V.hd; have := γ_le V; have := γ_pos V
  nlinarith

lemma T_le6 : (Tc L ρ ε d : ℝ) ≤ 6 * Kc d * L / γc ρ ε := by
  have h1 := T_le V
  have h2 := KLγ V
  have : 6 * Kc d * L / γc ρ ε = 4 * Kc d * L / γc ρ ε + 2 * (Kc d * L / γc ρ ε) := by ring
  rw [this]
  have : 1 ≤ Kc d * L / γc ρ ε := by
    rw [le_div_iff₀ (γ_pos V)]; have := Kc_ge V.hd; have := γ_le V; nlinarith [V.hL]
  linarith

lemma hθγ : 8 * θc ρ ε d ≤ γc ρ ε := by
  unfold θc
  rw [mul_div_assoc', div_le_iff₀ (by have := K_pos V; positivity)]
  have := Kc_ge V.hd; have := γ_pos V
  nlinarith

lemma hμ : 40 * θc ρ ε d * Tc L ρ ε d ≤ L := by
  have hT := T_le V
  have hK := Kc_ge V.hd
  have hγ := γ_pos V
  have hγL := γ_le V
  unfold θc
  have e : 40 * (γc ρ ε / (240 * Kc d)) * (4 * Kc d * L / γc ρ ε + 2) = 2 / 3 * L + γc ρ ε / (3 * Kc d) := by
    field_simp; ring
  have h2 : γc ρ ε / (3 * Kc d) ≤ L / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h3 : 40 * (γc ρ ε / (240 * Kc d)) * Tc L ρ ε d ≤ 40 * (γc ρ ε / (240 * Kc d)) * (4 * Kc d * L / γc ρ ε + 2) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  linarith

omit V in
lemma haT : (1 + 1 / (5 * (Tc L ρ ε d : ℝ))) ^ Tc L ρ ε d ≤ 5 / 4 := by
  have hT : (0 : ℝ) < Tc L ρ ε d := by unfold Tc; positivity
  have h1 := pow_le_exp (x := 1 / (5 * (Tc L ρ ε d : ℝ))) (by positivity) (Tc L ρ ε d)
  have e : (Tc L ρ ε d : ℝ) * (1 / (5 * (Tc L ρ ε d : ℝ))) = 1 / 5 := by field_simp
  rw [e] at h1
  refine h1.trans ?_
  have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 5) (by norm_num) (by norm_num)
  refine this.trans ?_
  norm_num

lemma hTL : L ≤ 60 * θc ρ ε d * (Tc L ρ ε d + 1) := by
  have hT := (T_ge (L := L) (ρ := ρ) (ε := ε) (d := d))
  have hK := Kc_ge V.hd
  have hγ := γ_pos V
  unfold θc
  have e : 60 * (γc ρ ε / (240 * Kc d)) * (4 * Kc d * L / γc ρ ε) = L := by field_simp; ring
  have h3 : 60 * (γc ρ ε / (240 * Kc d)) * (4 * Kc d * L / γc ρ ε) ≤
      60 * (γc ρ ε / (240 * Kc d)) * (Tc L ρ ε d + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

lemma hgrow : 20480 * Real.sqrt d ≤ (1 + (γc ρ ε - 4 * θc ρ ε d) / L) ^ Tc L ρ ε d := by
  have hK := Kc_ge V.hd
  have hγ := γ_pos V
  have hγL := γ_le V
  have hL := V.hL
  have hθ := θ_pos V
  have h8 := hθγ V
  set x := (γc ρ ε - 4 * θc ρ ε d) / L with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hL.le
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hL]; linarith
  have hexp : Real.exp (x / 2) ≤ 1 + x := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := x / 2) (by linarith) (by linarith)
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpow : Real.exp (Tc L ρ ε d * (x / 2)) ≤ (1 + x) ^ Tc L ρ ε d := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (Real.exp_pos _).le hexp _
  have hTx : Kc d ≤ Tc L ρ ε d * (x / 2) := by
    have hT := (T_ge (L := L) (ρ := ρ) (ε := ε) (d := d))
    have hθγ' : 4 * θc ρ ε d ≤ γc ρ ε / 2 := by linarith
    have hx2 : γc ρ ε / (2 * L) ≤ x := by
      rw [hx, div_le_div_iff₀ (by positivity) hL]; nlinarith
    have h4 : 4 * Kc d * L / γc ρ ε * (γc ρ ε / (2 * L) / 2) = Kc d := by field_simp; ring
    have h5 : 4 * Kc d * L / γc ρ ε * (γc ρ ε / (2 * L) / 2) ≤ Tc L ρ ε d * (x / 2) := by
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast V.hd
  have hsq : Real.sqrt d ≤ d := by
    have h := Real.sqrt_le_sqrt (show (d : ℝ) ≤ (d : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at h
  calc 20480 * Real.sqrt d ≤ 20480 * d := by linarith
    _ = Real.exp (Kc d) := (exp_Kc V.hd).symm
    _ ≤ Real.exp (Tc L ρ ε d * (x / 2)) := Real.exp_le_exp.mpr hTx
    _ ≤ (1 + x) ^ Tc L ρ ε d := hpow

end facts2

section facts3

variable {L ρ σ Δ ε δ : ℝ} {d : ℕ}
variable (V : Valid L ρ σ Δ ε δ d)
include V

lemma rho_over_γ3 : Real.sqrt ρ / (ε * Real.sqrt ε) = ρ ^ 2 / γc ρ ε ^ 3 := by
  have hρ := V.hρ
  have hε := V.hε
  rw [γ_split V]
  have h3 : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have h4 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have h1 : ρ = Real.sqrt ρ ^ 2 := (Real.sq_sqrt hρ.le).symm
  have h2 : ε = Real.sqrt ε ^ 2 := (Real.sq_sqrt hε.le).symm
  set a := Real.sqrt ρ
  set c := Real.sqrt ε
  rw [h1, h2]
  field_simp

lemma b_ge : 2 ^ 54 * Kc d ^ 2 * d * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε) +
    2 ^ 46 * Kc d ^ 4 * σ ^ 2 / ε ^ 2 ≤ (bc L ρ σ ε d : ℝ) := by
  have hK := Kc_ge V.hd
  have hL := V.hL
  have hε := V.hε
  have hX : 0 ≤ (d : ℝ) * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε) := by positivity
  have hY : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
  have hK2 : Kc d ^ 2 ≤ Kc d ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hK4 : 1 ≤ Kc d ^ 4 := one_le_pow₀ hK
  have e1 : 2 ^ 54 * Kc d ^ 2 * d * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε) =
      2 ^ 54 * Kc d ^ 2 * ((d : ℝ) * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε)) := by ring
  have e2 : 2 ^ 46 * Kc d ^ 4 * σ ^ 2 / ε ^ 2 = 2 ^ 46 * Kc d ^ 4 * (σ ^ 2 / ε ^ 2) := by ring
  have h1 : 2 ^ 54 * Kc d ^ 2 * ((d : ℝ) * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε)) ≤
      2 ^ 54 * Kc d ^ 4 * ((d : ℝ) * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε)) := by
    nlinarith [mul_le_mul_of_nonneg_right hK2 hX]
  have h2 : 2 ^ 46 * Kc d ^ 4 * (σ ^ 2 / ε ^ 2) ≤ 2 ^ 54 * Kc d ^ 4 * (σ ^ 2 / ε ^ 2) := by
    nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ Kc d) 4) hY]
  have h3 := Nat.le_ceil (2 ^ 54 * Kc d ^ 4 *
    (1 + d * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε) + σ ^ 2 / ε ^ 2))
  unfold bc; push_cast
  rw [e1, e2]
  nlinarith

lemma b_nonneg_terms : 0 ≤ 2 ^ 54 * Kc d ^ 2 * d * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε) ∧
    0 ≤ 2 ^ 46 * Kc d ^ 4 * σ ^ 2 / ε ^ 2 := by
  have := K_pos V; have := V.hL; have := V.hε
  constructor <;> positivity

lemma hbdev : 2 ^ 38 * d * σ ^ 2 ≤ bc L ρ σ ε d * L * γc ρ ε * rc ρ ε d ^ 2 := by
  have hb := b_ge V
  have ⟨h1, h2⟩ := b_nonneg_terms V
  have hγ := γ_pos V
  have hK := K_pos V
  have hL := V.hL
  have hρ := V.hρ
  have hb1 : 2 ^ 54 * Kc d ^ 2 * d * σ ^ 2 * (ρ ^ 2 / γc ρ ε ^ 3) / L ≤ bc L ρ σ ε d := by
    have e : 2 ^ 54 * Kc d ^ 2 * d * σ ^ 2 * Real.sqrt ρ / (L * ε * Real.sqrt ε) =
        2 ^ 54 * Kc d ^ 2 * d * σ ^ 2 * (ρ ^ 2 / γc ρ ε ^ 3) / L := by
      rw [← rho_over_γ3 V]; field_simp
    linarith
  have hr2 : L * γc ρ ε * rc ρ ε d ^ 2 = L * γc ρ ε ^ 3 / (57600 * Kc d ^ 2 * ρ ^ 2) := by
    unfold rc θc; field_simp; ring
  have hpos : 0 < L * γc ρ ε * rc ρ ε d ^ 2 := by have := r_pos V; positivity
  have key : 2 ^ 54 * Kc d ^ 2 * d * σ ^ 2 * (ρ ^ 2 / γc ρ ε ^ 3) / L * (L * γc ρ ε * rc ρ ε d ^ 2) =
      2 ^ 54 / 57600 * (d * σ ^ 2) := by
    rw [hr2]; field_simp
  have := mul_le_mul_of_nonneg_right hb1 hpos.le
  rw [key] at this
  have hds : 0 ≤ (d : ℝ) * σ ^ 2 := by positivity
  nlinarith

lemma hbL1 : 2 ^ 21 * (Tc L ρ ε d : ℝ) ^ 2 * σ ^ 2 ≤ bc L ρ σ ε d * L ^ 2 * rc ρ ε d ^ 2 := by
  have hb := b_ge V
  have ⟨h1, h2⟩ := b_nonneg_terms V
  have hγ := γ_pos V
  have hK := K_pos V
  have hL := V.hL
  have hρ := V.hρ
  have hε := V.hε
  have hT6 := T_le6 V
  have hT0 : (0 : ℝ) ≤ Tc L ρ ε d := Nat.cast_nonneg _
  have hT2 : (Tc L ρ ε d : ℝ) ^ 2 ≤ 36 * Kc d ^ 2 * L ^ 2 / (ρ * ε) := by
    have h := pow_le_pow_left₀ hT0 hT6 2
    have e : (6 * Kc d * L / γc ρ ε) ^ 2 = 36 * Kc d ^ 2 * L ^ 2 / (ρ * ε) := by
      rw [div_pow, γ_sq V]; ring
    rw [e] at h; exact h
  have hr2 : L ^ 2 * rc ρ ε d ^ 2 = L ^ 2 * (ρ * ε) / (57600 * Kc d ^ 2 * ρ ^ 2) := by
    unfold rc θc; rw [div_pow, div_pow, mul_pow, γ_sq V]; field_simp; ring
  have hb2 : 2 ^ 46 * Kc d ^ 4 * σ ^ 2 / ε ^ 2 ≤ bc L ρ σ ε d := by linarith
  have hpos : 0 < L ^ 2 * rc ρ ε d ^ 2 := by have := r_pos V; positivity
  have key : 2 ^ 46 * Kc d ^ 4 * σ ^ 2 / ε ^ 2 * (L ^ 2 * rc ρ ε d ^ 2) =
      2 ^ 46 / 57600 * Kc d ^ 2 * σ ^ 2 * L ^ 2 / (ρ * ε) := by
    rw [hr2]; field_simp
  have hm := mul_le_mul_of_nonneg_right hb2 hpos.le
  rw [key] at hm
  have hl : 2 ^ 21 * (Tc L ρ ε d : ℝ) ^ 2 * σ ^ 2 ≤ 2 ^ 21 * (36 * Kc d ^ 2 * L ^ 2 / (ρ * ε)) * σ ^ 2 := by
    gcongr
  have he : 2 ^ 21 * (36 * Kc d ^ 2 * L ^ 2 / (ρ * ε)) * σ ^ 2 ≤
      2 ^ 46 / 57600 * Kc d ^ 2 * σ ^ 2 * L ^ 2 / (ρ * ε) := by
    have hρε : 0 < ρ * ε := mul_pos hρ hε
    have e1 : 2 ^ 21 * (36 * Kc d ^ 2 * L ^ 2 / (ρ * ε)) * σ ^ 2 =
        (2 ^ 21 * 36) * (Kc d ^ 2 * σ ^ 2 * L ^ 2) / (ρ * ε) := by ring
    have e2 : 2 ^ 46 / 57600 * Kc d ^ 2 * σ ^ 2 * L ^ 2 / (ρ * ε) =
        (2 ^ 46 / 57600) * (Kc d ^ 2 * σ ^ 2 * L ^ 2) / (ρ * ε) := by ring
    rw [e1, e2]
    have : 0 ≤ Kc d ^ 2 * σ ^ 2 * L ^ 2 := by positivity
    exact div_le_div_of_nonneg_right (by nlinarith) hρε.le
  calc 2 ^ 21 * (Tc L ρ ε d : ℝ) ^ 2 * σ ^ 2 ≤ 2 ^ 46 / 57600 * Kc d ^ 2 * σ ^ 2 * L ^ 2 / (ρ * ε) :=
        hl.trans he
    _ ≤ bc L ρ σ ε d * (L ^ 2 * rc ρ ε d ^ 2) := hm
    _ = bc L ρ σ ε d * L ^ 2 * rc ρ ε d ^ 2 := by ring

lemma hben : 32 * (1 + Real.log (Tc L ρ ε d)) * σ ^ 2 ≤
    L * bc L ρ σ ε d * θc ρ ε d * rc ρ ε d ^ 2 := by
  have hb := b_ge V
  have ⟨h1, h2⟩ := b_nonneg_terms V
  have hγ := γ_pos V
  have hK := K_pos V
  have hL := V.hL
  have hρ := V.hρ
  have hε := V.hε
  have hT6 := T_le6 V
  have hTpos : (0 : ℝ) < Tc L ρ ε d := by unfold Tc; positivity
  have hlog : 1 + Real.log (Tc L ρ ε d) ≤ Tc L ρ ε d := by
    have := Real.log_le_sub_one_of_pos hTpos; linarith
  have hb2 : 2 ^ 46 * Kc d ^ 4 * σ ^ 2 / ε ^ 2 ≤ bc L ρ σ ε d := by linarith
  have hθr : θc ρ ε d * rc ρ ε d ^ 2 = γc ρ ε ^ 3 / (240 ^ 3 * Kc d ^ 3 * ρ ^ 2) := by
    unfold rc θc; field_simp
  have hpos : 0 < L * θc ρ ε d * rc ρ ε d ^ 2 := by have := r_pos V; have := θ_pos V; positivity
  have hm := mul_le_mul_of_nonneg_right hb2 hpos.le
  have key : 2 ^ 46 * Kc d ^ 4 * σ ^ 2 / ε ^ 2 * (L * θc ρ ε d * rc ρ ε d ^ 2) =
      2 ^ 46 / 240 ^ 3 * Kc d * σ ^ 2 * L * γc ρ ε ^ 3 / (ε ^ 2 * ρ ^ 2) := by
    rw [mul_assoc L, hθr]; field_simp
  rw [key] at hm
  have hγ4 : γc ρ ε ^ 4 = ρ ^ 2 * ε ^ 2 := by rw [show γc ρ ε ^ 4 = (γc ρ ε ^ 2) ^ 2 by ring, γ_sq V]; ring
  have hl : 32 * (1 + Real.log (Tc L ρ ε d)) * σ ^ 2 ≤ 32 * (6 * Kc d * L / γc ρ ε) * σ ^ 2 := by
    have := hlog.trans hT6
    gcongr
  have he : 32 * (6 * Kc d * L / γc ρ ε) * σ ^ 2 ≤
      2 ^ 46 / 240 ^ 3 * Kc d * σ ^ 2 * L * γc ρ ε ^ 3 / (ε ^ 2 * ρ ^ 2) := by
    have hX : 0 ≤ Kc d * L * σ ^ 2 := by positivity
    have e1 : 32 * (6 * Kc d * L / γc ρ ε) * σ ^ 2 = (32 * 6) * (Kc d * L * σ ^ 2) / γc ρ ε := by ring
    have e2 : 2 ^ 46 / 240 ^ 3 * Kc d * σ ^ 2 * L * γc ρ ε ^ 3 / (ε ^ 2 * ρ ^ 2) =
        (2 ^ 46 / 240 ^ 3) * (Kc d * L * σ ^ 2) / γc ρ ε := by
      rw [show ε ^ 2 * ρ ^ 2 = γc ρ ε ^ 4 by rw [hγ4]; ring]
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by nlinarith) hγ.le
  calc 32 * (1 + Real.log (Tc L ρ ε d)) * σ ^ 2 ≤ _ := hl.trans he
    _ ≤ bc L ρ σ ε d * (L * θc ρ ε d * rc ρ ε d ^ 2) := hm
    _ = L * bc L ρ σ ε d * θc ρ ε d * rc ρ ε d ^ 2 := by ring

end facts3

section facts4

variable {L ρ σ Δ ε δ : ℝ} {d : ℕ}
variable (V : Valid L ρ σ Δ ε δ d)
include V

lemma τ0_eq : rc ρ ε d * θc ρ ε d / 24 = ε / (1382400 * Kc d ^ 2) := by
  have hK := K_pos V
  have hρ := V.hρ
  have e1 : rc ρ ε d * θc ρ ε d / 24 = γc ρ ε ^ 2 / (1382400 * Kc d ^ 2 * ρ) := by
    unfold rc θc; field_simp; ring
  rw [e1, γ_sq V]
  field_simp

lemma hvar0 : σ ^ 2 / bc L ρ σ ε d / (rc ρ ε d * θc ρ ε d / 24) ^ 2 ≤ 1 / 16 := by
  have hb := b_ge V
  have ⟨h1, h2⟩ := b_nonneg_terms V
  have hK := K_pos V
  have hε := V.hε
  have hbpos : (0 : ℝ) < bc L ρ σ ε d := Nat.cast_pos.mpr (by unfold bc; omega)
  rw [τ0_eq V]
  set τ := ε / (1382400 * Kc d ^ 2) with hτdef
  have hτ : 0 < τ := by rw [hτdef]; positivity
  rw [div_div, div_le_div_iff₀ (mul_pos hbpos (pow_pos hτ 2)) (by norm_num)]
  have hb2 : 2 ^ 46 * Kc d ^ 4 * σ ^ 2 / ε ^ 2 ≤ bc L ρ σ ε d := by linarith
  have hm := mul_le_mul_of_nonneg_right hb2 (sq_nonneg τ)
  have k : 2 ^ 46 * Kc d ^ 4 * σ ^ 2 / ε ^ 2 * τ ^ 2 = (2 ^ 46 / 1382400 ^ 2) * σ ^ 2 := by
    rw [hτdef]; field_simp
  rw [k] at hm
  have hc : (16 : ℝ) ≤ 2 ^ 46 / 1382400 ^ 2 := by norm_num
  nlinarith [sq_nonneg σ]

omit V in
lemma var_mono {τ τ' : ℝ} (hτ : 0 < τ) (hle : τ ≤ τ') (h : σ ^ 2 / bc L ρ σ ε d / τ ^ 2 ≤ 1 / 16) :
    σ ^ 2 / bc L ρ σ ε d / τ' ^ 2 ≤ 1 / 16 := by
  refine le_trans ?_ h
  have hbpos : (0 : ℝ) < bc L ρ σ ε d := Nat.cast_pos.mpr (by unfold bc; omega)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hτ.le hle 2)

lemma τ0_pos : 0 < rc ρ ε d * θc ρ ε d / 24 := by have := r_pos V; have := θ_pos V; positivity

lemma τ0_le_g : rc ρ ε d * θc ρ ε d / 24 ≤ ε / 24 := by
  rw [τ0_eq V]
  have hK := Kc_ge V.hd
  have hε := V.hε
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hK 2]

lemma τ0_le_q : rc ρ ε d * θc ρ ε d / 24 ≤ rc ρ ε d * (θc ρ ε d / 8) := by
  have := r_pos V; have := θ_pos V; nlinarith

lemma κ_ge : 1 ≤ κc L ρ ε := by
  unfold κc; rw [le_div_iff₀ (γ_pos V), one_mul]; exact γ_le V

lemma D_nonneg : 0 ≤ Dc ρ Δ ε := by
  have := V.hΔ; have := V.hε; unfold Dc; positivity

lemma Z_ge : 1 ≤ Kc d * κc L ρ ε * (1 + Dc ρ Δ ε) := by
  have hK := Kc_ge V.hd; have hκ := κ_ge V; have hD := D_nonneg V
  have h1 : 1 ≤ Kc d * κc L ρ ε := one_le_mul_of_one_le_of_one_le hK hκ
  exact one_le_mul_of_one_le_of_one_le h1 (by linarith)

lemma arg_pos : 0 < 4096 * Kc d * κc L ρ ε * (1 + Dc ρ Δ ε) / δ := by
  have hZ := Z_ge V; have hδ := V.hδ
  have e : 4096 * Kc d * κc L ρ ε * (1 + Dc ρ Δ ε) = 4096 * (Kc d * κc L ρ ε * (1 + Dc ρ Δ ε)) := by ring
  rw [e]
  exact div_pos (by linarith) hδ

lemma exp_lg : Real.exp (lgc L ρ Δ ε δ d) = 4096 * (Kc d * κc L ρ ε * (1 + Dc ρ Δ ε)) / δ := by
  unfold lgc
  rw [Real.exp_log (arg_pos V)]
  ring

lemma lg_ge : 1 ≤ lgc L ρ Δ ε δ d := by
  have hZ := Z_ge V; have hδ := V.hδ; have hδ1 := V.hδ1
  unfold lgc
  rw [Real.le_log_iff_exp_le (arg_pos V)]
  have : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h4 : (4096 : ℝ) ≤ 4096 * Kc d * κc L ρ ε * (1 + Dc ρ Δ ε) := by
    have e : 4096 * Kc d * κc L ρ ε * (1 + Dc ρ Δ ε) = 4096 * (Kc d * κc L ρ ε * (1 + Dc ρ Δ ε)) := by ring
    rw [e]; nlinarith
  have h5 : 4096 * Kc d * κc L ρ ε * (1 + Dc ρ Δ ε) ≤ 4096 * Kc d * κc L ρ ε * (1 + Dc ρ Δ ε) / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith [mul_le_mul_of_nonneg_left hδ1.le (by linarith : (0 : ℝ) ≤ 4096 * Kc d * κc L ρ ε * (1 + Dc ρ Δ ε))]
  linarith

lemma M_ge6 : 6 ≤ Mc L ρ Δ ε δ d := by
  have h := lg_ge V
  have : (6 : ℝ) ≤ Mc L ρ Δ ε δ d := by
    unfold Mc; have := Nat.le_ceil (30 * lgc L ρ Δ ε δ d); linarith
  exact_mod_cast this

lemma hM6 : (19 / 32 : ℝ) ^ Mc L ρ Δ ε δ d ≤ 1 / 20 := by
  calc (19 / 32 : ℝ) ^ Mc L ρ Δ ε δ d ≤ (19 / 32) ^ 6 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (M_ge6 V)
    _ ≤ 1 / 20 := by norm_num

lemma T_κ : (Tc L ρ ε d : ℝ) ≤ 6 * Kc d * κc L ρ ε := by
  have h := T_le6 V
  unfold κc; rw [mul_div_assoc'] ; exact h

lemma LΔ_eq : 16 * L * Δ / ε ^ 2 = 16 * κc L ρ ε * Dc ρ Δ ε := by
  have hρ := V.hρ; have hε := V.hε
  have h3 : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have h4 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have h2 : ε = Real.sqrt ε ^ 2 := (Real.sq_sqrt hε.le).symm
  unfold κc Dc
  rw [γ_split V]
  set c := Real.sqrt ε
  rw [h2]
  field_simp

omit V in
lemma W_eq : Wc ρ Δ ε d = 2 ^ 27 * Kc d ^ 3 * Dc ρ Δ ε := by
  unfold Wc Dc; ring

lemma W_ge : 5 * Δ / (rc ρ ε d ^ 2 * θc ρ ε d) ≤ Wc ρ Δ ε d := by
  have hK := K_pos V
  have hρ := V.hρ
  have hε := V.hε
  have hγ := γ_pos V
  have hΔ := V.hΔ
  have hr2θ : rc ρ ε d ^ 2 * θc ρ ε d = γc ρ ε ^ 3 / (240 ^ 3 * Kc d ^ 3 * ρ ^ 2) := by
    unfold rc θc; field_simp
  unfold Wc
  rw [hr2θ]
  conv_rhs => rw [mul_div_assoc, rho_over_γ3 V]
  have e : 5 * Δ / (γc ρ ε ^ 3 / (240 ^ 3 * Kc d ^ 3 * ρ ^ 2)) = 5 * 240 ^ 3 * Kc d ^ 3 * Δ * (ρ ^ 2 / γc ρ ε ^ 3) := by
    field_simp
  rw [e]
  have : 0 ≤ Kc d ^ 3 * Δ * (ρ ^ 2 / γc ρ ε ^ 3) := by positivity
  nlinarith

end facts4

section facts5

lemma exp13 : (2 / 3 : ℝ) ≤ Real.exp (-(1 / 3)) := by
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 3) (by norm_num) (by norm_num)
  refine this.trans ?_
  norm_num

lemma tail_bound (M : ℕ) (hM : 1 ≤ M) :
    ((1 / 4 : ℝ) ^ M + M * (2 * (19 / 32) ^ M)) * M ≤ 216 * Real.exp (-(M / 6 : ℝ)) := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : (1 / 4 : ℝ) ^ M ≤ (19 / 32) ^ M := pow_le_pow_left₀ (by norm_num) (by norm_num) M
  have h2 : (19 / 32 : ℝ) ^ M ≤ (2 / 3) ^ M := pow_le_pow_left₀ (by norm_num) (by norm_num) M
  have h3 : (2 / 3 : ℝ) ^ M ≤ Real.exp (-(M / 3 : ℝ)) := by
    calc (2 / 3 : ℝ) ^ M ≤ Real.exp (-(1 / 3)) ^ M := pow_le_pow_left₀ (by norm_num) exp13 M
      _ = Real.exp (-(M / 3 : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
  have h4 : (M : ℝ) ^ 2 ≤ 72 * Real.exp (M / 6 : ℝ) := by
    have := Real.quadratic_le_exp_of_nonneg (x := (M / 6 : ℝ)) (by positivity)
    nlinarith
  have h5 : Real.exp (M / 6 : ℝ) * Real.exp (-(M / 3 : ℝ)) = Real.exp (-(M / 6 : ℝ)) := by
    rw [← Real.exp_add]; ring_nf
  have hq : (0 : ℝ) ≤ (19 / 32) ^ M := by positivity
  have hp : ((1 / 4 : ℝ) ^ M + M * (2 * (19 / 32) ^ M)) * M ≤ 3 * (M : ℝ) ^ 2 * (19 / 32) ^ M := by
    nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ M),
      mul_nonneg hq (by nlinarith : (0 : ℝ) ≤ (M : ℝ) ^ 2 - M)]
  calc _ ≤ 3 * (M : ℝ) ^ 2 * (19 / 32) ^ M := hp
    _ ≤ 3 * (72 * Real.exp (M / 6 : ℝ)) * Real.exp (-(M / 3 : ℝ)) := by
        apply mul_le_mul (by linarith) (h2.trans h3) hq (by positivity)
    _ = 216 * Real.exp (-(M / 6 : ℝ)) := by
        rw [show 3 * (72 * Real.exp (M / 6 : ℝ)) * Real.exp (-(M / 3 : ℝ)) =
          216 * (Real.exp (M / 6 : ℝ) * Real.exp (-(M / 3 : ℝ))) by ring, h5]

end facts5

section facts6

variable {L ρ σ Δ ε δ : ℝ} {d : ℕ}
variable (V : Valid L ρ σ Δ ε δ d)
include V

lemma hδ_bound :
    ((1 / 4 : ℝ) ^ Mc L ρ Δ ε δ d + (Mc L ρ Δ ε δ d : ℝ) * (2 * (19 / 32) ^ Mc L ρ Δ ε δ d)) *
      (1 + (Nc L ρ Δ ε δ d : ℝ) / Mc L ρ Δ ε δ d +
        ((Mc L ρ Δ ε δ d : ℝ) * (Mc L ρ Δ ε δ d + 1 + Tc L ρ ε d + Mc L ρ Δ ε δ d : ℕ)) / Mc L ρ Δ ε δ d) ≤ δ := by
  set M := Mc L ρ Δ ε δ d with hMd
  set T := Tc L ρ ε d
  set ℓ := lgc L ρ Δ ε δ d with hℓd
  set Z := Kc d * κc L ρ ε * (1 + Dc ρ Δ ε) with hZd
  have hK := Kc_ge V.hd
  have hκ := κ_ge V
  have hD := D_nonneg V
  have hZ1 : 1 ≤ Z := Z_ge V
  have hℓ1 : 1 ≤ ℓ := lg_ge V
  have hδ0 := V.hδ
  have hδ1 := V.hδ1
  have hM30 : 30 * ℓ ≤ M := by rw [hMd]; unfold Mc; exact Nat.le_ceil _
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1 : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hMr1 : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hT := T_κ V
  have hG0 : 0 ≤ Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε) := by
    have := mul_nonneg (mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ Kc d) 4)
      (by linarith : (0 : ℝ) ≤ κc L ρ ε)) (by linarith : (0 : ℝ) ≤ 1 + Dc ρ Δ ε)
    exact this
  have hN : (Nc L ρ Δ ε δ d : ℝ) ≤ 2 ^ 40 * ℓ ^ 2 * (Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε)) + 1 := by
    have e : 2 ^ 40 * ℓ ^ 2 * Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε) =
        2 ^ 40 * ℓ ^ 2 * (Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε)) := by ring
    unfold Nc; rw [← hℓd, e]
    exact (Nat.ceil_lt_add_one (mul_nonneg (by positivity) hG0)).le
  have hKZ : Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε) ≤ Z ^ 4 := by
    have hu : 1 ≤ κc L ρ ε * (1 + Dc ρ Δ ε) := one_le_mul_of_one_le_of_one_le hκ (by linarith)
    calc Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε) = Kc d ^ 4 * (κc L ρ ε * (1 + Dc ρ Δ ε)) := by ring
      _ ≤ Kc d ^ 4 * (κc L ρ ε * (1 + Dc ρ Δ ε)) ^ 4 :=
          mul_le_mul_of_nonneg_left (le_self_pow₀ hu (by norm_num)) (by positivity)
      _ = Z ^ 4 := by rw [hZd]; ring
  have hℓM : ℓ ^ 2 ≤ (M : ℝ) ^ 2 / 900 := by
    have h0 : 0 ≤ 30 * ℓ := by linarith
    have := pow_le_pow_left₀ h0 hM30 2
    nlinarith
  have hZ4 : 0 ≤ Z ^ 4 := by positivity
  have hNM : (Nc L ρ Δ ε δ d : ℝ) / M ≤ 2 ^ 31 * M * Z ^ 4 + 1 := by
    rw [div_le_iff₀ hMpos]
    have h1 : 2 ^ 40 * ℓ ^ 2 * (Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε)) ≤ 2 ^ 40 * ((M : ℝ) ^ 2 / 900) * Z ^ 4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hℓM (by norm_num)) hKZ hG0 (by positivity)
    nlinarith [mul_nonneg (sq_nonneg (M : ℝ)) hZ4]
  have hA : ((M : ℝ) * (M + 1 + T + M : ℕ)) / M = 2 * M + T + 1 := by
    push_cast; field_simp; ring
  have hKκ : Kc d * κc L ρ ε ≤ Z := by
    rw [hZd]; nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Kc d) (by linarith : (0 : ℝ) ≤ κc L ρ ε)) hD]
  have hZZ4 : Z ≤ Z ^ 4 := le_self_pow₀ hZ1 (by norm_num)
  have hMZ : (M : ℝ) ≤ M * Z ^ 4 := by nlinarith [one_le_pow₀ hZ1 (n := 4)]
  have hZM : Z ^ 4 ≤ M * Z ^ 4 := by nlinarith
  have hS : 1 + (Nc L ρ Δ ε δ d : ℝ) / M + ((M : ℝ) * (M + 1 + T + M : ℕ)) / M ≤ M * (2 ^ 32 * Z ^ 4) := by
    rw [hA]
    have hT' : (T : ℝ) ≤ 6 * Z := by
      have : 6 * Kc d * κc L ρ ε = 6 * (Kc d * κc L ρ ε) := by ring
      linarith
    nlinarith [one_le_pow₀ hZ1 (n := 4)]
  have htail := tail_bound M hM1
  have hp0 : 0 ≤ (1 / 4 : ℝ) ^ M + (M : ℝ) * (2 * (19 / 32) ^ M) := by positivity
  have hX : Real.exp ℓ = 4096 * Z / δ := exp_lg V
  have hE : Real.exp (-(M / 6 : ℝ)) ≤ (δ / (4096 * Z)) ^ 5 := by
    have e : (δ / (4096 * Z)) ^ 5 = Real.exp (-((5 : ℕ) * ℓ)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, hX, ← inv_pow, inv_div]
    rw [e]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have hδ5 : δ ^ 5 ≤ δ := by
    have := pow_le_pow_of_le_one hδ0.le hδ1.le (show 1 ≤ 5 by norm_num); simpa using this
  have hZ45 : Z ^ 4 ≤ Z ^ 5 := pow_le_pow_right₀ hZ1 (by norm_num)
  calc ((1 / 4 : ℝ) ^ M + (M : ℝ) * (2 * (19 / 32) ^ M)) *
        (1 + (Nc L ρ Δ ε δ d : ℝ) / M + ((M : ℝ) * (M + 1 + T + M : ℕ)) / M)
      ≤ ((1 / 4 : ℝ) ^ M + (M : ℝ) * (2 * (19 / 32) ^ M)) * (M * (2 ^ 32 * Z ^ 4)) :=
        mul_le_mul_of_nonneg_left hS hp0
    _ = (((1 / 4 : ℝ) ^ M + (M : ℝ) * (2 * (19 / 32) ^ M)) * M) * (2 ^ 32 * Z ^ 4) := by ring
    _ ≤ (216 * Real.exp (-(M / 6 : ℝ))) * (2 ^ 32 * Z ^ 4) :=
        mul_le_mul_of_nonneg_right htail (by positivity)
    _ ≤ (216 * (δ / (4096 * Z)) ^ 5) * (2 ^ 32 * Z ^ 4) := by gcongr
    _ = (216 * 2 ^ 32) * δ ^ 5 * Z ^ 4 / (4096 ^ 5 * Z ^ 5) := by
        have hz : Z ≠ 0 := (lt_of_lt_of_le one_pos hZ1).ne'
        field_simp
    _ ≤ δ := by
        have hz : 0 < Z := by linarith
        rw [div_le_iff₀ (by positivity)]
        have h1 : (216 * 2 ^ 32 : ℝ) * δ ^ 5 * Z ^ 4 ≤ (216 * 2 ^ 32) * δ * Z ^ 5 := by gcongr
        have h2 : 0 ≤ δ * Z ^ 5 := by positivity
        nlinarith

set_option maxHeartbeats 800000 in
lemma hN_facts :
    let M := Mc L ρ Δ ε δ d
    let A := M + 1 + Tc L ρ ε d + M
    let ϱ := 1 / (16 * L * M / ε ^ 2 + 5 * ((M + M * A : ℕ) : ℝ) / (rc ρ ε d ^ 2 * θc ρ ε d))
    0 < ϱ ∧ (M : ℝ) ≤ ε ^ 2 / (16 * L) / ϱ ∧ ((M + M * A : ℕ) : ℝ) ≤ rc ρ ε d ^ 2 * θc ρ ε d / 5 / ϱ ∧
      Δ / ϱ + ((M + M * A : ℕ) : ℝ) < Nc L ρ Δ ε δ d := by
  intro M A ϱ
  have hM6 := M_ge6 V
  have hMr : (6 : ℝ) ≤ M := by exact_mod_cast hM6
  have hL := V.hL
  have hε := V.hε
  have hΔ := V.hΔ
  have hr := r_pos V
  have hθ := θ_pos V
  have hden : 0 < 16 * L * M / ε ^ 2 + 5 * ((M + M * A : ℕ) : ℝ) / (rc ρ ε d ^ 2 * θc ρ ε d) := by
    have : 0 < 16 * L * M / ε ^ 2 := by positivity
    have : 0 ≤ 5 * ((M + M * A : ℕ) : ℝ) / (rc ρ ε d ^ 2 * θc ρ ε d) := by positivity
    linarith
  have hϱ : 0 < ϱ := by positivity
  have hinv : 1 / ϱ = 16 * L * M / ε ^ 2 + 5 * ((M + M * A : ℕ) : ℝ) / (rc ρ ε d ^ 2 * θc ρ ε d) := by
    simp only [ϱ, one_div, inv_inv]
  refine ⟨hϱ, ?_, ?_, ?_⟩
  · rw [show ε ^ 2 / (16 * L) / ϱ = ε ^ 2 / (16 * L) * (1 / ϱ) by ring, hinv]
    have h1 : 0 ≤ ε ^ 2 / (16 * L) * (5 * ((M + M * A : ℕ) : ℝ) / (rc ρ ε d ^ 2 * θc ρ ε d)) := by positivity
    have h2 : ε ^ 2 / (16 * L) * (16 * L * M / ε ^ 2) = M := by field_simp
    nlinarith
  · rw [show rc ρ ε d ^ 2 * θc ρ ε d / 5 / ϱ = rc ρ ε d ^ 2 * θc ρ ε d / 5 * (1 / ϱ) by ring, hinv]
    have h1 : 0 ≤ rc ρ ε d ^ 2 * θc ρ ε d / 5 * (16 * L * M / ε ^ 2) := by positivity
    have h2 : rc ρ ε d ^ 2 * θc ρ ε d / 5 * (5 * ((M + M * A : ℕ) : ℝ) / (rc ρ ε d ^ 2 * θc ρ ε d)) =
        ((M + M * A : ℕ) : ℝ) := by field_simp
    nlinarith
  · rw [show Δ / ϱ = Δ * (1 / ϱ) by ring, hinv]
    have hW := W_ge V
    have hcast : ((M + M * A : ℕ) : ℝ) = M * (2 * M + Tc L ρ ε d + 2) := by
      simp only [A]; push_cast; ring
    rw [hcast] at *
    have e1 : Δ * (16 * L * M / ε ^ 2 + 5 * (M * (2 * M + Tc L ρ ε d + 2)) / (rc ρ ε d ^ 2 * θc ρ ε d)) =
        M * (16 * L * Δ / ε ^ 2 + (2 * M + Tc L ρ ε d + 2) * (5 * Δ / (rc ρ ε d ^ 2 * θc ρ ε d))) := by
      field_simp
    rw [e1]
    set ℓ := lgc L ρ Δ ε δ d with hℓd
    have hK := Kc_ge V.hd
    have hκ := κ_ge V
    have hD := D_nonneg V
    have hℓ1 : 1 ≤ ℓ := lg_ge V
    have hM1' : (M : ℝ) ≤ 30 * ℓ + 1 := by
      show ((Mc L ρ Δ ε δ d : ℕ) : ℝ) ≤ _
      unfold Mc; rw [← hℓd]; exact (Nat.ceil_lt_add_one (by linarith)).le
    have hT0 : (0 : ℝ) ≤ Tc L ρ ε d := Nat.cast_nonneg _
    have hTκ := T_κ V
    have hKκ : 1 ≤ Kc d * κc L ρ ε := one_le_mul_of_one_le_of_one_le hK hκ
    have hA1 : 2 * (M : ℝ) + Tc L ρ ε d + 2 ≤ 70 * (ℓ * (Kc d * κc L ρ ε)) := by
      have : 6 * Kc d * κc L ρ ε = 6 * (Kc d * κc L ρ ε) := by ring
      have hℓKκ : 1 ≤ ℓ * (Kc d * κc L ρ ε) := one_le_mul_of_one_le_of_one_le hℓ1 hKκ
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ) (by linarith : (0 : ℝ) ≤ Kc d * κc L ρ ε - 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ - 1) (by linarith : (0 : ℝ) ≤ Kc d * κc L ρ ε)]
    have hK3 : 1 ≤ Kc d ^ 3 := one_le_pow₀ hK
    have hW1 : Wc ρ Δ ε d + 1 ≤ 2 ^ 27 * Kc d ^ 3 * (1 + Dc ρ Δ ε) := by
      rw [W_eq]; linarith
    have hWc' : 0 ≤ Wc ρ Δ ε d + 1 := by
      have : 0 ≤ Wc ρ Δ ε d := by
        rw [W_eq]; exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) 3)) hD
      linarith
    have hi1 : (2 * (M : ℝ) + Tc L ρ ε d + 2) * (5 * Δ / (rc ρ ε d ^ 2 * θc ρ ε d)) +
        (2 * M + Tc L ρ ε d + 2) ≤ (2 * (M : ℝ) + Tc L ρ ε d + 2) * (Wc ρ Δ ε d + 1) := by
      have := mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ 2 * M + Tc L ρ ε d + 2)
      linarith
    have hi2 : (2 * (M : ℝ) + Tc L ρ ε d + 2) * (Wc ρ Δ ε d + 1) ≤
        70 * (ℓ * (Kc d * κc L ρ ε)) * (2 ^ 27 * Kc d ^ 3 * (1 + Dc ρ Δ ε)) :=
      mul_le_mul hA1 hW1 hWc' (by have := one_le_mul_of_one_le_of_one_le hℓ1 hKκ; linarith)
    obtain ⟨G, hGd⟩ : ∃ G, G = Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε) := ⟨_, rfl⟩
    have hG1 : 1 ≤ G := by
      rw [hGd]
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK) hκ)
        (by linarith)
    have hi2' : 70 * (ℓ * (Kc d * κc L ρ ε)) * (2 ^ 27 * Kc d ^ 3 * (1 + Dc ρ Δ ε)) =
        70 * 2 ^ 27 * (ℓ * G) := by rw [hGd]; ring
    have hi3 : 16 * L * Δ / ε ^ 2 ≤ 16 * (ℓ * G) := by
      rw [LΔ_eq V]
      have h1 : κc L ρ ε * Dc ρ Δ ε ≤ κc L ρ ε * (1 + Dc ρ Δ ε) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have hu : 0 ≤ κc L ρ ε * (1 + Dc ρ Δ ε) := mul_nonneg (by linarith) (by linarith)
      have h2 : κc L ρ ε * (1 + Dc ρ Δ ε) ≤ G := by
        rw [hGd]
        calc κc L ρ ε * (1 + Dc ρ Δ ε) = 1 * (κc L ρ ε * (1 + Dc ρ Δ ε)) := by ring
          _ ≤ Kc d ^ 4 * (κc L ρ ε * (1 + Dc ρ Δ ε)) := mul_le_mul_of_nonneg_right (one_le_pow₀ hK) hu
          _ = Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε) := by ring
      have h3 : G ≤ ℓ * G := le_mul_of_one_le_left (by linarith) hℓ1
      linarith
    have hG0 : 0 < ℓ * G := mul_pos (by linarith) (by linarith)
    have hinner : 16 * L * Δ / ε ^ 2 + (2 * (M : ℝ) + Tc L ρ ε d + 2) * (5 * Δ / (rc ρ ε d ^ 2 * θc ρ ε d)) +
        (2 * M + Tc L ρ ε d + 2) ≤ 2 ^ 34 * (ℓ * G) := by
      linarith
    have hNc : 2 ^ 40 * ℓ ^ 2 * G ≤ (Nc L ρ Δ ε δ d : ℝ) := by
      have e : 2 ^ 40 * ℓ ^ 2 * G = 2 ^ 40 * ℓ ^ 2 * Kc d ^ 4 * κc L ρ ε * (1 + Dc ρ Δ ε) := by
        rw [hGd]; ring
      rw [e]; unfold Nc; rw [← hℓd]; exact Nat.le_ceil _
    have hin0 : 0 ≤ 16 * L * Δ / ε ^ 2 + (2 * (M : ℝ) + Tc L ρ ε d + 2) *
        (5 * Δ / (rc ρ ε d ^ 2 * θc ρ ε d)) + (2 * M + Tc L ρ ε d + 2) := by positivity
    calc (M : ℝ) * (16 * L * Δ / ε ^ 2 + (2 * M + Tc L ρ ε d + 2) * (5 * Δ / (rc ρ ε d ^ 2 * θc ρ ε d))) +
          M * (2 * M + Tc L ρ ε d + 2)
        = M * (16 * L * Δ / ε ^ 2 + (2 * M + Tc L ρ ε d + 2) * (5 * Δ / (rc ρ ε d ^ 2 * θc ρ ε d)) +
          (2 * M + Tc L ρ ε d + 2)) := by ring
      _ ≤ (30 * ℓ + 1) * (2 ^ 34 * (ℓ * G)) := mul_le_mul hM1' hinner hin0 (by linarith)
      _ < 2 ^ 40 * ℓ ^ 2 * G := by linarith [mul_nonneg hG0.le (by linarith : (0 : ℝ) ≤ ℓ - 1)]
      _ ≤ Nc L ρ Δ ε δ d := hNc

end facts6

end LongTails.Proofs.GatedEscapeBudget
