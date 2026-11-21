import LongTails.Proofs.ComponentHessianGap
import LongTails.Setups.ConvexFiniteSumMeanSquareHessian

namespace LongTails.Proofs.ComponentHessianTuning

open LongTails.Setups.ConvexFiniteSumMeanSquareHessian ComponentHessianFamily ComponentHessianGap

noncomputable def scale (p : Params) : ℝ :=
  (p.H * p.R^3 / (Real.sqrt p.n * p.ε)) ^ (2 / 7 : ℝ)

lemma choose_length {n b : ℕ} (hn : 0 < n) {S : ℝ} (_hS : 0 ≤ S)
    (hb : (b : ℝ) ≤ n * (1 + S) / 2^16) (hbig : n < 4*b) :
    ∃ k : ℕ, 0 < k ∧ 8*b ≤ n*k ∧ 2048 * (k+1 : ℕ) ≤ S ∧ k+1 ≤ 1 + ⌈S⌉₊ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hbig' : (n : ℝ) < 4 * b := by exact_mod_cast hbig
  have hnp : 16383 * (n : ℝ) < n*S := by linarith
  have hSbig : 16383 < S := by
    exact (mul_lt_mul_iff_right₀ hn').mp (by simpa [mul_comm] using hnp)
  let k := ⌊S / 4096⌋₊
  have hlo : (k : ℝ) ≤ S / 4096 := Nat.floor_le (by positivity)
  have hhi : S / 4096 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk : 0 < k := by
    by_contra! h
    have he : k = 0 := by omega
    rw [he, Nat.cast_zero] at hhi
    linarith
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · have h1 : 8 * (1 + S) / 2^16 ≤ (k : ℝ) := by linarith
    have hh : 8 * (b : ℝ) ≤ n*k := by nlinarith [mul_le_mul_of_nonneg_left h1 hn'.le]
    exact_mod_cast hh
  · push_cast
    linarith
  · have hle : (k : ℝ) ≤ (⌈S⌉₊ : ℝ) := by linarith [Nat.le_ceil S]
    have hh : k ≤ ⌈S⌉₊ := by exact_mod_cast hle
    omega

lemma dimension {p : Params} (hp : spec.valid p) {k b : ℕ} (hk : k+1 ≤ 1 + ⌈scale p⌉₊)
    (hb : 8*b ≤ p.n*k) :
    ∃ D : ℝ, 0 < D ∧ D + (k+1 : ℕ) ≤ p.d ∧
      32 * (b + 1 : ℕ) * (k + 1 : ℕ) * ((2 * radius p.n (k + 1 : ℕ)) ^ 2 / (1 / 80 : ℝ)^2) ≤ D ∧
      k + 1 ≤ p.d := by
  obtain ⟨hn, _, _, _, hd⟩ := hp
  let m := 1 + ⌈scale p⌉₊
  change 2^170 * p.n^3 * m^12 ≤ p.d at hd
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hb' : b+1 ≤ p.n*m := by
    have h := Nat.mul_le_mul_left p.n (show k+1 ≤ m from hk)
    rw [Nat.mul_succ] at h
    omega
  have hK : (k+1 : ℕ) ≤ m := hk
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnr : (1 : ℝ) ≤ p.n := by exact_mod_cast hn
  have hKr : ((k+1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hK
  let D := (2:ℝ)^169 * (p.n:ℝ)^3 * (m:ℝ)^12
  have hd' : (2:ℝ)^170 * (p.n:ℝ)^3 * (m:ℝ)^12 ≤ p.d := by exact_mod_cast hd
  have hle : (m : ℝ) ≤ D := by
    have h₁ := pow_le_pow_right₀ hmr (by decide : 1 ≤ 12)
    have h₂ : 1 ≤ (p.n : ℝ)^3 := one_le_pow₀ hnr
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_right h₂ (pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 12)]
  have hdD : D + (k+1 : ℕ) ≤ p.d := by dsimp [D] at *; linarith
  refine ⟨D, by dsimp [D]; positivity, hdD, ?_, ?_⟩
  · have hbr : ((b+1 : ℕ) : ℝ) ≤ (p.n:ℝ)*m := by exact_mod_cast hb'
    unfold radius
    calc
      _ ≤ 32 * ((p.n:ℝ)*m) * m * ((2*(2^70 * (p.n:ℝ) * (m:ℝ)^4))^2 / (1/80:ℝ)^2) := by gcongr
      _ = (2^147 * 6400 : ℝ) * (p.n:ℝ)^3 * (m:ℝ)^10 := by ring
      _ ≤ D := by
        unfold D
        gcongr <;> norm_num
  · have : ((k+1 : ℕ) : ℝ) ≤ p.d := by linarith
    exact_mod_cast this

lemma parameters {p : Params} (hp : spec.valid p) {k : ℕ}
    (hlen : 2048 * ((k+1 : ℕ) : ℝ) ≤ scale p) :
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      (∀ π : Fin (k+1) ↪ Fin p.d, ‖anchorPoint π‖ ≤ β*p.R) ∧
      2^56 * (c*β^3)^2 ≤ p.n*p.H^2 ∧ 32*p.ε < 23*(c*((k+1 : ℕ) : ℝ)/p.n) := by
  obtain ⟨hn, hH, hR, hε, _⟩ := hp
  let K : ℝ := (k+1 : ℕ)
  have hk : 0 < K := by dsimp [K]; positivity
  have hn' : (0 : ℝ) < p.n := by exact_mod_cast hn
  have hs := Real.sqrt_pos.mpr hn'
  have hsK := Real.sqrt_pos.mpr hk
  let Q := p.H*p.R^3 / (Real.sqrt p.n*p.ε)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hp7 : (2048*K)^7 ≤ Q^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2048*K) hlen 7
    change _ ≤ (Q ^ (2 / 7 : ℝ)) ^ (7:ℕ) at hh
    rw [← Real.rpow_mul_natCast hQ] at hh
    norm_num at hh
    exact hh
  have hmid : (2:ℝ)^36 * K^3 * Real.sqrt K < Q := by
    have hsq := Real.sq_sqrt hk.le
    have he : ((2:ℝ)^36 * K^3 * Real.sqrt K)^2 = 2^72*K^7 := by rw [mul_pow, hsq]; ring
    have hh : 2^72*K^7 < (2048*K)^7 := by nlinarith [pow_pos hk 7]
    nlinarith only [he, hh, hp7, hQ, show 0 ≤ (2:ℝ)^36 * K^3 * Real.sqrt K by positivity]
  have hQ' := (lt_div_iff₀ (mul_pos hs hε)).mp hmid
  have hHpos : 0 < p.H := by
    by_contra! h
    have hz := le_antisymm h hH
    rw [hz, zero_mul] at hQ'
    exact (not_lt_of_ge (by positivity)) hQ'
  let β := 4*K*Real.sqrt K/p.R
  let c := p.H * Real.sqrt p.n / (2^28 * β^3)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, β, hc, hβ, ?_, ?_, ?_⟩
  · intro π
    have he : β*p.R = 4*K*Real.sqrt K := by dsimp [β]; field_simp
    rw [he]
    have hh := anchor_norm_sq π
    change ‖anchorPoint π‖^2 = 16*K^3 at hh
    nlinarith [show (4*K*Real.sqrt K)^2 = 16*K^3 by rw [mul_pow, Real.sq_sqrt hk.le]; ring,
      show 0 ≤ 4*K*Real.sqrt K by positivity]
  · dsimp only [c]
    rw [show p.H*Real.sqrt p.n/(2^28*β^3)*β^3 = p.H*Real.sqrt p.n/2^28 by field_simp]
    rw [div_pow, mul_pow, Real.sq_sqrt hn'.le]
    ring_nf
    rfl
  · change 32*p.ε < 23*(c*K/p.n)
    dsimp [c, β]
    field_simp
    have he : Real.sqrt K ^ 3 = K * Real.sqrt K := by
      rw [pow_succ, Real.sq_sqrt hk.le]
    rw [he]
    have hr := mul_lt_mul_of_pos_right hQ' hs
    have hns := Real.sq_sqrt hn'.le
    ring_nf at hr
    rw [hns] at hr
    nlinarith only [hr, mul_pos (mul_pos hHpos (pow_pos hR 3)) hs]

end LongTails.Proofs.ComponentHessianTuning
