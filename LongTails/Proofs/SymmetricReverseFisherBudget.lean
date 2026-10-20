import LongTails.Proofs.SymmetricReverseFisherContraction
import Mathlib.Analysis.Complex.ExponentialBounds
namespace LongTails.Proofs.SymmetricReverseFisherBudget
open LongTails.Proofs.SymmetricReverseFisherTrajectory
noncomputable def rateFactor (a ε : ℝ) : ℝ := (1+a^2)/max (a^2) ε
lemma rateFactor_pos (a : ℝ) {ε : ℝ} (hε : 0 < ε) : 0 < rateFactor a ε := by
  unfold rateFactor
  have hd : 0 < max (a^2) ε := lt_of_lt_of_le hε (le_max_right _ _)
  positivity
lemma rateFactor_ge_one (a : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ rateFactor a ε := by
  have hd : 0 < max (a^2) ε := lt_of_lt_of_le hε (le_max_right _ _)
  apply (le_div_iff₀ hd).mpr
  have hm : max (a^2) ε ≤ 1+a^2 := max_le (by linarith) (by nlinarith [sq_nonneg a])
  simpa using hm
lemma rateFactor_compare {s a ε : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a)
    (hε : 0 < ε) (hε1 : ε ≤ 1) : rateFactor a ε ≤ 2*rateFactor s ε := by
  have hsq : s^2 ≤ a^2 := by nlinarith
  have hda : 0 < max (a^2) ε := lt_of_lt_of_le hε (le_max_right _ _)
  by_cases hsε : ε ≤ s^2
  · have hsp : 0 < s^2 := hε.trans_le hsε
    have hap : 0 < a^2 := hsp.trans_le hsq
    have hh : rateFactor a ε ≤ rateFactor s ε := by
      unfold rateFactor
      rw [max_eq_left (hsε.trans hsq), max_eq_left hsε]
      apply (div_le_div_iff₀ hap hsp).mpr
      nlinarith
    have hp := rateFactor_pos s hε
    linarith
  · have hsε' : s^2 ≤ ε := le_of_lt (lt_of_not_ge hsε)
    have ha2 : rateFactor a ε ≤ 2/ε := by
      unfold rateFactor
      apply (div_le_div_iff₀ hda hε).mpr
      by_cases haε : a^2 ≤ ε
      · rw [max_eq_right haε]
        nlinarith [mul_le_mul_of_nonneg_right (show a^2 ≤ 1 by linarith) hε.le]
      · rw [max_eq_left (le_of_lt (lt_of_not_ge haε))]
        nlinarith [mul_le_mul_of_nonneg_left hε1 (sq_nonneg a)]
    have hs1 : 1/ε ≤ rateFactor s ε := by
      unfold rateFactor
      rw [max_eq_right hsε']
      exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg s]) hε.le
    have he : 2/ε = 2*(1/ε) := by ring
    rw [he] at ha2
    linarith
lemma inverse_strength_bound {s a ε : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (haε : ε/10000 < a^2) :
    1/signalStrength a ≤ 2000000000*rateFactor s ε := by
  have ha2 : 0 < a^2 := lt_trans (by positivity) haε
  have hd : 0 < max (a^2) ε := lt_of_lt_of_le hε (le_max_right _ _)
  have hmax : max (a^2) ε ≤ 10000*a^2 := max_le (by nlinarith) (by linarith)
  have hid : 1/signalStrength a = 100000*(1+a^2)/a^2 := by
    unfold signalStrength
    field_simp
  have hh : 1/signalStrength a ≤ 1000000000*rateFactor a ε := by
    rw [hid]
    unfold rateFactor
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ ha2 hd).mpr
    have h := mul_le_mul_of_nonneg_left hmax (show 0 ≤ 100000*(1+a^2) by positivity)
    nlinarith
  have hc := mul_le_mul_of_nonneg_left (rateFactor_compare hs hsa hε hε1)
    (by norm_num : (0:ℝ) ≤ 1000000000)
  linarith
noncomputable def logArgument (d B δ ε : ℝ) : ℝ := 1000000000000000*d*(1+B)/(δ*ε)
lemma logArgument_lower {d B δ ε : ℝ} (hd : 1 ≤ d) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    1000000000000000*(1+B)/ε ≤ logArgument d B δ ε := by
  have hnum : 1000000000000000*(1+B) ≤ 1000000000000000*d*(1+B) := by
    nlinarith [mul_le_mul_of_nonneg_right hd (show 0 ≤ 1000000000000000*(1+B) by positivity)]
  have hden : δ*ε ≤ ε := by nlinarith
  exact (div_le_div_of_nonneg_left (by positivity) (mul_pos hδ hε) hden).trans
    (div_le_div_of_nonneg_right hnum (mul_nonneg hδ.le hε.le))
lemma logArgument_bounds {d B δ ε : ℝ} (hd : 1 ≤ d) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1000000000000000 ≤ logArgument d B δ ε ∧
      4/ε ≤ logArgument d B δ ε ∧ d/δ ≤ logArgument d B δ ε := by
  have hl := logArgument_lower hd hB hδ hδ1 hε
  have hbase : 1000000000000000 ≤ 1000000000000000*(1+B)/ε :=
    (le_div_iff₀ hε).mpr (by nlinarith)
  have hfour : 4/ε ≤ 1000000000000000*(1+B)/ε :=
    div_le_div_of_nonneg_right (by nlinarith) hε.le
  refine ⟨hbase.trans hl, hfour.trans hl, ?_⟩
  unfold logArgument
  have hd0 : 0 ≤ d := by linarith
  have hnum : d*ε ≤ 1000000000000000*d*(1+B) := by
    have hh := mul_le_mul_of_nonneg_left hε1 hd0
    nlinarith [mul_nonneg hd0 hB]
  apply (div_le_div_iff₀ hδ (mul_pos hδ hε)).mpr
  have hh := mul_le_mul_of_nonneg_left hnum hδ.le
  nlinarith
lemma logArgument_log_lower {d B δ ε : ℝ} (hd : 1 ≤ d) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ Real.log (logArgument d B δ ε) := by
  have hb := (logArgument_bounds hd hB hδ hδ1 hε hε1).1
  have hp : 0 < logArgument d B δ ε := by linarith
  apply (Real.le_log_iff_exp_le hp).mpr
  have he := Real.exp_one_lt_three
  linarith
lemma inverse_step_strength_bound {s a B ε : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a)
    (haB : a ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1) (haε : ε/10000 < a^2) :
    1/((1/(48+20*B))*signalStrength a) ≤ 96000000000*(1+B)*rateFactor s ε := by
  have hB : 0 ≤ B := hs.trans (hsa.trans haB)
  have hh := inverse_strength_bound hs hsa hε hε1 haε
  have hstep : 48+20*B ≤ 48*(1+B) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hh (show 0 ≤ 48+20*B by positivity)
  have h2 := mul_le_mul_of_nonneg_right hstep (show 0 ≤ 2000000000*rateFactor s ε by have h := rateFactor_pos s hε; positivity)
  have hid : 1/((1/(48+20*B))*signalStrength a) = (48+20*B)*(1/signalStrength a) := by field_simp
  rw [hid]
  nlinarith
lemma three_phase_cost {t z L P : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hz : 0 ≤ z) (hzL : z ≤ L) (hL : 1 ≤ L) (hP : 2889/t*L ≤ P) :
    ⌈2/t*z⌉₊ + ⌈4/t*z⌉₊ + ⌈2880/t*L⌉₊ ≤ ⌈P⌉₊ := by
  have hL0 : 0 ≤ L := by linarith
  have h1 := Nat.ceil_lt_add_one (show 0 ≤ 2/t*z by positivity)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ 4/t*z by positivity)
  have h3 := Nat.ceil_lt_add_one (show 0 ≤ 2880/t*L by positivity)
  have h4 := Nat.le_ceil P
  have hz1 := mul_le_mul_of_nonneg_left hzL (show 0 ≤ 2/t by positivity)
  have hz2 := mul_le_mul_of_nonneg_left hzL (show 0 ≤ 4/t by positivity)
  have hu : 1 ≤ L/t := (le_div_iff₀ ht).mpr (by linarith)
  have hreal : (⌈2/t*z⌉₊ : ℝ) + ⌈4/t*z⌉₊ + ⌈2880/t*L⌉₊ ≤ (⌈P⌉₊ : ℝ) := by
    simp only [div_eq_mul_inv] at *
    nlinarith
  exact_mod_cast hreal
lemma logarithm_projection_bound {d B δ ε ζ : ℝ} (hd : 1 ≤ d) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hζ : δ/d ≤ ζ) (hζ1 : ζ ≤ 1) :
    0 ≤ Real.log (1/ζ) ∧ Real.log (1/ζ) ≤ Real.log (logArgument d B δ ε) := by
  have hd0 : 0 < d := by linarith
  have hζ0 : 0 < ζ := (div_pos hδ hd0).trans_le hζ
  have h1 : 1 ≤ 1/ζ := (le_div_iff₀ hζ0).mpr (by linarith)
  have hratio : 1/ζ ≤ d/δ := by
    apply (div_le_div_iff₀ hζ0 hδ).mpr
    have hh := (div_le_iff₀ hd0).mp hζ
    nlinarith
  refine ⟨Real.log_nonneg h1, ?_⟩
  exact Real.log_le_log (by positivity)
    (hratio.trans (logArgument_bounds hd hB hδ hδ1 hε hε1).2.2)
lemma prefactor_bound {a B ε : ℝ} (ha : 0 ≤ a) (haB : a ≤ B)
    (hε : 0 < ε) (haε : ε/10000 < a^2) :
    148*(1+600*a)/signalStrength a ≤ 100000000000000*(1+B)^3/ε := by
  have hB : 0 ≤ B := ha.trans haB
  have ha2 : 0 < a^2 := lt_trans (by positivity) haε
  have hab2 : a^2 ≤ B^2 := by nlinarith
  have hm : 1/signalStrength a ≤ 1000000000*(1+B^2)/ε := by
    have hid : 1/signalStrength a = 100000*(1+a^2)/a^2 := by unfold signalStrength; field_simp
    rw [hid]
    apply (div_le_div_iff₀ ha2 hε).mpr
    have h1 := mul_le_mul_of_nonneg_left (show ε ≤ 10000*a^2 by linarith)
      (show 0 ≤ 100000*(1+a^2) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hab2 (show 0 ≤ 1000000000*a^2 by positivity)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ 148*(1+600*a) by positivity)
  have hpoly : 148*(1+600*a)*1000000000*(1+B^2) ≤ 100000000000000*(1+B)^3 := by
    have h1 := mul_le_mul_of_nonneg_right haB (show 0 ≤ 88800000000000*(1+B^2) by positivity)
    nlinarith [sq_nonneg B, pow_nonneg hB 3]
  have hd := div_le_div_of_nonneg_right hpoly hε.le
  calc
    _ = 148*(1+600*a)*(1/signalStrength a) := by ring
    _ ≤ 148*(1+600*a)*(1000000000*(1+B^2)/ε) := hmul
    _ = 148*(1+600*a)*1000000000*(1+B^2)/ε := by ring
    _ ≤ _ := hd
lemma prefactor_absorbed {d a B δ ε : ℝ} (hd : 1 ≤ d) (ha : 0 ≤ a) (haB : a ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (haε : ε/10000 < a^2) :
    148*(1+600*a)/signalStrength a ≤ ε*(logArgument d B δ ε)^3 := by
  have hB : 0 ≤ B := ha.trans haB
  have hl := logArgument_lower hd hB hδ hδ1 hε
  have hHp : 0 < logArgument d B δ ε := by
    have hh := (logArgument_bounds hd hB hδ hδ1 hε hε1).1
    linarith
  have hbase : 1000000000000000*(1+B) ≤ ε*logArgument d B δ ε := by
    have h := (div_le_iff₀ hε).mp hl
    nlinarith
  have hp := pow_le_pow_left₀ (show 0 ≤ 1000000000000000*(1+B) by positivity) hbase 3
  have heps : ε^3 ≤ ε^2 := by nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hε1)]
  have hmul := mul_le_mul_of_nonneg_right heps (pow_nonneg hHp.le 3)
  have hconst : 100000000000000*(1+B)^3 ≤ 1000000000000000^3*(1+B)^3 :=
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hscaled : 100000000000000*(1+B)^3 ≤ ε^2*(logArgument d B δ ε)^3 := by
    rw [mul_pow, mul_pow] at hp
    exact (hconst.trans hp).trans hmul
  apply (prefactor_bound ha haB hε haε).trans
  apply (div_le_iff₀ hε).mpr
  nlinarith
noncomputable def publicScale (d s B δ ε : ℝ) : ℝ :=
  (1+B)*rateFactor s ε*Real.log (logArgument d B δ ε)
noncomputable def iterations (d s B δ ε : ℝ) : ℕ := ⌈1000000000000000*publicScale d s B δ ε⌉₊
lemma positive_budget_cost {d s a B δ ε ζ : ℝ} (hd : 1 ≤ d) (hs : 0 ≤ s) (hsa : s ≤ a)
    (haB : a ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (haε : ε/10000 < a^2) (hζ : δ/d ≤ ζ) (hζ1 : ζ ≤ 1) :
    let η := 1/(48+20*B)
    let m := signalStrength a
    let L := Real.log (logArgument d B δ ε)
    ⌈2/(η*m)*Real.log (1/ζ)⌉₊ + ⌈4/(η*m)*Real.log (1/ζ)⌉₊ + ⌈2880/(η*m)*L⌉₊ ≤
      iterations d s B δ ε := by
  dsimp only
  have hB : 0 ≤ B := hs.trans (hsa.trans haB)
  have ha : 0 < a := by nlinarith
  have hm := LongTails.Proofs.SymmetricReverseFisherDynamics.strength_bounds ha
  have hm0 : 0 < signalStrength a := hm.1
  have hm1 : signalStrength a ≤ 1 := hm.2.trans (min_le_right _ _)
  have hη : 0 < 1/(48+20*B) := by positivity
  have hη1 : 1/(48+20*B) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have ht1 : 1/(48+20*B)*signalStrength a ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hm1 hη.le]
  have hL := logArgument_log_lower hd hB hδ hδ1 hε hε1
  have hz := logarithm_projection_bound hd hB hδ hδ1 hε hε1 hζ hζ1
  apply three_phase_cost (mul_pos hη hm0) ht1 hz.1 hz.2 hL
  have hi := inverse_step_strength_bound hs hsa haB hε hε1 haε
  have hh := mul_le_mul_of_nonneg_right hi
    (show 0 ≤ 2889*Real.log (logArgument d B δ ε) by positivity)
  have hW : 0 ≤ publicScale d s B δ ε := by
    unfold publicScale
    have hrate := rateFactor_pos s hε
    positivity
  unfold publicScale at hW ⊢
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith
lemma small_budget_cost {d s B δ ε : ℝ} (hd : 1 ≤ d) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hsε : s^2 ≤ ε) :
    960/((1/(48+20*B))*ε)*Real.log (4/ε) ≤ (iterations d s B δ ε : ℝ) := by
  have hL := logArgument_log_lower hd hB hδ hδ1 hε hε1
  have hl0 : 0 ≤ Real.log (4/ε) := Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  have hl : Real.log (4/ε) ≤ Real.log (logArgument d B δ ε) :=
    Real.log_le_log (by positivity) (logArgument_bounds hd hB hδ hδ1 hε hε1).2.1
  have hr : 1/ε ≤ rateFactor s ε := by
    unfold rateFactor
    rw [max_eq_right hsε]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg s]) hε.le
  have hs : 48+20*B ≤ 48*(1+B) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hr (show 0 ≤ 960*(48+20*B) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hs (show 0 ≤ 960*rateFactor s ε by have h := rateFactor_pos s hε; positivity)
  have hc : 960*(48+20*B)*(1/ε) ≤ 46080*(1+B)*rateFactor s ε := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right hc hl0
  have h4 := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 46080*(1+B)*rateFactor s ε by have h := rateFactor_pos s hε; positivity)
  have hW : 0 ≤ publicScale d s B δ ε := by
    unfold publicScale
    have h := rateFactor_pos s hε
    positivity
  have he : 960/((1/(48+20*B))*ε) = 960*(48+20*B)*(1/ε) := by field_simp
  rw [he]
  have hk := Nat.le_ceil (1000000000000000*publicScale d s B δ ε)
  change _ ≤ (⌈1000000000000000*publicScale d s B δ ε⌉₊ : ℝ)
  unfold publicScale at hW hk ⊢
  nlinarith
lemma exponential_tail_accuracy {C H η m ε : ℝ} (hH : 0 < H) (hη : 0 < η)
    (hm : 0 < m) (hε : 0 ≤ ε) (hC : C ≤ ε*H^3) {k : ℕ}
    (hk : 2880/(η*m)*Real.log H ≤ k) : C*Real.exp (-η*m*k/960) ≤ ε := by
  have hh := mul_le_mul_of_nonneg_left hk (mul_pos hη hm).le
  have hid : (η*m)*(2880/(η*m)*Real.log H) = 2880*Real.log H := by field_simp
  rw [hid] at hh
  have hexp : -η*m*k/960 + 3*Real.log H ≤ 0 := by linarith
  have hpow : Real.exp (3*Real.log H) = H^3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hH] using Real.exp_nat_mul (Real.log H) 3
  have hprod : H^3*Real.exp (-η*m*k/960) ≤ 1 := by
    rw [← hpow, ← Real.exp_add]
    exact (Real.exp_le_exp.mpr (by linarith : 3*Real.log H + -η*m*k/960 ≤ 0)).trans_eq Real.exp_zero
  have h1 := mul_le_mul_of_nonneg_right hC (Real.exp_pos (-η*m*k/960)).le
  have h2 := mul_le_mul_of_nonneg_left hprod hε
  nlinarith
lemma iterations_formula (d s B δ ε : ℝ) :
    iterations d s B δ ε = ⌈1000000000000000*(1+B)*(1+s^2)/max (s^2) ε * Real.log (1000000000000000*d*(1+B)/(δ*ε))⌉₊ := by
  unfold iterations publicScale rateFactor logArgument
  congr 1
  ring

end LongTails.Proofs.SymmetricReverseFisherBudget
