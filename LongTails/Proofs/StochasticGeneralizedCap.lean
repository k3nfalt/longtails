import LongTails.Proofs.StochasticGeneralizedStartup
import LongTails.Proofs.StochasticGeneralizedLogCounting

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate coupling)

lemma run_prefix_count_positive (p : Params) (hp : spec.valid p) (hL1 : 0 < p.L1)
    (hεΔ : p.ε < p.Δ) (v h : ℕ → p.E → p.E) (N : ℕ)
    (hD : (∑ i ∈ Finset.range N, dissipation p.L0 p.L1 (v i)
      (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i)) ≤ 3*p.R^2)
    (hT : (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) N).A < target p.R p.ε) :
    (N : ℝ) ≤ 1+770*Real.sqrt (p.L0*p.R^2/p.ε)+
      9272*(⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε) := by
  classical
  let s := initialIterate p.L0 p.R p.Δ p.ε p.x0
  let S := Real.sqrt (p.L0*p.R^2/p.ε)
  let C := (⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)
  let L := Real.log (4+4*p.Δ/p.ε)
  have hL0 := hp.1
  have hR := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hA : 0 < s.A := by dsimp [s, initialIterate]; positivity
  have hG := (initial_valid p hp).2
  have ha : 0 < p.L1*p.R := mul_pos hL1 hR
  have hr : 1 ≤ p.Δ/p.ε := (one_le_div hε).mpr hεΔ.le
  have htune := ratio_tuning ha hr
  have hCL : 0 ≤ C*L := by
    have hL : 0 ≤ L := by simpa only [L, mul_div_assoc] using (le_trans (by norm_num) htune.2.2.1)
    exact mul_nonneg (Nat.cast_nonneg _) hL
  by_cases hd : ∃ m < N, runUp p.L0 p.L1 v h s m = false
  · let m := Nat.find hd
    have hmN : m < N := (Nat.find_spec hd).1
    have hdown : runUp p.L0 p.L1 v h s m = false := (Nat.find_spec hd).2
    have hup : ∀ i < m, runUp p.L0 p.L1 v h s i = true := by
      intro i hi
      have hn := Nat.find_min hd hi
      have hiN : i < N := lt_trans hi hmN
      cases hu : runUp p.L0 p.L1 v h s i
      · exact False.elim (hn ⟨hiN, hu⟩)
      · rfl
    let n := N-m-1
    have hN : m+(n+1)=N := by dsimp [n]; omega
    let sm := run p.L0 p.L1 v h s m
    let vm := fun i => v (m+i)
    let hm := fun i => h (m+i)
    have hsm := run_valid hL0 hL1.le v h s hA.le hG m
    have hbase : s.A ≤ sm.A := run_weight_mono hL0 hL1.le v h s hA.le hG (Nat.zero_le m)
    have hsmA : 0 < sm.A := hA.trans_le hbase
    have hfirst : 16*(p.L0+p.L1*‖vm 0 (coupling sm)‖) ≤ sm.guess := by
      have hh : ¬(run p.L0 p.L1 v h s m).guess <
          16*(p.L0+p.L1*‖v m (coupling (run p.L0 p.L1 v h s m))‖) := of_decide_eq_false hdown
      simpa only [vm, Nat.add_zero] using le_of_not_gt hh
    have hDm : (∑ i ∈ Finset.range (n+1), dissipation p.L0 p.L1 (vm i)
        (run p.L0 p.L1 vm hm sm i)) ≤ 3*p.R^2 := by
      apply run_dissipation_shift_le hL0 hL1.le v h s hA.le hG m (n+1)
      simpa only [hN] using hD
    have heq : run p.L0 p.L1 vm hm sm (n+1) = run p.L0 p.L1 v h s N := by
      rw [← run_shift, hN]
    have hc := run_count_positive hL0 hL1 hR.le vm hm sm hsmA hsm.2 hfirst n hDm
    rw [heq] at hc
    let A := (run p.L0 p.L1 v h s N).A
    have hAF : sm.A ≤ A := run_weight_mono hL0 hL1.le v h s hA.le hG hmN.le
    have hAp : 0 < A := hsmA.trans_le hAF
    have hguess := initial_up_guess_bound p hp hL1 v h N m hmN.le hup hD
    have hB : sm.guess*A ≤ 1+8192*S^2+4194304*(p.L1*p.R)^2*(p.Δ/p.ε) :=
      (mul_le_mul_of_nonneg_left hT.le hsm.2.le).trans hguess
    have he := exceptional_count_simplify (Real.sqrt_nonneg _) ha hr (mul_nonneg hsm.2.le hAp.le) hB
    have hsmall : 4*p.L0*A ≤ 64*(p.L0*p.R^2/p.ε) := by
      have hh := mul_le_mul_of_nonneg_left hT.le (show 0 ≤ 4*p.L0 by positivity)
      dsimp [target] at hh
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith only [hh]
    have hroot := Real.sqrt_le_sqrt hsmall
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤64)] at hroot
    rw [show Real.sqrt (64 : ℝ)=8 by norm_num] at hroot
    have hratio : 2*A/sm.A ≤ 64*(p.Δ/p.ε) := by
      have hn := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT.le (by norm_num : (0 : ℝ)≤2)) hsmA.le
      have hh := div_le_div_of_nonneg_left (show 0 ≤ 2*target p.R p.ε by dsimp [target]; positivity) hA hbase
      have he : 2*target p.R p.ε/s.A = 64*(p.Δ/p.ε) := by
        dsimp [s, initialIterate, target]
        field_simp; ring
      exact hn.trans (hh.trans_eq he)
    have hh := high_count_simplify ha hr hsmA hAF hratio
    have hmcount := initial_up_prefix_bound p hp hL1 hεΔ v h N m hmN.le hup hD
    have hcast : (N : ℝ) = m+n+1 := by exact_mod_cast hN.symm
    simp only [← mul_div_assoc] at he hh
    change (n : ℝ) ≤ 2*Real.log (1+32*Real.sqrt (sm.guess*A))+
      96*Real.sqrt (4*p.L0*A)+384*(1+(8*(p.L1*p.R))^(2/3 : ℝ))*Real.log (2*A/sm.A) at hc
    change (N : ℝ) ≤ 1+770*S+9272*C*L
    change (m : ℝ) ≤ 16*C*L at hmcount
    change Real.sqrt (4*p.L0*A) ≤ 8*S at hroot
    change 2*Real.log (1+32*Real.sqrt (sm.guess*A)) ≤ 2*S+40*C*L at he
    change 384*(1+(8*(p.L1*p.R))^(2/3 : ℝ))*Real.log (2*A/sm.A) ≤ 9216*C*L at hh
    linarith
  · have hup : ∀ i < N, runUp p.L0 p.L1 v h s i = true := by
      intro i hi
      cases hu : runUp p.L0 p.L1 v h s i
      · exact False.elim (hd ⟨i, hi, hu⟩)
      · rfl
    have hh := initial_up_prefix_bound p hp hL1 hεΔ v h N N le_rfl hup hD
    change (N : ℝ) ≤ 16*C*L at hh
    change (N : ℝ) ≤ 1+770*S+9272*C*L
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    nlinarith only [hh, hCL, hS]

lemma run_prefix_count_self_normalized (p : Params) (hp : spec.valid p) (hL1 : 0 < p.L1)
    (hεΔ : p.ε < p.Δ) (v h : ℕ → p.E → p.E) (N : ℕ)
    (hD : (∑ i ∈ Finset.range N, dissipation p.L0 p.L1 (v i)
      (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i)) ≤ 3*p.R^2)
    (hT : (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) N).A < target p.R p.ε) :
    (N : ℝ) ≤ 770*Real.sqrt (p.L0*p.R^2/p.ε)+53*Real.log (4+4*p.Δ/p.ε)+
      6149*(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ) := by
  classical
  let s := initialIterate p.L0 p.R p.Δ p.ε p.x0
  let S := Real.sqrt (p.L0*p.R^2/p.ε)
  let C := (⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)
  let L := Real.log (4+4*p.Δ/p.ε)
  have hL0 := hp.1
  have hR := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hA : 0 < s.A := by dsimp [s, initialIterate]; positivity
  have hG := (initial_valid p hp).2
  have ha : 0 < p.L1*p.R := mul_pos hL1 hR
  have hr : 1 ≤ p.Δ/p.ε := (one_le_div hε).mpr hεΔ.le
  have htune := ratio_tuning ha hr
  let U := (p.L1*p.R*L)^(2/3 : ℝ)
  have hL : 3/2 ≤ L := by simpa only [L, mul_div_assoc] using htune.2.2.1
  have hlogr : Real.log (p.Δ/p.ε) ≤ L := by simpa only [L, mul_div_assoc] using htune.2.2.2
  have hU : 0 ≤ U := Real.rpow_nonneg (mul_nonneg ha.le (by linarith)) _
  have hat : (p.L1*p.R)^(2/3 : ℝ) ≤ U := by
    apply Real.rpow_le_rpow ha.le _ (by norm_num)
    nlinarith only [ha, hL]
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  by_cases hd : ∃ m < N, runUp p.L0 p.L1 v h s m = false
  · let m := Nat.find hd
    have hmN : m < N := (Nat.find_spec hd).1
    have hdown : runUp p.L0 p.L1 v h s m = false := (Nat.find_spec hd).2
    have hup : ∀ i < m, runUp p.L0 p.L1 v h s i = true := by
      intro i hi
      have hn := Nat.find_min hd hi
      have hiN : i < N := lt_trans hi hmN
      cases hu : runUp p.L0 p.L1 v h s i
      · exact False.elim (hn ⟨hiN, hu⟩)
      · rfl
    let n := N-m-1
    have hN : m+(n+1)=N := by dsimp [n]; omega
    let sm := run p.L0 p.L1 v h s m
    let vm := fun i => v (m+i)
    let hm := fun i => h (m+i)
    have hsm := run_valid hL0 hL1.le v h s hA.le hG m
    have hbase : s.A ≤ sm.A := run_weight_mono hL0 hL1.le v h s hA.le hG (Nat.zero_le m)
    have hsmA : 0 < sm.A := hA.trans_le hbase
    have hfirst : 16*(p.L0+p.L1*‖vm 0 (coupling sm)‖) ≤ sm.guess := by
      have hh : ¬(run p.L0 p.L1 v h s m).guess <
          16*(p.L0+p.L1*‖v m (coupling (run p.L0 p.L1 v h s m))‖) := of_decide_eq_false hdown
      simpa only [vm, Nat.add_zero] using le_of_not_gt hh
    have hDm : (∑ i ∈ Finset.range (n+1), dissipation p.L0 p.L1 (vm i)
        (run p.L0 p.L1 vm hm sm i)) ≤ 3*p.R^2 := by
      apply run_dissipation_shift_le hL0 hL1.le v h s hA.le hG m (n+1)
      simpa only [hN] using hD
    have heq : run p.L0 p.L1 vm hm sm (n+1) = run p.L0 p.L1 v h s N := by
      rw [← run_shift, hN]
    have hc := run_count_self_normalized hL0 hL1 hR.le vm hm sm hsmA hsm.2 hfirst n hDm
    rw [heq] at hc
    let A := (run p.L0 p.L1 v h s N).A
    have hAF : sm.A ≤ A := run_weight_mono hL0 hL1.le v h s hA.le hG hmN.le
    have hAp : 0 < A := hsmA.trans_le hAF
    have hguess := initial_up_guess_bound p hp hL1 v h N m hmN.le hup hD
    have hB : sm.guess*A ≤ 1+8192*S^2+4194304*(p.L1*p.R)^2*(p.Δ/p.ε) :=
      (mul_le_mul_of_nonneg_left hT.le hsm.2.le).trans hguess
    have he := exceptional_log_bound (Real.sqrt_nonneg _) ha.le hr (mul_nonneg hsm.2.le hAp.le) hB
    have hsmall : 4*p.L0*A ≤ 64*(p.L0*p.R^2/p.ε) := by
      have hh := mul_le_mul_of_nonneg_left hT.le (show 0 ≤ 4*p.L0 by positivity)
      dsimp [target] at hh
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith only [hh]
    have hroot := Real.sqrt_le_sqrt hsmall
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤64)] at hroot
    rw [show Real.sqrt (64 : ℝ)=8 by norm_num] at hroot
    have hratio : 2*A/sm.A ≤ 64*(p.Δ/p.ε) := by
      have hn := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT.le (by norm_num : (0 : ℝ)≤2)) hsmA.le
      have hh := div_le_div_of_nonneg_left (show 0 ≤ 2*target p.R p.ε by dsimp [target]; positivity) hA hbase
      have he : 2*target p.R p.ε/s.A = 64*(p.Δ/p.ε) := by
        dsimp [s, initialIterate, target]
        field_simp; ring
      exact hn.trans (hh.trans_eq he)
    have hh := high_self_normalized_simplify ha hr hsmA hAF hratio
    have hmcount := initial_up_prefix_raw p hp hL1 hεΔ v h N m hmN.le hup hD
    have hcast : (N : ℝ) = m+n+1 := by exact_mod_cast hN.symm
    simp only [← mul_div_assoc] at he hh
    change (n : ℝ) ≤ 2*Real.log (1+32*Real.sqrt (sm.guess*A))+
      96*Real.sqrt (4*p.L0*A)+4*Real.log (2*A/sm.A)+2048*(p.L1*p.R*Real.log (2*A/sm.A))^(2/3 : ℝ) at hc
    change (N : ℝ) ≤ 770*S+53*L+6149*U
    change (m : ℝ) ≤ 10+3/2*(p.L1*p.R)^(2/3 : ℝ)+1/2*Real.log (p.Δ/p.ε) at hmcount
    change Real.sqrt (4*p.L0*A) ≤ 8*S at hroot
    change 2*Real.log (1+32*Real.sqrt (sm.guess*A)) ≤ 47+2*S+3*(p.L1*p.R)^(2/3 : ℝ)+Real.log (p.Δ/p.ε) at he
    change 4*Real.log (2*A/sm.A)+2048*(p.L1*p.R*Real.log (2*A/sm.A))^(2/3 : ℝ) ≤ 12*L+6144*U at hh
    linarith
  · have hup : ∀ i < N, runUp p.L0 p.L1 v h s i = true := by
      intro i hi
      cases hu : runUp p.L0 p.L1 v h s i
      · exact False.elim (hd ⟨i, hi, hu⟩)
      · rfl
    have hh := initial_up_prefix_raw p hp hL1 hεΔ v h N N le_rfl hup hD
    change (N : ℝ) ≤ 10+3/2*(p.L1*p.R)^(2/3 : ℝ)+1/2*Real.log (p.Δ/p.ε) at hh
    change (N : ℝ) ≤ 770*S+53*L+6149*U
    linarith

lemma run_prefix_count_smooth (p : Params) (hp : spec.valid p) (hL1 : p.L1=0)
    (v h : ℕ → p.E → p.E) (N : ℕ)
    (hT : (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) N).A < target p.R p.ε) :
    (N : ℝ) ≤ 130+512*Real.sqrt (p.L0*p.R^2/p.ε) := by
  let s := initialIterate p.L0 p.R p.Δ p.ε p.x0
  let S := Real.sqrt (p.L0*p.R^2/p.ε)
  have hL0 := hp.1
  have hR := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hA : 0 < s.A := by dsimp [s, initialIterate]; positivity
  have hG := (initial_valid p hp).2
  have hTpos : 0 < target p.R p.ε := by dsimp [target]; positivity
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S^2=p.L0*p.R^2/p.ε := Real.sq_sqrt (by positivity)
  rw [hL1] at hT
  by_cases hN1 : N ≤ 1
  · have hn : (N : ℝ) ≤ 1 := by exact_mod_cast hN1
    change (N : ℝ) ≤ 130+512*S
    linarith
  · have hsG : s.guess ≤ p.L0+1/target p.R p.ε :=
      max_le (by linarith [one_div_pos.mpr hTpos]) (by linarith)
    have hex : ∃ m : ℕ, m ≤ 1 ∧ 16*p.L0 ≤ (run p.L0 0 v h s m).guess ∧
        (run p.L0 0 v h s m).guess ≤ 16*(p.L0+1/target p.R p.ε) := by
      by_cases hd : 16*p.L0 ≤ s.guess
      · refine ⟨0, by omega, hd, ?_⟩
        change s.guess ≤ _
        have hh : 0 ≤ p.L0+1/target p.R p.ε := by positivity
        linarith
      · have he : (run p.L0 0 v h s 1).guess = 16*s.guess := by
          change (step p.L0 0 (v 0) (h 0) s).guess = _
          rw [step_guess]
          simp only [zero_mul, add_zero, ite_eq_right hd]
        refine ⟨1, le_rfl, ?_, ?_⟩
        · rw [he]
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
        · rw [he]
          exact mul_le_mul_of_nonneg_left hsG (by norm_num)
    obtain ⟨m, hm1, hfirst, hguess⟩ := hex
    have hmN : m < N := by omega
    let n := N-m-1
    have hN : m+(n+1)=N := by dsimp [n]; omega
    let sm := run p.L0 0 v h s m
    let vm := fun i => v (m+i)
    let hm := fun i => h (m+i)
    have hv := run_valid hL0 (le_refl 0) v h s hA.le hG m
    have heq : run p.L0 0 vm hm sm (n+1) = run p.L0 0 v h s N := by rw [← run_shift, hN]
    have hK : 16*p.L0 ≤ 16*(p.L0+1/target p.R p.ε) := by
      have hh := one_div_pos.mpr hTpos
      linarith
    have hc := run_count_smooth hL0 vm hm sm hv.1 hv.2 hfirst hK hguess n
    rw [heq] at hc
    let A := (run p.L0 0 v h s N).A
    let X := p.L0+1/target p.R p.ε
    have hX : 0 < X := by dsimp [X]; positivity
    have hsmall : X*A ≤ (4*S+1)^2 := by
      have hh := mul_le_mul_of_nonneg_left hT.le hX.le
      have he : X*target p.R p.ε = 16*S^2+1 := by
        dsimp [X]
        rw [add_mul, one_div_mul_cancel hTpos.ne', hSsq]
        dsimp [target]
        ring
      change X*A ≤ X*target p.R p.ε at hh
      rw [he] at hh
      nlinarith
    have hroot : Real.sqrt (X*A) ≤ 4*S+1 := (Real.sqrt_le_iff).mpr ⟨by positivity, hsmall⟩
    have hid : Real.sqrt (16*X)*(32*Real.sqrt A) = 128*Real.sqrt (X*A) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤16), Real.sqrt_mul hX.le]
      norm_num
      ring
    change (n : ℝ) ≤ Real.sqrt (16*X)*(32*Real.sqrt A) at hc
    rw [hid] at hc
    have hmr : (m : ℝ) ≤ 1 := by exact_mod_cast hm1
    have hcast := congrArg (fun k : ℕ => (k : ℝ)) hN
    push_cast at hcast
    change (N : ℝ) ≤ 130+512*S
    linarith

lemma run_target (p : Params) (hp : spec.valid p) (hεΔ : p.ε < p.Δ)
    (v h : ℕ → p.E → p.E) (N : ℕ)
    (hN : 16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+
      (⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε)) ≤ N)
    (hD : (∑ i ∈ Finset.range N, dissipation p.L0 p.L1 (v i)
      (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i)) ≤ 3*p.R^2) :
    target p.R p.ε ≤ (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) N).A := by
  by_contra hT
  have ht := lt_of_not_ge hT
  have hS := Real.sqrt_nonneg (p.L0*p.R^2/p.ε)
  have hΔ := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hL : 0 ≤ Real.log (4+4*p.Δ/p.ε) := Real.log_nonneg (by
    have hh : 0 ≤ 4*p.Δ/p.ε := by positivity
    linarith)
  have hCL := mul_nonneg (show 0 ≤ (⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ) by positivity) hL
  by_cases hL1 : p.L1=0
  · have hc := run_prefix_count_smooth p hp hL1 v h N ht
    nlinarith only [hc, hN, hS, hCL]
  · have hL1p : 0 < p.L1 := lt_of_le_of_ne hp.2.1 (Ne.symm hL1)
    have hc := run_prefix_count_positive p hp hL1p hεΔ v h N hD ht
    nlinarith only [hc, hN, hS, hCL]

lemma run_target_min (p : Params) (hp : spec.valid p) (hεΔ : p.ε < p.Δ)
    (v h : ℕ → p.E → p.E) (N : ℕ)
    (hN : 16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+
      min ((⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε))
        (Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))) ≤ N)
    (hD : (∑ i ∈ Finset.range N, dissipation p.L0 p.L1 (v i)
      (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i)) ≤ 3*p.R^2) :
    target p.R p.ε ≤ (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) N).A := by
  by_contra hT
  have ht := lt_of_not_ge hT
  let S := Real.sqrt (p.L0*p.R^2/p.ε)
  let L := Real.log (4+4*p.Δ/p.ε)
  let C := (⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)
  let U := (p.L1*p.R*L)^(2/3 : ℝ)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hΔ := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hL : 0 ≤ L := Real.log_nonneg (by
    have hh : 0 ≤ 4*p.Δ/p.ε := by positivity
    linarith)
  have hU : 0 ≤ U := Real.rpow_nonneg (mul_nonneg (mul_nonneg hp.2.1 hp.2.2.1.le) hL) _
  have hCL : 0 ≤ C*L := mul_nonneg (Nat.cast_nonneg _) hL
  have hmin : 0 ≤ min (C*L) (L+U) := le_min hCL (add_nonneg hL hU)
  change 16384*(1+S+min (C*L) (L+U)) ≤ N at hN
  by_cases hL1 : p.L1=0
  · have hc := run_prefix_count_smooth p hp hL1 v h N ht
    change (N : ℝ) ≤ 130+512*S at hc
    nlinarith only [hc, hN, hS, hmin]
  · have hL1p : 0 < p.L1 := lt_of_le_of_ne hp.2.1 (Ne.symm hL1)
    have hc := run_prefix_count_positive p hp hL1p hεΔ v h N hD ht
    have hd := run_prefix_count_self_normalized p hp hL1p hεΔ v h N hD ht
    change (N : ℝ) ≤ 1+770*S+9272*C*L at hc
    change (N : ℝ) ≤ 770*S+53*L+6149*U at hd
    by_cases hh : C*L ≤ L+U
    · rw [min_eq_left hh] at hN
      nlinarith only [hc, hN, hS, hCL]
    · rw [min_eq_right (le_of_not_ge hh)] at hN
      nlinarith only [hd, hN, hS, hL, hU]

end OracleTemplate.StochasticGeneralized
