import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import LongTails.Proofs.BrightnessStiffPhase
import LongTails.Proofs.BrightnessFilterTransport
import LongTails.Proofs.BrightnessComparatorProgress

namespace LongTails.Proofs.BrightnessFirstFitBlocks

lemma moving_comparison (r y reserve bad : ℕ → ℝ) (N : ℕ) (D l : ℝ)
    (hr : ∀ k ≤ N, 0 ≤ r k) (hs : ∀ k ≤ N, 0 ≤ reserve k) (hb : ∀ k ≤ N, 0 ≤ bad k)
    (hl : 0 ≤ l) (h0 : r 0 + reserve 0 ≤ D)
    (step : ∀ k < N, r k+reserve k ≤ D →
      (r (k+1)+reserve (k+1) ≤ y k+reserve k ∧ y k^2+l ≤ r k^2 ∧ bad (k+1) = bad k) ∨
      (r (k+1)+reserve (k+1) ≤ r k+reserve k ∧ bad (k+1) = bad k-1)) :
    r N + reserve N ≤ D ∧ N*l ≤ (r 0+reserve 0)^2+bad 0*l := by
  have bound (k : ℕ) (hk : k ≤ N) : r k+reserve k ≤ D ∧
      (k:ℝ)*l+(r k+reserve k)^2+bad k*l ≤ (r 0+reserve 0)^2+bad 0*l := by
    induction k with
    | zero => exact ⟨h0,by simp⟩
    | succ k ih =>
      have hk' : k ≤ N := by omega
      obtain ⟨hcap,henergy⟩ := ih hk'
      rcases step k (by omega) hcap with ⟨hm,hy',he⟩ | ⟨hm,he⟩
      · have hh : y k ≤ r k := by nlinarith only [hy',hl,hr k hk']
        refine ⟨by linarith only [hm,hh,hcap],?_⟩
        rw [Nat.cast_succ,he]
        nlinarith only [henergy,hy',mul_le_mul_of_nonneg_right hh (hs k hk'),
          pow_le_pow_left₀ (add_nonneg (hr _ hk) (hs _ hk)) hm 2]
      · refine ⟨hm.trans hcap,?_⟩
        rw [Nat.cast_succ,he]
        nlinarith only [henergy,pow_le_pow_left₀ (add_nonneg (hr _ hk) (hs _ hk)) hm 2]
  refine ⟨(bound N le_rfl).1,?_⟩
  nlinarith only [(bound N le_rfl).2,sq_nonneg (r N+reserve N),mul_nonneg (hb N le_rfl) hl]

end LongTails.Proofs.BrightnessFirstFitBlocks

namespace LongTails.Proofs.BrightnessReadoutTracking

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma track (w u : ℕ → E) (bad : ℕ → Bool) (N : ℕ) (M L J B Δ : ℝ)
    (hM : 0 ≤ M) (hJ : 0 ≤ J) (hΔ : 0 ≤ Δ)
    (hu : ∀ k ≤ N, ‖u k‖ ≤ 1)
    (hL : (∑ k ∈ Finset.range N, ‖u k-u (k+1)‖) ≤ L)
    (hB : (∑ k ∈ Finset.range N, if bad k then (1:ℝ) else 0) ≤ B)
    (hgood : ∀ k < N, bad k = false →
      ‖w (k+1)-M • u k‖^2 + Δ ≤ ‖w k-M • u k‖^2)
    (hbad : ∀ k < N, bad k = true → ‖w (k+1)-w k‖ ≤ J) :
    let D := ‖w 0‖+M+M*L+J*B
    ‖w N‖ ≤ D+M ∧ N*Δ ≤ D^2+B*Δ := by
  let I k : ℝ := if bad k then 1 else 0
  let C k := M*‖u k-u (k+1)‖+J*I k
  let rest (f : ℕ → ℝ) k := (∑ j ∈ Finset.range N, f j)-(∑ j ∈ Finset.range k, f j)
  have hI (k : ℕ) : 0 ≤ I k := by dsimp [I]; split_ifs <;> norm_num
  have hC (k : ℕ) : 0 ≤ C k := add_nonneg (mul_nonneg hM (norm_nonneg _)) (mul_nonneg hJ (hI k))
  have left (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) (k : ℕ) (hk : k ≤ N) : 0 ≤ rest f k := by
    apply sub_nonneg.mpr
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
    exact fun j _ _ => hf j
  have next (f : ℕ → ℝ) (k : ℕ) : rest f (k+1) = rest f k-f k := by
    simp only [rest,Finset.sum_range_succ]
    ring
  have huM (k : ℕ) (hk : k ≤ N) : ‖M • u k‖ ≤ M := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hM]
    simpa using mul_le_mul_of_nonneg_left (hu k hk) hM
  have start : ‖w 0-M • u 0‖+rest C 0 ≤ ‖w 0‖+M+M*L+J*B := by
    simp only [rest,C,Finset.sum_range_zero,Finset.sum_add_distrib,← Finset.mul_sum]
    linarith only [norm_sub_le (w 0) (M • u 0),huM 0 (by omega),
      mul_le_mul_of_nonneg_left hL hM,mul_le_mul_of_nonneg_left hB hJ]
  have move (k : ℕ) : ‖w (k+1)-M • u (k+1)‖ ≤
      ‖w (k+1)-M • u k‖+M*‖u k-u (k+1)‖ := by
    have H := norm_sub_le (w (k+1)-M • u k) (M • (u (k+1)-u k))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hM,norm_sub_rev (u (k+1)) (u k),smul_sub] at H
    convert H using 2
    abel
  obtain ⟨hr,hnum⟩ := BrightnessFirstFitBlocks.moving_comparison
    (fun k => ‖w k-M • u k‖) (fun k => ‖w (k+1)-M • u k‖) (rest C) (rest I)
    N _ Δ (fun _ _ => norm_nonneg _) (left C hC) (left I hI) hΔ start (by
      intro k hk _
      rw [next C,next I]
      cases h : bad k with
      | false =>
        have hi : I k = 0 := by simp [I,h]
        exact Or.inl ⟨by dsimp [C]; rw [hi]; linarith only [move k],hgood k hk h,by rw [hi,sub_zero]⟩
      | true =>
        have hi : I k = 1 := by simp [I,h]
        have H := norm_sub_le (w (k+1)-w k) (M • u k-w k)
        rw [norm_sub_rev (M • u k) (w k)] at H
        have he : w (k+1)-w k-(M • u k-w k) = w (k+1)-M • u k := by abel
        rw [he] at H
        exact Or.inr ⟨by dsimp [C]; rw [hi]; linarith only [move k,H,hbad k hk h],by rw [hi]⟩)
  have hdist := norm_add_le (w N-M • u N) (M • u N)
  rw [sub_add_cancel] at hdist
  simp only [rest,sub_self,add_zero] at hr
  refine ⟨by linarith only [hr,hdist,huM N le_rfl],?_⟩
  have hstart := pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (left C hC 0 (by omega))) start 2
  have hi : rest I 0 ≤ B := by simpa [rest,I] using hB
  linarith only [hnum,hstart,mul_le_mul_of_nonneg_right hi hΔ]

end LongTails.Proofs.BrightnessReadoutTracking

namespace LongTails.Proofs.BrightnessQuietOrientation

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open BrightnessFirstFitParameters
open BrightnessScaledCoordinates
open BrightnessTrajectoryBounds
open BrightnessFirstFitGuard
open BrightnessFirstFitWork
open BrightnessScaledForces
open BrightnessOrientation
open BrightnessStiffPhase

noncomputable def sign (p : Params) : ℝ := if p.P < 0 then -1 else 1

lemma monotone_ref (p : Params) (x : Images p) (c : Scales) : Antitone (ξ p x c) :=
  antitone_nat_of_succ_le (fun k => (reference_mono _ _ k).2)

lemma quiet_sign (p : Params) (x : Images p) (valid : spec.valid p) (G : Geometry p x)
    (k : ℕ) (hk : k ≤ (scales p).H) (quiet : bad p x (scales p) k = false) :
    let c := scales p
    |(path p x c.κ k).P - sign p * max c.δ (ξ p x c k)| ≤ 7*c.δ := by
  let c := scales p
  let S := path p x c.κ
  have h : Tuning p c := tuning p valid
  have env := envelope p x valid G
  have κ := h.κpos
  have J := h.Jpos
  have U := h.Upos
  have μ := h.μpos
  have δ := h.δpos
  have R : 0 < p.R := by linarith only [h.Rlarge]
  have H : (1:ℝ) ≤ c.H := by exact_mod_cast env.horizon
  have hW : 0 ≤ radius p c := by unfold radius; positivity
  have hε : 0 ≤ error p c := by unfold error; positivity
  have hg : 0 ≤ growth p c := by unfold growth; positivity
  obtain ⟨herr,_,hs⟩ := scale_remainders p valid
  change c.H*error p c ≤ c.δ/4 at herr
  change (‖p.readout‖/p.R^2)^2 + c.H*growth p c +
    2*(1+c.U*radius p c)/(p.μ*p.R^2)+(c.V*c.M/p.R)^2 ≤ c.δ^2 at hs
  have hinit := pow_le_pow_left₀ (abs_nonneg _) (initial_brightness p) 2
  rw [sq_abs] at hinit
  have hq : |vote p x c k| ≤ c.f := by
    have hh : ¬ c.κ*c.f ≤ |β p x c k| := by simpa only [bad,decide_eq_false_iff_not] using quiet
    rw [β,abs_mul,abs_of_nonneg κ.le,not_le,mul_lt_mul_iff_right₀ κ] at hh
    exact hh.le
  have hprod : |(S k).P*(S k).T| ≤ c.δ^2 := by
    have hrest := restoring_at p x G (S k) R (path_centered p x c.κ k)
    have hbound : |p.R^2*(S k).P*(S k).T| ≤ 2*(1+c.U*radius p c)/p.μ := by
      apply BrightnessComparatorProgress.small_force _ (vote p x c k) _ c.f _ _ hq
        (small_tunings h).2.2.2 μ
      have hh := mul_le_mul (readout_cap p x c h env k hk) (env.cap k hk).2.2.2 (norm_nonneg _) U.le
      exact hrest.trans (by linarith only [hh])
    have hscalar : |(S k).P*(S k).T| ≤ 2*(1+c.U*radius p c)/(p.μ*p.R^2) := by
      rw [div_mul_eq_div_div,le_div_iff₀ (sq_pos_of_pos R)]
      rw [mul_assoc,abs_mul,abs_of_nonneg (sq_nonneg p.R)] at hbound
      nlinarith only [hbound]
    nlinarith only [hscalar,hs,sq_nonneg (‖p.readout‖/p.R^2),sq_nonneg (c.V*c.M/p.R),
      mul_nonneg (by positivity : (0:ℝ) ≤ c.H) hg]
  apply close_on_quiet_step (fun j => (S j).P) (fun j => (S j).T) (β p x c)
    (perturbation p x c) (ξ p x c) k (sign p) c.δ
    (by unfold sign; split_ifs <;> norm_num) δ
    (by change 0 ≤ sign p * p.P; unfold sign; split_ifs <;> simp <;> linarith)
    (reference_mono _ _ k).1 (fun j hj => monotone_ref p x c hj) _ (fun j _ => beta_cap p x c h G j)
    (fun j hj => (env.growth j (hj.trans_le hk)).2.2.trans
      (by nlinarith only [herr,mul_le_mul_of_nonneg_right H hε])) (fun j _ => update_P p x c j) hprod
  intro j hj
  have hj' := hj.trans hk
  have HH := imbalance_shadow (fun i => (S i).P) (fun i => (S i).T) (β p x c)
    (perturbation p x c) j (growth p c) (fun i _ => (beta_cap p x c h G i).trans (by norm_num))
    (fun i _ => update_P p x c i) (fun i _ => update_T p x c i)
    (fun i hi => (env.growth i (hi.trans_le hj')).2.1)
  apply HH.trans
  change (initial p).T^2+j*growth p c ≤ c.δ^2
  have hh : (j:ℝ) ≤ c.H := by exact_mod_cast hj'
  nlinarith only [hs,hinit,sq_nonneg (c.V*c.M/p.R),
    (by positivity : 0 ≤ 2*(1+c.U*radius p c)/(p.μ*p.R^2)),mul_le_mul_of_nonneg_right hh hg]

lemma quiet_transport (p : Params) (x : Images p) (valid : spec.valid p) (G : Geometry p x)
    (N : ℕ) (hn : N ≤ (scales p).H) :
    let c := scales p
    ∃ u : ℕ → Features p.d, (∀ k, ‖u k‖ ≤ 1) ∧
      (∑ k ∈ Finset.range N, ‖u k-u (k+1)‖) ≤ c.V-6 ∧
      ∀ k < N, bad p x c k = false →
        ∀ i, 2*c.Γ ≤ ⟪u k,readout (path p x c.κ k) (x i)⟫ := by
  let c := scales p
  let r k := max c.δ (ξ p x c k)
  have h : Tuning p c := tuning p valid
  have hr (k : ℕ) : 0 < r k := h.δpos.trans_le (le_max_left _ _)
  have hm : Antitone r := fun i j hij => max_le_max_left _ (monotone_ref p x c hij)
  have hs : sign p ≠ 0 := by unfold sign; split_ifs <;> norm_num
  obtain ⟨u,hu,marg,travel⟩ := BrightnessFilterTransport.transport p x G h.Qne (sign p) hs r N hr
    (fun k _ => hm (Nat.le_succ k))
  refine ⟨u,hu,?_,?_⟩
  · rw [h.Veq,add_sub_cancel_left]
    have hhi : r 0 ≤ c.δ + |p.P| := max_le (by linarith only [abs_nonneg p.P])
      (by change |p.P| ≤ _; linarith only [h.δpos])
    have hlo : c.δ ≤ r N := le_max_left _ _
    have hratio : (r 0)/(r N) ≤ 1+|p.P|/c.δ := by
      rw [div_le_iff₀ (hr N)]
      have he : (1+|p.P|/c.δ)*c.δ = c.δ+|p.P| := by field_simp [h.δpos.ne']
      exact hhi.trans (he ▸ mul_le_mul_of_nonneg_left hlo (by have := h.δpos; positivity))
    have HH := Real.log_le_log (div_pos (hr 0) (hr N)) hratio
    rw [Real.log_div (hr 0).ne' (hr N).ne'] at HH
    apply Real.le_sqrt_of_sq_le
    exact travel.trans HH
  · intro k hk quiet i
    let s := path p x c.κ k
    have env := envelope p x valid G
    have hQ := (env.cap k (hk.le.trans hn)).2.2.1
    have hP := quiet_sign p x valid G k (hk.le.trans hn) quiet
    have hA : ‖contrast (x i)‖ ≤ p.J := by linarith only [(G.1 i).2,norm_nonneg (smooth (x i))]
    have hC : ‖smooth (x i)‖ ≤ p.J := by linarith only [(G.1 i).2,norm_nonneg (contrast (x i))]
    have hh := BrightnessComparatorProgress.row_drift (u k) (contrast (x i)) (smooth (x i))
      s.Q p.Q s.P (sign p*r k) p.J (|p.Q| * p.γ) (hu k) hA hC (marg k i)
    change |s.P-sign p*r k| ≤ 7*c.δ at hP
    have ht := h.δeq
    change 2*c.Γ ≤ ⟪u k,s.Q • contrast (x i)+s.P • smooth (x i)⟫
    nlinarith only [hh,h.margin,ht,h.δpos,mul_le_mul_of_nonneg_right hQ h.Jpos.le,
      mul_le_mul_of_nonneg_right hP h.Jpos.le,mul_nonneg h.δpos.le h.Jpos.le]

end LongTails.Proofs.BrightnessQuietOrientation

namespace LongTails.Proofs.BrightnessPrefixLength

open LongTails.Setups.BrightnessScaledTwoTap
open BrightnessFirstFitParameters
open BrightnessScaledCoordinates
open BrightnessTrajectoryBounds
open BrightnessFirstFitGuard
open BrightnessFirstFitWork
open BrightnessScaledForces
open BrightnessStiffPhase

lemma margin_le_radius (p : Params) (x : Images p) (G : Geometry p x) (c : Scales) (h : Tuning p c) :
    c.Γ ≤ c.U := by
  obtain ⟨u,hu,hm⟩ := G.2.2.2
  have hi := hm (0 : Fin p.n)
  have hA := real_inner_le_norm u (contrast (x 0))
  rw [hu,one_mul] at hA
  have hγ : p.γ ≤ p.J := by linarith only [hi,hA,(G.1 0).2,norm_nonneg (smooth (x 0))]
  nlinarith only [h.margin,h.Ueq,mul_le_mul_of_nonneg_left hγ (abs_nonneg p.Q),h.Γpos,h.Jpos,
    mul_nonneg h.Jpos.le (abs_nonneg p.P)]

lemma prefix_bound (p : Params) (x : Images p) (valid : spec.valid p) (G : Geometry p x)
    (N : ℕ) (hn : N ≤ (scales p).H) (pre : ∀ k < N, let c := scales p
      c.V*c.M/p.R < pole p x c k ∧ ‖(path p x c.κ k).w‖ ≤ c.V*c.M)
    (nonfit : ∀ k < N, ¬Fitted p x (physical p (path p x (scales p).κ k))) :
    let c := scales p
    ‖(path p x c.κ N).w‖ ≤ c.V*c.M ∧ (N:ℝ)*c.κ*c.Γ ≤ 2*p.n*c.V^2*c.M := by
  let c := scales p
  let S := path p x c.κ
  have h : Tuning p c := tuning p valid
  have env : Envelope p x c := envelope p x valid G
  have M := h.Mpos
  have κ := h.κpos
  have Γ := h.Γpos
  have U := h.Upos
  have npos : 0 < (p.n:ℝ) := by exact_mod_cast p.n.property
  have nn : 1 ≤ (p.n:ℝ) := by exact_mod_cast p.n.property
  have V : 0 < c.V := by linarith only [h.Vge]
  obtain ⟨u,hu,hL,hm⟩ := BrightnessQuietOrientation.quiet_transport p x valid G N hn
  have hB := count p x valid G N hn pre
  let Δ := c.κ*c.Γ*c.M/p.n
  have H := BrightnessReadoutTracking.track (fun k => (S k).w) u (bad p x c) N
    c.M (c.V-6) (c.κ*c.U) c.B Δ M.le (mul_nonneg κ.le U.le) (by dsimp [Δ]; positivity)
    (fun k _ => hu k) hL hB (by
      intro k hk quiet
      have hf : |vote p x c k| ≤ c.f := by
        have hh : ¬ c.κ*c.f ≤ |β p x c k| := by simpa only [bad,decide_eq_false_iff_not] using quiet
        rw [β,abs_mul,abs_of_nonneg κ.le,not_le,mul_lt_mul_iff_right₀ κ] at hh
        exact hh.le
      exact BrightnessFirstFitDescent.good p x G (S k) c h (u k) hf (hm k hk quiet)
        (readout_cap p x c h env k (hk.le.trans hn)) (pre k hk).2 (path_centered p x c.κ k)
        (nonfit k hk)) (by
      intro k hk _
      let g := votes p x (S k)
      change ‖(S k).w + c.κ • readout (S k) (mixture x g) - (S k).w‖ ≤ _
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg κ.le]
      apply mul_le_mul_of_nonneg_left _ κ.le
      exact (readout_force p x G (S k) g (fun _ => Real.sigmoid_nonneg _)).trans
        (by
          have hmul := mul_le_mul (readout_cap p x c h env k (hk.le.trans hn))
            (vote_mass p x (S k)).2 (vote_mass p x (S k)).1 U.le
          nlinarith only [hmul]))
  let D := ‖(S 0).w‖+c.M+c.M*(c.V-6)+(c.κ*c.U)*c.B
  change ‖(S N).w‖ ≤ D+c.M ∧ N*Δ ≤ D^2+c.B*Δ at H
  have Msize := (comparator_size h).1
  have hD : D+c.M ≤ c.V*c.M := by
    change ‖(initial p).w‖+c.M+c.M*(c.V-6)+(c.κ*c.U)*c.B+c.M ≤ _
    nlinarith only [Msize,initial_norm p,M.le]
  have hB0 : 0 ≤ c.B := by linarith only [h.Bge]
  have hD₀ : 0 ≤ D := by dsimp [D]; have := h.Vge; positivity
  have hDs := pow_le_pow_left₀ hD₀ (by linarith only [hD,M.le] : D ≤ c.V*c.M) 2
  have hBM : c.κ*c.U*c.B ≤ c.M := by linarith only [Msize,norm_nonneg p.readout]
  have hBs : c.B*Δ ≤ c.M^2 := by
    dsimp [Δ]
    rw [← mul_div_assoc,div_le_iff₀ npos]
    nlinarith only [mul_le_mul_of_nonneg_right (margin_le_radius p x G c h)
      (by positivity : 0 ≤ c.κ*c.B*c.M),mul_le_mul_of_nonneg_right hBM M.le,
      mul_le_mul_of_nonneg_left nn (sq_nonneg c.M)]
  refine ⟨H.1.trans hD,?_⟩
  have hvv : (1:ℝ) ≤ c.V^2 := by
    nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 6) h.Vge 2]
  have hnum : (N:ℝ)*Δ ≤ 2*c.V^2*c.M^2 := by
    nlinarith only [H.2,hDs,hBs,mul_le_mul_of_nonneg_right hvv (sq_nonneg c.M)]
  change (N:ℝ)*(c.κ*c.Γ*c.M/p.n) ≤ _ at hnum
  rw [← mul_div_assoc,div_le_iff₀ npos] at hnum
  exact le_of_mul_le_mul_right (a := c.M) (by nlinarith only [hnum]) M

end LongTails.Proofs.BrightnessPrefixLength
