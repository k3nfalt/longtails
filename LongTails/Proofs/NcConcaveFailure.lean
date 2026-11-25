import LongTails.Proofs.NcConcaveSecret
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.NcConcaveFailure

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcavePsi
open LongTails.Proofs.NcConcavePartTwo LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveBlock
open LongTails.Proofs.NcConcaveModel LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveEmbed LongTails.Proofs.NcConcaveValue
open LongTails.Proofs.NcConcaveProx
open LongTails.Setups.StochasticNonconvexConcaveMinimax

variable {n m : ℕ}

lemma continuous_nu' : Continuous nu :=
  continuous_iff_continuousAt.2 fun x => (nu_hasDerivAt x).continuousAt

lemma continuous_rr' : Continuous rr :=
  continuous_iff_continuousAt.2 fun x => (rr_hasDerivAt x).continuousAt

lemma continuous_q (i : Fin n) : Continuous (fun u : Fin (n + 1) → ℝ => q u i) := by
  unfold q
  exact (continuous_nu'.comp (continuous_apply _)).mul
    (continuous_const.sub (continuous_nu'.comp (continuous_apply _)))

lemma continuous_nrm : Continuous (fun u : Fin (n + 1) → ℝ => nrm u) := by
  unfold nrm sq2
  exact (continuous_const.add (continuous_finsetSum _ fun i _ => (continuous_q i).pow 2)).sqrt

lemma continuous_rho (i : Fin n) : Continuous (fun u : Fin (n + 1) → ℝ => rho u i) := by
  unfold rho
  exact (continuous_q i).div continuous_nrm (fun u => (nrm_pos u).ne')

lemma continuous_psi : Continuous (fun c : (Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
    psi c.1 c.2.1 c.2.2) := by
  have hu : Continuous (fun c : (Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => c.1) := continuous_fst
  have ha : Continuous (fun c : (Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => c.2.1) :=
    continuous_fst.comp continuous_snd
  have hb : Continuous (fun c : (Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => c.2.2) :=
    continuous_snd.comp continuous_snd
  have hH : Continuous (fun c : (Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => hpart c.1) := by
    unfold hpart
    refine ((continuous_const.mul ((continuous_apply 0).comp hu)).sub
      (continuous_const.mul (continuous_finsetSum _ fun j _ =>
        continuous_nu'.comp ((continuous_apply _).comp hu)))).add
      (continuous_const.mul (continuous_finsetSum _ fun j _ =>
        (continuous_rr'.comp ((continuous_apply _).comp hu)).pow 2))
  unfold psi
  refine ((((hH.add (continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (((continuous_apply i).comp ha).sub ((continuous_rho i).comp hu)).pow 2))).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp hb).sub (continuous_rr'.comp ((continuous_apply _).comp hu))).pow 2))).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp ha).pow 2))).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hb).pow 2))).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp ha).sub (((continuous_apply i).comp hb).div_const 2)).pow 2))

lemma continuous_phiW {d : ℕ} (C : Coords d n) (s ℓ : ℝ) : Continuous (phiW C s ℓ) := by
  have hs : Continuous (fun x : Prim d => (selU C s x, selA C s x, selB C s x)) := by
    refine (continuous_pi fun j => ?_).prodMk ((continuous_pi fun i => ?_).prodMk (continuous_pi fun i => ?_))
    all_goals exact (PiLp.continuous_apply 2 (fun _ : Fin 2 × Fin d => ℝ) _).div_const s
  unfold phiW
  exact continuous_const.mul (continuous_psi.comp hs)

lemma continuous_blockSq {d : ℕ} (b : Fin 2) : Continuous (fun x : Prim d => blockSq x b) := by
  unfold blockSq
  exact continuous_finsetSum _ fun i _ => (PiLp.continuous_apply 2 _ _).pow 2

lemma primBall_compact {d : ℕ} (RU RA : ℝ) : IsCompact (primBall (d := d) RU RA) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le (continuous_blockSq 0) continuous_const).inter
      (isClosed_le (continuous_blockSq 1) continuous_const)
  · apply (Metric.isBounded_closedBall (x := (0 : Prim d)) (r := Real.sqrt (RU ^ 2 + RA ^ 2))).subset
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Real.le_sqrt (norm_nonneg _) (by positivity), norm_sq_prim]
    linarith [hx.1, hx.2]

lemma primBall_convex {d : ℕ} (RU RA : ℝ) : Convex ℝ (primBall (d := d) RU RA) := by
  intro x hx z hz a b ha hb hab
  have := primBall_segment hx hz b hb (by linarith)
  convert this using 1
  rw [show a = 1 - b by linarith]
  module

lemma zero_mem_primBall {d : ℕ} (RU RA : ℝ) : (0 : Prim d) ∈ primBall RU RA := by
  constructor <;> simp [blockSq] <;> positivity

lemma norm_le_of_primBall {d : ℕ} {RU RA : ℝ} {x : Prim d} (hx : x ∈ primBall RU RA) :
    ‖x‖ ≤ Real.sqrt (RU ^ 2 + RA ^ 2) := by
  rw [Real.le_sqrt (norm_nonneg _) (by positivity), norm_sq_prim]; linarith [hx.1, hx.2]

lemma fhat_continuous_x {d : ℕ} {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (y : Dual d) : Continuous (fun x => fhat θ τ W s ℓ x y) :=
  continuous_iff_continuousAt.2 fun x =>
    (fhat_hasGradientAt_x hθ hθ1 hτ W hs hℓ x y).differentiableAt.continuousAt

lemma fhat_continuous_y {d : ℕ} {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (x : Prim d) : Continuous (fhat θ τ W s ℓ x) :=
  continuous_iff_continuousAt.2 fun y =>
    (fhat_hasGradientAt_y hθ hθ1 hτ W hs hℓ x y).differentiableAt.continuousAt

lemma value_bdd {d : ℕ} {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (x : Prim d) (R : ℝ) :
    BddAbove (fhat θ τ W s ℓ x '' Metric.closedBall 0 R) :=
  (isCompact_closedBall 0 R).bddAbove_image (fhat_continuous_y hθ hθ1 hτ W hs hℓ x).continuousOn

lemma value_lsc {d : ℕ} {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (R : ℝ) :
    LowerSemicontinuous (fun x => sSup (fhat θ τ W s ℓ x '' Metric.closedBall 0 R)) := by
  have he : (fun x => sSup (fhat θ τ W s ℓ x '' Metric.closedBall 0 R)) =
      fun x => ⨆ y : Metric.closedBall (0 : Dual d) R, fhat θ τ W s ℓ x y := by
    funext x; rw [sSup_image']
  rw [he]
  apply lowerSemicontinuous_ciSup
  · intro x
    rw [← Set.image_eq_range]
    exact value_bdd hθ hθ1 hτ W hs hℓ x R
  · intro y
    exact (fhat_continuous_x hθ hθ1 hτ W hs hℓ y.1).lowerSemicontinuous

lemma parallelogram_mid {d : ℕ} (z w x : Prim d) :
    ‖(1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w - x‖ ^ 2 =
      ‖z - x‖ ^ 2 / 2 + ‖w - x‖ ^ 2 / 2 - ‖z - w‖ ^ 2 / 4 := by
  have e1 : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w - x = (1 / 2 : ℝ) • ((z - x) + (w - x)) := by module
  have e2 : z - w = (z - x) - (w - x) := by abel
  rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h := parallelogram_law_with_norm ℝ (z - x) (w - x)
  rw [← e2] at h
  linarith [h]

theorem value_midpoint {d : ℕ} {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (W : Word d n m)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) (R : ℝ) (hR : 0 ≤ R) (z w : Prim d)
    (hm : blockSq ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) 1 ≤ (2 * s) ^ 2) :
    sSup (fhat θ τ W s ℓ ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) '' Metric.closedBall 0 R) ≤
      sSup (fhat θ τ W s ℓ z '' Metric.closedBall 0 R) / 2 +
        sSup (fhat θ τ W s ℓ w '' Metric.closedBall 0 R) / 2 + ℓ * cF 2 * ‖z - w‖ ^ 2 / 4 := by
  have hne : (Metric.closedBall (0 : Dual d) R).Nonempty := ⟨0, by simp [hR]⟩
  apply csSup_le (hne.image _)
  rintro _ ⟨y, hy, rfl⟩
  have h1 := fhat_midpoint hθ hθ1 hτ W hs hℓ z w y hm
  have h2 : fhat θ τ W s ℓ z y ≤ sSup (fhat θ τ W s ℓ z '' Metric.closedBall 0 R) :=
    le_csSup (value_bdd hθ hθ1 hτ W hs hℓ z R) ⟨y, hy, rfl⟩
  have h3 : fhat θ τ W s ℓ w y ≤ sSup (fhat θ τ W s ℓ w '' Metric.closedBall 0 R) :=
    le_csSup (value_bdd hθ hθ1 hτ W hs hℓ w R) ⟨y, hy, rfl⟩
  linarith

theorem stationarity_lower (q : Params) (W : Word q.d n m) {θ τ s ℓ η : ℝ}
    (hs : 0 < s) (hRA : radiusAB q = 2 * s) (hℓ : 0 < ℓ) (hL : q.L = 6 * (ℓ * cF 2))
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτα : alpha m ≤ τ) (hτ2 : τ ≤ 2)
    (hRU0 : 0 < radiusU q) (hRU : 256 * (n + 1) * s ^ 2 ≤ radiusU q ^ 2)
    (hsmall : cδ / 3 * ℓ / (2 * q.L) + θ / 2 ≤ 1 / 4)
    (hη : ℓ * s ^ 2 * (θ * closeBound n m (radiusU q / s) (q.D / 2 / s)) ≤ η)
    (hηL : 32 * q.L * η ≤ (cδ / 6 * ℓ * s) ^ 2)
    (hD : 8 * (s * (m + 1)) ^ 2 ≤ (q.D / 2) ^ 2) (hD0 : 0 < q.D)
    (x : Prim q.d) (hx : |x (0, W.πU (Fin.last n))| ≤ θ / 2 * s ∨
      2 * Real.sqrt (radiusU q ^ 2 + (2 * s) ^ 2) ≤ ‖x‖) :
    cδ / 6 * ℓ * s ≤ stationarity (fhat θ τ W s ℓ) x := by
  have hτ : 0 < τ := lt_of_lt_of_le (alpha_pos m) hτα
  have hcF : 0 < cF 2 := by unfold cF cP; norm_num
  have hLpos : 0 < q.L := by rw [hL]; positivity
  set f := fhat θ τ W s ℓ
  set X := primalSet q
  have hXe : X = primBall (radiusU q) (2 * s) := by
    simp only [X, primalSet, primBall, hRA]
  have hcomp : IsCompact X := by rw [hXe]; exact primBall_compact _ _
  have hXne : X.Nonempty := ⟨0, by rw [hXe]; exact zero_mem_primBall _ _⟩
  have hdual : dualSet q = Metric.closedBall 0 (q.D / 2) := rfl
  have hval : ∀ z, value f z = sSup (f z '' Metric.closedBall 0 (q.D / 2)) := fun z => rfl
  have hobj : LowerSemicontinuous (fun z => value f z + q.L * ‖z - x‖ ^ 2) := by
    have h1 := value_lsc hθ hθ1 hτ W hs hℓ.le (q.D / 2)
    have h2 : Continuous (fun z : Prim q.d => q.L * ‖z - x‖ ^ 2) := by fun_prop
    exact h1.add h2.lowerSemicontinuous
  obtain ⟨p1, hp1X, hp1min⟩ := (hobj.lowerSemicontinuousOn X).exists_isMinOn hXne hcomp
  have hprox_ne : (proxSet f x).Nonempty :=
    ⟨p1, hp1X, fun z hz => (isMinOn_iff.mp hp1min) z hz⟩
  have key : ∀ p ∈ proxSet f x, cδ / 6 * ℓ * s ≤ 2 * q.L * ‖x - p‖ := by
    intro p hp
    have hpX : p ∈ primBall (radiusU q) (2 * s) := by rw [← hXe]; exact hp.1
    rcases hx with hxs | hfar
    · -- coordinate small: compare with the prox point of the base value
      have hphi : Continuous (fun z => phiW W.coords s ℓ z + q.L * ‖z - x‖ ^ 2) := by
        have := continuous_phiW (n := n) W.coords s ℓ
        fun_prop
      obtain ⟨p0, hp0X, hp0min⟩ := hcomp.exists_isMinOn hXne hphi.continuousOn
      have hp0X' : p0 ∈ primBall (radiusU q) (2 * s) := by rw [← hXe]; exact hp0X
      have hmin0 : ∀ z ∈ primBall (radiusU q) (2 * s),
          phiW W.coords s ℓ p0 + q.L * ‖p0 - x‖ ^ 2 ≤ phiW W.coords s ℓ z + q.L * ‖z - x‖ ^ 2 :=
        fun z hz => (isMinOn_iff.mp hp0min) z (by rw [hXe]; exact hz)
      have h3 := part_three W.coords hs hℓ hLpos hRU hRU0 hsmall x hxs p0 hp0X' hmin0
      have hXc : Convex ℝ X := by rw [hXe]; exact primBall_convex _ _
      have hclose : ∀ z ∈ X, |(value f z + q.L * ‖z - x‖ ^ 2) -
          (phiW W.coords s ℓ z + q.L * ‖z - x‖ ^ 2)| ≤ η := by
        intro z hz
        have := Vf_close W hs hℓ.le hθ hθ1 hτα hτ2 hRU0.le hη hD hD0.le z (by rw [← hXe]; exact hz)
        simp only [Vf] at this
        rw [hval z, add_sub_add_right_eq_sub]
        exact this
      have hstrong : ∀ z ∈ X, ∀ w ∈ X,
          value f ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) + q.L * ‖(1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w - x‖ ^ 2 ≤
            (value f z + q.L * ‖z - x‖ ^ 2) / 2 + (value f w + q.L * ‖w - x‖ ^ 2) / 2 -
              q.L / 8 * ‖z - w‖ ^ 2 := by
        intro z hz w hw
        have hmX : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w ∈ X := hXc hz hw (by norm_num) (by norm_num) (by norm_num)
        rw [hXe] at hmX
        have hv := value_midpoint hθ hθ1 hτ W hs hℓ.le (q.D / 2) (by linarith) z w hmX.2
        have hpar := parallelogram_mid z w x
        rw [hval, hval, hval, hpar]
        have e : ℓ * cF 2 = q.L / 6 := by rw [hL]; ring
        rw [e] at hv
        have hzw := sq_nonneg ‖z - w‖
        nlinarith
      have happ := approx_prox hXc hLpos hclose hstrong hp0X hp.1
        (fun z hz => (isMinOn_iff.mp hp0min) z hz) (fun z hz => hp.2 z hz)
      have hd1 : (2 * q.L * ‖p0 - p‖) ^ 2 ≤ (cδ / 6 * ℓ * s) ^ 2 := by
        have : (2 * q.L * ‖p0 - p‖) ^ 2 = 4 * q.L ^ 2 * ‖p0 - p‖ ^ 2 := by ring
        rw [this]
        have h8 : q.L * ‖p0 - p‖ ^ 2 ≤ 8 * η := by rwa [le_div_iff₀ hLpos, mul_comm] at happ
        nlinarith
      have hd2 : 2 * q.L * ‖p0 - p‖ ≤ cδ / 6 * ℓ * s := by
        have h0 : 0 ≤ cδ / 6 * ℓ * s := by unfold cδ; positivity
        exact (pow_le_pow_iff_left₀ (by positivity) h0 (by norm_num)).mp hd1
      have htri : ‖x - p0‖ ≤ ‖x - p‖ + ‖p - p0‖ := norm_sub_le_norm_sub_add_norm_sub x p p0
      have hsym : ‖p - p0‖ = ‖p0 - p‖ := norm_sub_rev _ _
      nlinarith
    · have hpn := norm_le_of_primBall hpX
      have h1 : ‖x‖ - ‖p‖ ≤ ‖x - p‖ := norm_sub_norm_le x p
      have h2 : 2 * s ≤ Real.sqrt (radiusU q ^ 2 + (2 * s) ^ 2) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith [sq_nonneg (radiusU q)]
      have h3 : 2 * s ≤ ‖x - p‖ := by linarith
      have h4 : cδ / 6 * ℓ ≤ 2 * q.L * 2 := by
        have hc1 : (1 : ℝ) ≤ cF 2 := by unfold cF cP; norm_num
        rw [hL]; unfold cδ; nlinarith [mul_le_mul_of_nonneg_left hc1 hℓ.le]
      nlinarith
  unfold stationarity
  by_contra hcon
  push Not at hcon
  have hlt : Metric.infDist x (proxSet f x) < cδ / 6 * ℓ * s / (2 * q.L) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨p, hp, hpd⟩ := (Metric.infDist_lt_iff hprox_ne).mp hlt
  have := key p hp
  rw [dist_eq_norm] at hpd
  rw [lt_div_iff₀ (by positivity)] at hpd
  linarith

end LongTails.Proofs.NcConcaveFailure
