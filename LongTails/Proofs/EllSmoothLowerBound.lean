import LongTails.Setups.HighDimensionalEllSmoothNonconvex
import LongTails.Proofs.EllSmoothSimulation
import LongTails.Proofs.CorruptedFirstOrderLowerBound
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate
open scoped BigOperators ENNReal

namespace LongTails.Proofs.EllSmoothHiding

open LongTails.Proofs.EllSmoothProfiles LongTails.Proofs.EllSmoothHard
open LongTails.Proofs.EllSmoothHardBounds LongTails.Proofs.EllSmoothSimulation
open LongTails.Proofs.AbcHardFunction (sel sel_apply)
open LongTails.Proofs.AbcHardOracle (Scale toUnit)
open LongTails.Proofs.SmoothConvexFiniteHiding
open LongTails.Proofs.FiniteSumNondualLowerHiding LongTails.Proofs.FiniteSumNondualLowerExposure
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound

open Classical

variable (S : Shape) {d n : ℕ}

def Hit (A : Method d) (s : A.State) (Sc : Scale) (x0 : Space d) (w : List (Fin d)) : Prop :=
  ∃ j : Fin (n + 1), ∃ π : Fin (n + 1) ↪ Fin d, List.ofFn π = w ∧
    0 < hits (largeSet (4 * rad S n) (1 / 4) (observation S A s Sc x0 j π)) (w.drop j.val)

lemma few_hits (A : Method d) (s : A.State) (Sc : Scale) (x0 : Space d)
    (hd : 2 ^ 56 * ((n : ℝ) + 1) ^ 6 / S.mu ^ 4 ≤ (d : ℝ)) :
    8 * (∑ w : CoordinateWords d n, if Hit (n := n) S A s Sc x0 w.val then (1 : ℝ) else 0) ≤
      Fintype.card (CoordinateWords d n) := by
  have hmu := S.hmu
  have hmu' := S.hmu'
  have hn1 := n1_ge n
  let X : ℝ := 2 ^ 52 * ((n : ℝ) + 1) ^ 4 / S.mu ^ 4
  let D : ℝ := d - (n + 1)
  have hr : (4 * rad S n) ^ 2 / (1 / 4) ^ 2 = X := by
    simp only [X, rad]
    field_simp; ring
  have hXpos : 0 < X := by simp only [X]; positivity
  have hXge : ((n : ℝ) + 1) ≤ X * ((n : ℝ) + 1) ^ 2 := by
    have h1 : (1 : ℝ) ≤ X := by
      simp only [X]
      rw [le_div_iff₀ (by positivity)]
      have : S.mu ^ 4 ≤ 1 := pow_le_one₀ hmu.le hmu'
      have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 4 := one_le_pow₀ hn1
      nlinarith
    nlinarith [mul_le_mul h1 (by nlinarith : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2) (by positivity)
      hXpos.le]
  have hroom : 8 * (((n : ℝ) + 1) ^ 2 * X) ≤ D := by
    have e : 2 ^ 56 * ((n : ℝ) + 1) ^ 6 / S.mu ^ 4 = 16 * (((n : ℝ) + 1) ^ 2 * X) := by
      simp only [X]
      field_simp; ring
    rw [e] at hd
    simp only [D]
    have hpos : 0 ≤ ((n : ℝ) + 1) ^ 2 * X := by positivity
    nlinarith
  have hD : 0 ≤ D :=
    (by positivity : (0 : ℝ) ≤ 8 * (((n : ℝ) + 1) ^ 2 * X)).trans hroom
  have hc := bounded_prefix_bad_count (d := d) (K := n + 1) (4 * rad S n) (1 / 4) D
    (by have := rad_pos S n; positivity) (by norm_num) hD (by simp only [D]; push_cast; linarith)
    Fin.val (fun j : Fin (n + 1) => j.isLt.le) (observation S A s Sc x0)
    (observation_prefix S A s Sc x0)
  let U := (distinctWords (n + 1) (Finset.univ : Finset (Fin d)))
  let B := U.filter (Hit (n := n) S A s Sc x0)
  have heq := subtype_indicator_sum U (Hit (n := n) S A s Sc x0)
  change (∑ w : CoordinateWords d n, if Hit (n := n) S A s Sc x0 w.val then (1 : ℝ) else 0) =
    (B.card : ℝ) at heq
  rw [heq]
  simp only [Fintype.card_fin, hr, Nat.cast_succ] at hc
  have hcnt : D * (B.card : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) * X * (U.card : ℝ) := by
    convert hc using 1
    apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
    ext w
    simp only [B, U, Finset.mem_filter, Hit]
  change 8 * (B.card : ℝ) ≤ Fintype.card (↥U)
  rw [Fintype.card_coe]
  have hm := mul_le_mul_of_nonneg_right hroom (Nat.cast_nonneg B.card : (0 : ℝ) ≤ B.card)
  have hx : 0 < ((n : ℝ) + 1) ^ 2 * X := by positivity
  apply (mul_le_mul_iff_right₀ hx).mp
  nlinarith only [hm, hcnt]

lemma miss_lower (A : Method d) (s : A.State) (Sc : Scale) (x0 : Space d)
    (w : CoordinateWords d n) (hh : ¬ Hit (n := n) S A s Sc x0 w.val) :
    Sc.a / Sc.lam / 2 ≤ ‖objGrad S Sc (coordinateEmbedding w) x0
      (A.output ((realStep S A Sc x0 (coordinateEmbedding w))^[n] s))‖ := by
  apply hard_output
  intro j hj i hi
  rw [sel_apply]
  apply not_largeSet_small _ _ _ hj
  intro hm
  exact hh ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w,
    by simpa only [coordinateEmbedding_labels] using (hits_drop_positive (coordinateEmbedding w)
      j.val _ i hi hm)⟩

end LongTails.Proofs.EllSmoothHiding

namespace LongTails.Proofs.EllSmoothLowerBound

open LongTails.Setups.EllSmoothNonconvex
open LongTails.Proofs.EllSmoothProfiles LongTails.Proofs.EllSmoothHard
open LongTails.Proofs.EllSmoothHardBounds LongTails.Proofs.EllSmoothSimulation
open LongTails.Proofs.EllSmoothHiding
open LongTails.Proofs.AbcHardOracle (Scale toUnit)
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound
open LongTails.Proofs.CorruptedFirstOrderAveraging

open Classical

abbrev HD := LongTails.Setups.HighDimensionalEllSmoothNonconvex.spec

lemma ell_pos (p : Params) (hp : HD.valid p) : 0 < p.ℓ p.ε := hp.1.2.2.1.2.2 p.ε hp.1.2.2.2.2

lemma ell_zero_le (p : Params) (hp : HD.valid p) : p.ℓ 0 ≤ p.ℓ p.ε :=
  hp.1.2.2.1.1 0 p.ε le_rfl hp.1.2.2.2.2.le

noncomputable def shape (p : Params) (hp : HD.valid p) : Shape where
  th := min (2 - p.ρ) (1 / 2)
  mu := p.ℓ 0 / p.ℓ p.ε
  hth := lt_min (by linarith [hp.2.1]) (by norm_num)
  hth' := min_le_right _ _
  hmu := div_pos hp.2.2.1 (ell_pos p hp)
  hmu' := (div_le_one (ell_pos p hp)).mpr (ell_zero_le p hp)

noncomputable def scale (p : Params) (hp : HD.valid p) : Scale :=
  ⟨512000 * p.ε ^ 2 / ((shape p hp).th * p.ℓ p.ε), 64000 * p.ε / ((shape p hp).th * p.ℓ p.ε),
    by have := (shape p hp).hth; have := ell_pos p hp; have := hp.1.2.2.2.2; positivity,
    by have := (shape p hp).hth; have := ell_pos p hp; have := hp.1.2.2.2.2; positivity⟩

lemma scale_ratio (p : Params) (hp : HD.valid p) :
    (scale p hp).a / (scale p hp).lam = 8 * p.ε := by
  have h1 := (shape p hp).hth
  have h2 := ell_pos p hp
  have h3 := hp.1.2.2.2.2
  simp only [scale]
  field_simp; ring

lemma scale_curv (p : Params) (hp : HD.valid p) :
    (scale p hp).a / (scale p hp).lam ^ 2 * (4000 / (shape p hp).th) = p.ℓ p.ε / 2 := by
  have h1 := (shape p hp).hth
  have h2 := ell_pos p hp
  have h3 := hp.1.2.2.2.2
  simp only [scale]
  field_simp; ring

lemma th_ge (p : Params) (hp : HD.valid p) : (2 - p.ρ) / 4 ≤ (shape p hp).th := by
  simp only [shape]
  have h0 := hp.1.1
  have h2 := hp.1.2.1
  rw [le_min_iff]
  constructor <;> linarith

lemma th_le (p : Params) (hp : HD.valid p) : (shape p hp).th ≤ 2 - p.ρ := min_le_left _ _

lemma class_scalar (p : Params) (hp : HD.valid p) (t : ℝ) (ht : 0 ≤ t) :
    p.ℓ p.ε / 2 * (min 1 (t ^ (2 - (shape p hp).th)) + (shape p hp).mu) ≤
      p.ℓ (8 * p.ε * t) := by
  have hmono := hp.1.2.2.1.1
  have hreg := hp.1.2.2.1.2.1
  have hε : 0 < p.ε := hp.1.2.2.2.2
  have h0 : 0 < p.ℓ 0 := hp.2.2.1
  have hle := ell_pos p hp
  have hthle : (shape p hp).th ≤ 2 - p.ρ := th_le p hp
  have hthhalf : (shape p hp).th ≤ 1 / 2 := (shape p hp).hth'
  have hg0 : 0 ≤ 8 * p.ε * t := by positivity
  have hmueq : (shape p hp).mu = p.ℓ 0 / p.ℓ p.ε := rfl
  have hmu : p.ℓ p.ε / 2 * (p.ℓ 0 / p.ℓ p.ε) = p.ℓ 0 / 2 := by field_simp
  have hmu2 : p.ℓ 0 ≤ p.ℓ (8 * p.ε * t) := hmono 0 (8 * p.ε * t) le_rfl hg0
  have hmain : p.ℓ p.ε * min 1 (t ^ (2 - (shape p hp).th)) ≤ p.ℓ (8 * p.ε * t) := by
    rcases le_total 1 (8 * t) with h8 | h8
    · have h1 : p.ℓ p.ε ≤ p.ℓ (8 * p.ε * t) := hmono _ _ hε.le (by nlinarith)
      have h2 : min 1 (t ^ (2 - (shape p hp).th)) ≤ 1 := min_le_left _ _
      nlinarith
    · rcases eq_or_lt_of_le ht with h0t | h0t
      · rw [← h0t, Real.zero_rpow (by linarith), min_eq_right zero_le_one, mul_zero]
        exact h0.le.trans (hmono 0 _ le_rfl (by simp))
      · have hg : 0 < 8 * p.ε * t := by positivity
        have hgle : 8 * p.ε * t ≤ p.ε := by nlinarith
        have hr := hreg (8 * p.ε * t) p.ε hg hgle
        have h8t0 : 0 < 8 * t := by positivity
        have hpow1 : t ^ (2 - (shape p hp).th) ≤ (8 * t) ^ (2 - (shape p hp).th) :=
          Real.rpow_le_rpow ht (by linarith) (by linarith)
        have hpow2 : (8 * t) ^ (2 - (shape p hp).th) ≤ (8 * t) ^ p.ρ :=
          Real.rpow_le_rpow_of_exponent_ge h8t0 h8 (by linarith)
        have he : (8 * p.ε * t) ^ p.ρ = (8 * t) ^ p.ρ * p.ε ^ p.ρ := by
          rw [show 8 * p.ε * t = (8 * t) * p.ε by ring, Real.mul_rpow h8t0.le hε.le]
        rw [he] at hr
        have hεp : 0 < p.ε ^ p.ρ := Real.rpow_pos_of_pos hε _
        have h3 : p.ℓ p.ε * (8 * t) ^ p.ρ ≤ p.ℓ (8 * p.ε * t) := by
          have : p.ℓ p.ε * (8 * t) ^ p.ρ * p.ε ^ p.ρ ≤ p.ℓ (8 * p.ε * t) * p.ε ^ p.ρ := by
            linarith
          exact le_of_mul_le_mul_right this hεp
        have hmin : min 1 (t ^ (2 - (shape p hp).th)) ≤ (8 * t) ^ p.ρ :=
          (min_le_right _ _).trans (hpow1.trans hpow2)
        have := mul_le_mul_of_nonneg_left hmin hle.le
        linarith
  rw [hmueq, mul_add, hmu]
  linarith

lemma instance_admissible (p : Params) (hp : HD.valid p) (n : ℕ)
    (hn : ((n : ℝ) + 1) * (2 ^ 26 * p.ε ^ 2) ≤ (2 - p.ρ) * p.Δ * p.ℓ p.ε)
    (π : Fin (n + 1) ↪ Fin p.d) :
    HD.admissible p (objective (shape p hp) (scale p hp) π p.x0)
      (oracle (objective (shape p hp) (scale p hp) π p.x0)) := by
  set S := shape p hp with hS
  set Sc := scale p hp with hSc
  have ha := Sc.ha
  have hl := Sc.hlam
  have hε := hp.1.2.2.2.2
  have hell := ell_pos p hp
  have hgr : gradient (objective S Sc π p.x0) = objGrad S Sc π p.x0 :=
    funext (objective_gradient S Sc π p.x0)
  refine ⟨fun x => ?_, ?_, fun x => ?_, fun x => ?_, fun _ _ _ => rfl⟩
  · rw [objective_gradient]; exact objective_hasGradientAt _ _ _ _ _
  · rw [hgr]
    exact fun x => (objGrad_hasFDerivAt S Sc π p.x0 x).differentiableAt
  · rw [hgr]
    have h1 := objGrad_fderiv_norm_le S Sc π p.x0 x
    have h2 := hgrad_class S π (toUnit Sc p.x0 x)
    have hnorm : ‖objGrad S Sc π p.x0 x‖ = 8 * p.ε * ‖hgrad S π (toUnit Sc p.x0 x)‖ := by
      unfold objGrad
      rw [norm_smul, Real.norm_of_nonneg (by positivity), hSc, scale_ratio p hp]
    rw [hnorm]
    have h3 := class_scalar p hp ‖hgrad S π (toUnit Sc p.x0 x)‖ (norm_nonneg _)
    have hcurv := scale_curv p hp
    have hc0 : 0 ≤ Sc.a / Sc.lam ^ 2 := by positivity
    calc ‖fderiv ℝ (objGrad S Sc π p.x0) x‖
        ≤ Sc.a / Sc.lam ^ 2 * ‖fderiv ℝ (hgrad S π) (toUnit Sc p.x0 x)‖ := h1
      _ ≤ Sc.a / Sc.lam ^ 2 * (4000 / S.th *
          (min 1 (‖hgrad S π (toUnit Sc p.x0 x)‖ ^ (2 - S.th)) + S.mu)) :=
          mul_le_mul_of_nonneg_left h2 hc0
      _ = p.ℓ p.ε / 2 * (min 1 (‖hgrad S π (toUnit Sc p.x0 x)‖ ^ (2 - S.th)) + S.mu) := by
          rw [← mul_assoc, hSc, hS, scale_curv p hp]
      _ ≤ _ := h3
  · have h0 : toUnit Sc p.x0 p.x0 = 0 := by simp [toUnit]
    have hv0 := hval_zero_le S π (d := p.d)
    have hv1 := hval_ge S π (toUnit Sc p.x0 x)
    have hth := th_ge p hp
    have hthpos := S.hth
    have hn1 := n1_pos n
    have hbound : Sc.a * (20 * ((n : ℝ) + 1)) ≤ p.Δ := by
      have ea : Sc.a = 512000 * p.ε ^ 2 / (S.th * p.ℓ p.ε) := rfl
      rw [ea, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have h4 : (2 - p.ρ) * p.Δ * p.ℓ p.ε ≤ 4 * (S.th * (p.Δ * p.ℓ p.ε)) := by
        have hΔℓ : 0 ≤ p.Δ * p.ℓ p.ε := mul_nonneg hp.1.2.2.2.1 hell.le
        nlinarith
      nlinarith [sq_nonneg p.ε, mul_nonneg hn1.le (sq_nonneg p.ε)]
    simp only [objective, h0]
    nlinarith

lemma exists_failure (p : Params) (hp : HD.valid p) (A : Method p.d) (N : ℕ)
    (hN : N ≤ ⌊(2 - p.ρ) * p.Δ * p.ℓ p.ε / (2 ^ 27 * p.ε ^ 2)⌋₊) :
    ∃ (f : Space p.d → ℝ) (O : Oracle (Space p.d) (ℝ × Space p.d)),
      HD.admissible p f O ∧
      ¬HD.successful p f (fun z : A.Seed × ((j : ℕ) → O.Seed j) =>
        execute O A (fun _ => N) z.1 z.2) ⟨(A.law : Measure _).prod (O.law : Measure _),
          inferInstance⟩ := by
  have hε := hp.1.2.2.2.2
  have hell := ell_pos p hp
  set S := shape p hp with hS
  set Sc := scale p hp with hSc
  let W := CoordinateWords p.d N
  have hfl : (N : ℝ) ≤ (2 - p.ρ) * p.Δ * p.ℓ p.ε / (2 ^ 27 * p.ε ^ 2) := by
    have h1 : (N : ℝ) ≤ (⌊(2 - p.ρ) * p.Δ * p.ℓ p.ε / (2 ^ 27 * p.ε ^ 2)⌋₊ : ℕ) := by
      exact_mod_cast hN
    refine h1.trans (Nat.floor_le ?_)
    have h2 := hp.2.2.2.1
    have : (0 : ℝ) ≤ (2 - p.ρ) * p.Δ * p.ℓ p.ε := by nlinarith [sq_nonneg p.ε]
    positivity
  rw [le_div_iff₀ (by positivity)] at hfl
  have hreg := hp.2.2.2.1
  have hgap : ((N : ℝ) + 1) * (2 ^ 26 * p.ε ^ 2) ≤ (2 - p.ρ) * p.Δ * p.ℓ p.ε := by
    nlinarith
  have hdim : 2 ^ 56 * ((N : ℝ) + 1) ^ 6 / S.mu ^ 4 ≤ (p.d : ℝ) := by
    have h3 := hp.2.2.2.2
    have hmu : S.mu = p.ℓ 0 / p.ℓ p.ε := rfl
    have h0 := hp.2.2.1
    have hN1 : ((N : ℝ) + 1) ≤
        (⌊(2 - p.ρ) * p.Δ * p.ℓ p.ε / (2 ^ 27 * p.ε ^ 2)⌋₊ : ℝ) + 1 := by
      have : (N : ℝ) ≤ (⌊(2 - p.ρ) * p.Δ * p.ℓ p.ε / (2 ^ 27 * p.ε ^ 2)⌋₊ : ℕ) := by
        exact_mod_cast hN
      linarith
    have hN0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    have hpow := pow_le_pow_left₀ hN0 hN1 6
    refine le_trans ?_ h3
    have e : 2 ^ 56 * ((N : ℝ) + 1) ^ 6 / S.mu ^ 4 =
        2 ^ 56 * ((N : ℝ) + 1) ^ 6 * (p.ℓ p.ε / p.ℓ 0) ^ 4 := by
      rw [hmu]; field_simp
    rw [e]
    have hq : (0 : ℝ) ≤ (p.ℓ p.ε / p.ℓ 0) ^ 4 := by positivity
    nlinarith
  have hnd : N + 1 ≤ p.d := by
    have hmu4 : S.mu ^ 4 ≤ 1 := pow_le_one₀ S.hmu.le S.hmu'
    have hmupos : 0 < S.mu ^ 4 := pow_pos S.hmu 4
    have h1 : ((N : ℝ) + 1) ≤ 2 ^ 56 * ((N : ℝ) + 1) ^ 6 / S.mu ^ 4 := by
      rw [le_div_iff₀ hmupos]
      have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith
      have h6 : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ 6 := by
        calc ((N : ℝ) + 1) = ((N : ℝ) + 1) ^ 1 := (pow_one _).symm
          _ ≤ ((N : ℝ) + 1) ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
      nlinarith
    have : ((N : ℝ) + 1) ≤ (p.d : ℝ) := h1.trans hdim
    exact_mod_cast this
  let f (w : W) := objective S Sc (coordinateEmbedding w) p.x0
  let B (w : W) := {z : A.Seed × (ℕ → Unit) |
    4 * p.ε ≤ ‖gradient (f w) (execute (oracle (f w)) A (fun _ => N) z.1 z.2)‖}
  let Q : Measure (ℕ → Unit) := Measure.dirac (fun _ => ())
  let P : Measure (A.Seed × (ℕ → Unit)) := (A.law : Measure _).prod Q
  have hc : 0 < Fintype.card W := coordinateWords_card_pos p.d N hnd
  have hw (z : A.Seed × (ℕ → Unit)) :
      (Fintype.card W : ℝ) / 2 ≤ ∑ w, if z ∈ B w then (1 : ℝ) else 0 := by
    let st := A.initial z.1
    let bad (w : W) := Hit (n := N) S A st Sc p.x0 w.val
    have hbad := few_hits S A st Sc p.x0 hdim
    change 8 * (∑ w : W, if bad w then (1 : ℝ) else 0) ≤ Fintype.card W at hbad
    have hpoint (w : W) : 1 ≤ (if bad w then (1 : ℝ) else 0) + (if z ∈ B w then (1 : ℝ) else 0) := by
      by_cases hh : bad w
      · simp [hh]; split <;> norm_num
      · have hl := miss_lower S A st Sc p.x0 w hh
        have hratio : Sc.a / Sc.lam = 8 * p.ε := scale_ratio p hp
        rw [hratio] at hl
        have hz : z ∈ B w := by
          change 4 * p.ε ≤ ‖gradient (f w) (execute (oracle (f w)) A (fun _ => N) z.1 z.2)‖
          erw [exact_output S A z.1 p.x0 Sc (coordinateEmbedding w) z.2, objective_gradient]
          linarith
        simp [hh, hz]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hpoint w)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at hs
    linarith
  have : IsProbabilityMeasure Q :=
    inferInstanceAs (IsProbabilityMeasure (Measure.dirac (fun _ : ℕ => ())))
  have : IsProbabilityMeasure P :=
    inferInstanceAs (IsProbabilityMeasure ((A.law : Measure A.Seed).prod Q))
  obtain ⟨w, hw⟩ := some_bad_set P B hc hw
  refine ⟨f w, oracle (f w), instance_admissible p hp N hgap _, ?_⟩
  intro hs
  obtain ⟨-, hint, hle⟩ := hs
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun z => ‖gradient (f w) (execute (oracle (f w)) A (fun _ => N) z.1 z.2)‖)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hint (4 * p.ε)
  have hreal : (1 / 4 : ℝ) < P.real (B w) := by
    have h1 : P (B w) ≠ ⊤ := measure_ne_top _ _
    have h2 := (ENNReal.toReal_lt_toReal (by norm_num) h1).mpr hw
    have h3 : ((1 / 4 : ℝ≥0∞)).toReal = 1 / 4 := by norm_num
    rw [h3] at h2
    exact h2
  have hB : P.real (B w) = P.real {z : A.Seed × (ℕ → Unit) |
      4 * p.ε ≤ ‖gradient (f w) (execute (oracle (f w)) A (fun _ => N) z.1 z.2)‖} := rfl
  rw [hB] at hreal
  have hfin : 4 * p.ε * P.real {z : A.Seed × (ℕ → Unit) |
      4 * p.ε ≤ ‖gradient (f w) (execute (oracle (f w)) A (fun _ => N) z.1 z.2)‖} ≤ p.ε :=
    hmark.trans hle
  nlinarith

end LongTails.Proofs.EllSmoothLowerBound
