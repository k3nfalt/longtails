import LongTails.Algorithms.WassersteinAcceleratedProximal
import LongTails.Proofs.WassersteinOracleGeometry
import LongTails.Proofs.WassersteinExecution

open MeasureTheory
open LongTails.Setups.WassersteinSmoothComposite
open LongTails.Algorithms.WassersteinAcceleratedProximal
open LongTails.Proofs.WassersteinAccelerationEnergy
open LongTails.Proofs.WassersteinCouplings
open LongTails.Proofs.WassersteinExtrapolationGeometry

namespace LongTails.Proofs.WassersteinPotential

noncomputable def energy {p : Public} (I : Instance p) (k : ℕ)
    (x previous : Distribution p.d) : ℝ :=
  (1 / p.L) * (((k : ℝ) + 1) / 2) ^ 2 * (objective I x - objective I I.minimizer) +
    (((k : ℝ) + 1) / 2) * squaredDistance x I.minimizer -
    ((((k : ℝ) + 1) / 2) - 1) * squaredDistance previous I.minimizer +
    (((k : ℝ) + 1) / 2) * ((((k : ℝ) + 1) / 2) - 1) * squaredDistance x previous

lemma energy_step {p : Params} {I : Instance p.toPublic}
    {O : OracleTemplate.Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (hL : 0 < p.L) (ξ : (j : ℕ) → O.Seed j) (k : ℕ) (hk : 1 ≤ k)
    (x previous u : Distribution p.d) (hxQ : x ∈ I.Q)
    (T : OptimalTransport x previous)
    (hevi : ∀ v ∈ I.Q,
      let y := extrapolate T.toTransport (((k : ℝ) - 1) / ((k : ℝ) + 2))
      (1 / p.L) * (objective I u - objective I v) ≤
        squaredDistance y v - squaredDistance u v - (1 / 2 : ℝ) * squaredDistance y u) :
    energy I (k + 1) u x ≤ energy I k x previous := by
  let s : ℝ := ((k : ℝ) + 1) / 2
  let t : ℝ := ((k : ℝ) + 2) / 2
  let β : ℝ := ((k : ℝ) - 1) / ((k : ℝ) + 2)
  let y := extrapolate T.toTransport β
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have hβ : 0 ≤ β := div_nonneg (by linarith) (by positivity)
  have hbt : t * β = s - 1 := by
    dsimp [t, β, s]
    field_simp [show (k : ℝ) + 2 ≠ 0 by positivity]
    ring
  have hrec : t * (t - 1) ≤ s ^ 2 := by dsimp [t, s]; nlinarith
  obtain ⟨B⟩ := WassersteinOracleGeometry.transport_exists h ξ x I.minimizer hxQ
  have hyz := extrapolation_distance_upper x previous I.minimizer y T B β hβ rfl
  have hyx := extrapolation_movement_upper x previous y T β rfl
  have hz := hevi I.minimizer h.minimizerFeasible
  have hx := hevi x hxQ
  have hscale : 2 * (1 / (2 * p.L)) = 1 / p.L := by ring
  have hz' : 2 * (1 / (2 * p.L)) * (objective I u - objective I I.minimizer) ≤
      squaredDistance y I.minimizer - squaredDistance u I.minimizer -
        (1 / 2 : ℝ) * squaredDistance y u := by simpa only [hscale] using hz
  have hx' : 2 * (1 / (2 * p.L)) *
      ((objective I u - objective I I.minimizer) - (objective I x - objective I I.minimizer)) ≤
      squaredDistance y x - squaredDistance u x - (1 / 2 : ℝ) * squaredDistance y u := by
    rw [hscale]
    convert hx using 1
    ring
  have hd := weighted_descent s t β (1 / (2 * p.L))
    (objective I u - objective I I.minimizer) (objective I x - objective I I.minimizer)
    (squaredDistance y I.minimizer) (squaredDistance y x)
    (squaredDistance u I.minimizer) (squaredDistance u x)
    (squaredDistance x I.minimizer) (squaredDistance previous I.minimizer)
    (squaredDistance x previous) ((1 / 2 : ℝ) * squaredDistance y u)
    ht (by positivity) (sub_nonneg.mpr (h.minimal x hxQ)) hrec hbt hz' hx' hyz hyx
  have hr : 0 ≤ t ^ 2 * ((1 / 2 : ℝ) * squaredDistance y u) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (squaredDistance_nonnegative y u))
  have hd' := hd.trans (sub_le_self _ hr)
  rw [hscale] at hd'
  convert hd' using 1 <;> simp only [energy, Nat.cast_add, Nat.cast_one, s, t]
  all_goals ring

lemma energy_gap_lower {p : Params} {I : Instance p.toPublic}
    {O : OracleTemplate.Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (ξ : (j : ℕ) → O.Seed j) (k : ℕ) (hk : 1 ≤ k)
    (x previous : Distribution p.d) (hx : x ∈ I.Q) :
    (1 / p.L) * (((k : ℝ) + 1) / 2) ^ 2 * (objective I x - objective I I.minimizer) ≤
      energy I k x previous := by
  obtain ⟨A⟩ := WassersteinOracleGeometry.transport_exists h ξ x previous hx
  obtain ⟨B⟩ := WassersteinOracleGeometry.transport_exists h ξ x I.minimizer hx
  have ht : (1 : ℝ) ≤ ((k : ℝ) + 1) / 2 := by
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hn := transport_energy_nonnegative x previous I.minimizer A B
    (((k : ℝ) + 1) / 2) ht
  dsimp [energy]
  linarith

lemma run_energy_bound {p : Params} {I : Instance p.toPublic}
    {O : OracleTemplate.Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (hL : 0 < p.L) (ξ : (j : ℕ) → O.Seed j)
    (R : ℕ → Query p.d → Reply p.d)
    (hR : ∀ n q, CorrectReply p.toPublic I q (R n q)) (n : ℕ) :
    let s := WassersteinExecution.run p.toPublic R (2 + 3 * n)
    s.phase = .transport ∧ s.steps = n + 1 ∧ s.current ∈ I.Q ∧
      energy I (n + 1) s.current s.previous ≤ p.R ^ 2 := by
  induction n with
  | zero =>
    obtain ⟨b, u, he, hu, hv⟩ := WassersteinExecution.forward_pair h hL ξ R hR 0 rfl
    have hz := hv I.minimizer h.minimizerFeasible
    change (1 / p.L) * (objective I u - objective I I.minimizer) ≤
      squaredDistance p.initial I.minimizer - squaredDistance u I.minimizer -
        (1 / 2 : ℝ) * squaredDistance p.initial u at hz
    have hn := squaredDistance_nonnegative p.initial u
    have hb : (1 / p.L) * (objective I u - objective I I.minimizer) +
        squaredDistance u I.minimizer ≤ p.R ^ 2 := by
      linarith [h.initialDistance]
    change WassersteinExecution.run p.toPublic R 2 =
      { phase := .transport, previous := p.initial, current := u, probe := b, steps := 1 } at he
    dsimp only
    rw [show 2 + 3 * 0 = 2 by omega, he]
    refine ⟨rfl, rfl, hu, ?_⟩
    simpa [energy] using hb
  | succ n ih =>
    obtain ⟨hphase, hsteps, hx, hb⟩ := ih
    obtain ⟨T, b, u, he, hu, hv⟩ := WassersteinExecution.triple_step h hL ξ R hR
      (2 + 3 * n) hphase hx
    have hv' : ∀ v ∈ I.Q,
        let y := extrapolate T.toTransport ((((n + 1 : ℕ) : ℝ) - 1) / (((n + 1 : ℕ) : ℝ) + 2))
        (1 / p.L) * (objective I u - objective I v) ≤
          squaredDistance y v - squaredDistance u v - (1 / 2 : ℝ) * squaredDistance y u := by
      simpa only [hsteps] using hv
    have hn := (energy_step h hL ξ (n + 1) (by omega) _ _ u hx T hv').trans hb
    dsimp only
    rw [show 2 + 3 * (n + 1) = (2 + 3 * n) + 3 by omega, he]
    refine ⟨rfl, ?_, hu, hn⟩
    simp only [hsteps]

lemma accuracy_from_energy (L R ε gap : ℝ) (n : ℕ)
    (hL : 0 < L) (hR : 0 ≤ R) (hε : 0 < ε)
    (hroot : 2 * R * Real.sqrt (L / ε) ≤ n)
    (hgap : (1 / L) * (((n : ℝ) + 2) / 2) ^ 2 * gap ≤ R ^ 2) : gap ≤ ε := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : 0 ≤ 2 * R * Real.sqrt (L / ε) := by positivity
  have hsq : (2 * R * Real.sqrt (L / ε)) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hs := Real.sq_sqrt (show 0 ≤ L / ε by positivity)
  have hs' : ε * Real.sqrt (L / ε) ^ 2 = L := by
    have he := (eq_div_iff hε.ne').mp hs
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq hε.le
  have he : ε * (2 * R * Real.sqrt (L / ε)) ^ 2 = 4 * L * R ^ 2 := by
    calc
      _ = 4 * R ^ 2 * (ε * Real.sqrt (L / ε) ^ 2) := by ring
      _ = _ := by rw [hs']; ring
  rw [he] at hm
  have hd : ((((n : ℝ) + 2) / 2) ^ 2 * gap) / L ≤ R ^ 2 := by
    convert hgap using 1
    ring
  have hd' := (div_le_iff₀ hL).mp hd
  by_contra hbad
  have hgt : ε < gap := lt_of_not_ge hbad
  have hp := mul_lt_mul_of_pos_right hgt (sq_pos_of_pos (by linarith : 0 < (n : ℝ) + 2))
  have hmore : ε * (n : ℝ) ^ 2 ≤ ε * ((n : ℝ) + 2) ^ 2 := by nlinarith
  nlinarith

lemma run_accuracy {p : Params} {I : Instance p.toPublic}
    {O : OracleTemplate.Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (hL : 0 < p.L) (hR : 0 ≤ p.R) (hε : 0 < p.ε) (ξ : (j : ℕ) → O.Seed j)
    (R : ℕ → Query p.d → Reply p.d)
    (hcorrect : ∀ n q, CorrectReply p.toPublic I q (R n q))
    (n : ℕ) (hn : 2 * p.R * Real.sqrt (p.L / p.ε) ≤ n) :
    (WassersteinExecution.run p.toPublic R (2 + 3 * n)).current ∈ I.Q ∧
      objective I (WassersteinExecution.run p.toPublic R (2 + 3 * n)).current -
        objective I I.minimizer ≤ p.ε := by
  obtain ⟨_, _, hx, hb⟩ := run_energy_bound h hL ξ R hcorrect n
  refine ⟨hx, ?_⟩
  have he := (energy_gap_lower h ξ (n + 1) (by omega) _ _ hx).trans hb
  apply accuracy_from_energy p.L p.R p.ε _ n hL hR hε hn
  convert he using 1
  simp only [Nat.cast_add, Nat.cast_one]
  ring

end LongTails.Proofs.WassersteinPotential
