import LongTails.Proofs.OnlineMetricBasics
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ}

def BandOK (Λ : BandLearner d) : Prop :=
  (∀ i, bandLo d ≤ Λ.φ i ∧ Λ.φ i ≤ bandHi) ∧ 0 ≤ Λ.G

def CutsOK (w b : Fin d → ℝ) (cuts : List (Fin d → ℝ)) : Prop :=
  ∀ a ∈ cuts, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ 4 * d ∧ ∑ i, a i * (1 / w i / (2 * b i)) ≤ 1

noncomputable def kappaRoot (μ : ℝ) : ℝ := Real.sqrt (1 / μ)

noncomputable def lossCap (d : ℕ) (μ : ℝ) : ℝ := 17 * d * kappaRoot μ

noncomputable def runCap (d : ℕ) (μ : ℝ) : ℝ := 8 * d * kappaRoot μ

noncomputable def logTwo (d : ℕ) : ℝ := Real.logb 2 (2 * d)

def prevSteps (s : Core d) : ℕ :=
  match s.prev with
  | some R => R.steps
  | none => 0

def prevSeg (s : Core d) : ℕ :=
  match s.prev with
  | some R => R.seg
  | none => s.seg

def LearnerLedger (D F : ℝ) (u : Fin d → ℝ) (κr : ℝ) (Λ : BandLearner d) (X X' : ℝ)
    (n : ℕ) : Prop :=
  0 ≤ X ∧ X - X' ≤ learnerPotential D u Λ ∧ Λ.G ≤ F * X ∧ X' ≤ 12 * κr * n

section

variable (f : EuclideanSpace ℝ (Fin d) → ℝ) (w : Fin d → ℝ) (μ fstar : ℝ)
  (x0 : EuclideanSpace ℝ (Fin d)) (b0 : Fin d → ℝ)

def PrevOK (s : Core d) : Prop :=
  match s.prev with
  | none => s.ep = 0
  | some R =>
      1 ≤ s.ep ∧ R.fs = f R.xs ∧ s.fs - fstar ≤ (R.fs - fstar) / 2 ∧
      (∀ i, bandLo d ≤ R.φ i ∧ R.φ i ≤ bandHi) ∧ CutsOK w R.b R.cuts ∧
      (∀ i, 1 / w i ≤ R.b i) ∧ R.seg ≤ s.seg ∧
      (R.seg = s.seg → R.b = s.b ∧ (learnerFor s (s.ep + 1)).φ = R.φ) ∧
      (∀ u, f u - fstar ≤ (R.fs - fstar) / 4 →
        (R.steps : ℝ) ≤ 1 + lossL (recordLoss fstar R u) R.cuts R.φ + logTwo d) ∧
      (R.steps : ℝ) ≤ runCap d μ + 1 + logTwo d

def Ledger (s : Core d) (n : ℕ) : Prop :=
  ∃ (Xc X0 X0' X1 X1' : ℝ) (nc n0 n1 ndrop : ℕ),
    s.ep = nc + n0 + n1 + ndrop + (if s.prev.isSome then 1 else 0) ∧
    ndrop ≤ prevSeg s ∧ prevSeg s ≤ s.seg ∧
    Xc ≤ 24 * kappaRoot μ * nc + s.seg * (9 / 2 * bandWidth d ^ 2 * lossCap d μ) ∧
    LearnerLedger (bandWidth d) (lossCap d μ) (comparator w s.b) (kappaRoot μ) s.learner0
      X0 X0' n0 ∧
    LearnerLedger (bandWidth d) (lossCap d μ) (comparator w s.b) (kappaRoot μ) s.learner1
      X1 X1' n1 ∧
    (n : ℝ) ≤ (nc + n0 + n1) * (1 + logTwo d) + Xc + X0 + X1 +
      ndrop * (runCap d μ + 1 + logTwo d) + prevSteps s +
      s.seg * (runCap d μ + 2 + logTwo d) + (s.k + s.cuts.length)

structure Inv (s : Core d) (n : ℕ) : Prop where
  stage : s.stage = d
  box_ge : ∀ i, 1 / w i ≤ s.b i
  box_pow : ∃ m : Fin d → ℕ, (∀ i, s.b i = b0 i / 2 ^ m i) ∧ s.seg = ∑ i, m i
  band0 : BandOK s.learner0
  band1 : BandOK s.learner1
  phi : s.φ = (learnerFor s s.ep).φ
  fs : s.fs = f s.xs
  halving : s.fs - fstar ≤ (f x0 - fstar) / 2 ^ s.ep
  pot : ∀ u, s.A * (f s.x - f u) + (∑ i, (s.z i - u i) ^ 2 / metric s i) / 2 ≤
    (∑ i, (s.xs i - u i) ^ 2 / metric s i) / 2
  A_nonneg : 0 ≤ s.A
  A_lower : stepScale s * (s.k * (s.k + 1)) / 4 ≤ s.A
  not_halved : 1 ≤ s.k → (s.fs - fstar) / 2 < f s.x - fstar
  cuts : CutsOK w s.b s.cuts
  certified : 1 / stepScale s ≤ (bestCut s.cuts s.φ).1
  prev : PrevOK f w μ fstar s
  ledger : Ledger w μ s n

end

lemma stepScale_pos (s : Core d) : 0 < stepScale s := by
  unfold stepScale; positivity

lemma learnerFor_band {s : Core d} (h0 : BandOK s.learner0) (h1 : BandOK s.learner1) (r : ℕ) :
    BandOK (learnerFor s r) := by
  unfold learnerFor; split_ifs <;> assumption

lemma bestCut_band {w b φ : Fin d → ℝ} {cuts : List (Fin d → ℝ)} (hd : 1 ≤ (d : ℝ))
    (hc : CutsOK w b cuts) (hφ : ∀ i, bandLo d ≤ φ i ∧ φ i ≤ bandHi) :
    (bestCut cuts φ).1 ≤ 2 * d := by
  apply bestCut_le cuts φ (by linarith)
  intro a ha
  obtain ⟨ha0, has, -⟩ := hc a ha
  have : cutValue a φ ≤ (∑ i, a i) / 2 := by
    rw [cutValue, Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (band_exp hd hφ i).2 (ha0 i)
  linarith

lemma cuts_length_le {w : Fin d → ℝ} {s : Core d} (hd : 1 ≤ (d : ℝ))
    (hc : CutsOK w s.b s.cuts) (hφ : ∀ i, bandLo d ≤ s.φ i ∧ s.φ i ≤ bandHi)
    (hcert : 1 / stepScale s ≤ (bestCut s.cuts s.φ).1) :
    (s.cuts.length : ℝ) ≤ logTwo d := by
  have h1 := bestCut_band hd hc hφ
  have h2 : (2 : ℝ) ^ s.cuts.length ≤ 2 * d := by
    have : 1 / stepScale s = (2 : ℝ) ^ s.cuts.length := by
      unfold stepScale; rw [one_div_pow, one_div_one_div]
    linarith
  unfold logTwo
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  exact_mod_cast h2

lemma metric_pos {s : Core d} {w : Fin d → ℝ} (hw : ∀ i, 0 < w i)
    (hb : ∀ i, 1 / w i ≤ s.b i) (i : Fin d) : 0 < metric s i := by
  unfold metric
  have : 0 < s.b i := lt_of_lt_of_le (by have := hw i; positivity) (hb i)
  positivity

lemma metric_dist_le {s : Core d} {w : Fin d → ℝ} (hd : 1 ≤ (d : ℝ)) (hw : ∀ i, 0 < w i)
    (hb : ∀ i, 1 / w i ≤ s.b i) (hφ : ∀ i, bandLo d ≤ s.φ i ∧ s.φ i ≤ bandHi)
    (v : Fin d → ℝ) :
    ∑ i, v i ^ 2 / metric s i ≤ 4 * d * ∑ i, w i * v i ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hbpos : 0 < s.b i := lt_of_lt_of_le (by have := hw i; positivity) (hb i)
  have hm := metric_pos hw hb i
  have he := (band_exp hd hφ i).1
  rw [div_le_iff₀ hm]
  have h1 : 1 ≤ w i * s.b i := by
    have := hb i; rw [div_le_iff₀ (hw i)] at this; linarith
  have h2 : 1 ≤ 4 * d * Real.exp (s.φ i) := by
    rw [div_le_iff₀ (by positivity)] at he; linarith
  unfold metric
  have hv := sq_nonneg (v i)
  have hw0 := (hw i).le
  calc v i ^ 2 = v i ^ 2 * 1 * 1 := by ring
    _ ≤ v i ^ 2 * (w i * s.b i) * (4 * d * Real.exp (s.φ i)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hv) h2 (by norm_num) (by positivity)
    _ = 4 * d * (w i * v i ^ 2) * (s.b i * Real.exp (s.φ i)) := by ring

end OracleTemplate.OnlineMetricAccelerated
