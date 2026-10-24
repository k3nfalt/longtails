import LongTails.Proofs.NoisyBatchQuadraticPerceptronEscape
namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialPaths
open Classical LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
open LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift
open LongTails.Proofs.NoisyBatchQuadraticPerceptronEscape
open scoped RealInnerProductSpace
lemma sequence_pastPoint_recurrence (P : Public) (data : Data P) (η : ℝ)
    (s : ℕ → Weights P.dimension) (t : ℕ) :
    let w := pastPoint P data η t (fun j => s j)
    pastPoint P data η (t + 1) (fun j => s j) = if Separates data w then w else
      WithLp.toLp 2 (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
        w.ofLp.2 + η * ⟪selected data w.ofLp.1 w.ofLp.2, w.ofLp.1⟫) + P.noiseScale • s t := by
  rw [pastPoint]
  dsimp only [Fin.val_castSucc, Fin.val_last]
  rw [deterministic_proposal]
lemma sequence_separation_persists (P : Public) (data : Data P) (η : ℝ)
    (s : ℕ → Weights P.dimension) (t n : ℕ)
    (hs : Separates data (pastPoint P data η t (fun j => s j))) :
    Separates data (pastPoint P data η (t + n) (fun j => s j)) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    rw [← Nat.add_assoc, sequence_pastPoint_recurrence, ite_eq_left ih]
    exact ih
noncomputable def finiteSamples {E : Type*} [Zero E] {N : ℕ} (z : Fin N → E) (k : ℕ) : E :=
  if hk : k < N then z ⟨k, hk⟩ else 0
lemma finiteSamples_val {E : Type*} [Zero E] {N : ℕ} (z : Fin N → E) (j : Fin N) :
    finiteSamples z j = z j := by simp [finiteSamples, j.isLt]
lemma finiteSamples_append_initial {E : Type*} [Zero E] {t B : ℕ}
    (x : Fin t → E) (y : Fin B → E) (j : Fin t) :
    finiteSamples (Fin.append x y) j = x j := by
  have he := finiteSamples_val (Fin.append x y) (Fin.castAdd B j)
  simpa only [Fin.val_castAdd, Fin.append_left] using he
lemma finiteSamples_append_future {E : Type*} [Zero E] {t B : ℕ}
    (x : Fin t → E) (y : Fin B → E) (j : Fin B) :
    finiteSamples (Fin.append x y) (t + j) = y j := by
  have he := finiteSamples_val (Fin.append x y) (Fin.natAdd t j)
  simpa only [Fin.val_natAdd, Fin.append_right] using he
lemma finiteSamples_pastPoint (P : Public) (data : Data P) (η : ℝ) (N : ℕ)
    (z : Fin N → Weights P.dimension) :
    pastPoint P data η N (fun j => finiteSamples z j) = pastPoint P data η N z := by
  congr 1
  funext j
  exact finiteSamples_val z j
lemma sequence_current_escape (P : Public) (data : Data P) (u : Features P.dimension)
    (η δ ε : ℝ) (K t : ℕ) (s : ℕ → Weights P.dimension)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hσ : 0 ≤ P.noiseScale)
    (hescape : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η
      (pastPoint P data η t (fun k => s k)).ofLp.1
      (pastPoint P data η t (fun k => s k)).ofLp.2)
    (hv : P.noiseScale ≤ |(pastPoint P data η t (fun k => s k)).ofLp.2|)
    (hnoise : ∀ j < K, ‖s (t + j)‖ ≤ ε) :
    Separates data (pastPoint P data η (t + K) (fun k => s k)) := by
  apply frozen_escape P data u
    (fun j => (pastPoint P data η (t + j) (fun k => s k)))
    (fun j => P.noiseScale • s (t + j))
    (pastPoint P data η t (fun k => s k)) 0 η δ ε K
    hη hδ hsmall hε hεtotal hεprogress hK hR hu hmargin ht hescape
  · simp
  · simp only [norm_zero]
    positivity
  · intro j hj
    convert sequence_pastPoint_recurrence P data η s (t + j) using 1
  · intro j hj
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    calc
      _ ≤ P.noiseScale * ε := mul_le_mul_of_nonneg_left (hnoise j hj) hσ
      _ ≤ ε * |(pastPoint P data η t (fun k => s k)).ofLp.2| := by nlinarith
lemma sequence_proposal_escape (P : Public) (data : Data P) (u : Features P.dimension)
    (η δ ε : ℝ) (K t : ℕ) (s : ℕ → Weights P.dimension) (b : Weights P.dimension)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hσ : 0 ≤ P.noiseScale)
    (hbase : b = WithLp.toLp 2
      ((pastPoint P data η t (fun k => s k)).ofLp.1 +
        (η * (pastPoint P data η t (fun k => s k)).ofLp.2) •
          LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry.selected data
            (pastPoint P data η t (fun k => s k)).ofLp.1
            (pastPoint P data η t (fun k => s k)).ofLp.2,
      (pastPoint P data η t (fun k => s k)).ofLp.2 + η *
        ⟪LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry.selected data
          (pastPoint P data η t (fun k => s k)).ofLp.1
          (pastPoint P data η t (fun k => s k)).ofLp.2,
        (pastPoint P data η t (fun k => s k)).ofLp.1⟫))
    (hwrong : ¬Separates data (pastPoint P data η t (fun k => s k)))
    (hescape : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η b.ofLp.1 b.ofLp.2)
    (hv : P.noiseScale ≤ |b.ofLp.2|)
    (hnoise : ∀ j < K + 1, ‖s (t + j)‖ ≤ ε) :
    Separates data (pastPoint P data η (t + 1 + K) (fun k => s k)) := by
  have hn (j : ℕ) (hj : j < K + 1) : ‖P.noiseScale • s (t + j)‖ ≤ ε * |b.ofLp.2| := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    have hh := mul_le_mul_of_nonneg_left (hnoise j hj) hσ
    nlinarith
  apply frozen_escape P data u
    (fun j => (pastPoint P data η (t + 1 + j) (fun k => s k)))
    (fun j => P.noiseScale • s (t + 1 + j))
    b (P.noiseScale • s t) η δ ε K
    hη hδ hsmall hε hεtotal hεprogress hK hR hu hmargin ht hescape
  · have hh := sequence_pastPoint_recurrence P data η s t
    simpa only [Nat.add_zero, ite_eq_right hwrong, ← hbase] using hh
  · simpa only [Nat.add_zero] using hn 0 (by omega)
  · intro j hj
    convert sequence_pastPoint_recurrence P data η s (t + 1 + j) using 1
  · intro j hj
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hn (j + 1) (by omega)
lemma sequence_separation_mono (P : Public) (data : Data P) (η : ℝ)
    (s : ℕ → Weights P.dimension) (t r : ℕ) (htr : t ≤ r)
    (hs : Separates data (pastPoint P data η t (fun j => s j))) :
    Separates data (pastPoint P data η r (fun j => s j)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le htr
  exact sequence_separation_persists P data η s t n hs
lemma finiteSamples_append_pastPoint_initial (P : Public) (data : Data P) (η : ℝ) (t B : ℕ)
    (x : Fin t → Weights P.dimension) (y : Fin B → Weights P.dimension) :
    pastPoint P data η t (fun j => finiteSamples (Fin.append x y) j) = pastPoint P data η t x := by
  congr 1
  funext j
  exact finiteSamples_append_initial x y j
lemma block_separation_persists (P : Public) (data : Data P) (η : ℝ) (t B : ℕ)
    (x : Fin t → Weights P.dimension) (y : Fin B → Weights P.dimension)
    (hs : Separates data (pastPoint P data η t x)) :
    Separates data (pastPoint P data η (t + B) (Fin.append x y)) := by
  have hi : Separates data (pastPoint P data η t (fun j => finiteSamples (Fin.append x y) j)) := by
    rw [finiteSamples_append_pastPoint_initial]
    exact hs
  have hh := sequence_separation_persists P data η (finiteSamples (Fin.append x y)) t B hi
  rw [finiteSamples_pastPoint] at hh
  exact hh
lemma block_current_escape (P : Public) (data : Data P) (u : Features P.dimension)
    (η δ ε : ℝ) (K t B : ℕ) (x : Fin t → Weights P.dimension) (y : Fin B → Weights P.dimension)
    (hKB : K ≤ B)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hσ : 0 ≤ P.noiseScale)
    (hescape : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η
      (pastPoint P data η t x).ofLp.1
      (pastPoint P data η t x).ofLp.2)
    (hv : P.noiseScale ≤ |(pastPoint P data η t x).ofLp.2|)
    (hnoise : ∀ j : Fin B, ‖y j‖ ≤ ε) :
    Separates data (pastPoint P data η (t + B) (Fin.append x y)) := by
  let z := finiteSamples (Fin.append x y)
  have hx : pastPoint P data η t (fun j => z j) = pastPoint P data η t x :=
    finiteSamples_append_pastPoint_initial P data η t B x y
  have hn (j : ℕ) (hj : j < K) : ‖z (t + j)‖ ≤ ε := by
    have hlt : j < B := lt_of_lt_of_le hj hKB
    have he := finiteSamples_append_future x y (⟨j, hlt⟩ : Fin B)
    change ‖finiteSamples (Fin.append x y) (t + j)‖ ≤ ε
    rw [he]
    exact hnoise ⟨j, hlt⟩
  have hh := sequence_current_escape P data u η δ ε K t z hη hδ hsmall hε hεtotal hεprogress
    hK hR hu hmargin ht hσ (by simpa only [hx] using hescape) (by simpa only [hx] using hv) hn
  have hm := sequence_separation_mono P data η z (t + K) (t + B) (by omega) hh
  change Separates data (pastPoint P data η (t + B) (fun j => finiteSamples (Fin.append x y) j)) at hm
  rw [finiteSamples_pastPoint] at hm
  exact hm
lemma block_proposal_escape (P : Public) (data : Data P) (u : Features P.dimension)
    (η δ ε : ℝ) (K t B : ℕ) (x : Fin t → Weights P.dimension) (y : Fin B → Weights P.dimension)
    (b : Weights P.dimension) (hKB : K + 1 ≤ B)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hsmall : η * P.radius ≤ 1 / 16) (hε : 0 ≤ ε)
    (hεtotal : ((K + 1 : ℕ) : ℝ) * ε ≤ 1 / 64)
    (hεprogress : ε ≤ η * δ * (P.count : ℝ)⁻¹ / 4)
    (hK : 16 * (P.count : ℝ) ≤ (K : ℝ) * η * δ)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, δ ≤ ⟪data i, u⟫)
    (ht : 2 * η * P.radius ^ 2 * (4 * (P.count : ℝ) + 1) < δ)
    (hσ : 0 ≤ P.noiseScale)
    (hbase : b = WithLp.toLp 2
      ((pastPoint P data η t x).ofLp.1 +
        (η * (pastPoint P data η t x).ofLp.2) •
          LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry.selected data
            (pastPoint P data η t x).ofLp.1
            (pastPoint P data η t x).ofLp.2,
      (pastPoint P data η t x).ofLp.2 + η *
        ⟪LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry.selected data
          (pastPoint P data η t x).ofLp.1
          (pastPoint P data η t x).ofLp.2,
        (pastPoint P data η t x).ofLp.1⟫))
    (hwrong : ¬Separates data (pastPoint P data η t x))
    (hescape : LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift.Escape data η b.ofLp.1 b.ofLp.2)
    (hv : P.noiseScale ≤ |b.ofLp.2|)
    (hnoise : ∀ j : Fin B, ‖y j‖ ≤ ε) :
    Separates data (pastPoint P data η (t + B) (Fin.append x y)) := by
  let z := finiteSamples (Fin.append x y)
  have hx : pastPoint P data η t (fun j => z j) = pastPoint P data η t x :=
    finiteSamples_append_pastPoint_initial P data η t B x y
  have hn (j : ℕ) (hj : j < K + 1) : ‖z (t + j)‖ ≤ ε := by
    have hlt : j < B := lt_of_lt_of_le hj hKB
    have he := finiteSamples_append_future x y (⟨j, hlt⟩ : Fin B)
    change ‖finiteSamples (Fin.append x y) (t + j)‖ ≤ ε
    rw [he]
    exact hnoise ⟨j, hlt⟩
  have hh := sequence_proposal_escape P data u η δ ε K t z b hη hδ hsmall hε hεtotal hεprogress
    hK hR hu hmargin ht hσ (by simpa only [hx] using hbase) (by simpa only [hx] using hwrong) hescape hv hn
  have hm := sequence_separation_mono P data η z (t + 1 + K) (t + B) (by omega) hh
  change Separates data (pastPoint P data η (t + B) (fun j => finiteSamples (Fin.append x y) j)) at hm
  rw [finiteSamples_pastPoint] at hm
  exact hm
lemma block_first_sample_success (P : Public) (data : Data P) (η : ℝ) (t B : ℕ)
    (hB : 0 < B) (x : Fin t → Weights P.dimension) (y : Fin B → Weights P.dimension)
    (hy : Separates data (WithLp.toLp 2
      ((pastPoint P data η t x).ofLp.1 + (η * (pastPoint P data η t x).ofLp.2) •
        selected data (pastPoint P data η t x).ofLp.1 (pastPoint P data η t x).ofLp.2,
      (pastPoint P data η t x).ofLp.2 + η * ⟪selected data (pastPoint P data η t x).ofLp.1
        (pastPoint P data η t x).ofLp.2, (pastPoint P data η t x).ofLp.1⟫) + P.noiseScale • y ⟨0, hB⟩)) :
    Separates data (pastPoint P data η (t + B) (Fin.append x y)) := by
  let z := finiteSamples (Fin.append x y)
  have hx : pastPoint P data η t (fun j => z j) = pastPoint P data η t x :=
    finiteSamples_append_pastPoint_initial P data η t B x y
  have hz : z t = y ⟨0, hB⟩ := by
    simpa only [Nat.add_zero] using finiteSamples_append_future x y (⟨0, hB⟩ : Fin B)
  have hs : Separates data (pastPoint P data η (t + 1) (fun j => z j)) := by
    rw [sequence_pastPoint_recurrence, hx]
    split_ifs with hh
    · exact hh
    · simpa only [hz] using hy
  have hm := sequence_separation_mono P data η z (t + 1) (t + B) (by omega) hs
  change Separates data (pastPoint P data η (t + B) (fun j => finiteSamples (Fin.append x y) j)) at hm
  rw [finiteSamples_pastPoint] at hm
  exact hm

end LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialPaths
