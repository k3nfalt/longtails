import LongTails.Proofs.NcConcavePooled
import LongTails.Proofs.NcConcaveLine
import LongTails.Proofs.NcConcaveProx
import LongTails.Setups.StochasticNonconvexConcaveMinimax

open scoped BigOperators

namespace LongTails.Proofs.NcConcavePartThree

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcavePsi
open LongTails.Proofs.NcConcavePartTwo LongTails.Proofs.NcConcavePooled
open LongTails.Proofs.NcConcaveLine LongTails.Proofs.NcConcaveProx
open LongTails.Setups.StochasticNonconvexConcaveMinimax

variable {d n : ℕ}

structure Coords (d n : ℕ) where
  πU : Fin (n + 1) → Fin d
  πA : Fin n → Fin d
  πB : Fin n → Fin d
  hU : Function.Injective πU
  hA : Function.Injective πA
  hB : Function.Injective πB
  hAB : ∀ i j, πA i ≠ πB j

noncomputable def selU (C : Coords d n) (s : ℝ) (x : Prim d) : Fin (n + 1) → ℝ :=
  fun j => x (0, C.πU j) / s

noncomputable def selA (C : Coords d n) (s : ℝ) (x : Prim d) : Fin n → ℝ :=
  fun i => x (1, C.πA i) / s

noncomputable def selB (C : Coords d n) (s : ℝ) (x : Prim d) : Fin n → ℝ :=
  fun i => x (1, C.πB i) / s

noncomputable def phiW (C : Coords d n) (s ℓ : ℝ) (x : Prim d) : ℝ :=
  ℓ * s ^ 2 * psi (selU C s x) (selA C s x) (selB C s x)

def primBall (RU RA : ℝ) : Set (Prim d) := {x | blockSq x 0 ≤ RU ^ 2 ∧ blockSq x 1 ≤ RA ^ 2}

noncomputable def emb {k : ℕ} (π : Fin k → Fin d) (g : Fin k → ℝ) (i : Fin d) : ℝ :=
  ∑ j, if π j = i then g j else 0

lemma emb_sum {k : ℕ} (π : Fin k → Fin d) (g : Fin k → ℝ) (w : Fin d → ℝ) :
    ∑ j, g j * w (π j) = ∑ i, emb π g i * w i := by
  simp only [emb, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

lemma emb_apply {k : ℕ} {π : Fin k → Fin d} (hπ : Function.Injective π) (g : Fin k → ℝ) (j : Fin k) :
    emb π g (π j) = g j := by
  simp only [emb]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'; rw [ite_eq_right (fun h => hj' (hπ h))]
  · simp

lemma emb_off {k : ℕ} {π : Fin k → Fin d} (g : Fin k → ℝ) (i : Fin d) (hi : ∀ j, π j ≠ i) :
    emb π g i = 0 := by
  simp only [emb]; exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right (hi j)]

lemma blockSq_eq (x : Prim d) (b : Fin 2) : blockSq x b = ∑ i, x (b, i) ^ 2 := rfl

lemma norm_sq_prim (x : Prim d) : ‖x‖ ^ 2 = blockSq x 0 + blockSq x 1 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two]; rfl

lemma blockSq_convex (x z : Prim d) (b : Fin 2) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    blockSq (x + t • (z - x)) b ≤ (1 - t) * blockSq x b + t * blockSq z b := by
  simp only [blockSq, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  have : 0 ≤ t * (1 - t) * (x (b, i) - z (b, i)) ^ 2 := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  nlinarith

lemma primBall_segment {RU RA : ℝ} {x z : Prim d} (hx : x ∈ primBall RU RA) (hz : z ∈ primBall RU RA)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : x + t • (z - x) ∈ primBall RU RA := by
  constructor
  · have := blockSq_convex x z 0 t h0 h1; nlinarith [hx.1, hz.1]
  · have := blockSq_convex x z 1 t h0 h1; nlinarith [hx.2, hz.2]

lemma sel_line (C : Coords d n) (s : ℝ) (hs : 0 < s) (p v : Prim d) (t : ℝ) :
    selU C s (p + t • v) = (fun j => selU C s p j + t * selU C s v j) ∧
    selA C s (p + t • v) = (fun i => selA C s p i + t * selA C s v i) ∧
    selB C s (p + t • v) = (fun i => selB C s p i + t * selB C s v i) := by
  refine ⟨?_, ?_, ?_⟩ <;> funext j <;>
    simp only [selU, selA, selB, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> field_simp

lemma normsq_line (p x v : Prim d) :
    HasDerivAt (fun t : ℝ => ‖p + t • v - x‖ ^ 2) (∑ c, 2 * (p c - x c) * v c) 0 := by
  have e : (fun t : ℝ => ‖p + t • v - x‖ ^ 2) = fun t => ∑ c, (p c - x c + t * v c) ^ 2 := by
    funext t
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e]
  have h := sumsq_line (fun c t => p c - x c + t * v c) (fun c => v c) (fun c => by
    have := line_coord (p c - x c) (v c); exact this)
  convert h using 1
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma vi_of_min (C : Coords d n) {s ℓ L RU RA : ℝ} (hs : 0 < s) (x p : Prim d)
    (hp : p ∈ primBall RU RA)
    (hmin : ∀ z ∈ primBall RU RA, phiW C s ℓ p + L * ‖p - x‖ ^ 2 ≤ phiW C s ℓ z + L * ‖z - x‖ ^ 2)
    (z : Prim d) (hz : z ∈ primBall RU RA) :
    0 ≤ ℓ * s ^ 2 * (dpsiU (selU C s p) (selA C s p) (selB C s p) (selU C s (z - p)) +
        ∑ i, ((gab (selU C s p) (selA C s p) (selB C s p) i).1 * selA C s (z - p) i +
          (gab (selU C s p) (selA C s p) (selB C s p) i).2 * selB C s (z - p) i)) +
      L * ∑ c, 2 * (p c - x c) * (z - p) c := by
  set v := z - p
  set g : ℝ → ℝ := fun t => phiW C s ℓ (p + t • v) + L * ‖p + t • v - x‖ ^ 2
  have hpsi := psi_line (selU C s p) (selU C s v) (selA C s p) (selB C s p) (selA C s v) (selB C s v)
  have hg : HasDerivAt g (ℓ * s ^ 2 * (dpsiU (selU C s p) (selA C s p) (selB C s p) (selU C s v) +
        ∑ i, ((gab (selU C s p) (selA C s p) (selB C s p) i).1 * selA C s v i +
          (gab (selU C s p) (selA C s p) (selB C s p) i).2 * selB C s v i)) +
      L * ∑ c, 2 * (p c - x c) * v c) 0 := by
    have h1 : (fun t => phiW C s ℓ (p + t • v)) = fun t => ℓ * s ^ 2 *
        psi (fun j => selU C s p j + t * selU C s v j) (fun i => selA C s p i + t * selA C s v i)
          (fun i => selB C s p i + t * selB C s v i) := by
      funext t
      obtain ⟨e1, e2, e3⟩ := sel_line C s hs p v t
      simp only [phiW, e1, e2, e3]
    have h2 := (HasDerivAt.const_mul (ℓ * s ^ 2) hpsi).add
      (HasDerivAt.const_mul L (normsq_line p x v))
    have hfun : (fun t => phiW C s ℓ (p + t • v) + L * ‖p + t • v - x‖ ^ 2) =
        (fun t => ℓ * s ^ 2 * psi (fun j => selU C s p j + t * selU C s v j)
          (fun i => selA C s p i + t * selA C s v i) (fun i => selB C s p i + t * selB C s v i)) +
        (fun t => L * ‖p + t • v - x‖ ^ 2) := by
      funext t
      have h1t : phiW C s ℓ (p + t • v) = ℓ * s ^ 2 * psi (fun j => selU C s p j + t * selU C s v j)
          (fun i => selA C s p i + t * selA C s v i) (fun i => selB C s p i + t * selB C s v i) :=
        congrFun h1 t
      rw [Pi.add_apply, h1t]
    simp only [g]
    rw [hfun]
    exact h2
  apply deriv_nonneg_of_min hg
  intro t ht0 ht1
  have hzt := primBall_segment hp hz t ht0.le ht1
  have := hmin _ hzt
  simp only [g, zero_smul, add_zero]
  exact this

lemma split_sum {k : ℕ} (π : Fin k → Fin d) (hπ : Function.Injective π) (F : Fin d → ℝ) :
    ∑ i, F i = ∑ j, F (π j) + ∑ i ∈ (Finset.univ.map ⟨π, hπ⟩)ᶜ, F i := by
  rw [← Finset.sum_add_sum_compl (Finset.univ.map ⟨π, hπ⟩), Finset.sum_map]
  rfl

lemma split_sum2 {k : ℕ} (πa πb : Fin k → Fin d) (ha : Function.Injective πa)
    (hb : Function.Injective πb) (hab : ∀ i j, πa i ≠ πb j) (F : Fin d → ℝ) :
    ∑ i, F i = ∑ j, F (πa j) + ∑ j, F (πb j) +
      ∑ i ∈ (Finset.univ.map ⟨πa, ha⟩ ∪ Finset.univ.map ⟨πb, hb⟩)ᶜ, F i := by
  have hdisj : Disjoint (Finset.univ.map ⟨πa, ha⟩) (Finset.univ.map ⟨πb, hb⟩) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hi hi'
    obtain ⟨j, rfl⟩ := hi
    obtain ⟨j', hj'⟩ := hi'
    exact hab j j' hj'.symm
  rw [← Finset.sum_add_sum_compl (Finset.univ.map ⟨πa, ha⟩ ∪ Finset.univ.map ⟨πb, hb⟩),
    Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map]
  rfl

lemma resid_split1 {k : ℕ} (π : Fin k → Fin d) (hπ : Function.Injective π) (g : Fin k → ℝ)
    (w : Fin d → ℝ) (l : ℝ) :
    ∑ i, (emb π g i + l * w i) ^ 2 =
      ∑ j, (g j + l * w (π j)) ^ 2 + l ^ 2 * ∑ i ∈ (Finset.univ.map ⟨π, hπ⟩)ᶜ, w i ^ 2 := by
  rw [split_sum π hπ]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by rw [emb_apply hπ]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h0 : emb π g i = 0 := by
      apply emb_off
      intro j hj
      apply Finset.mem_compl.mp hi
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
      exact ⟨j, hj⟩
    rw [h0]; ring

lemma resid_split2 {k : ℕ} (πa πb : Fin k → Fin d) (ha : Function.Injective πa)
    (hb : Function.Injective πb) (hab : ∀ i j, πa i ≠ πb j) (ga gb : Fin k → ℝ) (w : Fin d → ℝ)
    (m : ℝ) :
    ∑ i, (emb πa ga i + emb πb gb i + m * w i) ^ 2 =
      ∑ j, ((ga j + m * w (πa j)) ^ 2 + (gb j + m * w (πb j)) ^ 2) +
        m ^ 2 * ∑ i ∈ (Finset.univ.map ⟨πa, ha⟩ ∪ Finset.univ.map ⟨πb, hb⟩)ᶜ, w i ^ 2 := by
  rw [split_sum2 πa πb ha hb hab, Finset.sum_add_distrib]
  have h1 : ∀ j, emb πb gb (πa j) = 0 := fun j => emb_off gb _ (fun j' h => hab j j' h.symm)
  have h2 : ∀ j, emb πa ga (πb j) = 0 := fun j => emb_off ga _ (fun j' h => hab j' j h)
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun j _ => by rw [emb_apply ha, h1]; ring
    · exact Finset.sum_congr rfl fun j _ => by rw [emb_apply hb, h2]; ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_compl.mp hi
    have h3 : emb πa ga i = 0 := by
      apply emb_off; intro j hj; apply hi'
      apply Finset.mem_union_left
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
      exact ⟨j, hj⟩
    have h4 : emb πb gb i = 0 := by
      apply emb_off; intro j hj; apply hi'
      apply Finset.mem_union_right
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
      exact ⟨j, hj⟩
    rw [h3, h4]; ring

theorem part_three (C : Coords d n) {s ℓ L RU θ : ℝ} (hs : 0 < s) (hℓ : 0 < ℓ) (hL : 0 < L)
    (hRU : 256 * (n + 1) * s ^ 2 ≤ RU ^ 2) (hRU0 : 0 < RU)
    (hsmall : cδ / 3 * ℓ / (2 * L) + θ / 2 ≤ 1 / 4)
    (x : Prim d) (hx : |x (0, C.πU (Fin.last n))| ≤ θ / 2 * s)
    (p : Prim d) (hp : p ∈ primBall RU (2 * s))
    (hmin : ∀ z ∈ primBall RU (2 * s), phiW C s ℓ p + L * ‖p - x‖ ^ 2 ≤ phiW C s ℓ z + L * ‖z - x‖ ^ 2) :
    cδ / 3 * ℓ * s ≤ 2 * L * ‖x - p‖ := by
  by_contra hcon
  push Not at hcon
  set u := selU C s p
  set a := selA C s p
  set b := selB C s p
  set GU : Fin d → ℝ := emb C.πU (gu u a b)
  set GA : Fin d → ℝ := emb C.πA (fun i => (gab u a b i).1)
  set GB : Fin d → ℝ := emb C.πB (fun i => (gab u a b i).2)
  have vi0 : ∀ z0 : Fin d → ℝ, ∑ i, z0 i ^ 2 ≤ RU ^ 2 →
      0 ≤ ∑ i, (ℓ * s * GU i + 2 * L * (p (0, i) - x (0, i))) * (z0 i - p (0, i)) := by
    intro z0 hz0
    set z : Prim d := WithLp.toLp 2 (fun c => if c.1 = 0 then z0 c.2 else p c)
    have hz : z ∈ primBall RU (2 * s) := by
      refine ⟨?_, ?_⟩
      · simp only [blockSq, z]; exact hz0
      · have : blockSq z 1 = blockSq p 1 := by
          simp only [blockSq, z]; rfl
        rw [this]; exact hp.2
    have h := vi_of_min C hs x p hp hmin z hz
    have hA0 : selA C s (z - p) = 0 := by
      funext i; simp [selA, z, PiLp.sub_apply]
    have hB0 : selB C s (z - p) = 0 := by
      funext i; simp [selB, z, PiLp.sub_apply]
    rw [hA0, hB0] at h
    simp only [Pi.zero_apply, mul_zero, add_zero, Finset.sum_const_zero] at h
    rw [dpsiU_eq_sum] at h
    have e1 : ∑ j, selU C s (z - p) j * gu u a b j = (1 / s) * ∑ i, GU i * (z0 i - p (0, i)) := by
      have : ∀ j, selU C s (z - p) j * gu u a b j = (1 / s) * (gu u a b j * (z0 (C.πU j) - p (0, C.πU j))) := by
        intro j
        have hz0' : z (0, C.πU j) = z0 (C.πU j) := by simp [z]
        simp only [selU, PiLp.sub_apply, hz0']; ring
      simp only [this, ← Finset.mul_sum]
      rw [emb_sum C.πU (gu u a b) (fun i => z0 i - p (0, i))]
    rw [e1] at h
    have e2 : ∑ c, 2 * (p c - x c) * (z - p) c = ∑ i, 2 * (p (0, i) - x (0, i)) * (z0 i - p (0, i)) := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      have : ∑ i, 2 * (p (1, i) - x (1, i)) * (z - p) (1, i) = 0 := by
        apply Finset.sum_eq_zero; intro i _
        simp [z, PiLp.sub_apply]
      rw [this, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [z, PiLp.sub_apply]
    rw [e2] at h
    have e3 : ℓ * s ^ 2 * ((1 / s) * ∑ i, GU i * (z0 i - p (0, i))) +
        L * ∑ i, 2 * (p (0, i) - x (0, i)) * (z0 i - p (0, i)) =
        ∑ i, (ℓ * s * GU i + 2 * L * (p (0, i) - x (0, i))) * (z0 i - p (0, i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [← e3]; exact h
  have vi1 : ∀ z1 : Fin d → ℝ, ∑ i, z1 i ^ 2 ≤ (2 * s) ^ 2 →
      0 ≤ ∑ i, (ℓ * s * (GA i + GB i) + 2 * L * (p (1, i) - x (1, i))) * (z1 i - p (1, i)) := by
    intro z1 hz1
    set z : Prim d := WithLp.toLp 2 (fun c => if c.1 = 1 then z1 c.2 else p c)
    have hz : z ∈ primBall RU (2 * s) := by
      refine ⟨?_, ?_⟩
      · have : blockSq z 0 = blockSq p 0 := by
          simp only [blockSq, z]; rfl
        rw [this]; exact hp.1
      · simp only [blockSq, z]; exact hz1
    have h := vi_of_min C hs x p hp hmin z hz
    have hU0 : selU C s (z - p) = 0 := by
      funext j; simp [selU, z, PiLp.sub_apply]
    rw [hU0] at h
    have hd0 : dpsiU u a b 0 = 0 := by
      have := dpsiU_smul u a b 0 0; simpa using this
    rw [hd0, zero_add] at h
    have e1 : ∑ i, ((gab u a b i).1 * selA C s (z - p) i + (gab u a b i).2 * selB C s (z - p) i) =
        (1 / s) * ∑ i, (GA i + GB i) * (z1 i - p (1, i)) := by
      have hA : ∀ i, selA C s (z - p) i = (z1 (C.πA i) - p (1, C.πA i)) / s := by
        intro i; simp [selA, z, PiLp.sub_apply]
      have hB : ∀ i, selB C s (z - p) i = (z1 (C.πB i) - p (1, C.πB i)) / s := by
        intro i; simp [selB, z, PiLp.sub_apply]
      simp only [hA, hB, Finset.sum_add_distrib, add_mul]
      rw [← emb_sum C.πA (fun i => (gab u a b i).1) (fun i => z1 i - p (1, i)),
        ← emb_sum C.πB (fun i => (gab u a b i).2) (fun i => z1 i - p (1, i))]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> field_simp
    rw [e1] at h
    have e2 : ∑ c, 2 * (p c - x c) * (z - p) c = ∑ i, 2 * (p (1, i) - x (1, i)) * (z1 i - p (1, i)) := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      have : ∑ i, 2 * (p (0, i) - x (0, i)) * (z - p) (0, i) = 0 := by
        apply Finset.sum_eq_zero; intro i _
        simp [z, PiLp.sub_apply]
      rw [this, zero_add]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [z, PiLp.sub_apply]
    rw [e2] at h
    have e3 : ℓ * s ^ 2 * ((1 / s) * ∑ i, (GA i + GB i) * (z1 i - p (1, i))) +
        L * ∑ i, 2 * (p (1, i) - x (1, i)) * (z1 i - p (1, i)) =
        ∑ i, (ℓ * s * (GA i + GB i) + 2 * L * (p (1, i) - x (1, i))) * (z1 i - p (1, i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [← e3]; exact h
  obtain ⟨l0, hl0, hv0, hsl0⟩ := ball_normal
    (fun i => ℓ * s * GU i + 2 * L * (p (0, i) - x (0, i))) (fun i => p (0, i)) hRU0 hp.1 vi0
  obtain ⟨l1, hl1, hv1, hsl1⟩ := ball_normal
    (fun i => ℓ * s * (GA i + GB i) + 2 * L * (p (1, i) - x (1, i))) (fun i => p (1, i))
    (by positivity) hp.2 vi1
  have r0 : ∀ i, 2 * L * (x (0, i) - p (0, i)) = ℓ * s * (GU i + l0 / ℓ * (p (0, i) / s)) := by
    intro i; have := hv0 i; simp only at this; field_simp; linarith
  have r1 : ∀ i, 2 * L * (x (1, i) - p (1, i)) =
      ℓ * s * ((GA i + GB i) + l1 / ℓ * (p (1, i) / s)) := by
    intro i; have := hv1 i; simp only at this; field_simp; linarith
  set l := l0 / ℓ
  set mm := l1 / ℓ
  set Su := ∑ i ∈ (Finset.univ.map ⟨C.πU, C.hU⟩)ᶜ, (p (0, i) / s) ^ 2
  set Sab := ∑ i ∈ (Finset.univ.map ⟨C.πA, C.hA⟩ ∪ Finset.univ.map ⟨C.πB, C.hB⟩)ᶜ, (p (1, i) / s) ^ 2
  have hSu : 0 ≤ Su := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSab : 0 ≤ Sab := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hblk0 : ∑ i, (p (0, i) / s) ^ 2 = sq1 u + Su := by
    rw [split_sum C.πU C.hU]; rfl
  have hblk1 : ∑ i, (p (1, i) / s) ^ 2 = sq2 a + sq2 b + Sab := by
    rw [split_sum2 C.πA C.πB C.hA C.hB C.hAB]; rfl
  have hsq0 : ∑ i, (p (0, i) / s) ^ 2 = blockSq p 0 / s ^ 2 := by
    simp only [blockSq, div_pow, ← Finset.sum_div]
  have hsq1 : ∑ i, (p (1, i) / s) ^ 2 = blockSq p 1 / s ^ 2 := by
    simp only [blockSq, div_pow, ← Finset.sum_div]
  set R2 := RU ^ 2 / s ^ 2
  have hR2 : 256 * (n + 1) ≤ R2 := by rw [le_div_iff₀ (by positivity)]; linarith
  have hABfeas : sq2 a + sq2 b + Sab ≤ Rab ^ 2 := by
    rw [← hblk1, hsq1]
    have : (2 * s) ^ 2 / s ^ 2 = Rab ^ 2 := by norm_num [Rab]; field_simp; ring
    rw [← this]; exact div_le_div_of_nonneg_right hp.2 (by positivity)
  have hlslack : 0 < l → sq1 u + Su = R2 := by
    intro hl
    have : 0 < l0 := by
      by_contra h; push Not at h
      have : l0 = 0 := le_antisymm h hl0
      simp [l, this] at hl
    have := hsl0 this
    rw [← hblk0, hsq0]; simp only [R2]; rw [← this]; rfl
  have hmslack : 0 < mm → sq2 a + sq2 b + Sab = Rab ^ 2 := by
    intro hm
    have : 0 < l1 := by
      by_contra h; push Not at h
      have : l1 = 0 := le_antisymm h hl1
      simp [mm, this] at hm
    have := hsl1 this
    rw [← hblk1, hsq1]
    have e : blockSq p 1 = (2 * s) ^ 2 := this
    rw [e]; norm_num [Rab]; field_simp; ring
  have hl : 0 ≤ l := div_nonneg hl0 hℓ.le
  have hm : 0 ≤ mm := div_nonneg hl1 hℓ.le
  have hxp : ‖x - p‖ < cδ / 3 * ℓ * s / (2 * L) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hT : u (Fin.last n) ≤ 1 / 4 := by
    have h1 : |x (0, C.πU (Fin.last n)) - p (0, C.πU (Fin.last n))| ≤ ‖x - p‖ := by
      have := PiLp.norm_apply_le (x - p) (0, C.πU (Fin.last n))
      simpa [PiLp.sub_apply, Real.norm_eq_abs] using this
    have h2 : p (0, C.πU (Fin.last n)) ≤ θ / 2 * s + cδ / 3 * ℓ * s / (2 * L) := by
      linarith [(abs_le.mp hx).2, (abs_le.mp h1).1, hxp]
    have h3 : u (Fin.last n) = p (0, C.πU (Fin.last n)) / s := rfl
    rw [h3, div_le_iff₀ hs]
    have : θ / 2 * s + cδ / 3 * ℓ * s / (2 * L) = (cδ / 3 * ℓ / (2 * L) + θ / 2) * s := by ring
    nlinarith
  have hpool := pooled u a b Su Sab l mm R2 hSu hSab hl hm hR2 hABfeas hlslack hmslack hT
  have b0 : ∑ i, (2 * L * (x (0, i) - p (0, i))) ^ 2 = (ℓ * s) ^ 2 * (resU u a b l + l ^ 2 * Su) := by
    have e : ∀ i, (2 * L * (x (0, i) - p (0, i))) ^ 2 = (ℓ * s) ^ 2 * (GU i + l * (p (0, i) / s)) ^ 2 := by
      intro i; rw [r0 i]; ring
    simp only [e, ← Finset.mul_sum]
    congr 1
    exact resid_split1 C.πU C.hU (gu u a b) (fun i => p (0, i) / s) l
  have b1 : ∑ i, (2 * L * (x (1, i) - p (1, i))) ^ 2 = (ℓ * s) ^ 2 * (resAB u a b mm + mm ^ 2 * Sab) := by
    have e : ∀ i, (2 * L * (x (1, i) - p (1, i))) ^ 2 =
        (ℓ * s) ^ 2 * (GA i + GB i + mm * (p (1, i) / s)) ^ 2 := by
      intro i; rw [r1 i]; ring
    simp only [e, ← Finset.mul_sum]
    congr 1
    exact resid_split2 C.πA C.πB C.hA C.hB C.hAB (fun i => (gab u a b i).1) (fun i => (gab u a b i).2)
      (fun i => p (1, i) / s) mm
  have hnorm : (2 * L * ‖x - p‖) ^ 2 = (ℓ * s) ^ 2 *
      (resU u a b l + l ^ 2 * Su + (resAB u a b mm + mm ^ 2 * Sab)) := by
    have hsplit : (2 * L * ‖x - p‖) ^ 2 = ∑ i, (2 * L * (x (0, i) - p (0, i))) ^ 2 +
        ∑ i, (2 * L * (x (1, i) - p (1, i))) ^ 2 := by
      rw [mul_pow, norm_sq_prim, blockSq_eq, blockSq_eq, mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp only [PiLp.sub_apply] <;> ring
    rw [hsplit, b0, b1]; ring
  have hpos : 0 ≤ cδ / 3 * ℓ * s := by have : (0 : ℝ) < cδ := by norm_num [cδ]
                                       positivity
  have hsq : (2 * L * ‖x - p‖) ^ 2 < (cδ / 3 * ℓ * s) ^ 2 :=
    pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  rw [hnorm] at hsq
  have : (ℓ * s) ^ 2 * (cδ / 3) ^ 2 ≤ (ℓ * s) ^ 2 *
      (resU u a b l + l ^ 2 * Su + (resAB u a b mm + mm ^ 2 * Sab)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  nlinarith

end LongTails.Proofs.NcConcavePartThree
