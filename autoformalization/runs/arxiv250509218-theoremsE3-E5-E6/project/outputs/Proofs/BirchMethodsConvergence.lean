import outputs.Algorithms.BirchMethods
import LongTails.Proofs.BirchSgdConvergence
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import outputs.Setups.BirchLocalSgd
import outputs.Setups.BirchCycleSgd
import outputs.Setups.BirchAsyncLocalSgd

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.BirchMethods

open OracleTemplate OracleTemplate.BirchSgd LongTails.Setups.BirchSgd
open OracleTemplate.Rennala (Point Instance)

theorem chain_wellFormed (src : ℕ → ℕ) (cont : ℕ → Bool) (hsrc : ∀ k, src k ≤ k) :
    (chainTree src cont).WellFormed := by
  intro j
  have haux : ∀ k, chainAux src cont k ≤ 2 * k := by
    intro k
    unfold chainAux
    split_ifs
    · omega
    · have := hsrc k
      omega
  refine ⟨?_, ?_, ?_⟩
  · change (if j % 2 = 0 then chainAux src cont (j / 2) else j - 1) ≤ j
    split_ifs
    · have := haux (j / 2)
      omega
    · omega
  · change chainAux src cont (j / 2) ≤ j
    have := haux (j / 2)
    omega
  · change 2 * (j / 2) ≤ j
    omega

theorem chain_mainBranch (src : ℕ → ℕ) (cont : ℕ → Bool) :
    (chainTree src cont).IsMainBranch chainBranch := by
  refine ⟨rfl, fun k => ⟨?_, ?_⟩⟩
  · change 0 < 2 * (k + 1)
    omega
  · change (if (2 * (k + 1) - 1) % 2 = 0 then chainAux src cont ((2 * (k + 1) - 1) / 2)
      else 2 * (k + 1) - 1 - 1) = 2 * k
    rw [ite_eq_right (by omega)]
    omega

theorem chain_auxSample (src : ℕ → ℕ) (cont : ℕ → Bool) (k : ℕ) :
    (chainTree src cont).auxSample chainBranch k = 2 * k := by
  change 2 * ((2 * (k + 1) - 1) / 2) = 2 * k
  omega

theorem chain_auxNode (src : ℕ → ℕ) (cont : ℕ → Bool) (k : ℕ) :
    (chainTree src cont).auxNode chainBranch k = chainAux src cont k := by
  change chainAux src cont ((2 * ((2 * (k + 1) - 1) / 2)) / 2) = chainAux src cont k
  congr 1
  omega

theorem self_mem_ancestors (T : Tree) (hT : T.WellFormed) (y : ℕ) : y ∈ T.ancestors y := by
  rcases y with _ | j
  · exact Finset.mem_singleton_self 0
  · rw [ancestors_succ T j (hT j).1]
    exact Finset.mem_insert_self _ _

theorem chain_structure (src : ℕ → ℕ) (cont : ℕ → Bool) (hsrc : ∀ k, src k ≤ k)
    (hcont : ∀ k, cont k = true → 0 < k ∧ src k = src (k - 1)) (k : ℕ) :
    ∃ a, src k ≤ a ∧ a ≤ k ∧
      (chainTree src cont).repr (chainAux src cont k) =
        (chainTree src cont).repr (2 * src k) + (Finset.Ico a k).val.map (fun i => 2 * i) ∧
      (chainTree src cont).depth (chainAux src cont k) = src k + (k - a) ∧
      2 * src k ∈ (chainTree src cont).ancestors (chainAux src cont k) := by
  have hT := chain_wellFormed src cont hsrc
  induction k with
  | zero =>
    have hc0 : cont 0 = false := by
      cases h : cont 0
      · rfl
      · exact absurd (hcont 0 h).1 (lt_irrefl 0)
    have hs0 : src 0 = 0 := Nat.le_zero.mp (hsrc 0)
    have haux : chainAux src cont 0 = 2 * src 0 := by
      unfold chainAux
      rw [hc0]
      rfl
    refine ⟨0, by omega, le_rfl, ?_, ?_, ?_⟩
    · rw [haux]
      simp
    · rw [haux, hs0]
      rfl
    · rw [haux]
      exact self_mem_ancestors _ hT _
  | succ k ih =>
    obtain ⟨a, hsa, hak, hrepr, hdepth, hanc⟩ := ih
    cases hck : cont (k + 1) with
    | false =>
      have haux : chainAux src cont (k + 1) = 2 * src (k + 1) := by
        unfold chainAux
        rw [hck]
        rfl
      refine ⟨k + 1, hsrc (k + 1), le_rfl, ?_, ?_, ?_⟩
      · rw [haux]
        simp
      · rw [haux]
        change (chainTree src cont).depth (chainBranch (src (k + 1))) = _
        rw [branch_depth _ hT chainBranch (chain_mainBranch src cont) (src (k + 1))]
        omega
      · rw [haux]
        exact self_mem_ancestors _ hT _
    | true =>
      obtain ⟨-, hseq⟩ := hcont (k + 1) hck
      rw [Nat.add_sub_cancel] at hseq
      have haux : chainAux src cont (k + 1) = 2 * k + 1 := by
        unfold chainAux
        rw [hck]
        simp only [ite_true]
        omega
      have hb : (chainTree src cont).base (2 * k) = chainAux src cont k := by
        change (if 2 * k % 2 = 0 then chainAux src cont (2 * k / 2) else 2 * k - 1) = _
        rw [ite_eq_left (by omega)]
        congr 1
        omega
      have hg : (chainTree src cont).grad (2 * k) = 2 * k := by
        change 2 * (2 * k / 2) = 2 * k
        omega
      have hbk := (hT (2 * k)).1
      refine ⟨a, by omega, by omega, ?_, ?_, ?_⟩
      · rw [haux, repr_succ _ (2 * k) hbk, hb, hg, hrepr, hseq,
          Nat.Ico_succ_right_eq_insert_Ico hak, Finset.insert_val_of_notMem (by simp),
          Multiset.map_cons, Multiset.add_cons]
      · rw [haux, depth_succ _ (2 * k) hbk, hb, hdepth, hseq]
        omega
      · rw [haux, ancestors_succ _ (2 * k) hbk, hb, hseq]
        exact Finset.mem_insert_of_mem hanc

theorem chain_repr (src : ℕ → ℕ) (cont : ℕ → Bool) (hsrc : ∀ k, src k ≤ k)
    (hcont : ∀ k, cont k = true → 0 < k ∧ src k = src (k - 1)) :
    ReprContained (chainTree src cont) chainBranch := by
  intro k
  have hT := chain_wellFormed src cont hsrc
  have hm := chain_mainBranch src cont
  obtain ⟨a, hsa, hak, hrepr, -, -⟩ := chain_structure src cont hsrc hcont k
  rw [chain_auxNode, hrepr]
  have hI := branch_repr_Ico _ hT chainBranch hm (src k) k (hsrc k)
  have hsamp : (chainTree src cont).auxSample chainBranch = fun i => 2 * i :=
    funext (chain_auxSample src cont)
  rw [hsamp] at hI
  change _ ≤ (chainTree src cont).repr (chainBranch k)
  rw [hI]
  refine add_le_add (le_of_eq rfl) (Multiset.map_le_map ?_)
  exact Finset.val_le_iff.mpr (Finset.Ico_subset_Ico_left hsa)

theorem chain_dist (src : ℕ → ℕ) (cont : ℕ → Bool) (hsrc : ∀ k, src k ≤ k)
    (hcont : ∀ k, cont k = true → 0 < k ∧ src k = src (k - 1)) (k : ℕ) :
    (chainTree src cont).dist (chainBranch k) ((chainTree src cont).auxNode chainBranch k) ≤
      k - src k := by
  classical
  have hT := chain_wellFormed src cont hsrc
  have hm := chain_mainBranch src cont
  obtain ⟨a, hsa, hak, -, hdepth, hanc⟩ := chain_structure src cont hsrc hcont k
  rw [chain_auxNode]
  set T := chainTree src cont
  have hmem : 2 * src k ∈ T.ancestors (chainBranch k) ∩ T.ancestors (chainAux src cont k) := by
    refine Finset.mem_inter.mpr ⟨?_, hanc⟩
    rw [branch_ancestors T hT chainBranch hm k]
    exact Finset.mem_image.mpr ⟨src k, Finset.mem_range.mpr (by have := hsrc k; omega), rfl⟩
  have hsup : src k ≤ (T.ancestors (chainBranch k) ∩ T.ancestors (chainAux src cont k)).sup
      T.depth := by
    have h := Finset.le_sup (f := T.depth) hmem
    rwa [show 2 * src k = chainBranch (src k) from rfl, branch_depth T hT chainBranch hm] at h
  have hdk : T.depth (chainBranch k) = k := branch_depth T hT chainBranch hm k
  unfold Tree.dist
  rw [hdk, hdepth]
  omega

theorem chain_distanceBounded (src : ℕ → ℕ) (cont : ℕ → Bool) (hsrc : ∀ k, src k ≤ k)
    (hcont : ∀ k, cont k = true → 0 < k ∧ src k = src (k - 1)) (R : ℝ)
    (hR : ∀ k, ((k - src k : ℕ) : ℝ) ≤ R) :
    DistanceBounded (chainTree src cont) chainBranch R := by
  intro k
  refine le_trans ?_ (hR k)
  exact_mod_cast chain_dist src cont hsrc hcont k

theorem chainAux_le (src : ℕ → ℕ) (cont : ℕ → Bool) (hsrc : ∀ k, src k ≤ k) (k : ℕ) :
    chainAux src cont k ≤ 2 * k := by
  unfold chainAux
  split_ifs
  · omega
  · have := hsrc k
    omega

theorem realize_congr {d : ℕ} {Ω : Type} (T : Tree) (gamma : ℝ) (x0 : Point d)
    (g : Point d → Ω → Point d) (η η' : ℕ → Ω) (k : ℕ) (h : ∀ c < k, η c = η' c) :
    T.realize gamma x0 g η k = T.realize gamma x0 g η' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (T.realize gamma x0 g η k).step T gamma k
        (g ((T.realize gamma x0 g η k).nodes (T.point k)) (η k)) =
      (T.realize gamma x0 g η' k).step T gamma k
        (g ((T.realize gamma x0 g η' k).nodes (T.point k)) (η' k))
    rw [ih (fun c hc => h c (by omega)), h k (by omega)]

theorem vertex_congr {d : ℕ} {Ω : Type} (T : Tree) (gamma : ℝ) (x0 : Point d)
    (g : Point d → Ω → Point d) (η η' : ℕ → Ω) (j : ℕ) (h : ∀ c < j, η c = η' c) :
    T.vertex gamma x0 g η j = T.vertex gamma x0 g η' j := by
  change (T.realize gamma x0 g η j).nodes j = (T.realize gamma x0 g η' j).nodes j
  rw [realize_congr T gamma x0 g η η' j h]

theorem chain_sampleIndependent {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (src : ℕ → ℕ)
    (cont : ℕ → Bool) (hsrc : ∀ k, src k ≤ k) (gamma : ℝ) (x0 : Point d)
    (g : Point d → Ω → Point d) (hg : Measurable (Function.uncurry g)) (μ : Measure Ω)
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (η : ℕ → Ω) => η k) μ P) :
    SampleIndependent (chainTree src cont) chainBranch gamma x0 g P := by
  classical
  intro k
  set T := chainTree src cont with hTdef
  have hne : Nonempty (ℕ → Ω) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨η0⟩ := hne
  set S : Finset ℕ := Finset.range (2 * k) with hS
  let E : (S → Ω) → (ℕ → Ω) := fun ζ c => if h : c ∈ S then ζ ⟨c, h⟩ else η0 c
  have hEm : Measurable E := by
    refine Measurable.of_eval (fun c => ?_)
    by_cases h : c ∈ S
    · have e : (fun ζ : S → Ω => E ζ c) = fun ζ => ζ ⟨c, h⟩ := by
        funext ζ
        simp only [E, h, dite_true]
      rw [e]
      fun_prop
    · have e : (fun ζ : S → Ω => E ζ c) = fun _ => η0 c := by
        funext ζ
        simp only [E, h, dite_false]
      rw [e]
      exact measurable_const
  have hEη : ∀ η : ℕ → Ω, ∀ c < 2 * k, E (fun i : S => η i) c = η c := by
    intro η c hc
    have h : c ∈ S := Finset.mem_range.mpr hc
    simp only [E, h, dite_true]
  set Φ : (ℕ → Ω) → (Fin k → Point d × Point d × Ω) := fun η i =>
    (T.vertex gamma x0 g η (chainBranch (i.val + 1)),
      T.vertex gamma x0 g η (T.auxNode chainBranch (i.val + 1)),
      η (T.auxSample chainBranch i.val)) with hΦ
  have hΦm : Measurable Φ := past_measurable T chainBranch gamma x0 g hg k
  have hind := hiid.independent.indepFun_finset {2 * k} S (by simp [hS])
    (fun i => hiid.measurable i)
  have hev : Measurable (fun ζ : ({2 * k} : Finset ℕ) → Ω =>
      ζ ⟨2 * k, Finset.mem_singleton_self _⟩) := measurable_pi_apply _
  have hcomp := hind.comp (φ := fun ζ : ({2 * k} : Finset ℕ) → Ω =>
      ζ ⟨2 * k, Finset.mem_singleton_self _⟩) (ψ := Φ ∘ E)
    hev (hΦm.comp hEm)
  have hl : (fun η : ℕ → Ω => η (T.auxSample chainBranch k)) =
      (fun ζ : ({2 * k} : Finset ℕ) → Ω => ζ ⟨2 * k, Finset.mem_singleton_self _⟩) ∘
        (fun η : ℕ → Ω => fun i : ({2 * k} : Finset ℕ) => η i) := by
    funext η
    simp only [Function.comp, hTdef, chain_auxSample]
  have hr : (fun η : ℕ → Ω => Φ η) = (Φ ∘ E) ∘ (fun η : ℕ → Ω => fun i : S => η i) := by
    funext η
    change Φ η = Φ (E (fun i : S => η i))
    funext i
    have hi := i.isLt
    have hagree : ∀ c < 2 * (i.val + 1), η c = E (fun i : S => η i) c :=
      fun c hc => (hEη η c (by omega)).symm
    simp only [hΦ]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact vertex_congr T gamma x0 g _ _ _ hagree
    · refine vertex_congr T gamma x0 g _ _ _ (fun c hc => (hEη η c ?_).symm)
      have := chainAux_le src cont hsrc (i.val + 1)
      rw [hTdef, chain_auxNode] at hc
      omega
    · change η (T.auxSample chainBranch i.val) = E (fun i : S => η i) (T.auxSample chainBranch i.val)
      rw [hTdef, chain_auxSample, hEη η _ (by omega)]
  change IndepFun (fun η : ℕ → Ω => η (T.auxSample chainBranch k)) (fun η => Φ η) P
  rw [hl, hr]
  exact hcomp

theorem chainStep_facts (L σ ε Rt : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hRt : 0 < Rt) :
    0 < chainStep L σ ε Rt ∧ L * chainStep L σ ε Rt * Rt ≤ 1 / 2 ∧
      L * chainStep L σ ε Rt * σ ^ 2 ≤ ε / 4 ∧
      (L * chainStep L σ ε Rt * Rt = 1 / 2 ∨ L * chainStep L σ ε Rt * σ ^ 2 = ε / 4) := by
  set a : ℝ := 1 / (2 * Rt * L) with ha
  set b : ℝ := if σ = 0 then 1 / (2 * Rt * L) else ε / (4 * σ ^ 2 * L) with hb
  have hγ : chainStep L σ ε Rt = min a b := rfl
  have ha0 : 0 < a := by positivity
  have hLa : L * a * Rt = 1 / 2 := by rw [ha]; field_simp
  have hb0 : 0 < b := by
    rw [hb]; split_ifs with h
    · positivity
    · have : 0 < σ := lt_of_le_of_ne hσ (Ne.symm h)
      positivity
  have hbσ : L * b * σ ^ 2 ≤ ε / 4 ∧ (σ ≠ 0 → L * b * σ ^ 2 = ε / 4) := by
    rw [hb]; split_ifs with h
    · refine ⟨by rw [h]; nlinarith, fun h' => absurd h h'⟩
    · have : 0 < σ := lt_of_le_of_ne hσ (Ne.symm h)
      have e : L * (ε / (4 * σ ^ 2 * L)) * σ ^ 2 = ε / 4 := by field_simp
      exact ⟨e.le, fun _ => e⟩
  have hbR : σ = 0 → b = a := by
    intro h; rw [hb, ha]; simp [h]
  rw [hγ]
  refine ⟨lt_min ha0 hb0, ?_, ?_, ?_⟩
  · have h1 : L * min a b * Rt ≤ L * a * Rt := by
      have := min_le_left a b
      have : 0 ≤ L * Rt := by positivity
      nlinarith
    linarith
  · by_cases hσ0 : σ = 0
    · rw [hσ0]; nlinarith
    · have h1 : L * min a b * σ ^ 2 ≤ L * b * σ ^ 2 := by
        have := min_le_right a b
        have : 0 ≤ L * σ ^ 2 := by positivity
        nlinarith
      linarith [hbσ.1]
  · rcases min_choice a b with h | h
    · left; rw [h, hLa]
    · by_cases hσ0 : σ = 0
      · left; rw [h, hbR hσ0, hLa]
      · right; rw [h, hbσ.2 hσ0]

theorem poly_half (l r q : ℝ) (hl0 : 0 ≤ l) (hr0 : 0 ≤ r) (hrl : r + l ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) :
    (1 + r) * (1 + 2 * r) + (1 + 4 * q) * ((1 + r) * (1 + 2 * r) * q * (1 + 2 * r) +
      2 * (1 - l - 2 * r ^ 2) * q * (1 + r)) ≤
      (1 + 4 * q) * ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) := by
  nlinarith [mul_nonneg hr0 hq0, mul_nonneg hl0 hq0, mul_nonneg (mul_nonneg hr0 hr0) hq0,
    mul_nonneg (mul_nonneg hr0 hq0) hq0, mul_nonneg (mul_nonneg hl0 hq0) hq0,
    mul_nonneg hq0 (by linarith : (0:ℝ) ≤ 1/4 - q),
    mul_nonneg (mul_nonneg hr0 hq0) (by linarith : (0:ℝ) ≤ 1/2 - r - l),
    mul_nonneg (mul_nonneg hq0 hq0) (by linarith : (0:ℝ) ≤ 1/2 - r - l),
    mul_nonneg hq0 (by linarith : (0:ℝ) ≤ 1/2 - r - l),
    mul_nonneg (mul_nonneg (mul_nonneg hr0 hr0) hq0) hq0,
    mul_nonneg (mul_nonneg (mul_nonneg hr0 hr0) hr0) hq0]

theorem final_half (A B Y Kε l r q : ℝ) (hl0 : 0 ≤ l) (hr0 : 0 ≤ r) (hrl : r + l ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) (hK : 0 ≤ Kε)
    (hA : A + (1 - l - 2 * r ^ 2) * B ≤ Y + Kε * q * (1 + 2 * r))
    (hA3 : A ≤ (1 + r) * (1 + 2 * r) * B + 2 * (1 + r) * Kε * q)
    (hY : Y * (1 + 4 * q) ≤ Kε) : A ≤ Kε := by
  have hP0 : 0 < (1 + r) * (1 + 2 * r) := by positivity
  have hβ0 : 0 ≤ 1 - l - 2 * r ^ 2 := by nlinarith
  have hH := poly_half l r q hl0 hr0 hrl hq0 hq
  have h1 : ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) * A ≤
      (1 + r) * (1 + 2 * r) * Y + Kε * ((1 + r) * (1 + 2 * r) * q * (1 + 2 * r) +
        2 * (1 - l - 2 * r ^ 2) * q * (1 + r)) := by
    have e1 := mul_le_mul_of_nonneg_left hA hP0.le
    have e2 := mul_le_mul_of_nonneg_left hA3 hβ0
    linarith
  have h2 := mul_le_mul_of_nonneg_left hY hP0.le
  have e1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + 4 * q)
  have e2 := mul_le_mul_of_nonneg_left hH hK
  have hpos : 0 < (1 + 4 * q) * ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) := by
    positivity
  have h3 : (1 + 4 * q) * ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) * A ≤
      (1 + 4 * q) * ((1 + r) * (1 + 2 * r) + (1 - l - 2 * r ^ 2)) * Kε := by
    nlinarith
  exact le_of_mul_le_mul_left h3 hpos

theorem assembly_core (K : ℕ) (L σ ε R γ Δ : ℝ) (hL : 0 < L) (hε : 0 < ε) (hR : 0 ≤ R)
    (hγ0 : 0 < γ)
    (hq : L * γ * σ ^ 2 ≤ ε / 4)
    (a b D F : ℕ → ℝ) (p : ℕ → ℕ) (I : ℕ → Finset ℕ)
    (hb0 : ∀ k, 0 ≤ b k)
    (hstep : ∀ k, F (k + 1) ≤ F k - γ / 2 * a k - γ / 2 * (1 - L * γ) * b k +
      γ * L ^ 2 / 2 * D k + γ ^ 2 * L / 2 * σ ^ 2)
    (hFK : F 0 - F K ≤ Δ)
    (hI : ∀ k, I k ⊆ Finset.Ico (p k) k) (hpk : ∀ k, p k ≤ k)
    (hpR : ∀ k : ℕ, (k : ℝ) - (p k : ℝ) ≤ R)
    (hDk : ∀ k, D k ≤ 2 * γ ^ 2 * (I k).card * ((∑ i ∈ I k, b i) + σ ^ 2))
    (hyoung : ∀ k, L * γ * R * a k ≤ L * γ * R * (1 + L * γ * R) * b k +
      (1 + L * γ * R) * L ^ 2 * D k)
    (hzero : R = 0 → ∀ k, a k = b k) :
    (∑ k ∈ Finset.range K, a k) + (1 - L * γ - 2 * (L * γ * R) ^ 2) *
        (∑ k ∈ Finset.range K, b k) ≤
      2 * Δ / γ + K * ε * (L * γ * σ ^ 2 / ε) * (1 + 2 * (L * γ * R)) ∧
    (∑ k ∈ Finset.range K, a k) ≤ (1 + L * γ * R) * (1 + 2 * (L * γ * R)) *
        (∑ k ∈ Finset.range K, b k) +
      2 * (1 + L * γ * R) * (K * ε) * (L * γ * σ ^ 2 / ε) := by
  have hcard : ∀ k, ((I k).card : ℝ) ≤ R := by
    intro k
    have h := Finset.card_le_card (hI k)
    rw [Nat.card_Ico] at h
    have h' : ((I k).card : ℝ) ≤ ((k - p k : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub (hpk k)] at h'
    linarith [hpR k]
  have hDk' : ∀ k, D k ≤ 2 * γ ^ 2 * R * ((∑ i ∈ I k, b i) + σ ^ 2) := by
    intro k
    refine (hDk k).trans ?_
    have hnn : 0 ≤ (∑ i ∈ I k, b i) + σ ^ 2 :=
      add_nonneg (Finset.sum_nonneg (fun i _ => hb0 i)) (sq_nonneg σ)
    have h1 := mul_le_mul_of_nonneg_right (hcard k) hnn
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * γ ^ 2)
    linarith
  have hwin := window_sum K R hR p I hI hpR b hb0
  set A := ∑ k ∈ Finset.range K, a k with hAdef
  set B := ∑ k ∈ Finset.range K, b k with hBdef
  set Ds := ∑ k ∈ Finset.range K, D k with hDsdef
  have hE1 : γ / 2 * A + γ / 2 * (1 - L * γ) * B ≤ Δ + γ * L ^ 2 / 2 * Ds +
      K * (γ ^ 2 * L / 2 * σ ^ 2) := by
    have hs : ∀ k ∈ Finset.range K, F (k + 1) - F k ≤ -(γ / 2) * a k +
        (-(γ / 2 * (1 - L * γ))) * b k + γ * L ^ 2 / 2 * D k + γ ^ 2 * L / 2 * σ ^ 2 :=
      fun k _ => by linarith [hstep k]
    have hsum := Finset.sum_le_sum hs
    rw [Finset.sum_range_sub] at hsum
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hsum
    linarith
  have hE2 : Ds ≤ 2 * γ ^ 2 * R * (R * B + K * σ ^ 2) := by
    have hs : ∀ k ∈ Finset.range K, D k ≤ 2 * γ ^ 2 * R * ((∑ i ∈ I k, b i) + σ ^ 2) :=
      fun k _ => hDk' k
    have hsum := Finset.sum_le_sum hs
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hsum
    have h2 := mul_le_mul_of_nonneg_left hwin (by positivity : (0 : ℝ) ≤ 2 * γ ^ 2 * R)
    nlinarith
  have hq0 : 0 ≤ L * γ * σ ^ 2 / ε := by positivity
  have hq' : L * γ * σ ^ 2 / ε ≤ 1 / 4 := by rw [div_le_iff₀ hε]; linarith
  have hqε : K * ε * (L * γ * σ ^ 2 / ε) = K * (L * γ * σ ^ 2) := by field_simp
  have hq0 : 0 ≤ L * γ * σ ^ 2 / ε := by positivity
  have hqε : K * ε * (L * γ * σ ^ 2 / ε) = K * (L * γ * σ ^ 2) := by field_simp
  have hE3 : A ≤ (1 + L * γ * R) * (1 + 2 * (L * γ * R)) * B +
      2 * (1 + L * γ * R) * (K * ε) * (L * γ * σ ^ 2 / ε) := by
    rw [mul_assoc (2 * (1 + L * γ * R)) (K * ε), hqε]
    by_cases hR0 : R = 0
    · have hAB : A = B := Finset.sum_congr rfl (fun k _ => hzero hR0 k)
      rw [hR0, hAB]
      have : 0 ≤ (K : ℝ) * (L * γ * σ ^ 2) := by positivity
      nlinarith
    · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
      have hρp : 0 < L * γ * R := by positivity
      have hs : ∀ k ∈ Finset.range K, L * γ * R * a k ≤
          L * γ * R * (1 + L * γ * R) * b k + (1 + L * γ * R) * L ^ 2 * D k :=
        fun k _ => hyoung k
      have hsum := Finset.sum_le_sum hs
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        at hsum
      have hE2' := mul_le_mul_of_nonneg_left hE2
        (by positivity : (0 : ℝ) ≤ (1 + L * γ * R) * L ^ 2)
      have hkey : L * γ * R * A ≤ L * γ * R * ((1 + L * γ * R) * (1 + 2 * (L * γ * R)) * B +
          2 * (1 + L * γ * R) * (K * (L * γ * σ ^ 2))) := by
        have e1 : (1 + L * γ * R) * L ^ 2 * (2 * γ ^ 2 * R * (R * B + K * σ ^ 2)) =
            L * γ * R * (2 * (1 + L * γ * R) * (L * γ * R) * B +
              2 * (1 + L * γ * R) * (K * (L * γ * σ ^ 2))) := by ring
        nlinarith
      exact le_of_mul_le_mul_left hkey hρp
  have hA1 : A + (1 - L * γ - 2 * (L * γ * R) ^ 2) * B ≤
      2 * Δ / γ + K * ε * (L * γ * σ ^ 2 / ε) * (1 + 2 * (L * γ * R)) := by
    rw [hqε]
    have hE2' := mul_le_mul_of_nonneg_left hE2 (by positivity : (0 : ℝ) ≤ γ * L ^ 2 / 2)
    have e1 : γ * L ^ 2 / 2 * (2 * γ ^ 2 * R * (R * B + K * σ ^ 2)) =
        γ / 2 * (2 * (L * γ * R) ^ 2 * B + 2 * (L * γ * R) * (K * (L * γ * σ ^ 2))) := by ring
    have e2 : γ / 2 * (2 * Δ / γ) = Δ := by field_simp
    have e3 : K * (γ ^ 2 * L / 2 * σ ^ 2) = γ / 2 * (K * (L * γ * σ ^ 2)) := by ring
    have hmain : γ / 2 * (A + (1 - L * γ - 2 * (L * γ * R) ^ 2) * B) ≤
        γ / 2 * (2 * Δ / γ + K * (L * γ * σ ^ 2) * (1 + 2 * (L * γ * R))) := by
      rw [mul_add (γ / 2) (2 * Δ / γ), e2]
      nlinarith
    exact le_of_mul_le_mul_left hmain (by positivity)
  exact ⟨hA1, hE3⟩

theorem assembly_general (K : ℕ) (L σ ε R Rt γ Δ : ℝ) (hL : 0 < L) (hε : 0 < ε) (hR : 0 ≤ R)
    (hRt : R + 1 ≤ Rt) (hΔ : 0 ≤ Δ) (hγ0 : 0 < γ) (ht : L * γ * Rt ≤ 1 / 2)
    (hq : L * γ * σ ^ 2 ≤ ε / 4) (hcase : L * γ * Rt = 1 / 2 ∨ L * γ * σ ^ 2 = ε / 4)
    (a b D F : ℕ → ℝ) (p : ℕ → ℕ) (I : ℕ → Finset ℕ)
    (hb0 : ∀ k, 0 ≤ b k)
    (hstep : ∀ k, F (k + 1) ≤ F k - γ / 2 * a k - γ / 2 * (1 - L * γ) * b k +
      γ * L ^ 2 / 2 * D k + γ ^ 2 * L / 2 * σ ^ 2)
    (hFK : F 0 - F K ≤ Δ)
    (hI : ∀ k, I k ⊆ Finset.Ico (p k) k) (hpk : ∀ k, p k ≤ k)
    (hpR : ∀ k : ℕ, (k : ℝ) - (p k : ℝ) ≤ R)
    (hDk : ∀ k, D k ≤ 2 * γ ^ 2 * (I k).card * ((∑ i ∈ I k, b i) + σ ^ 2))
    (hyoung : ∀ k, L * γ * R * a k ≤ L * γ * R * (1 + L * γ * R) * b k +
      (1 + L * γ * R) * L ^ 2 * D k)
    (hzero : R = 0 → ∀ k, a k = b k)
    (hK : 4 * Rt * L * Δ / ε + 8 * σ ^ 2 * L * Δ / ε ^ 2 ≤ K) :
    ∑ k ∈ Finset.range K, a k ≤ K * ε := by
  have hlγ : 0 < L * γ := by positivity
  have hlam1 : L * γ ≤ 1 / 2 := by nlinarith
  have hrho1 : L * γ * R ≤ 1 / 2 := by nlinarith
  rcases hcase with hcase | hcase
  swap
  · have hK' : 4 * (R + 1) * L * Δ / ε + 8 * σ ^ 2 * L * Δ / ε ^ 2 ≤ K := by
      have : 4 * (R + 1) * L * Δ / ε ≤ 4 * Rt * L * Δ / ε := by
        apply div_le_div_of_nonneg_right _ hε.le
        have : 0 ≤ L * Δ := by positivity
        nlinarith
      linarith
    exact OracleTemplate.BirchSgd.assembly K L σ ε R γ Δ hL hε hR hγ0 hlam1 hrho1 hq
      (Or.inr (Or.inr hcase)) a b D F p I hb0 hstep hFK hI hpk hpR hDk hyoung hzero hK'
  obtain ⟨hA1, hE3⟩ := assembly_core K L σ ε R γ Δ hL hε hR hγ0 hq a b D F p I hb0
    hstep hFK hI hpk hpR hDk hyoung hzero
  set A := ∑ k ∈ Finset.range K, a k
  set B := ∑ k ∈ Finset.range K, b k
  have hq0 : 0 ≤ L * γ * σ ^ 2 / ε := by positivity
  have hq' : L * γ * σ ^ 2 / ε ≤ 1 / 4 := by rw [div_le_iff₀ hε]; linarith
  have hY : 2 * Δ / γ * (1 + 4 * (L * γ * σ ^ 2 / ε)) ≤ K * ε := by
    have e : 2 * Δ / γ * (1 + 4 * (L * γ * σ ^ 2 / ε)) =
        ε * (4 * Rt * L * Δ / ε + 8 * σ ^ 2 * L * Δ / ε ^ 2) := by
      have hRt' : Rt = 1 / (2 * L * γ) := by
        field_simp
        linarith
      rw [hRt']
      field_simp
      ring
    rw [e, mul_comm (K : ℝ) ε]
    exact mul_le_mul_of_nonneg_left hK hε.le
  exact final_half A B (2 * Δ / γ) (K * ε) (L * γ) (L * γ * R) (L * γ * σ ^ 2 / ε)
    hlγ.le (by positivity) (by nlinarith) hq0 hq' (by positivity) hA1 hE3 hY

theorem general_rate {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ)
    (L σ ε R Rt lower : ℝ) (x0 : Point d) (T : Tree) (m : ℕ → ℕ)
    (μ : MeasureTheory.ProbabilityMeasure Ω) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → Point d)
    (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hR : 0 ≤ R) (hRt : R + 1 ≤ Rt)
    (hsmooth : SmoothObjective f L) (hlower : LowerBounded f lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun η => η c) = (μ : Measure Ω))
    (hT : T.WellFormed) (hm : T.IsMainBranch m)
    (h1 : SampleIndependent T m (chainStep L σ ε Rt) x0 g (P : Measure (ℕ → Ω)))
    (h2 : ReprContained T m) (h3 : DistanceBounded T m R) (K : ℕ)
    (hK : 4 * Rt * L * (f x0 - lower) / ε + 8 * σ ^ 2 * L * (f x0 - lower) / ε ^ 2 ≤ K) :
    (∀ k, Integrable (fun η => ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (m k))‖ ^ 2)
      (P : Measure (ℕ → Ω))) ∧
    1 / (K : ℝ) * ∑ k ∈ Finset.range K,
      ∫ η, ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (m k))‖ ^ 2 ∂(P : Measure (ℕ → Ω)) ≤
      ε := by
  classical
  obtain ⟨hγ0, ht, hq, hcase⟩ := chainStep_facts L σ ε Rt hL hσ hε (by linarith)
  have hgm := hg.measurable
  have hXm := vertex_measurable T (chainStep L σ ε Rt) x0 g hgm
  have hmo := moments f L σ R T hT m hm μ P g (chainStep L σ ε Rt) x0 hsmooth hg hlaw h1 h2 h3
  have hgX : ∀ k, Integrable (fun η => ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (m k))‖ ^ 2)
      (P : Measure (ℕ → Ω)) := fun k =>
    (growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _) (hmo k).1).2
  refine ⟨hgX, ?_⟩
  have hgZ : ∀ k, Integrable (fun η =>
      ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k))‖ ^ 2)
      (P : Measure (ℕ → Ω)) := fun k =>
    (growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _) (hmo k).2.1).2
  have hXZ : ∀ k, Integrable (fun η => ‖T.vertex (chainStep L σ ε Rt) x0 g η (m k) -
      T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k)‖ ^ 2) (P : Measure (ℕ → Ω)) :=
    fun k => sub_sq_integrable (P : Measure (ℕ → Ω)) _ _ (hXm _) (hXm _) (hmo k).1 (hmo k).2.1
  choose p hpk hpR I hI hDb using fun k =>
    delay_bound f L σ R T hT m hm μ P g (chainStep L σ ε Rt) x0 hL hsmooth hg hlaw h1 h2 h3 k
  have hFK : (∫ η, f (T.vertex (chainStep L σ ε Rt) x0 g η (m 0)) ∂(P : Measure (ℕ → Ω))) -
      (∫ η, f (T.vertex (chainStep L σ ε Rt) x0 g η (m K)) ∂(P : Measure (ℕ → Ω))) ≤
      f x0 - lower := by
    have hfun : (fun η : ℕ → Ω => f (T.vertex (chainStep L σ ε Rt) x0 g η (m 0))) =
        fun _ => f x0 :=
      funext (fun η => by rw [(aux_zero T hT m hm R h2 h3 (chainStep L σ ε Rt) x0 g η).1])
    have hfi := (growth_integrable f L hL hsmooth (P : Measure (ℕ → Ω)) _ (hXm _) (hmo K).1).1
    have hlow := integral_mono (integrable_const lower) hfi (fun η => hlower _)
    rw [hfun, integral_const]
    rw [integral_const] at hlow
    simp only [probReal_univ, smul_eq_mul, one_mul] at hlow ⊢
    linarith
  have hyoung : ∀ k, L * chainStep L σ ε Rt * R *
      (∫ η, ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (m k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤
      L * chainStep L σ ε Rt * R * (1 + L * chainStep L σ ε Rt * R) *
        (∫ η, ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k))‖ ^ 2
          ∂(P : Measure (ℕ → Ω))) +
      (1 + L * chainStep L σ ε Rt * R) * L ^ 2 *
        (∫ η, ‖T.vertex (chainStep L σ ε Rt) x0 g η (m k) -
          T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) := by
    intro k
    have hρ0 : 0 ≤ L * chainStep L σ ε Rt * R := by positivity
    have i0 := (hgX k).const_mul (L * chainStep L σ ε Rt * R)
    have i1 := (hgZ k).const_mul (L * chainStep L σ ε Rt * R * (1 + L * chainStep L σ ε Rt * R))
    have i2 := (hXZ k).const_mul ((1 + L * chainStep L σ ε Rt * R) * L ^ 2)
    have i12 : Integrable (fun η => L * chainStep L σ ε Rt * R * (1 + L * chainStep L σ ε Rt * R) *
        ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k))‖ ^ 2 +
        (1 + L * chainStep L σ ε Rt * R) * L ^ 2 * ‖T.vertex (chainStep L σ ε Rt) x0 g η (m k) -
          T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k)‖ ^ 2) (P : Measure (ℕ → Ω)) :=
      i1.add i2
    have hmono := integral_mono i0 i12 (fun η => young_split _ L hρ0 _ _ _ _
      (hsmooth.2 (T.vertex (chainStep L σ ε Rt) x0 g η (m k))
        (T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k))))
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul] at hmono
    exact hmono
  have hzero : R = 0 → ∀ k,
      (∫ η, ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (m k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) =
      ∫ η, ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k))‖ ^ 2
        ∂(P : Measure (ℕ → Ω)) := by
    intro hR0 k
    obtain ⟨p', hp', hpR', I', hI', hZ'⟩ :=
      tree_gap (Ω := Ω) T hT m hm R h2 h3 (chainStep L σ ε Rt) x0 g k
    have hpk' : p' = k := by
      rw [hR0] at hpR'
      have : (k : ℝ) ≤ p' := by linarith
      have : k ≤ p' := by exact_mod_cast this
      omega
    have hIe : I' = ∅ := by
      rw [hpk', Finset.Ico_self] at hI'
      exact Finset.subset_empty.mp hI'
    congr 1
    funext η
    rw [hZ' η, hIe, Finset.sum_empty, smul_zero, add_zero]
  have hΔ : 0 ≤ f x0 - lower := sub_nonneg.mpr (hlower x0)
  have hA := assembly_general K L σ ε R Rt (chainStep L σ ε Rt) (f x0 - lower) hL hε hR hRt hΔ hγ0
    ht hq hcase
    (fun k => ∫ η, ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (m k))‖ ^ 2
      ∂(P : Measure (ℕ → Ω)))
    (fun k => ∫ η, ‖gradient f (T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k))‖ ^ 2
      ∂(P : Measure (ℕ → Ω)))
    (fun k => ∫ η, ‖T.vertex (chainStep L σ ε Rt) x0 g η (m k) -
      T.vertex (chainStep L σ ε Rt) x0 g η (T.auxNode m k)‖ ^ 2 ∂(P : Measure (ℕ → Ω)))
    (fun k => ∫ η, f (T.vertex (chainStep L σ ε Rt) x0 g η (m k)) ∂(P : Measure (ℕ → Ω)))
    p I (fun k => integral_nonneg (fun _ => sq_nonneg _))
    (fun k => expected_step f L σ R T hT m hm μ P g (chainStep L σ ε Rt) x0 hL hγ0.le hsmooth hg
      hlaw h1 h2 h3 k)
    hFK hI hpk hpR hDb hyoung hzero hK
  rcases Nat.eq_zero_or_pos K with hK0 | hKp
  · subst hK0
    simp only [Nat.cast_zero, div_zero, Finset.range_zero, Finset.sum_empty, mul_zero]
    exact hε.le
  · have hKr : (0 : ℝ) < K := by exact_mod_cast hKp
    rw [one_div, inv_mul_le_iff₀ hKr]
    exact hA

theorem local_src_le (B k : ℕ) : localSrc B k ≤ k := by
  exact Nat.mul_div_le k B

theorem local_cont (n B : ℕ) (M : ℕ → Fin n → ℕ) (hB : 0 < B) (hM : ∀ r, ∑ i, M r i = B)
    (k : ℕ) (h : localCont n B M k = true) : 0 < k ∧ localSrc B k = localSrc B (k - 1) := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have := hM 0
      simp at this
      omega
    · exact h0
  have h0mem : 0 ∈ localOffsets n M (k / B) := by
    refine Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have := (Finset.mem_filter.mp hj).2
    exact absurd (Fin.lt_def.mp this) (Nat.not_lt_zero _)
  have hmod : k % B ≠ 0 := by
    intro h0
    have h' := of_decide_eq_true h
    rw [h0] at h'
    exact h' h0mem
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at hmod
    · exact h0
  refine ⟨hk, ?_⟩
  unfold localSrc
  congr 1
  have e1 := Nat.div_add_mod k B
  have e2 := Nat.div_add_mod (k - 1) B
  have e3 := Nat.mod_lt k hB
  have e4 := Nat.mod_lt (k - 1) hB
  have hk1 : k - 1 = (k % B - 1) + B * (k / B) := by omega
  have hdiv : (k - 1) / B = k / B := by
    rw [hk1, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (show k % B - 1 < B by omega),
      Nat.zero_add]
  rw [hdiv]

theorem local_gap (B k : ℕ) (hB : 0 < B) : ((k - localSrc B k : ℕ) : ℝ) ≤ (B : ℝ) - 1 := by
  have h1 : k - localSrc B k = k % B := by
    unfold localSrc
    have := Nat.div_add_mod k B
    omega
  rw [h1]
  have h2 : k % B + 1 ≤ B := Nat.mod_lt k hB
  have h3 : ((k % B + 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast h2
  push_cast at h3
  linarith

theorem local_sgd_rate {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ)
    (L σ ε lower : ℝ) (x0 : Point d) (n B : ℕ) (M : ℕ → Fin n → ℕ)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Point d → Ω → Point d)
    (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hB : 0 < B) (hM : ∀ r, ∑ i, M r i = B)
    (hsmooth : SmoothObjective f L) (hlower : LowerBounded f lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (η : ℕ → Ω) => η k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (K : ℕ)
    (hK : 4 * B * L * (f x0 - lower) / ε + 8 * σ ^ 2 * L * (f x0 - lower) / ε ^ 2 ≤ K) :
    (localTree n B M).IsMainBranch chainBranch ∧
    (∀ k, Integrable (fun η => ‖gradient f
      ((localTree n B M).vertex (localStep L σ ε B) x0 g η (chainBranch k))‖ ^ 2)
      (P : Measure (ℕ → Ω))) ∧
    1 / (K : ℝ) * ∑ k ∈ Finset.range K,
      ∫ η, ‖gradient f ((localTree n B M).vertex (localStep L σ ε B) x0 g η (chainBranch k))‖ ^ 2
        ∂(P : Measure (ℕ → Ω)) ≤ ε := by
  have hsrc := local_src_le B
  have hcont := local_cont n B M hB hM
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  refine ⟨chain_mainBranch _ _, ?_⟩
  exact general_rate f L σ ε ((B : ℝ) - 1) B lower x0 (localTree n B M) chainBranch μ P g hL hσ
    hε (by linarith) (by linarith) hsmooth hlower hg (fun c => hiid.marginal c)
    (chain_wellFormed _ _ hsrc) (chain_mainBranch _ _)
    (chain_sampleIndependent _ _ hsrc _ x0 g hg.measurable _ _ hiid)
    (chain_repr _ _ hsrc hcont) (chain_distanceBounded _ _ hsrc hcont _ (fun k => local_gap B k hB))
    K hK

theorem div_pred_eq (B k : ℕ) (hB : 0 < B) (hmod : k % B ≠ 0) : (k - 1) / B = k / B := by
  have e1 := Nat.div_add_mod k B
  have e3 := Nat.mod_lt k hB
  have hk1 : k - 1 = (k % B - 1) + B * (k / B) := by omega
  rw [hk1, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (show k % B - 1 < B by omega),
    Nat.zero_add]

theorem async_src_le (M : ℕ) (δ : ℕ → ℕ) (k : ℕ) : asyncSrc M δ k ≤ k := by
  exact le_trans (Nat.mul_le_mul_left M (Nat.sub_le _ _)) (Nat.mul_div_le k M)

theorem async_cont (M : ℕ) (δ : ℕ → ℕ) (hM : 0 < M) (k : ℕ) (h : asyncCont M k = true) :
    0 < k ∧ asyncSrc M δ k = asyncSrc M δ (k - 1) := by
  have hmod : k % M ≠ 0 := of_decide_eq_true h
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at hmod
    · exact h0
  refine ⟨hk, ?_⟩
  unfold asyncSrc
  rw [div_pred_eq M k hM hmod]

theorem async_gap (B M : ℕ) (δ : ℕ → ℕ) (hM : 0 < M) (hδ : ∀ b, δ b ≤ b ∧ M * δ b < B)
    (k : ℕ) : ((k - asyncSrc M δ k : ℕ) : ℝ) ≤ (B : ℝ) + M - 2 := by
  have e1 := Nat.div_add_mod k M
  have e3 := Nat.mod_lt k hM
  obtain ⟨h1, h2⟩ := hδ (k / M)
  have hle : M * δ (k / M) ≤ M * (k / M) := Nat.mul_le_mul_left M h1
  have h3 : k - asyncSrc M δ k = M * δ (k / M) + k % M := by
    unfold asyncSrc
    rw [Nat.mul_sub]
    omega
  rw [h3]
  have h4 : M * δ (k / M) + k % M + 2 ≤ B + M := by omega
  have h5 : ((M * δ (k / M) + k % M + 2 : ℕ) : ℝ) ≤ ((B + M : ℕ) : ℝ) := by exact_mod_cast h4
  push_cast at h5 ⊢
  linarith

theorem async_local_rate {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ)
    (L σ ε lower : ℝ) (x0 : Point d) (B M : ℕ) (δ : ℕ → ℕ)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Point d → Ω → Point d)
    (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hB : 0 < B) (hM : 0 < M)
    (hδ : ∀ b, δ b ≤ b ∧ M * δ b < B)
    (hsmooth : SmoothObjective f L) (hlower : LowerBounded f lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (η : ℕ → Ω) => η k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (K : ℕ)
    (hK : 4 * (B + M - 1) * L * (f x0 - lower) / ε + 8 * σ ^ 2 * L * (f x0 - lower) / ε ^ 2 ≤ K) :
    (asyncTree M δ).IsMainBranch chainBranch ∧
    (∀ k, Integrable (fun η => ‖gradient f
      ((asyncTree M δ).vertex (asyncStep L σ ε B M) x0 g η (chainBranch k))‖ ^ 2)
      (P : Measure (ℕ → Ω))) ∧
    1 / (K : ℝ) * ∑ k ∈ Finset.range K,
      ∫ η, ‖gradient f ((asyncTree M δ).vertex (asyncStep L σ ε B M) x0 g η (chainBranch k))‖ ^ 2
        ∂(P : Measure (ℕ → Ω)) ≤ ε := by
  have hsrc := async_src_le M δ
  have hcont := async_cont M δ hM
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  refine ⟨chain_mainBranch _ _, ?_⟩
  exact general_rate f L σ ε ((B : ℝ) + M - 2) ((B : ℝ) + M - 1) lower x0 (asyncTree M δ)
    chainBranch μ P g hL hσ hε (by linarith) (by linarith) hsmooth hlower hg
    (fun c => hiid.marginal c) (chain_wellFormed _ _ hsrc) (chain_mainBranch _ _)
    (chain_sampleIndependent _ _ hsrc _ x0 g hg.measurable _ _ hiid)
    (chain_repr _ _ hsrc hcont)
    (chain_distanceBounded _ _ hsrc hcont _ (fun k => async_gap B M δ hM hδ k)) K hK

theorem cycle_length_pos (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) : 0 < cycleLength n s := by
  unfold cycleLength
  exact Nat.div_pos (by omega) hs

theorem cycle_group_pos (n s g : ℕ) (hs : 0 < s) (hg : g < cycleLength n s) :
    0 < cycleGroup n s g := by
  unfold cycleGroup
  refine Finset.card_pos.mpr ⟨g * s, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
  · have h1 : cycleLength n s * s ≤ n + s - 1 := Nat.div_mul_le_self _ _
    have h2 : (g + 1) * s ≤ cycleLength n s * s := Nat.mul_le_mul_right s hg
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  · exact Nat.mul_div_cancel g hs

theorem cycle_count_pos (n s t : ℕ) (hs : 0 < s) (hsn : s ≤ n) :
    0 < cycleGroup n s (t % cycleLength n s) * cycleSteps n s t := by
  have hm := cycle_length_pos n s hs hsn
  refine Nat.mul_pos (cycle_group_pos n s _ hs (Nat.mod_lt _ hm)) ?_
  unfold cycleSteps
  omega

theorem cycle_pos_succ (n s t : ℕ) :
    cyclePos n s (t + 1) =
      cyclePos n s t + cycleGroup n s (t % cycleLength n s) * cycleSteps n s t := by
  unfold cyclePos
  rw [Finset.sum_range_succ]

theorem cycle_pos_mono (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (t t' : ℕ) (h : t < t') :
    cyclePos n s t + 1 ≤ cyclePos n s t' := by
  induction t', h using Nat.le_induction with
  | base =>
    rw [cycle_pos_succ]
    have := cycle_count_pos n s t hs hsn
    omega
  | succ t' _ ih =>
    rw [cycle_pos_succ]
    omega

theorem cycle_pos_ge (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (t : ℕ) : t ≤ cyclePos n s t := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    have := cycle_pos_mono n s hs hsn t (t + 1) (Nat.lt_succ_self t)
    omega

theorem cycle_loop_spec (n s k : ℕ) (hs : 0 < s) (hsn : s ≤ n) :
    cyclePos n s (cycleLoop n s k) ≤ k ∧ k < cyclePos n s (cycleLoop n s k + 1) := by
  have h0 : cyclePos n s 0 ≤ k := by
    unfold cyclePos
    simp
  refine ⟨Nat.findGreatest_spec (P := fun t => cyclePos n s t ≤ k) (Nat.zero_le k) h0, ?_⟩
  have hle : cycleLoop n s k ≤ k := Nat.findGreatest_le k
  by_cases ht : cycleLoop n s k + 1 ≤ k
  · have := Nat.findGreatest_is_greatest (P := fun t => cyclePos n s t ≤ k)
      (Nat.lt_succ_self (cycleLoop n s k)) ht
    exact Nat.lt_of_not_le this
  · have hk : cycleLoop n s k = k := by omega
    rw [hk]
    have := cycle_pos_ge n s hs hsn (k + 1)
    omega

theorem cycle_loop_eq (n s k t : ℕ) (hs : 0 < s) (hsn : s ≤ n) (h1 : cyclePos n s t ≤ k)
    (h2 : k < cyclePos n s (t + 1)) : cycleLoop n s k = t := by
  obtain ⟨h3, h4⟩ := cycle_loop_spec n s k hs hsn
  rcases lt_trichotomy (cycleLoop n s k) t with h | h | h
  · have := cycle_pos_mono n s hs hsn (cycleLoop n s k) t h
    have h5 : cyclePos n s (cycleLoop n s k + 1) ≤ cyclePos n s t := by
      rcases Nat.lt_or_ge (cycleLoop n s k + 1) t with h' | h'
      · exact le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self _)
          (cycle_pos_mono n s hs hsn _ t h'))
      · rw [show cycleLoop n s k + 1 = t by omega]
    omega
  · exact h
  · have h5 : cyclePos n s (t + 1) ≤ cyclePos n s (cycleLoop n s k) := by
      rcases Nat.lt_or_ge (t + 1) (cycleLoop n s k) with h' | h'
      · exact le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self _)
          (cycle_pos_mono n s hs hsn _ _ h'))
      · rw [show t + 1 = cycleLoop n s k by omega]
    omega

theorem cycle_src_le (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (k : ℕ) : cycleSrc n s k ≤ k := by
  unfold cycleSrc
  split_ifs with h
  · have hm := cycle_length_pos n s hs hsn
    have h1 := (cycle_loop_spec n s k hs hsn).1
    rcases Nat.lt_or_ge (cycleLoop n s k + 1 - cycleLength n s) (cycleLoop n s k) with h' | h'
    · have := cycle_pos_mono n s hs hsn _ _ h'
      omega
    · rw [show cycleLoop n s k + 1 - cycleLength n s = cycleLoop n s k by omega]
      exact h1
  · exact Nat.zero_le k

theorem cycle_cont (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (k : ℕ) (h : cycleCont n s k = true) :
    0 < k ∧ cycleSrc n s k = cycleSrc n s (k - 1) := by
  have hmod := of_decide_eq_true h
  obtain ⟨h1, h2⟩ := cycle_loop_spec n s k hs hsn
  have hne : k - cyclePos n s (cycleLoop n s k) ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_mod] at hmod
    exact hmod rfl
  have hk : 0 < k := by omega
  refine ⟨hk, ?_⟩
  have hl : cycleLoop n s (k - 1) = cycleLoop n s k :=
    cycle_loop_eq n s (k - 1) _ hs hsn (by omega) (by omega)
  unfold cycleSrc
  rw [hl]

theorem cycle_window (n s a w : ℕ) (hs : 0 < s) (hsn : s ≤ n) (hw : w ≤ cycleLength n s) :
    ∑ u ∈ Finset.Ico a (a + w), cycleGroup n s (u % cycleLength n s) ≤ n := by
  classical
  have hm := cycle_length_pos n s hs hsn
  set G : ℕ → Finset ℕ := fun u =>
    (Finset.range n).filter fun i => i / s = u % cycleLength n s with hG
  have hdisj : (↑(Finset.Ico a (a + w)) : Set ℕ).PairwiseDisjoint G := by
    intro u hu u' hu' huu'
    simp only [Finset.coe_Ico, Set.mem_Ico] at hu hu'
    refine Finset.disjoint_left.mpr (fun i hi hi' => huu' ?_)
    have e1 := (Finset.mem_filter.mp hi).2
    have e2 := (Finset.mem_filter.mp hi').2
    have hmod : u % cycleLength n s = u' % cycleLength n s := e1.symm.trans e2
    rcases lt_trichotomy u u' with h | h | h
    · have hd : cycleLength n s ∣ u' - u := (Nat.modEq_iff_dvd' h.le).mp hmod
      have := Nat.le_of_dvd (by omega) hd
      omega
    · exact h
    · have hd : cycleLength n s ∣ u - u' := (Nat.modEq_iff_dvd' h.le).mp hmod.symm
      have := Nat.le_of_dvd (by omega) hd
      omega
  have hcard := Finset.card_biUnion hdisj
  have hsub : (Finset.Ico a (a + w)).biUnion G ⊆ Finset.range n := by
    intro i hi
    obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hu).1
  have := Finset.card_le_card hsub
  rw [Finset.card_range, hcard] at this
  exact this

theorem cycle_gap (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (k : ℕ) :
    k - cycleSrc n s k + 1 ≤ cycleLength n s * n := by
  have hm := cycle_length_pos n s hs hsn
  set m := cycleLength n s with hmdef
  obtain ⟨h1, h2⟩ := cycle_loop_spec n s k hs hsn
  set t := cycleLoop n s k with htdef
  set a := if m ≤ t then t + 1 - m else 0 with ha
  have hsrc : cycleSrc n s k = cyclePos n s a := by
    show (if m ≤ t then cyclePos n s (t + 1 - m) else 0) = cyclePos n s a
    rw [ha]
    split_ifs
    · rfl
    · unfold cyclePos
      rw [Finset.sum_range_zero]
  have hat : a ≤ t + 1 := by
    rw [ha]; split_ifs <;> omega
  have hw : t + 1 - a ≤ m := by
    rw [ha]; split_ifs <;> omega
  have hsplit : cyclePos n s (t + 1) = cyclePos n s a +
      ∑ u ∈ Finset.Ico a (t + 1), cycleGroup n s (u % m) * cycleSteps n s u := by
    unfold cyclePos
    rw [Finset.sum_range_add_sum_Ico _ hat]
  have hbound : ∑ u ∈ Finset.Ico a (t + 1), cycleGroup n s (u % m) * cycleSteps n s u ≤
      m * n := by
    calc ∑ u ∈ Finset.Ico a (t + 1), cycleGroup n s (u % m) * cycleSteps n s u
        ≤ ∑ u ∈ Finset.Ico a (t + 1), cycleGroup n s (u % m) * m := by
          refine Finset.sum_le_sum (fun u _ => Nat.mul_le_mul_left _ ?_)
          unfold cycleSteps
          exact min_le_right _ _
      _ = m * ∑ u ∈ Finset.Ico a (t + 1), cycleGroup n s (u % m) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun u _ => Nat.mul_comm _ _)
      _ ≤ m * n := by
          refine Nat.mul_le_mul_left m ?_
          have := cycle_window n s a (t + 1 - a) hs hsn hw
          rwa [Nat.add_sub_cancel' hat] at this
  rw [hsrc]
  show k - cyclePos n s a + 1 ≤ m * n
  have hmn : 1 ≤ m * n := Nat.mul_pos hm (by omega)
  omega

theorem cycle_step_eq (L σ ε : ℝ) (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (hL : 0 < L) :
    cycleStep L σ ε n s = chainStep L σ ε (2 * n ^ 2 / s) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have e : (s : ℝ) / (4 * n ^ 2 * L) = 1 / (2 * (2 * n ^ 2 / s) * L) := by
    field_simp
    ring
  unfold cycleStep chainStep
  rw [e]

theorem cycle_sgd_rate {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ)
    (L σ ε lower : ℝ) (x0 : Point d) (n s : ℕ)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Point d → Ω → Point d)
    (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hs : 0 < s) (hsn : s ≤ n)
    (hsmooth : SmoothObjective f L) (hlower : LowerBounded f lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω
      (μ : Measure Ω) f g σ)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (η : ℕ → Ω) => η k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (K : ℕ)
    (hK : 8 * n ^ 2 * L * (f x0 - lower) / (s * ε) + 8 * σ ^ 2 * L * (f x0 - lower) / ε ^ 2 ≤ K) :
    (cycleTree n s).IsMainBranch chainBranch ∧
    (∀ k, Integrable (fun η => ‖gradient f
      ((cycleTree n s).vertex (cycleStep L σ ε n s) x0 g η (chainBranch k))‖ ^ 2)
      (P : Measure (ℕ → Ω))) ∧
    1 / (K : ℝ) * ∑ k ∈ Finset.range K,
      ∫ η, ‖gradient f ((cycleTree n s).vertex (cycleStep L σ ε n s) x0 g η (chainBranch k))‖ ^ 2
        ∂(P : Measure (ℕ → Ω)) ≤ ε := by
  have hsrc := cycle_src_le n s hs hsn
  have hcont := cycle_cont n s hs hsn
  have hm := cycle_length_pos n s hs hsn
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hmn : (1 : ℝ) ≤ (cycleLength n s * n : ℕ) := by
    exact_mod_cast Nat.mul_pos hm (show 0 < n by omega)
  have hms : cycleLength n s * s ≤ n + s - 1 := Nat.div_mul_le_self _ _
  have hRt : ((cycleLength n s * n : ℕ) : ℝ) - 1 + 1 ≤ 2 * n ^ 2 / s := by
    rw [sub_add_cancel, le_div_iff₀ hs']
    have h1 : cycleLength n s * n * s ≤ 2 * n ^ 2 := by
      have : cycleLength n s * s * n ≤ (2 * n) * n := Nat.mul_le_mul_right n (by omega)
      nlinarith
    exact_mod_cast h1
  have hgap : ∀ k, ((k - cycleSrc n s k : ℕ) : ℝ) ≤ ((cycleLength n s * n : ℕ) : ℝ) - 1 := by
    intro k
    have h := cycle_gap n s hs hsn k
    have h' : ((k - cycleSrc n s k + 1 : ℕ) : ℝ) ≤ ((cycleLength n s * n : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    linarith
  have hK' : 4 * (2 * n ^ 2 / s) * L * (f x0 - lower) / ε +
      8 * σ ^ 2 * L * (f x0 - lower) / ε ^ 2 ≤ K := by
    have e : 4 * (2 * (n : ℝ) ^ 2 / s) * L * (f x0 - lower) / ε =
        8 * n ^ 2 * L * (f x0 - lower) / (s * ε) := by
      field_simp
      ring
    rw [e]
    exact hK
  rw [cycle_step_eq L σ ε n s hs hsn hL]
  refine ⟨chain_mainBranch _ _, ?_⟩
  exact general_rate f L σ ε (((cycleLength n s * n : ℕ) : ℝ) - 1) (2 * n ^ 2 / s) lower x0
    (cycleTree n s) chainBranch μ P g hL hσ hε (by linarith) hRt hsmooth hlower hg
    (fun c => hiid.marginal c) (chain_wellFormed _ _ hsrc) (chain_mainBranch _ _)
    (chain_sampleIndependent _ _ hsrc _ x0 g hg.measurable _ _ hiid)
    (chain_repr _ _ hsrc hcont) (chain_distanceBounded _ _ hsrc hcont _ hgap) K hK'

theorem horizon_bound (A C D1 D2 x Δ : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD1 : 0 < D1)
    (hD2 : 0 < D2) (hx : x ≤ Δ) :
    A * x / D1 + C * x / D2 ≤ ((⌈A * Δ / D1 + C * Δ / D2⌉₊ + 1 : ℕ) : ℝ) := by
  have h1 : A * x / D1 ≤ A * Δ / D1 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx hA) hD1.le
  have h2 : C * x / D2 ≤ C * Δ / D2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx hC) hD2.le
  have h3 := Nat.le_ceil (A * Δ / D1 + C * Δ / D2)
  push_cast
  linarith

theorem chain_success {Ω : Type} [MeasurableSpace Ω] (q : Public) (hT : q.tree.WellFormed)
    (hm : q.tree.IsMainBranch q.branch) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point q.d → Ω → Point q.d) (hg : Measurable (Function.uncurry g))
    (f : Point q.d → ℝ) (ε : ℝ)
    (hint : ∀ k, Integrable (fun η => ‖gradient f (q.tree.vertex q.gamma q.x0 g η (q.branch k))‖ ^ 2)
      (P : Measure (ℕ → Ω)))
    (hacc : 1 / ((q.K + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.range (q.K + 1),
      ∫ η, ‖gradient f (q.tree.vertex q.gamma q.x0 g η (q.branch k))‖ ^ 2
        ∂(P : Measure (ℕ → Ω)) ≤ ε) :
    Measurable (fun z : Fin (q.K + 1) × (ℕ → Ω) =>
      execute (gradientOracle P g) (birch q) (fun _ => q.branch q.K) z.1 z.2) ∧
    Integrable (fun z : Fin (q.K + 1) × (ℕ → Ω) => ‖gradient f
      (execute (gradientOracle P g) (birch q) (fun _ => q.branch q.K) z.1 z.2)‖ ^ 2)
      (((PMF.uniformOfFintype (Fin (q.K + 1))).toMeasure).prod (P : Measure (ℕ → Ω))) ∧
    (∫ z, ‖gradient f (execute (gradientOracle P g) (birch q) (fun _ => q.branch q.K)
      z.1 z.2)‖ ^ 2 ∂(((PMF.uniformOfFintype (Fin (q.K + 1))).toMeasure).prod
        (P : Measure (ℕ → Ω)))) ≤ ε := by
  classical
  let x : Fin (q.K + 1) → (ℕ → Ω) → Point q.d := fun j η =>
    q.tree.vertex q.gamma q.x0 g η (q.branch j.val)
  have hxm (j : Fin (q.K + 1)) : Measurable (x j) :=
    vertex_measurable q.tree _ q.x0 g hg _
  have hxi (j : Fin (q.K + 1)) : Integrable (fun η => ‖gradient f (x j η)‖ ^ 2)
      (P : Measure (ℕ → Ω)) := hint j.val
  have ha : (1 / ((q.K + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.K + 1),
      (∫ η, ‖gradient f (x j η)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ ε := by
    have hs := Fin.sum_univ_eq_sum_range (fun k => ∫ η, ‖gradient f
      (q.tree.vertex q.gamma q.x0 g η (q.branch k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) (q.K + 1)
    show (1 / ((q.K + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.K + 1), (fun k => ∫ η, ‖gradient f
      (q.tree.vertex q.gamma q.x0 g η (q.branch k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) (j : ℕ) ≤ ε
    rw [hs]
    exact hacc
  have hu := OracleTemplate.Rennala.uniform_prefix_accuracy P f q.K x ε hxm hxi ha
  have hpt : ∀ z : Fin (q.K + 1) × (ℕ → Ω),
      execute (gradientOracle P g) (birch q) (fun _ => q.branch q.K) z.1 z.2 = x z.1 z.2 :=
    fun z => execute_birch q hT hm P g z.1 z.2
  simp only [hpt]
  exact ⟨hu.1, hu.2.1, hu.2.2.2⟩

theorem local_success (p : outputs.Setups.BirchLocalSgd.Params)
    (hp : outputs.Setups.BirchLocalSgd.spec.valid p) (I : Instance p.d)
    (O : Oracle (Point p.d) (Point p.d))
    (hO : outputs.Setups.BirchLocalSgd.spec.admissible p I O) :
    outputs.Setups.BirchLocalSgd.spec.successful p I
      (fun z : (birch (outputs.Setups.BirchLocalSgd.publicInput p)).Seed ×
          ((k : ℕ) → O.Seed k) =>
        execute O (birch (outputs.Setups.BirchLocalSgd.publicInput p))
          (fun _ => 2 * ⌈4 * p.B * p.L * p.Δ / p.ε + 8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2⌉₊)
          z.1 z.2)
      ⟨((birch (outputs.Setups.BirchLocalSgd.publicInput p)).law : Measure _).prod
        (O.law : Measure _), inferInstance⟩ := by
  classical
  obtain ⟨hL, hσ, hε, hΔ, hB, hM⟩ := hp
  obtain ⟨hsm, hlow, hgap, Ω, mΩ, μ, P, g, hiid, hgs, rfl⟩ := hO
  let := mΩ
  set q := outputs.Setups.BirchLocalSgd.publicInput p with hq
  have hbound := horizon_bound (4 * p.B * p.L) (8 * p.σ ^ 2 * p.L) p.ε (p.ε ^ 2)
    (I.f p.x0 - I.lower) p.Δ (by positivity) (by positivity) hε (by positivity) hgap
  obtain ⟨-, hint, hacc⟩ := local_sgd_rate I.f p.L p.σ p.ε I.lower p.x0 p.n p.B p.M μ P g hL hσ hε
    hB hM hsm hlow hgs hiid _ hbound
  have hT : q.tree.WellFormed := chain_wellFormed _ _ (local_src_le p.B)
  have hm : q.tree.IsMainBranch q.branch := chain_mainBranch _ _
  exact chain_success q hT hm P g hgs.measurable I.f p.ε hint hacc

theorem cycle_success (p : outputs.Setups.BirchCycleSgd.Params)
    (hp : outputs.Setups.BirchCycleSgd.spec.valid p) (I : Instance p.d)
    (O : Oracle (Point p.d) (Point p.d))
    (hO : outputs.Setups.BirchCycleSgd.spec.admissible p I O) :
    outputs.Setups.BirchCycleSgd.spec.successful p I
      (fun z : (birch (outputs.Setups.BirchCycleSgd.publicInput p)).Seed ×
          ((k : ℕ) → O.Seed k) =>
        execute O (birch (outputs.Setups.BirchCycleSgd.publicInput p))
          (fun _ => 2 * ⌈8 * p.n ^ 2 * p.L * p.Δ / (p.s * p.ε) +
            8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2⌉₊)
          z.1 z.2)
      ⟨((birch (outputs.Setups.BirchCycleSgd.publicInput p)).law : Measure _).prod
        (O.law : Measure _), inferInstance⟩ := by
  classical
  obtain ⟨hL, hσ, hε, hΔ, hs, hsn⟩ := hp
  obtain ⟨hsm, hlow, hgap, Ω, mΩ, μ, P, g, hiid, hgs, rfl⟩ := hO
  let := mΩ
  set q := outputs.Setups.BirchCycleSgd.publicInput p with hq
  have hs' : (0 : ℝ) < p.s := by exact_mod_cast hs
  have hbound := horizon_bound (8 * p.n ^ 2 * p.L) (8 * p.σ ^ 2 * p.L) (p.s * p.ε) (p.ε ^ 2)
    (I.f p.x0 - I.lower) p.Δ (by positivity) (by positivity) (by positivity) (by positivity) hgap
  obtain ⟨-, hint, hacc⟩ := cycle_sgd_rate I.f p.L p.σ p.ε I.lower p.x0 p.n p.s μ P g hL hσ hε
    hs hsn hsm hlow hgs hiid _ hbound
  have hT : q.tree.WellFormed := chain_wellFormed _ _ (cycle_src_le p.n p.s hs hsn)
  have hm : q.tree.IsMainBranch q.branch := chain_mainBranch _ _
  exact chain_success q hT hm P g hgs.measurable I.f p.ε hint hacc

theorem async_success (p : outputs.Setups.BirchAsyncLocalSgd.Params)
    (hp : outputs.Setups.BirchAsyncLocalSgd.spec.valid p) (I : Instance p.d)
    (O : Oracle (Point p.d) (Point p.d))
    (hO : outputs.Setups.BirchAsyncLocalSgd.spec.admissible p I O) :
    outputs.Setups.BirchAsyncLocalSgd.spec.successful p I
      (fun z : (birch (outputs.Setups.BirchAsyncLocalSgd.publicInput p)).Seed ×
          ((k : ℕ) → O.Seed k) =>
        execute O (birch (outputs.Setups.BirchAsyncLocalSgd.publicInput p))
          (fun _ => 2 * ⌈4 * (p.B + p.M - 1) * p.L * p.Δ / p.ε +
            8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2⌉₊)
          z.1 z.2)
      ⟨((birch (outputs.Setups.BirchAsyncLocalSgd.publicInput p)).law : Measure _).prod
        (O.law : Measure _), inferInstance⟩ := by
  classical
  obtain ⟨hL, hσ, hε, hΔ, hB, hM, hδ⟩ := hp
  obtain ⟨hsm, hlow, hgap, Ω, mΩ, μ, P, g, hiid, hgs, rfl⟩ := hO
  let := mΩ
  set q := outputs.Setups.BirchAsyncLocalSgd.publicInput p with hq
  have hBr : (1 : ℝ) ≤ p.B := by exact_mod_cast hB
  have hMr : (1 : ℝ) ≤ p.M := by exact_mod_cast hM
  have hbound := horizon_bound (4 * (p.B + p.M - 1) * p.L) (8 * p.σ ^ 2 * p.L) p.ε (p.ε ^ 2)
    (I.f p.x0 - I.lower) p.Δ (by nlinarith) (by positivity) hε (by positivity) hgap
  obtain ⟨-, hint, hacc⟩ := async_local_rate I.f p.L p.σ p.ε I.lower p.x0 p.B p.M p.δ μ P g hL hσ
    hε hB hM hδ hsm hlow hgs hiid _ hbound
  have hT : q.tree.WellFormed := chain_wellFormed _ _ (async_src_le p.M p.δ)
  have hm : q.tree.IsMainBranch q.branch := chain_mainBranch _ _
  exact chain_success q hT hm P g hgs.measurable I.f p.ε hint hacc

end OracleTemplate.BirchMethods
