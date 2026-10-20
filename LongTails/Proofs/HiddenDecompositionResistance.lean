import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.HiddenDecompositionResistance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_unit_extension {K L : Submodule ℝ E} (hKL : K < L) :
    ∃ e : E, e ∈ L ∧ e ∈ Kᗮ ∧ ‖e‖ = 1 := by
  obtain ⟨v, hvL, hvK⟩ := IsConcreteLE.exists_of_lt hKL
  let d := v - K.starProjection v
  have hdL : d ∈ L := L.sub_mem hvL (hKL.le (K.starProjection_apply_mem v))
  have hdK : d ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have hd : d ≠ 0 := by
    intro h
    have he : v = K.starProjection v := sub_eq_zero.mp h
    exact hvK (he ▸ K.starProjection_apply_mem v)
  refine ⟨‖d‖⁻¹ • d, L.smul_mem _ hdL, Kᗮ.smul_mem _ hdK, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd)]

lemma rotate_into_extension {K L : Submodule ℝ E} (hKL : K < L) (v : E) :
    ∃ U : E ≃ₗᵢ[ℝ] E, (∀ x ∈ K, U x = x) ∧ U v ∈ L ∧ U.symm = U := by
  obtain ⟨e, heL, heK, hen⟩ := exists_unit_extension hKL
  let p := K.starProjection v
  let d := v - p
  let w := p + ‖d‖ • e
  have hp : p ∈ K := K.starProjection_apply_mem v
  have hd : d ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have hpe : ⟪p, e⟫ = 0 := (K.mem_orthogonal e).mp heK p hp
  have hpd : ⟪p, d⟫ = 0 := (K.mem_orthogonal d).mp hd p hp
  have hnorm : ‖v‖ = ‖w‖ := by
    have hv : v = p + d := by dsimp [d]; abel
    have h₁ : ‖v‖ ^ 2 = ‖p‖ ^ 2 + ‖d‖ ^ 2 := by
      rw [hv, norm_add_sq_real, hpd]
      ring
    have h₂ : ‖w‖ ^ 2 = ‖p‖ ^ 2 + ‖d‖ ^ 2 := by
      dsimp [w]
      rw [norm_add_sq_real, inner_smul_right, hpe, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), hen]
      ring
    nlinarith [norm_nonneg v, norm_nonneg w]
  have hwL : w ∈ L := L.add_mem (hKL.le hp) (L.smul_mem _ heL)
  have hvw : v - w ∈ Kᗮ := by
    have heq : v - w = d - ‖d‖ • e := by dsimp [w, d]; abel
    rw [heq]
    exact Kᗮ.sub_mem hd (Kᗮ.smul_mem _ heK)
  refine ⟨(ℝ ∙ (v - w))ᗮ.reflection, ?_, ?_, Submodule.reflection_symm⟩
  · intro x hx
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact (K.mem_orthogonal (v - w)).mp hvw x hx
  · rw [Submodule.reflection_sub hnorm]
    exact hwL

def krylov (A : E →ₗ[ℝ] E) (b : E) (n : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun j : Fin n => (A : E → E)^[j.val] b))

omit [FiniteDimensional ℝ E] in
lemma krylov_mono (A : E →ₗ[ℝ] E) (b : E) {m n : ℕ} (hmn : m ≤ n) :
    krylov A b m ≤ krylov A b n := by
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j.val, lt_of_lt_of_le j.isLt hmn⟩, rfl⟩

omit [FiniteDimensional ℝ E] in
lemma base_mem_krylov (A : E →ₗ[ℝ] E) (b : E) (n : ℕ) :
    b ∈ krylov A b (n + 1) := by
  apply Submodule.subset_span
  exact ⟨⟨0, by omega⟩, rfl⟩

omit [FiniteDimensional ℝ E] in
lemma map_mem_krylov (A : E →ₗ[ℝ] E) (b : E) (n : ℕ) {x : E}
    (hx : x ∈ krylov A b n) : A x ∈ krylov A b (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
      exact Function.iterate_succ_apply' (A : E → E) j.val b
  | zero => simpa only [map_zero] using (krylov A b (n + 1)).zero_mem
  | add x y _ _ hx hy =>
      simpa only [map_add] using (krylov A b (n + 1)).add_mem hx hy
  | smul r x _ hx =>
      simpa only [map_smul] using (krylov A b (n + 1)).smul_mem r hx

lemma krylov_strict_of_missing_root (A : E →ₗ[ℝ] E) (u : E) (hinj : Function.Injective A)
    {n j : ℕ} (hu : u ∉ krylov A (A u) n) (hj : j < n) :
    krylov A (A u) j < krylov A (A u) (j + 1) := by
  have hle := krylov_mono A (A u) (Nat.le_succ j)
  apply lt_of_le_of_ne hle
  intro he
  have hmap : ∀ x ∈ krylov A (A u) j, A x ∈ krylov A (A u) j := by
    intro x hx
    rw [he]
    exact map_mem_krylov A (A u) j hx
  let B : krylov A (A u) j →ₗ[ℝ] krylov A (A u) j :=
    { toFun := fun x => ⟨A x, hmap x x.property⟩
      map_add' := by intro x y; apply Subtype.ext; exact A.map_add x y
      map_smul' := by intro r x; apply Subtype.ext; exact A.map_smul r x }
  have hB : Function.Injective B := by
    intro x y hxy
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective B := LinearMap.surjective_of_injective hB
  have hb : A u ∈ krylov A (A u) j := by
    rw [he]
    exact base_mem_krylov A (A u) j
  obtain ⟨v, hv⟩ := hsurj ⟨A u, hb⟩
  have hvu : (v : E) = u := hinj (congrArg Subtype.val hv)
  apply hu
  have hvn := krylov_mono A (A u) hj.le v.property
  rwa [hvu] at hvn

def rotatedField (A : E →ₗ[ℝ] E) (b : E) (U : E ≃ₗᵢ[ℝ] E) (x : E) : E :=
  U (A (U.symm x) - b)

def trajectory {State : Type*} (A : E →ₗ[ℝ] E) (b : E) (U : E ≃ₗᵢ[ℝ] E)
    (initial : State) (query : State → E) (update : State → E → State) (n : ℕ) : State :=
  (fun state => update state (rotatedField A b U (query state)))^[n] initial

omit [FiniteDimensional ℝ E] in
lemma rotatedField_agrees (A : E →ₗ[ℝ] E) (b : E) (U V : E ≃ₗᵢ[ℝ] E)
    (K : Submodule ℝ E) (hV : ∀ x ∈ K, V x = x) (hVs : V.symm = V)
    (x : E) (hx : U.symm x ∈ K) (hAx : A (U.symm x) - b ∈ K) :
    rotatedField A b (V.trans U) x = rotatedField A b U x := by
  change U (V (A (V.symm (U.symm x)) - b)) = U (A (U.symm x) - b)
  rw [hVs, hV _ hx, hV _ hAx]

omit [FiniteDimensional ℝ E] in
lemma trajectory_prefix_agrees {State : Type*} (A : E →ₗ[ℝ] E) (b : E)
    (U V : E ≃ₗᵢ[ℝ] E) (initial : State) (query : State → E) (update : State → E → State)
    (n : ℕ)
    (hpast : ∀ j < n,
      U.symm (query (trajectory A b U initial query update j)) ∈ krylov A b (2 * j + 2))
    (hV : ∀ x ∈ krylov A b (2 * n + 1), V x = x) (hVs : V.symm = V) :
    ∀ j ≤ n, trajectory A b (V.trans U) initial query update j =
      trajectory A b U initial query update j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
      have hij := ih (by omega)
      have hp := hpast j (by omega)
      have hq : U.symm (query (trajectory A b U initial query update j)) ∈
          krylov A b (2 * n + 1) := krylov_mono A b (by omega) hp
      have ha : A (U.symm (query (trajectory A b U initial query update j))) - b ∈
          krylov A b (2 * n + 1) := by
        apply (krylov A b (2 * n + 1)).sub_mem
        · exact krylov_mono A b (by omega) (map_mem_krylov A b (2 * j + 2) hp)
        · exact base_mem_krylov A b (2 * n)
      simp only [trajectory, Function.iterate_succ_apply'] at hij ⊢
      change update (trajectory A b (V.trans U) initial query update j)
        (rotatedField A b (V.trans U) (query (trajectory A b (V.trans U) initial query update j))) =
        update (trajectory A b U initial query update j)
          (rotatedField A b U (query (trajectory A b U initial query update j)))
      change trajectory A b (V.trans U) initial query update j =
        trajectory A b U initial query update j at hij
      rw [hij, rotatedField_agrees A b U V _ hV hVs _ hq ha]

lemma resisting_queries {State : Type*} (A : E →ₗ[ℝ] E) (b : E)
    (initial : State) (query : State → E) (update : State → E → State) (n : ℕ)
    (hstrict : ∀ j < 2 * n, krylov A b j < krylov A b (j + 1)) :
    ∃ U : E ≃ₗᵢ[ℝ] E, ∀ j < n,
      U.symm (query (trajectory A b U initial query update j)) ∈ krylov A b (2 * j + 2) := by
  induction n with
  | zero => exact ⟨LinearIsometryEquiv.refl ℝ E, by intro j hj; omega⟩
  | succ n ih =>
      obtain ⟨U, hU⟩ := ih (fun j hj => hstrict j (by omega))
      have hstep : krylov A b (2 * n + 1) < krylov A b (2 * n + 2) := by
        simpa only [Nat.add_assoc] using hstrict (2 * n + 1) (by omega)
      obtain ⟨V, hV, hv, hVs⟩ := rotate_into_extension hstep
        (U.symm (query (trajectory A b U initial query update n)))
      have heq := trajectory_prefix_agrees A b U V initial query update n hU hV hVs
      refine ⟨V.trans U, ?_⟩
      intro j hj
      have hjn : j ≤ n := by omega
      rw [heq j hjn]
      change V.symm (U.symm (query (trajectory A b U initial query update j))) ∈ _
      rw [hVs]
      by_cases hje : j = n
      · subst j
        exact hv
      · have hjlt : j < n := by omega
        have hp := hU j hjlt
        rw [hV _ (krylov_mono A b (by omega) hp)]
        exact hp

lemma resisting_output {State : Type*} (A : E →ₗ[ℝ] E) (b : E)
    (initial : State) (query : State → E) (update : State → E → State) (output : State → E)
    (n : ℕ) (hstrict : ∀ j < 2 * n + 2, krylov A b j < krylov A b (j + 1)) :
    ∃ U : E ≃ₗᵢ[ℝ] E,
      U.symm (output (trajectory A b U initial query update n)) ∈ krylov A b (2 * n + 2) := by
  obtain ⟨U, hU⟩ := resisting_queries A b initial query update n
    (fun j hj => hstrict j (by omega))
  have hstep : krylov A b (2 * n + 1) < krylov A b (2 * n + 2) := by
    simpa only [Nat.add_assoc] using hstrict (2 * n + 1) (by omega)
  obtain ⟨V, hV, hv, hVs⟩ := rotate_into_extension hstep
    (U.symm (output (trajectory A b U initial query update n)))
  have heq := trajectory_prefix_agrees A b U V initial query update n hU hV hVs
  refine ⟨V.trans U, ?_⟩
  rw [heq n le_rfl]
  change V.symm (U.symm (output (trajectory A b U initial query update n))) ∈ _
  rw [hVs]
  exact hv

lemma resisting_error {State : Type*} (A : E →ₗ[ℝ] E) (u : E)
    (hinj : Function.Injective A)
    (initial : State) (query : State → E) (update : State → E → State) (output : State → E)
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ x ∈ krylov A (A u) (2 * n + 2), δ ≤ ‖x - u‖) :
    ∃ U : E ≃ₗᵢ[ℝ] E,
      δ ≤ ‖output (trajectory A (A u) U initial query update n) - U u‖ := by
  have hu : u ∉ krylov A (A u) (2 * n + 2) := by
    intro h
    have hh := hlower u h
    simp only [sub_self, norm_zero] at hh
    linarith
  obtain ⟨U, hU⟩ := resisting_output A (A u) initial query update output n
    (fun j hj => krylov_strict_of_missing_root A u hinj hu hj)
  refine ⟨U, ?_⟩
  have h := hlower _ hU
  have he : ‖output (trajectory A (A u) U initial query update n) - U u‖ =
      ‖U.symm (output (trajectory A (A u) U initial query update n)) - u‖ := by
    rw [← U.symm.norm_map, map_sub, U.symm_apply_apply]
  rw [he]
  exact h

end OracleTemplate.HiddenDecompositionResistance
