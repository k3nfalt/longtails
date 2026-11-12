import LongTails.Includes
import LongTails.TemplateLowerBound

open MeasureTheory

namespace OracleTemplate

universe v uP₁ uD₁ uP₂ uD₂ uI uQ uR uO

private def succeeds {Q : Type uQ} {R : Type uR} {Out : Type uO} {n : ℕ}
    (success : {Ω : Type} → [MeasurableSpace Ω] → (Ω → Out) → ProbabilityMeasure Ω → Prop)
    (A : Algorithm Q R Out n) (O : Oracle Q R n) (budget : Fin n → ℕ) : Prop :=
  success (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A budget seed.1 seed.2)
    ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩

private lemma succeeds_cast {Q₁ Q₂ : Type uQ} {R₁ R₂ : Type uR} {Out₁ Out₂ : Type uO}
    {n₁ n₂ : ℕ} (hq : Q₁ = Q₂) (hr : R₁ = R₂) (ho : Out₁ = Out₂) (hn : n₁ = n₂)
    (success₁ : {Ω : Type} → [MeasurableSpace Ω] → (Ω → Out₁) → ProbabilityMeasure Ω → Prop)
    (success₂ : {Ω : Type} → [MeasurableSpace Ω] → (Ω → Out₂) → ProbabilityMeasure Ω → Prop)
    (hs : ∀ {Ω : Type} [MeasurableSpace Ω] (output : Ω → Out₂) (P : ProbabilityMeasure Ω),
      success₁ (fun ω => cast ho.symm (output ω)) P → success₂ output P)
    (A : Algorithm Q₁ R₁ Out₁ n₁) (O : Oracle Q₂ R₂ n₂) (budget : Fin n₁ → ℕ) :
    succeeds success₁ A (cast (by rw [hq, hr, hn]) O) budget →
      succeeds success₂ (cast (by rw [hq, hr, ho, hn]) A) O
        (fun i => budget (Fin.cast hn.symm i)) := by
  subst Q₂
  subst R₂
  subst Out₂
  subst n₂
  exact hs _ _

private lemma cast_apply {α : Sort*} {β : α → Sort v} {γ : Sort v}
    (f : (a : α) → β a) {a b : α} (h : a = b) (ha : β a = γ) (hb : β b = γ) :
    cast ha (f a) = cast hb (f b) := by
  subst b
  rfl

private lemma predicate_cast {α : Sort*} {β : α → Sort v}
    (P : (a : α) → β a → Prop) {a b : α} (h : a = b) (x : β a) :
    P a x → P b (cast (congrArg β h) x) := by
  subst b
  exact id

namespace Inclusion

variable {strong : Setup.{uP₁, uD₁, uI, uQ, uR, uO}}
  {weak : Setup.{uP₂, uD₂, uI, uQ, uR, uO}}

def mapBudget (h : Inclusion strong weak) (budget : strong.Params → Fin strong.numOracles → ℕ) :
    weak.Params → Fin weak.numOracles → ℕ :=
  fun p i => budget (h.mapParams p) (Fin.cast h.numOracles_eq.symm i)

lemma convergence (h : Inclusion strong weak)
    (budget : strong.Params → Fin strong.numOracles → ℕ)
    (hc : Convergence strong budget) : Convergence weak (h.mapBudget budget) := by
  obtain ⟨make, hc, ha⟩ := hc
  let makeWeak := fun q => cast
    (by rw [h.numOracles_eq, h.query_eq q, h.reply_eq q, h.output_eq q]) (make (h.mapPublic q))
  refine ⟨makeWeak, ?_, ?_⟩
  · intro p hp I O had
    have hq := (congrArg strong.Query (h.public_eq p)).trans (h.query_eq (weak.publicInput p))
    have hr := (congrArg strong.Reply (h.public_eq p)).trans (h.reply_eq (weak.publicInput p))
    have ho := (congrArg strong.Output (h.public_eq p)).trans (h.output_eq (weak.publicInput p))
    have hs := hc (h.mapParams p) (h.valid p hp) _ _ (h.admissible p hp I O had)
    have ht := succeeds_cast hq hr ho h.numOracles_eq
      (fun {_} _ output P => strong.successful (h.mapParams p)
        (cast (by rw [h.public_eq p, h.instance_eq]) I) output P)
      (fun {_} _ output P => weak.successful p I output P)
      (h.successful p hp I O had) (make (strong.publicInput (h.mapParams p))) O
      (budget (h.mapParams p)) hs
    have heq : cast (by rw [hq, hr, ho, h.numOracles_eq])
        (make (strong.publicInput (h.mapParams p))) = makeWeak (weak.publicInput p) :=
      cast_apply make (h.public_eq p) _ _
    rw [heq] at ht
    exact ht
  · intro p hp
    have hs := ha (h.mapParams p) (h.valid p hp)
    rw [h.public_eq p] at hs
    exact h.allowedAlgorithm (weak.publicInput p) _ hs

lemma nonconvergence (h : Inclusion strong weak)
    (budget : strong.Params → Fin strong.numOracles → ℕ)
    (coverage : ∀ p, strong.valid p → ∃ q, weak.valid q ∧ h.mapParams q = p)
    (hn : NonConvergence weak (h.mapBudget budget)) : NonConvergence strong budget := by
  intro p hp A ha b hb
  obtain ⟨q, hqvalid, rfl⟩ := coverage p hp
  have hq := (congrArg strong.Query (h.public_eq q)).trans (h.query_eq (weak.publicInput q))
  have hr := (congrArg strong.Reply (h.public_eq q)).trans (h.reply_eq (weak.publicInput q))
  have ho := (congrArg strong.Output (h.public_eq q)).trans (h.output_eq (weak.publicInput q))
  let Aw : Algorithm (weak.Query (weak.publicInput q)) (weak.Reply (weak.publicInput q))
      (weak.Output (weak.publicInput q)) weak.numOracles :=
    cast (by rw [hq, hr, ho, h.numOracles_eq]) A
  have hal := predicate_cast strong.allowedAlgorithm (h.public_eq q) A ha
  have haw : weak.allowedAlgorithm (weak.publicInput q) Aw := by
    simpa only [cast_cast] using h.allowedAlgorithm (weak.publicInput q) _ hal
  obtain ⟨I, O, had, hbad⟩ := hn q hqvalid Aw haw
    (fun i => b (Fin.cast h.numOracles_eq.symm i))
    (fun i => hb (Fin.cast h.numOracles_eq.symm i))
  refine ⟨cast (by rw [h.public_eq q, h.instance_eq]) I,
    cast (by rw [hq, hr, h.numOracles_eq]) O, h.admissible q hqvalid I O had, ?_⟩
  dsimp only
  intro hs
  exact hbad (succeeds_cast hq hr ho h.numOracles_eq
    (fun {_} _ output P => strong.successful (h.mapParams q)
      (cast (by rw [h.public_eq q, h.instance_eq]) I) output P)
    (fun {_} _ output P => weak.successful q I output P)
    (h.successful q hqvalid I O had) A O b hs)

end Inclusion

end OracleTemplate

namespace OracleTemplate.IncludesTests

example (S : Setup) : Includes S S := by
  exact ⟨{
    mapPublic := id
    mapParams := id
    public_eq := fun _ => rfl
    numOracles_eq := rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    instance_eq := fun _ => rfl
    valid := fun _ h => h
    allowedAlgorithm := fun _ _ h => h
    admissible := fun _ _ _ _ h => h
    successful := fun _ _ _ _ _ _ _ _ _ h => h }⟩

abbrev testSpec (success : Prop) : Setup where
  Params := Unit
  Public := Unit
  Instance _ := Unit
  Query _ := Unit
  Reply _ := Unit
  Output _ := Unit
  publicInput := id
  valid _ := True
  admissible _ _ _ := True
  successful _ _ _ _ := success

example : Includes (testSpec False) (testSpec True) := by
  exact ⟨{
    mapPublic := id
    mapParams := id
    public_eq := fun _ => rfl
    numOracles_eq := rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    instance_eq := fun _ => rfl
    valid := fun _ h => h
    allowedAlgorithm := fun _ _ h => h
    admissible := fun _ _ _ _ h => h
    successful := fun _ _ _ _ _ _ _ _ _ _ => trivial }⟩

example : ¬ Includes (testSpec True) (testSpec False) := by
  rintro ⟨h⟩
  exact h.successful () trivial () { answer := fun _ _ _ => () } trivial
    (fun _ : Unit => ()) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ trivial

example : ¬ Includes { testSpec True with valid := fun _ => False } (testSpec True) := by
  rintro ⟨h⟩
  exact h.valid () trivial

example : ¬ Includes (testSpec True) { testSpec True with allowedAlgorithm := fun _ _ => False } := by
  rintro ⟨h⟩
  exact h.allowedAlgorithm ()
    { State := Unit, initial := fun _ => (), query := fun _ => (0, ()),
      update := fun _ _ => (), output := fun _ => () } trivial

example : ¬ Includes { testSpec True with admissible := fun _ _ _ => False } (testSpec True) := by
  rintro ⟨h⟩
  exact h.admissible () trivial () { answer := fun _ _ _ => () } trivial

abbrev instanceSpec (target : Bool) : Setup :=
  { testSpec True with
    Instance := fun _ => Bool
    admissible := fun _ _ _ => True
    successful := fun _ I _ _ => I = target }

example : ¬ Includes (instanceSpec true) (instanceSpec false) := by
  rintro ⟨h⟩
  have hfalse := h.successful () trivial true { answer := fun _ _ _ => () } trivial
    (fun _ : Unit => ()) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
  have hf : true = false := hfalse (by simp [instanceSpec])
  cases hf

noncomputable def unitAlgorithm : Algorithm Unit Unit Unit where
  State := Unit
  initial _ := ()
  query _ := (0, ())
  update _ _ := ()
  output _ := ()

example (h : Inclusion (testSpec True) (testSpec True))
    (budget : Unit → Fin 1 → ℕ) : h.mapBudget budget = budget := by
  funext p i
  have hp : h.mapParams p = p := Subsingleton.elim _ _
  simp [Inclusion.mapBudget, hp]

example : ¬ (NonConvergence (testSpec False) (fun _ _ => 0) →
    NonConvergence (testSpec True) (fun _ _ => 0)) := by
  intro transfer
  have hard : NonConvergence (testSpec False) (fun _ _ => 0) := by
    intro p _ A _ b hb
    exact ⟨(), { answer := fun _ _ _ => () }, trivial, by simp⟩
  obtain ⟨I, O, _, hbad⟩ := transfer hard () trivial unitAlgorithm trivial (fun _ => 0) (fun _ => le_rfl)
  exact hbad trivial

abbrev parameterSpec : Setup where
  Params := Bool
  Public := Bool
  Instance _ := Unit
  Query _ := Unit
  Reply _ := Unit
  Output _ := Unit
  publicInput := id
  valid _ := True
  admissible _ _ _ := True
  successful p _ _ _ := p = true

example :
    Includes parameterSpec { parameterSpec with valid := fun p => p = false } ∧
    NonConvergence { parameterSpec with valid := fun p => p = false } (fun _ _ => 0) ∧
    ¬ NonConvergence parameterSpec (fun _ _ => 0) := by
  refine ⟨⟨{
    numOracles_eq := rfl
    mapParams := id
    mapPublic := id
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := fun _ _ => trivial
    admissible := fun _ _ _ _ h => h
    successful := fun _ _ _ _ _ _ _ _ _ h => h
    allowedAlgorithm := fun _ _ h => h }⟩, ?_, ?_⟩
  · intro p hp A _ b hb
    subst p
    exact ⟨(), { answer := fun _ _ _ => () }, trivial, by simp⟩
  · intro h
    obtain ⟨I, O, _, hbad⟩ := h true trivial unitAlgorithm trivial (fun _ => 0) (fun _ => le_rfl)
    exact hbad rfl

end OracleTemplate.IncludesTests
