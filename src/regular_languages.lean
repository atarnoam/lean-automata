import DFA
import data.fintype.basic
import order.boolean_algebra
import data.quot
import language_addon


universes u

def is_regular {α : Type u} [fintype α] (l : language α) : Prop := 
∃ (Q : Type u) [fintype Q], ∃ (A : DFA α Q), DFA.language_of A = l

lemma is_regular_def {α : Type u} [fintype α] {l : language α} : (is_regular.{u}) l ↔ (∃ (Q : Type u) [fintype Q] (A : DFA α Q), DFA.language_of A = l) :=
iff.refl _

namespace regular_language

open DFA

section basics
/--
Here we prove basic things on regular languages, such as the they form a boolean algebra
-/

variables {α : Type u} [fintype α]
variables {l l' : language α}

lemma inf_regular : (is_regular.{u} l) → (is_regular.{u} l') → is_regular.{u} (l ⊓ l') :=
begin
  rintros ⟨Q, hQ, A, hA⟩,
  rintros ⟨Q', hQ', B, hB⟩,
  resetI,
  refine ⟨Q × Q', infer_instance, and_DFA A B, _⟩,
  rw [and_language, hA, hB],
end

lemma compl_regular : (is_regular.{u} l) → (is_regular.{u} lᶜ) :=
begin
  rintros ⟨Q, hQ, A, hA⟩,
  refine ⟨Q, hQ, compl_DFA A, _⟩,
  rw [compl_language, hA]
end

lemma compl_regular_iff : (is_regular.{u} lᶜ) ↔ (is_regular.{u} l) :=
begin
  split,
  intro h,
  rw ← compl_compl l,
  exact compl_regular h,
  exact compl_regular,
end

lemma sup_regular : (is_regular.{u} l) → (is_regular.{u} l') → is_regular.{u} (l ⊔ l') :=
begin
  intros hl hl',
  rw [←compl_compl (l ⊔ l'), compl_sup, compl_regular_iff],
  exact inf_regular (compl_regular hl) (compl_regular hl'),
end

end basics

section relation
/-!
### Myhill-Nerode theorem

Given `l`, we define an equivalence relation on `list α`. 
The main theorem is that `l` is regular iff the number of equivalence classes of this relation is finite.
-/


parameters {α : Type u} [fintype α]

section basic

parameters (l : language α)

def language_rel : list α → list α → Prop :=
λ x y, ∀ (w : list α), (x ++ w ∈ l) ↔ (y ++ w ∈ l)

parameter {l}

lemma iff_mem_language_of_equiv {x y : list α} (Rxy : language_rel x y) : x ∈ l ↔ y ∈ l :=
begin
  specialize Rxy [],
  repeat {rwa list.append_nil at Rxy},
end 

parameter (l)

lemma is_reflexive : reflexive (language_rel) := λ _ _, by refl
lemma is_symmetric : symmetric (language_rel) := λ _ _ hxy w, iff.symm (hxy w)
lemma is_transitive : transitive (language_rel) := λ _ _ _ hxy hyz w, iff.trans (hxy w) (hyz w)
lemma is_equivalence : equivalence (language_rel) := ⟨is_reflexive, is_symmetric, is_transitive⟩

instance language_space.setoid : setoid (list α) := setoid.mk language_rel is_equivalence

definition language_space := quotient language_space.setoid

parameter {l}

definition mk (x : list α) : language_space := @quotient.mk _ language_space.setoid x

@[simp] lemma mk_def (x : list α) : mk x = @quotient.mk _ language_space.setoid x := rfl

end basic

section finite_class_space
/-!
### Myhill-Nerode, first direction

We build an automaton accepting `l` whose states are `language_space l`.
As a consequence, if `language_space l` is finite, then `l` is regular.
-/

parameters (l : language α)

def DFA_of : DFA α (language_space l) := 
{
  start := mk [],
  accepting := begin
    apply quot.lift (∈ l),
    intros x y r,
    simp [iff_mem_language_of_equiv r],
  end,
  δ := begin
    apply quot.lift (λ (w : list α) (σ : α), (mk (w ++ [σ]) : language_space l)),
    intros x y r,
    ext σ,
    simp only [regular_language.mk_def, quotient.eq],
    intro w,
    simp [r (σ :: w)],
  end
}

@[simp] lemma DFA_start : DFA_of.start = mk [] := rfl
@[simp] lemma DFA_accepting (w : list α) : DFA_of.accepting (mk w) = (w ∈ l) := rfl
@[simp] lemma DFA_δ (w : list α) (σ : α) : DFA_of.δ (mk w) σ = mk (w ++ [σ]) := rfl

@[simp] lemma DFA_run_on (x y : list α) : run_on DFA_of (mk x) y = mk (x ++ y) :=
begin
  revert x,
  induction y with σ y;
  intros x,
  simp,
  exact is_reflexive l _,
  specialize y_ih (x ++ [σ]),
  simp at *,
  exact y_ih,
end

@[simp] lemma DFA_accepts (x : list α) : accepts DFA_of x ↔ x ∈ l :=
begin
  rw [accepts_def, DFA_start, DFA_run_on, DFA_accepting],
  simp,
end

lemma DFA_language : language_of DFA_of = l := by {ext, simp}

theorem regular_of_fintype_language_space [fintype (language_space l)] : is_regular l := 
  ⟨language_space l, infer_instance, DFA_of, DFA_language⟩

end finite_class_space

section regular
/-!
### Myhill-Nerode, the other direction.

Now we wish to prove that if `l` is regular then `language_space l` is finite.
We prove this using the functions `Q ↩ DFA_space ↠ language_space l`,
the first of which we constructed in DFA.relation.
-/
parameters {Q : Type u} (A : DFA α Q)

private def l := language_of A

@[simp] private lemma l_def : l = language_of A := rfl

lemma language_equiv_of_DFA_equiv (x y : list α) : DFA_rel A x y → language_rel l x y :=
begin
  intros r w,
  rw DFA_rel_def at r,
  rw [l_def, language_of_def, language_of_def, 
    accepts_def, accepts_def,
    ←run_chain_assoc, ←run_chain_assoc, r],
end

definition g : DFA_space A → language_space l := by exact quot.map id (language_equiv_of_DFA_equiv _)

@[simp] lemma g_def (w : list α) : g (DFA_space.mk w) = mk w := rfl

lemma g_surjective : function.surjective g :=
begin
  apply quotient.ind,
  intro w,
  use DFA_space.mk w,
  rw g_def,
  refl
end

open classical
local attribute [instance] prop_decidable

noncomputable instance fintype_language_space_of_regular (l : language α) (r : is_regular l) : fintype (language_space l) :=
begin
  choose Q fQ A hA using r,
  rw ← hA,
  resetI,
  haveI : fintype (DFA_space A) := DFA.fintype_DFA_space_of_fintype_states _,
  exact fintype.of_surjective _ (g_surjective _),
end

end regular

end relation

end regular_language

variable (α : Type u)
