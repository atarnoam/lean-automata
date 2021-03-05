import DFA
import data.fintype.basic
import order.boolean_algebra
import data.quot


universes u v

def is_regular {α : Type u} [fintype α] (l : language α) : Prop := 
∃ (σ : Type v) [fintype σ] (A : DFA α σ), A.accepts = l

lemma is_regular_def {α : Type u} [fintype α] {l : language α} : 
(is_regular.{u v}) l ↔ (∃ (σ : Type v) [fintype σ] (A : DFA α σ), A.accepts = l) :=
iff.refl _

namespace regular_language

open DFA

section basic
/--
Here we prove basic things on regular languages, such as the they form a boolean algebra
-/

variables {α : Type u} [fintype α]
variables {l l' : language α}

lemma inf_regular : (is_regular.{u v} l) → (is_regular.{u v} l') → is_regular.{u v} (l ⊓ l') :=
begin
  rintros ⟨σ, hσ, A, hA⟩,
  rintros ⟨τ, hτ, B, hB⟩,
  resetI,
  refine ⟨σ × τ, infer_instance, inter A B, _⟩,
  rw [inter_accepts, hA, hB],
end

lemma compl_regular : (is_regular.{u v} l) → (is_regular.{u v} lᶜ) :=
begin
  rintros ⟨Q, hQ, A, hA⟩,
  refine ⟨Q, hQ, A.compl, _⟩,
  rw [compl_accepts, hA]
end

lemma compl_regular_iff : (is_regular.{u v} lᶜ) ↔ (is_regular.{u v} l) :=
begin
  split,
  {
    intro h,
    rw ← compl_compl l,
    exact compl_regular h 
  },
  { exact compl_regular },
end

lemma sup_regular : (is_regular.{u v} l) → (is_regular.{u v} l') → is_regular.{u v} (l ⊔ l') :=
begin
  intros hl hl',
  rw [←compl_compl (l ⊔ l'), compl_sup, compl_regular_iff],
  exact inf_regular (compl_regular hl) (compl_regular hl'),
end

end basic

section relation
/-!
### Myhill-Nerode theorem

Given `l`, we define an equivalence relation on `list α`. 
The main theorem is that `l` is regular iff the number of 
equivalence classes of this relation is finite.
-/


parameters {α : Type u} [fintype α]

section basic

parameters (l : language α)

/--
A relation on `list α`, identifying `x, y` if for all 
`z : list α`, `(x ++ z ∈ l) ↔ (y ++ z ∈ l)`.
-/
def rel : list α → list α → Prop :=
λ x y, ∀ (z : list α), (x ++ z ∈ l) ↔ (y ++ z ∈ l)

parameter {l}

lemma iff_mem_language_of_equiv {x y : list α} (Rxy : rel x y) : x ∈ l ↔ y ∈ l :=
begin
  specialize Rxy [],
  repeat {rwa list.append_nil at Rxy},
end 

parameter (l)

lemma rel_refl : reflexive (rel) := λ _ _, by refl
lemma rel_symm : symmetric (rel) := λ _ _ hxy z, iff.symm (hxy z)
lemma rel_trans : transitive (rel) := λ _ _ _ hxy hyz z, iff.trans (hxy z) (hyz z)
lemma rel_equiv : equivalence (rel) := ⟨rel_refl, rel_symm, rel_trans⟩

instance space.setoid : setoid (list α) := setoid.mk rel rel_equiv

definition space := quotient space.setoid

parameter {l}

definition mk (x : list α) : space := @quotient.mk _ space.setoid x

@[simp] lemma mk_def (x : list α) : mk x = @quotient.mk _ space.setoid x := rfl

end basic

section finite_class_space
/-!
### Myhill-Nerode, first direction

We build an automaton accepting `l` whose states are `space l`.
As a consequence, if `space l` is finite, then `l` is regular.
-/

parameters (l : language α)

def to_DFA : DFA α (space l) := 
{
  step := begin
    apply quot.lift (λ (z : list α) (σ : α), (mk (z ++ [σ]) : space l)),
    intros x y r,
    ext σ,
    simp only [regular_language.mk_def, quotient.eq],
    intro z,
    simp [r (σ :: z)],
  end,
  start := mk [],
  accept := begin
    apply quot.lift (∈ l),
    intros x y r,
    simp [iff_mem_language_of_equiv r],
  end
}

@[simp] lemma to_DFA_step (w : list α) (σ : α) : to_DFA.step (mk w) σ = mk (w ++ [σ]) := rfl
@[simp] lemma to_DFA_start : to_DFA.start = mk [] := rfl
@[simp] lemma to_DFA_accept (w : list α) : (mk w) ∈ to_DFA.accept ↔ w ∈ l := by refl

@[simp] lemma to_DFA_eval_from (x y : list α) : eval_from to_DFA (mk x) y = mk (x ++ y) :=
begin
  induction y with σ y generalizing x,
  { 
    simp,
    exact rel_refl l _,
  },
  {
    specialize y_ih (x ++ [σ]),
    simp at *,
    exact y_ih,
  }
end

lemma to_DFA_accepts : accepts to_DFA = l :=
begin
  ext,
  rw [mem_accepts, to_DFA_start, to_DFA_eval_from, list.nil_append, to_DFA_accept],
end

theorem regular_of_fintype_language_space [fintype (space l)] : is_regular.{u u} l := 
  ⟨space l, infer_instance, to_DFA, to_DFA_accepts⟩

end finite_class_space

section regular
/-!
### Myhill-Nerode, the other direction.

Now we wish to prove that if `l` is regular then `space l` is finite.
We prove this using the canonical functions `Q ↩ DFA_space ↠ space l`,
the first of which we constructed in DFA.relation.
-/
parameters {Q : Type u} (A : DFA α Q)

private def l := A.accepts

@[simp] private lemma l_def : l = A.accepts := rfl

lemma language_rel_of_DFA_rel (x y : list α) : A.rel x y → rel l x y :=
begin
  intros r z,
  rw rel_def at r,
  rw [l_def, mem_accepts, mem_accepts, eval_from_of_append, eval_from_of_append,
  ← eval_def, ← eval_def, r],
end

definition language_space_of_DFA_space : A.space → space l := 
by exact quot.map id (language_rel_of_DFA_rel _)

@[simp] lemma language_space_of_DFA_space_def (w : list α) : 
language_space_of_DFA_space (DFA.space.mk w) = mk w := rfl

lemma language_space_of_DFA_space_surjective : function.surjective language_space_of_DFA_space :=
begin
  apply quotient.ind,
  intro w,
  use DFA.space.mk w,
  rw language_space_of_DFA_space_def,
  refl
end

open classical
local attribute [instance] prop_decidable

noncomputable instance fintype_language_space_of_regular (l : language α) (r : is_regular l) : 
fintype (space l) :=
begin
  choose Q fQ A hA using r,
  rw ← hA,
  resetI,
  haveI : fintype A.space := DFA.fintype_space_of_fintype_states _,
  exact fintype.of_surjective _ (language_space_of_DFA_space_surjective _),
end

end regular

end relation

end regular_language

variable (α : Type u)
