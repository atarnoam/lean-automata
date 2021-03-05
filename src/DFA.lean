import computability.DFA
import computability.language
import data.fintype.basic
import data.list

import language


universes u v w

namespace DFA

variables {α : Type u}
variables {σ τ : Type v}

section basics

variables {A : DFA α σ} (p : σ) (a : α) (x y : list α)

@[simp] lemma eval_from_nil : A.eval_from p [] = p :=
list.foldl_nil _ _

@[simp] lemma eval_from_cons : A.eval_from p (a :: x) = A.eval_from (A.step p a) x :=
list.foldl_cons _ _ _ _


@[simp] lemma eval_def : A.eval x = A.eval_from A.start x := rfl


attribute [simp] mem_accepts

end basics


section intersection

/-!
### Intersection automaton

Here we construct from two DFAs a DFA whose language is the intersection of the two DFAs, and prove it.
-/

variables (A : DFA α σ) (B : DFA α τ) (s : σ) (t : τ) (a : α) (x : list α)

/--
Given two DFAs, returns a DFA whose language is the intersection of the two DFAs' languages.
-/
def inter : DFA α (σ × τ):=
{
  step := λ ⟨s, t⟩ a, ⟨A.step s a, B.step t a⟩,
  start := ⟨A.start, B.start⟩,
  accept := { st | st.1 ∈ A.accept ∧ st.2 ∈ B.accept}
}

@[simp] lemma inter_step : (inter A B).step (s, t) a = (A.step s a, B.step t a) := rfl
@[simp] lemma inter_start : (inter A B).start = (A.start, B.start) := rfl
@[simp] lemma inter_accept : (s, t) ∈ (inter A B).accept  ↔ s ∈ A.accept ∧ t ∈ B.accept := 
iff.refl _

@[simp]
lemma inter_eval_from : eval_from (inter A B) (s, t) x = (eval_from A s x, eval_from B t x) :=
begin
  induction x with a x ih generalizing s t,
  { tauto },
  { simp [ih _ _] }
end

@[simp]
lemma inter_accepts : accepts (inter A B) = (accepts A) ⊓ (accepts B) := 
by {ext, simp}

end intersection

section complement
/-!
### Complement automaton

Here we construct a DFA whose language is the complement of the given DFA's language.
-/
 
variables (A : DFA α σ) (s : σ) (a : α) (x : list α) 

/--
Given a DFA, returns a DFA whose language is the complement of the given DFA's language.
-/
def compl : DFA α σ :=
{
  step := A.step,
  start := A.start,
  accept := { s | s ∉ A.accept }
}

@[simp] lemma compl_step : A.compl.step = A.step := rfl
@[simp] lemma compl_start : A.compl.start = A.start := rfl
@[simp] lemma compl_accept : s ∈ A.compl.accept ↔ s ∉ A.accept := by refl

@[simp]
lemma compl_eval_from : eval_from A.compl s x = eval_from A s x :=
begin
  induction x with a x ih generalizing s,
  { tauto },
  { simp [ih _] }
end

@[simp]
lemma compl_accepts : accepts (compl A) = (accepts A)ᶜ := 
by {ext, simp}

end complement

section relation
/-!
### Equivalence relation on `list α`
Here we give the basics of the equivalence relation on `list α` that we get for every DFA `A`,
defined as:
`x ≈ y ↔ A.eval x = A.eval y`.
-/

variables (A : DFA α σ)

/--
A relation on `list α`, identifying `x, y` if `A.eval x = A.eval y`.
-/
definition rel : list α → list α → Prop :=
λ x y, A.eval x = A.eval y

@[simp] lemma rel_def {x y : list α} : rel A x y ↔ A.eval x = A.eval y := by refl

lemma rel_refl : reflexive (rel A) := λ _, by rw rel_def
lemma rel_symm : symmetric (rel A) := λ _ _ hxy, eq.symm hxy
lemma rel_trans : transitive (rel A) := λ _ _ _ hxy hyz, eq.trans hxy hyz
lemma rel_equiv : equivalence (rel A) := ⟨rel_refl A, rel_symm A, rel_trans A⟩

instance space.setoid : setoid (list α) := setoid.mk A.rel A.rel_equiv

definition space := quotient (space.setoid A)

variable {A}

definition space.mk (x : list α) : space A := @quotient.mk _ (space.setoid A) x


@[simp] lemma space.mk_def (x : list α) : space.mk x = @quotient.mk _ (space.setoid A) x := rfl
@[simp] lemma space.mk_def' (x : list α) : @quotient.mk' _ (space.setoid A) x = space.mk x := rfl

variable (A)

-- The canonical map. We show it is injective, as a part of the proof of Myhill-Nerode.
def to_states : space A → σ :=
begin
  apply quot.lift A.eval,
  intros x y rab,
  rw (rel_def A).1 rab
end

@[simp] lemma to_states_def (x : list α) : to_states A (space.mk x) = A.eval x := rfl

lemma injective_to_states : function.injective (to_states A) :=
begin
  apply @quotient.ind₂' (list α) (list α) _ _ (λ ex ey, to_states A ex = to_states A ey → ex = ey) ,
  intros x y h,
  repeat {rw space.mk_def' _ at h, rw f_def A _ at h},
  simp,
  exact h,
end

-- What we actually care about, sadly noncomputable :(
noncomputable instance fintype_space_of_fintype_states [fintype σ] : fintype (space A) :=
fintype.of_injective (to_states A) (injective_to_states A)

end relation

end DFA

