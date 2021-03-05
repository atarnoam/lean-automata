import computability.language
import data.fintype.basic
import language_addon


universes u v w

/--
The DFA is a left `α*`-module
-/
structure DFA (α : Type u) [fintype α] (Q : Type v) :=
(start : Q)
(accepting : set Q)
(δ : Q → α → Q)

namespace DFA

variables {α : Type u} [fintype α] {Q : Type v}

section basics

variables {A : DFA α Q} (q : Q) (σ : α) (w w' : list α)

def run_on (A : DFA α Q) (q : Q) (w : list α) : Q :=
begin
  revert q,
  induction w with σ w',
  exact id,
  exact λ q, w_ih (A.δ q σ)
end

local infix ` • ` := A.run_on

@[simp]
lemma run_on_nil : q • [] = q := rfl

@[simp]
lemma run_on_cons : q • (σ :: w) = (A.δ q σ) • w := rfl

@[simp] 
lemma run_chain_assoc : (q • w) • w' = q • (w ++ w') :=
begin
  revert q,
  induction w with σ w;
  intro q,
  rw [run_on_nil, list.nil_append],
  simp [w_ih _],
end

variable (A)

def accepts : Prop := A.accepting (A.run_on A.start w)

@[simp] lemma accepts_def : (accepts A w) ↔ A.accepting (A.start • w) := 
by rw accepts

local infix ` ⊨ `:50 := accepts

def language_of : language α := 
{w : list α | A ⊨ w}

@[simp] lemma language_of_def : w ∈ language_of A ↔ A ⊨ w := 
iff.refl _

local notation `L ` := language_of

end basics

section intersection
/-!
### Intersection automaton

Here we construct from two DFAs a DFA whose language is the intersection of the two DFAs, and prove it.
-/
variables {Q₁ Q₂ : Type v}
variables (A : DFA α Q₁) (B : DFA α Q₂) (q₁ : Q₁) (q₂ : Q₂) (σ : α) (w : list α) 

def and_DFA : DFA α (Q₁ × Q₂):=
{
  start := ⟨A.start, B.start⟩,
  accepting := λ ⟨q₁, q₂⟩, A.accepting q₁ ∧ B.accepting q₂,
  δ := λ ⟨q₁, q₂⟩ σ, ⟨A.δ q₁ σ, B.δ q₂ σ⟩
}

@[simp] lemma and_start : (and_DFA A B).start = ⟨A.start, B.start⟩ := rfl
@[simp] lemma and_step : (and_DFA A B).δ ⟨q₁, q₂⟩ σ = ⟨A.δ q₁ σ, B.δ q₂ σ⟩ := rfl
@[simp] lemma and_accepting : (and_DFA A B).accepting ⟨q₁, q₂⟩ ↔ A.accepting q₁ ∧ B.accepting q₂ := 
iff.refl _

@[simp]
lemma and_run : run_on (and_DFA A B) ⟨q₁, q₂⟩ w = ⟨run_on A q₁ w, run_on B q₂ w⟩ :=
begin
  revert q₁ q₂,
  induction w with σ w,
  simp,
  intros q₁ q₂,
  simp [w_ih _ _],
end

lemma and_accepts : accepts (and_DFA A B) w ↔ accepts A w ∧ accepts B w := by simp

theorem and_language : language_of (and_DFA A B) = language_of A ⊓ language_of B := 
by {ext, simp}

end intersection

section complement
/-!
### Complement automaton

Here we construct a DFA whose language is the complement of the given DFA.
-/
 
variables (A : DFA α Q) (q : Q) (σ : α) (w : list α) 

def compl_DFA : DFA α Q :=
{
  start := A.start,
  accepting := λ q, ¬A.accepting q,
  δ := A.δ
}

@[simp] lemma compl_start : (compl_DFA A).start = A.start := rfl
@[simp] lemma compl_step : (compl_DFA A).δ = A.δ := rfl
@[simp] lemma compl_accepting : (compl_DFA A).accepting q = ¬A.accepting q := rfl

@[simp]
lemma compl_run : run_on (compl_DFA A) q w = run_on A q w :=
begin
  revert q,
  induction w with σ w,
  simp,
  intro q,
  simp [w_ih _],
end

lemma compl_accepts : accepts (compl_DFA A) w ↔ ¬accepts A w := by simp

theorem compl_language : language_of (compl_DFA A) = (language_of A)ᶜ := by {ext, simp}

end complement

section relation
/-!
### Equivalence relation on `list α`
Here we give the basics of the equivalence relation on `list α` that we get for every DFA `A`,
defined as:
`x ~ y ↔ run_on A A.start x = run_on A A.start y`.

-/

variables (A : DFA α Q)

definition DFA_rel : list α → list α → Prop :=
λ x y, run_on A A.start x = run_on A A.start y

@[simp] lemma DFA_rel_def {x y : list α} : DFA_rel A x y ↔ run_on A A.start x = run_on A A.start y := by refl

lemma is_reflexive : reflexive (DFA_rel A) := λ _, by rw DFA_rel_def
lemma is_symmetric : symmetric (DFA_rel A) := λ _ _ hxy, eq.symm hxy
lemma is_transitive : transitive (DFA_rel A) := λ _ _ _ hxy hyz, eq.trans hxy hyz
lemma is_equivalence : equivalence (DFA_rel A) := ⟨is_reflexive A, is_symmetric A, is_transitive A⟩

instance DFA_space.setoid : setoid (list α) := setoid.mk (DFA_rel A) (is_equivalence _)

definition DFA_space := quotient (DFA_space.setoid A)

variable {A}

definition DFA_space.mk (x : list α) : DFA_space A := @quotient.mk _ (DFA_space.setoid A) x

@[simp] lemma DFA_space.mk_def (x : list α) : DFA_space.mk x = @quotient.mk _ (DFA_space.setoid A) x := rfl
@[simp] lemma DFA_space.mk_def' (x : list α) : @quotient.mk' _ (DFA_space.setoid A) x = DFA_space.mk x := rfl

variable (A)

-- The canonical map. We show it is injective, as a part of the proof of Myhill-Nerode.
def f : DFA_space A → Q :=
begin
  apply quot.lift (run_on A A.start),
  intros x y Rab,
  rw (DFA_rel_def A).1 Rab
end

@[simp] lemma f_def (x : list α) : f A (DFA_space.mk x) = run_on A A.start x := rfl

lemma injective_f : function.injective (f A) :=
begin
  apply @quotient.ind₂' (list α) (list α) _ _ (λ ex ey, f A ex = f A ey → ex = ey) ,
  intros x y h,
  repeat {rw DFA_space.mk_def' _ at h, rw f_def A _ at h},
  simp,
  exact h,
end

-- What we actually care about, sadly noncomputable :(
noncomputable instance fintype_DFA_space_of_fintype_states [fintype Q] : fintype (DFA_space A) :=
fintype.of_injective (f A) (injective_f A)

end relation

end DFA

