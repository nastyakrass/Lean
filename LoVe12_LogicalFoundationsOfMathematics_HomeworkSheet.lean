/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Homework 12 (10 points + 2 bonus points):
# Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (8 points): Even Numbers as a Subtype

Usually, the most convenient way to represent even natural numbers is to use the
larger type `ℕ`, which also includes the odd natural numbers. If we want to
quantify only over even numbers `n`, we can add an assumption `Even n` to our
theorem statement.

An alternative is to encode evenness in the type, using a subtype. We will
explore this approach.

1.1 (1 point). Define the type `Eveℕ` of even natural numbers, using the `Even`
predicate introduced in the lecture 5 demo. -/

#print Even

/-
inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)
-/

def Eveℕ : Type :=
    { n : ℕ // Even n }

/- 1.2 (1 point). Prove the following theorem about
 the `Even` predicate. You will
need it to answer question 1.3.

Hint: The theorems `add_assoc` and `add_comm` might be useful. -/

theorem Even.add {m n : ℕ} (hm : Even m) (hn : Even n) :
    Even (m + n) :=
  by
    induction hm generalizing n
    simp_all
    rw[add_assoc]
    apply a_ih
    rw[add_comm]
    apply Even.add_two
    simp_all




/- 1.3 (2 points). Define zero and addition of even numbers by filling in the
`sorry` placeholders. -/

def Eveℕ.zero : Eveℕ :=
  ⟨0, Even.zero⟩


 def Eveℕ.add (m n : Eveℕ) : Eveℕ :=
  ⟨Subtype.val m + Subtype.val n,
   Even.add (Subtype.property m) (Subtype.property n)⟩

/- 1.4 (4 points). Prove that addition of even numbers is commutative and
associative, and has 0 as an identity element. -/

theorem Eveℕ.add_comm (m n : Eveℕ) :
    Eveℕ.add m n = Eveℕ.add n m :=
  by
     apply Subtype.ext
    -- simp разворачивает определение Eveℕ.add, а add_comm меняет местами m.val и n.val
     simp_all [Eveℕ.add, Nat.add_comm]









theorem Eveℕ.add_assoc (l m n : Eveℕ) :
    Eveℕ.add (Eveℕ.add l m) n = Eveℕ.add l (Eveℕ.add m n) :=
  by
    apply Subtype.ext
    -- simp разворачивает определение Eveℕ.add, а add_comm меняет местами m.val и n.val
    simp_all [Eveℕ.add,  Nat.add_assoc]


theorem Eveℕ.add_iden_left (n : Eveℕ) :
    Eveℕ.add Eveℕ.zero n = n :=
  by
    apply Subtype.ext
    -- simp разворачивает определение Eveℕ.add, а add_comm меняет местами m.val и n.val
    simp_all [Eveℕ.add,  Eveℕ.zero]


theorem Eveℕ.add_iden_right (n : Eveℕ) :
    Eveℕ.add n Eveℕ.zero = n :=
  by
    apply Subtype.ext
    -- simp разворачивает определение Eveℕ.add, а add_comm меняет местами m.val и n.val
    simp_all [Eveℕ.add,  Eveℕ.zero]


/- ## Question 2 (2 points + 2 bonus points): Hilbert Choice

2.1 (2 bonus points). Prove the following theorem.

Hints:

* A good way to start is
 to make a case distinction on whether `∃n, f n < x`
  is true or false.

* The theorem `le_of_not_gt` might be useful. -/

theorem exists_minimal_arg_helper (f : ℕ → ℕ) :
    ∀x m, f m = x → ∃n, ∀i, f n ≤ f i
  | x, m, eq =>
    by
      intros
      by_cases h_exists : ∃n, f n < x
      rcases h_exists
      {
        apply exists_minimal_arg_helper f (f w) w
        simp_all

      }
      {
        exists m
        intro i
        simp_all[le_of_not_gt]
        }










/- Now this interesting theorem falls off: -/

theorem exists_minimal_arg (f : ℕ → ℕ) :
    ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
  exists_minimal_arg_helper f _ 0 (by rfl)

/- 2.2 (1 point). Use what you learned about Hilbert choice in the lecture to
define the following function, which returns the (or an) index
 of the minimal
element in `f`'s image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
  Classical.choose (exists_minimal_arg_helper f (f 0) 0 rfl)

/- 2.3 (1 point). Prove the following characteristic theorem about your
definition. -/

theorem minimal_arg_spec (f : ℕ → ℕ) :
    ∀i : ℕ, f (minimal_arg f) ≤ f i :=
  by
    intro i
    have h := exists_minimal_arg_helper f (f 0) 0 rfl
    exact Classical.choose_spec h i






end LoVe
