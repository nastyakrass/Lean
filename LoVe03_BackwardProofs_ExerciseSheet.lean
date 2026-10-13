/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics such as `intro`,
`apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
    a → a :=
  by
   intro ha
   exact ha

theorem K (a b : Prop) :
    a → b → b :=
  by
    intro ha
    intro hb
    clear ha
    exact hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  by
    intros
    apply a_1
    exact a_3
    exact a_2


theorem proj_fst (a : Prop) :
    a → a → a :=
  by
    intros
    exact a_1

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
    a → a → a :=
    by
      intros
      exact a_2


theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  by
    intros
    apply a_3
    exact a_2

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  by
    intros
    rw [Not]
    intros
    apply a_2
    apply a_1
    exact a_3



/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by
    intros
    apply Iff.intro
    { intros
      apply And.intro
      intros
      specialize a x
      apply And.left
      exact a
      intros
      specialize a x
      apply And.right
      exact a

       }
    { intros
      apply And.intro
      rcases a with ⟨hA, hB⟩
      specialize hA x
      exact hA

      rcases a with ⟨hA, hB⟩
      specialize hB x
      exact hB
    }







/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [mul, add, ih]

#check add_succ

theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n :=
    by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [mul, add_succ, add, add_assoc, ih]


/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
    by
    induction n with
    | zero       =>  induction m  with
                    | zero => rfl
                    | succ m' ih =>  rw [mul_succ, ih,  mul, add, add_zero]

    | succ n' ih => simp [mul, mul_succ, ih, add_assoc, add_comm]

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  by
  induction n with
  | zero => simp [mul]
  | succ n' ih =>
    calc
      mul (mul l m) (Nat.succ n')
        = add (mul (mul l m) n') (mul l m)    := by simp [mul_succ, mul_comm, mul_add, ih, add_assoc, add_comm,
      mul, add, add_zero]
      _ = add (mul l (mul m n')) (mul l m)     := by rw [ ih ]
      _ = mul l (add (mul m n') m)             := by rw [mul_add]
      _ = mul l (mul m (Nat.succ n'))          := by simp [mul_succ, mul_comm, mul_add, ih, add_assoc, add_comm,
      mul, add, add_zero]



/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

macro "my_simp" : tactic =>
  `(tactic| simp [mul_succ, mul_comm, add_assoc, add_comm, mul, add, add_zero])

theorem add_mul (l m n : ℕ) :
    mul (add l m) n = add (mul n l) (mul n m) :=
    by
    induction n with
  | zero => my_simp
  | succ n' ih =>
    calc
      mul (add l m) (n' + 1)
        = add (mul (add l m) n') (add l m)    := by my_simp
      _ = add (add (mul n' l) (mul n' m)) (add l m) := by rw [ ih ]
      _ = add (mul n' l) (add (mul n' m) (add l m)) := by rw[ add_assoc ]
      _ = add (mul n' l) (add (add l m) (mul n' m)) := by my_simp
      _ = add (mul n' l) (add l (add m (mul n' m))) := by my_simp
      _ = add (add (mul n' l) l) (add m (mul n' m)) := by rw[ add_assoc ]
      _ = add (mul (n' + 1) l) (add m (mul n' m)) := by my_simp
      _ = add (mul (n' + 1) l) (add (mul n' m) m) := by my_simp
      _ = add (mul (n' + 1) l) (mul (n' + 1) m) := by my_simp




/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/



theorem Peirce_of_EM :
    ExcludedMiddle → Peirce :=
    by
    rw [ExcludedMiddle]
    rw[Peirce]
    intros
    specialize a a_1
    apply Or.elim
    {
      exact a
    }
    {
      intros
      exact a_3
    }
    {
      intros
      apply a_2
      intros
      apply False.elim (a_3 a_4)

      /-have h_impl : a_1 → b
       :=
      fun (h : a_1) => False.elim (a_3 h)
      apply a_2
      exact h_impl -/
    }


/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
    Peirce → DoubleNegation :=
    by
    rw [DoubleNegation]
    rw[Peirce]
    intros
    specialize a a_1
    specialize a ¬a_1
    apply a
    intros
    exfalso
    apply a_2
    rw[Not]
    intros
    exact a_2 (a_3 a_4)





/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
    by
    rw [DoubleNegation]
    rw [ExcludedMiddle]
    intros
    specialize a (a_1 ∨ ¬a_1)
    apply a
    intros
    rw[Not]
    intros
    apply a_2
    right
    rw[Not]
    intros
    apply a_2
    left
    exact a_3


end SorryTheorems

end BackwardProofs

end LoVe
