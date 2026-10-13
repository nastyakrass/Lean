/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4 (10 points): Forward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (2 points). Prove the same theorem again,
this time by providing a proof
term.
Hint: There is an easy way. -/
theorem about_Impl_term :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fun (a b : Prop) (hor : ¬a ∨ b) (ha : a) =>
    Or.elim hor
      (fun hna : ¬a => False.elim (hna ha))
      (fun hb : b => hb)

 theorem about_Implterm ( a b: Prop):
     ¬ a ∨ b → a → b :=
  fun hab : ¬ a ∨ b ↦ Or.elim hab (fun hna: ¬a ↦ (fun ha : a ↦
  False.elim (hna ha))) (fun ha: b ↦ (fun _ : a ↦ ha))

/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
    fix a b : Prop
    assume hab : ¬ a ∨ b
    assume ha : a
    show b from
    by
    apply Or.elim hab
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }


/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
    (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
    Iff.intro
    (assume h : ∀x, p x ∨ q x
     show ∀x, q x ∨ p x from
     by
      intros
      specialize h x
      apply Or.elim h
      {
        intros
        right
        exact a

      }
      {
        intros
        left
        exact a

      }
      )
    (assume hc : ∀x, q x ∨ p x
     show ∀x, p x ∨ q x from
     by
      intros
      specialize hc x
      apply Or.elim hc
      {
        intros
        right
        exact a
      }
      {
        intros
        left
        exact a
      }
      )

/- 2.2 (3 points). We have proved or stated three of the six possible
implications between `ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the
exercise of lecture 3. Prove the three missing implications using structured
proofs, exploiting the three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem DN_of_EM :
    ExcludedMiddle →  DoubleNegation:=
    by
    rw [DoubleNegation]
    rw [ExcludedMiddle]
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
      exfalso
      exact (a_2 a_3)

    }

    theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
    by
    rw [DoubleNegation]
    rw[Peirce]
    intros
    specialize a a_1
    apply a
    rw[Not]
    intros
    apply a_3
    apply a_2
    intros
    apply False.elim (a_3 a_4)

  theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
    by
    rw [ExcludedMiddle]
    rw[Peirce]
    intros
    specialize a (a_1 ∨ ¬a_1)
    specialize a (a_1 ∨ ¬a_1)
    apply a
    intros
    apply a_2
    by_contra h
    apply h
    right
    rw[Not]
    intros
    apply h
    left
    exact a_3
    /- или вместо b  подставляем False -> exfalso ->  то же самое доказательство
    оно избыточное во всех случаях! -/


end BackwardProofs

end LoVe
