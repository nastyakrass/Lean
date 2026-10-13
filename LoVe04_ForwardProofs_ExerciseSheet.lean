/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
    a → a :=
  assume ha : a
  show a from
    ha

theorem K (a b : Prop) :
    a → b → b :=
  assume ha : a
  assume hb : b
  show b from
    hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  assume hcb : a → b → c
  assume hb : b
  assume ha : a
  show c from
     ((hcb ha) hb)


theorem proj_fst (a : Prop) :
    a → a → a :=
    assume ha : a
    assume haa: a
    show a from
      ha

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
    a → a → a :=
    assume ha : a
    assume haa: a
    show a from
      haa

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
     assume enot : a → b → c
     assume cat : a
     assume table : (a → c)
     assume hb : b
     show c from
       (table cat)


/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
    assume hab : a → b
    assume negb : ¬ b
    assume ha : a
    show False from
    (negb (hab ha))




/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
    Iff.intro
    (assume hall : ∀x, p x ∧ q x
     show (∀x, p x) ∧ (∀x, q x)  from
       by
         apply And.intro
         {
          intros
          specialize hall x
          apply And.left hall
         }
         {
          intros
          specialize hall x
          apply And.right hall
         }
)
    (assume cat : (∀x, p x) ∧ (∀x, q x)

     show ∀x, p x ∧ q x from
       by
         intros
         apply And.intro
         {
          apply And.left cat

         }
         {
          apply And.right cat

         }

         )


/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
    (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
     assume heq : (∃x, ∀y, p x y)
     show (∀y, ∃x, p x y) from
     by
       intros
       apply Exists.elim heq
       intros
       specialize a_1 y
       apply Exists.intro a
       exact a_1





/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/
macro "my_simp" : tactic =>
  `(tactic| simp [mul_comm, add_assoc, add_comm,
                  mul_assoc, add_zero, add_mul, mul_add])

theorem binomial_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
     (a + b) * (a + b) = (a + b) * a + (a + b) * b := by rw[mul_add]
     _ =  a * (a + b) + b * (a + b) := by my_simp
     _ = a * a + a * b + b * (a + b) := by rw[mul_add]
     _ = a * a + a * b + (b * a + b * b) := by rw[mul_add]
     _ = a * a + a * b + (a * b + b * b) := by my_simp
     _ = a * a + (a * b + a * b) + b * b := by ac_rfl
     _ = a * a + 2 * (a * b) + b * b := by rw [← Nat.two_mul (a * b)]
     _ = a * a + 2 * a * b + b * b := by ac_rfl

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binom_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  have h1 :
     (a + b) * (a + b) = (a + b) * a + (a + b) * b := by rw[mul_add]
  have h2 : (a + b) * a + (a + b) * b = a * (a + b) + b * (a + b) := by my_simp
  have h3 :  a * (a + b) + b * (a + b) = a * a + a * b + b * (a + b) := by rw[mul_add]
  have h4 :  a * a + a * b + b * (a + b) = a * a + a * b + (b * a + b * b) := by rw[mul_add]
  have h5 :  a * a + a * b + (b * a + b * b) = a * a + a * b + (a * b + b * b) := by my_simp
  have h6 :  a * a + a * b + (a * b + b * b) = a * a + (a * b + a * b) + b * b := by ac_rfl
  have h7 :   a * a + (a * b + a * b) + b * b = a * a + 2 * (a * b) + b * b := by rw [← Nat.two_mul (a * b)]
  have h8 :  a * a + 2 * (a * b) + b * b = a * a + 2 * a * b + b * b := by ac_rfl
  show _ from
    Eq.trans h1 (Eq.trans h2 (Eq.trans h3 (Eq.trans h4 (Eq.trans h5 (Eq.trans h6 (Eq.trans h7 h8))))))



/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
    False :=
    have ar := All.one_point_wrong (2 : ℕ) (fun x ↦ x < 3)
    by
     rcases ar
     have less : 2 < 3  := by norm_num
     have contr : 5 = 2 ∧ 5 < 3 := by
       specialize (mpr less) 5
       exact mpr
     simp_all

  theorem Al.proof_of_False :
    False :=
  have h := All.one_point_wrong (2 : ℕ) (fun x ↦ x < 3)
  have h_left := h.mpr (by norm_num)  -- 2 < 3
  have h_false := h_left 3
  show False from
  by
    simp_all





/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
    False := have h := Exists.one_point_wrong (2 : ℕ) (fun x ↦ x > 3)
    by
      rcases h
      simp_all
      specialize mp 5
      simp_all


end LoVe
