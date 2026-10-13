/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe12_LogicalFoundationsOfMathematics_Demo


/- # LoVe Exercise 12: Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Vectors as Subtypes

Recall the definition of vectors from the demo: -/

#check Vector

/- The following function adds two lists of integers elementwise.

 If one
function is longer than the other,
 the tail of the longer list is ignored. -/

def List.add : List ℤ → List ℤ → List ℤ
  | [],      []      => []
  | x :: xs, y :: ys => (x + y) :: List.add xs ys
  | [],      y :: ys => []
  | x :: xs, []      => []

/- 1.1. Show that if the lists have the same length,
 the resulting list also
has that length. -/

theorem List.length_add :
    ∀xs ys, List.length xs = List.length ys →
      List.length (List.add xs ys) = List.length xs
  | [], [] =>
    by
      simp_all[add]
  | x :: xs, y :: ys =>
    by
      intro h
      simp [List.add]
      apply List.length_add xs ys
      injection h
  | [], y :: ys =>
    by
     intro h
     simp [List.add]
  | x :: xs, [] =>
    by
     intro h
     simp_all [List.add]


/- 1.2. Define componentwise addition on vectors using `List.add` and
`List.length_add`. -/

  def Vector.add {n : ℕ} : Vector ℤ n → Vector ℤ n → Vector ℤ n
  | ⟨xs, hxs⟩, ⟨ys, hys⟩ =>
      have h_len : List.length xs = List.length ys := by
        simp_all
      have h_res : List.length (List.add xs ys) = n := by
        simp_all[List.length_add]
      ⟨List.add xs ys, h_res⟩

/- 1.3. Show that `List.add` and `Vector.add` are commutative. -/

theorem List.add.comm :
    ∀xs ys, List.add xs ys = List.add ys xs :=
      /-intro xs ys
      induction xs generalizing ys
      induction ys
      simp_all
      simp_all[add]
      rw [List.add.comm (head :: tail) ys]-/
     by
       intro xs ys
       induction xs generalizing ys with
      | nil =>
        induction ys <;> simp [List.add]
      | cons x xs ih =>
        induction ys with
        | nil => simp [List.add]
        | cons y ys =>
          simp_all [add]
          rw [add_comm]


theorem Vector.add.comm {n : ℕ} (u v : Vector ℤ n) :
    Vector.add u v = Vector.add v u :=
  by
    simp_all[Vector.add]
    aesop
    simp_all[List.add.comm]



/- ## Question 2: Integers as Quotients

Recall the construction of integers from the lecture, not to be confused with
Lean's predefined type `Int` (= `ℤ`): -/

#check Int.Setoid
#check Int.Setoid_Iff
#check Int

/- 2.1. Define negation on these integers. Observe that if `(p, n)` represents
an integer, then `(n, p)` represents its negation. -/

def Int.neg : Int → Int :=
  Quotient.lift
    (fun (pn : ℕ × ℕ) => ⟦(pn.2, pn.1)⟧)
    (by
       intro pn₁ pn₂ h
       apply Quotient.sound
       rw [Int.Setoid_Iff] at *
       linarith)

/- 2.2. Prove the following theorems about negation. -/

theorem Int.neg_eq (p n : ℕ) :
    Int.neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
  by rfl

theorem int.neg_neg (a : Int) :
    Int.neg (Int.neg a) = a :=
  by
    induction a using Quotient.inductionOn with
    | h pn =>
      cases pn with
      | mk p n => simp_all [Int.neg]


end LoVe
