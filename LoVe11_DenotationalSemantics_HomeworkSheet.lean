/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe11_DenotationalSemantics_Demo


/- # LoVe Homework 11 (10 points + 2 bonus points): Denotational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

/- The following command enables noncomputable decidability on every `Prop`.
The `0` argument ensures this is used only when necessary; otherwise, it would
make some computable definitions noncomputable for Lean. Depending on how you
solve question 2.2, this command might help you. -/

attribute [instance 0] Classical.propDecidable

/- Denotational semantics are well suited to functional programming.
 In this
exercise, we will study some representations of functional programs
 in Lean and
their denotational semantics.

The `Nondet` type represents functional programs that can perform
nondeterministic computations: A program can choose between many
 different
computation paths / return values.
Returning no results at all is represented
by `fail`, and nondeterministic choice between two options,
identified by the
`Bool` values `true` and `false`, is represented by `choice`. -/

inductive Nondet (α : Type) : Type
  | just   : α → Nondet α
  | fail   : Nondet α
  | choice : (Bool → Nondet α) → Nondet α

namespace Nondet


/- ## Question 1 (5 points + 1 bonus point): The `Nondet` Monad

The `Nondet` inductive type forms a monad.
 The `pure` operator is `Nondet.just`.
`bind` is as follows: -/

def bind {α β : Type} : Nondet α → (α → Nondet β) → Nondet β
  | just a,   f => f a
  | fail,     f => fail
  | choice k, f => choice (fun b ↦ bind (k b) f)

instance : Pure Nondet :=
  { pure := just }

instance : Bind Nondet :=
  { bind := bind }

/- 1.1 (5 points). Prove the three monad laws for `Nondet`.

Hints:

* To unfold the definition of `pure` and `>>=`, invoke
  `simp [Bind.bind, Pure.pure]`.

* To reduce `f = g` to `∀x, f x = g x`, use the theorem `funext`. -/

theorem pure_bind {α β : Type} (a : α) (f : α → Nondet β) :
    pure a >>= f = f a :=
  by
    simp [Bind.bind, Pure.pure]
    funext
    simp_all[bind]



theorem bind_pure {α : Type} :
    ∀na : Nondet α, na >>= pure = na :=
  by
    simp [Bind.bind, Pure.pure, bind]
    funext
    intros
    cases na
    simp_all[bind]
    simp_all[bind]
    simp_all[bind]
    funext
    apply bind_pure

theorem bind_assoc {α β γ : Type} :
    ∀(na : Nondet α) (f : α → Nondet β) (g : β → Nondet γ),
      ((na >>= f) >>= g) = (na >>= (fun a ↦ f a >>= g)) :=
    by
      simp [Bind.bind, Pure.pure, bind]
      funext
      intros
      cases na
      simp_all[bind]
      simp_all[bind]
      simp_all[bind]
      funext
      apply bind_assoc






/- The function `portmanteau` computes a portmanteau of two lists: A
portmanteau of `xs` and `ys` has `xs` as a prefix and `ys` as a suffix,
 and they
overlap. We use `startsWith xs ys` to test that `ys` has `xs` as a prefix. -/

def startsWith : List ℕ → List ℕ → Bool
  | x :: xs, []      => false
  | [],      ys      => true
  | x :: xs, y :: ys => x = y && startsWith xs ys

#eval startsWith [1, 2] [1, 2, 3]
#eval startsWith [1, 2, 3] [1, 2]

def portmanteau : List ℕ → List ℕ → List (List ℕ)
| [],      ys => []
| x :: xs, ys =>
  List.map (List.cons x) (portmanteau xs ys) ++
  (if startsWith (x :: xs) ys then [ys] else [])

/- Here are some examples of portmanteaux: -/

#eval portmanteau [0, 1, 2, 3] [2, 3, 4]
#eval portmanteau [0, 1] [2, 3, 4]
#eval portmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4]

/- 1.2 (1 bonus point). Translate the `portmanteau` program from the `List`
monad to the `Nondet` monad. -/

def orElse {α : Type} (a b : Nondet α) : Nondet α :=
  Nondet.choice (fun (c : Bool) => if c then a else b)

def nondetPortmanteau : List ℕ → List ℕ → Nondet (List ℕ)
  | [],      ys => Nondet.fail
  | x :: xs, ys =>
      let result := nondetPortmanteau xs ys >>=
       (fun tail => Nondet.just (x :: tail))
      if startsWith (x :: xs) ys then
        Nondet.choice (fun b => if b then result else Nondet.just ys)
      else
        result

/- ## Question 2 (5 points + 1 bonus point): Nondeterminism, Denotationally

2.1 (2 points). Give a denotational semantics for `Nondet`,
 mapping it into a
`List` of all results. `pure` returns one result, `fail` returns zero, and
`choice` combines the results of either option. -/

def listSem {α : Type} : Nondet α → List α
  | Nondet.just a   => [a]
  | Nondet.fail     => []
  | Nondet.choice k => listSem (k true) ++ listSem (k false)

/- Check that the following lines give the same output as for `portmanteau` (if
you have answered question 1.2): -/

#reduce listSem (nondetPortmanteau [0, 1, 2, 3] [2, 3, 4])
#reduce listSem (nondetPortmanteau [0, 1] [2, 3, 4])
#reduce listSem (nondetPortmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4])

/- 2.2 (3 points). Often, we are not interested
in getting all outcomes, just
the first successful one. Give a semantics for `Nondet`
 that produces the first
successful result, if any. Your solution should *not* use `listSem`. -/

noncomputable def optionSem {α : Type} : Nondet α → Option α
  | Nondet.just a   => some a
  | Nondet.fail     => none
  | Nondet.choice k =>
      match optionSem (k true) with
      | some a => some a
      | none   => optionSem (k false)

/- 2.3 (1 bonus point). Prove the theorem `List_Option_compat` below, showing
that the two semantics you defined are compatible.

`List.head?` returns the head of a list wrapped in an `Option.some`, or
`Option.none` for an empty list. It corresponds to the function we called
`headOpt` in lecture 5. -/

theorem List_Option_compat {α : Type} :
    ∀na : Nondet α, optionSem na = List.head? (listSem na) :=
  by
   intros
   induction na
   simp_all [Bind.bind, Pure.pure, bind, optionSem, listSem]
   simp_all [Bind.bind, Pure.pure, bind, optionSem, listSem]
   simp_all[a_ih]
   cases a_ih
   simp_all [optionSem, listSem]
   aesop



end Nondet

end LoVe
