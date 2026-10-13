/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 8 (10 points + 2 bonus points): Metaprogramming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## Question 1 (10 points): A `safe` Tactic

You will develop a tactic that applies all safe introduction
 and elimination
rules for the connectives and quantifiers exhaustively.
 A rule is said to be
__safe__ if, given a provable goal, it always gives rise
 to provable subgoals.
In addition, we will require that safe rules do not introduce
 metavariables
(since these can easily be instantiated accidentally with the wrong terms).

You will proceed in three steps.

1.1 (4 points). Develop a `safe_intros` tactic
 that repeatedly applies the
introduction rules for `True`, `∧`, and `↔` and that
invokes `intro _` for
`→`/`∀`. The tactic generalizes `intro_and` from the exercise. -/

macro "safe_intros" : tactic =>
  `(tactic|
    (repeat (
      first
      | apply True.intro
      | apply And.intro
      | apply Iff.intro
      | intro
    )))

theorem abcd (a b c d : Prop) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe_intros
    /- The proof state should be roughly as follows:

        case left
        a b c d : Prop
        a_1 : a
        a_2 : b
        ⊢ False

        case right.mp
        a b c d : Prop
        a_1 : a
        a_2 : c
        ⊢ d

        case right.mpr
        a b c d : Prop
        a_1 : a
        a_2 : d
        ⊢ c -/
    repeat' sorry

/- 1.2 (4 points). Develop a `safe_cases` tactic that performs case
distinctions on `False`, `∧` (`And`), and `∃` (`Exists`). The tactic generalizes
`cases_and` from the exercise.

Hints:

* The last argument of `Expr.isAppOfArity` is the number of arguments expected
  by the logical symbol. For example, the arity of `∧` is 2.

* The "or" connective on `Bool` is called `||`.

Hint: When iterating over the declarations in the local context, make sure to
skip any declaration that is an implementation detail. -/

#check @False
#check @And
#check @Exists

partial def safeCases : TacticM Unit := do
  withMainContext do
    let ctx ← getLCtx
    let mut found := false
    for decl in ctx do
      let ty ← inferType decl.toExpr
      if ty.isAppOfArity ``And 2 then
        cases decl.fvarId
        safeCases
        found := true
        break
      else if ty.isAppOfArity ``False 0 then
        cases decl.fvarId  -- False в гипотезах даёт 0 подцелей!
        found := true
        break
      else if ty.isAppOfArity ``Exists 2 then
        cases decl.fvarId
        safeCases
        found := true
        break
    if not found then
      return ()

elab "safe_cases" : tactic =>
  safeCases

theorem abcdef (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    False :=
  by
    safe_cases
  /- The proof state should be roughly as follows:

      case intro.intro.intro
      a b c d e f : Prop
      P : ℕ → Prop
      hneg : ¬a
      hor : c ∨ d
      himp : b → e
      hiff : e ↔ f
      left : a
      w : ℕ
      h : P w
      left_1 : b
      right : c
      ⊢ False -/
    sorry

/- 1.3 (2 points). Implement a `safe` tactic that
first invokes `safe_intros`
on all goals, then `safe_cases` on all emerging subgoals,
 before it tries
`assumption` on all emerging subsubgoals. -/

macro "safe" : tactic =>
  `(tactic|
    (safe_intros
     safe_cases
     try repeat assumption
     ))

theorem abcdef_abcd (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe
    /- The proof state should be roughly as follows:

        case left.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : b
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ False

        case right.mp.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : c
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ d -/
    repeat' sorry


/- ## Question 2 (2 bonus points): An `aesop`-Like Tactic

2.1 (1 bonus point). Develop a simple `aesop`-like tactic.

This tactic should apply all safe introduction and elimination rules. In
addition, it should try potentially unsafe rules (such as `Or.inl` and
`False.elim`) but backtrack at some point
(or try several possibilities in
parallel).
Iterative deepening may be a valid approach, or best-first search, or
breadth-first search. The tactic should also try to apply assumptions whose
conclusion matches the goal, but backtrack if necessary.

Hint: The `MonadBacktrack` monad class might be useful.
-/

open Lean Elab Tactic Meta

/--
Простой поисковый тактик, похожий на aesop.
-/
partial def simpleAesop (depth : Nat) : TacticM Unit := do
  if depth > 10 then
    failure  -- предел глубины

  -- 1. Сначала безопасные шаги
  let goals ← getUnsolvedGoals
  if goals.isEmpty then
    return ()

  -- 2. Пробуем `assumption`
  try

    return ()
  catch _ =>
    pure ()

  -- 3. Пробуем безопасные введения
  try
    evalTactic (← `(tactic| safe_intros))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  -- 4. Пробуем безопасные случаи
  try
    evalTactic (← `(tactic| safe_cases))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  -- 5. Пробуем `False.elim` (опасный!)
  try
    evalTactic (← `(tactic| apply False.elim))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  -- 6. Пробуем `Or.inl` и `Or.inr` (опасные!)
  try
    evalTactic (← `(tactic| first | apply Or.inl | apply Or.inr))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  -- 7. Пробуем `Exists.intro` (опасный!)
  try
    evalTactic (← `(tactic| apply Exists.intro))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  -- 8. Пробуем применять гипотезы к цели
  let ctx ← getLCtx
  for decl in ctx do
    let ty ← inferType decl.toExpr
    -- Проверяем, можно ли применить гипотезу к цели
    try
      evalTactic (← `(tactic| apply $(mkIdent decl.userName)))
      simpleAesop (depth + 1)
      return ()
    catch _ =>
      pure ()

  -- Если ничего не сработало — неудача
  failure

elab "simple_aesop" : tactic =>
  simpleAesop 0

open Lean.Meta.Tactic.Backtrack

partial def simplAesop (depth : Nat) : TacticM Unit := do
  if depth > 10 then
    failure

  -- Используем `orElse` для backtracking
  let rec tryTactic (tac : TacticM Unit) : TacticM Unit := do
    (do tac; simpleAesop (depth + 1)) <|>
    (do simpleAesop (depth + 1))  -- пробуем дальше

  -- Пробуем различные тактики с возвратом
  tryTactic (evalTactic (← `(tactic| assumption)))
  tryTactic (evalTactic (← `(tactic| safe_intros)))
  tryTactic (evalTactic (← `(tactic| safe_cases)))
  tryTactic (evalTactic (← `(tactic| apply False.elim)))
  tryTactic (evalTactic (← `(tactic| first | apply Or.inl | apply Or.inr)))
  tryTactic (evalTactic (← `(tactic| apply Exists.intro)))

  -- Применяем гипотезы
  let ctx ← getLCtx
  for decl in ctx do
    tryTactic (evalTactic (← `(tactic| apply $(mkIdent decl.userName))))

  failure
partial def simplerAesop (depth : Nat) : TacticM Unit := do
  if depth > 10 then
    failure

  let goals ← getUnsolvedGoals
  if goals.isEmpty then
    return ()

  -- 1. Сначала применяем все введения (важно!)
  try
    evalTactic (← `(tactic| repeat intro))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  -- 2. Пробуем assumption
  try
    evalTactic (← `(tactic| assumption))
    return ()
  catch _ =>
    pure ()

  -- 3. Пробуем безопасные случаи
  try
    evalTactic (← `(tactic| safe_cases))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  -- 4. Пробуем опасные правила
  try
    evalTactic (← `(tactic| first | apply Or.inl | apply Or.inr))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  try
    evalTactic (← `(tactic| apply False.elim))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  -- 5. Пробуем применять гипотезы
  let ctx ← getLCtx
  for decl in ctx do
    try
      evalTactic (← `(tactic| apply $(mkIdent decl.userName)))
      simpleAesop (depth + 1)
      return ()
    catch _ =>
      pure ()

  -- 6. Пробуем Exists.intro
  try
    evalTactic (← `(tactic| apply Exists.intro))
    simpleAesop (depth + 1)
    return ()
  catch _ =>
    pure ()

  failure

elab "simple_aesopr" : tactic =>
  simplerAesop 5

macro "simple_aesop" : tactic =>
  `(tactic|
    (repeat (
      intro  safe_intros
      safe_cases
      try (assumption)
      try (apply Or.inl)
      try (apply Or.inr)
      /-try (apply False.elim)-/
      try (apply Exists.intro)
    )))
     /-try (apply False.elim)))  -/

open Lean.Meta.Tactic.Backtrack

partial def simpleEnotAesop (depth : Nat) : TacticM Unit := do
  if depth > 10 then
    failure

  -- Используем `orElse` для backtracking
  let rec tryTactic (tac : TacticM Unit) : TacticM Unit := do
    (do tac; simpleAesop (depth + 1)) <|>
    (do simpleAesop (depth + 1))  -- пробуем дальше

  -- Пробуем различные тактики с возвратом
  tryTactic (evalTactic (← `(tactic| assumption)))
  tryTactic (evalTactic (← `(tactic| safe_intros)))
  tryTactic (evalTactic (← `(tactic| safe_cases)))
  /-tryTactic (evalTactic (← `(tactic| apply False.elim)))-/
  tryTactic (evalTactic (← `(tactic| first | apply Or.inl | apply Or.inr)))
  tryTactic (evalTactic (← `(tactic| apply Exists.intro)))

  -- Применяем гипотезы
  let ctx ← getLCtx
  for decl in ctx do
    tryTactic (evalTactic (← `(tactic| apply $(mkIdent decl.userName))))

  failure

  elab "simple_aesopen" : tactic =>
  simpleEnotAesop 5
/-2.2 (1 bonus point). Test your tactic on some benchmarks.

You can try your tactic on logic puzzles of the kinds we proved in exercise and
homework 3. Please include these below. -/

theorem forall_and (p q : Prop):
   p → (q → p) :=
  by
    simple_aesop

theorem forallme (p q r: Prop):
(p → q) → ((q → r) → (p → r)) :=
  by
    simple_aesopr
    aesop

end LoVe
