/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import Aesop
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF

import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Convex.Basic





/- # LoVelib: Logical Verification Library -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Parser
open Lean.Parser.Term
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## Structured Proofs -/

@[term_parser] def «fix» :=
  leading_parser withPosition ("fix " >> many1 Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

@[term_parser] def «assume» :=
  leading_parser withPosition ("assume " >> Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

macro_rules
| `(fix $x* : $ty; $y) => `(fun $x* : $ty ↦ $y)
| `(assume $h : $ty; $y) => `(fun $h : $ty ↦ $y)


/- ## Natural Numbers -/

theorem Nat.two_mul (n : ℕ) :
    2 * n = n + n :=
  by ring

@[simp] theorem Nat.sub_one_add (n m : ℕ) (h : ¬ n = 0) :
    n - 1 + m = n + m - 1 :=
  by
    induction n with
    | zero => aesop
    | succ => simp

@[simp] theorem Nat.le_lt_imp (m n : ℕ) (p : Prop) (hge : m ≥ n) :
    (m < n → p) ↔ True :=
  by
    apply Iff.intro
    { intro himp
      apply True.intro }
    { intro htrue
      intro hlt
      have hle : n ≤ m :=
        hge
      rw [←Nat.not_lt_eq] at hle
      aesop }

@[simp] theorem Nat.lt_succ {m n : ℕ} :
    Nat.succ m < Nat.succ n ↔ m < n :=
  by
    apply Iff.intro
    { apply Nat.lt_of_succ_lt_succ }
    { apply Nat.succ_lt_succ }

@[simp] theorem Nat.le_succ {m n : ℕ} :
    Nat.succ m ≤ Nat.succ n ↔ m ≤ n :=
  by
    apply Iff.intro
    { apply Nat.le_of_succ_le_succ }
    { apply Nat.succ_le_succ }


/- ## Integers -/

@[simp] theorem Int.neg_neg :
    Int.neg ∘ Int.neg = id :=
  by
    apply funext
    intro i
    cases i with
    | ofNat n =>
      { cases n <;>
          aesop }
    | negSucc n =>
      { aesop }


/- ## Rationals -/

@[simp] theorem Rat.div_two_add_div_two (x : ℚ) :
    x / 2 + x / 2 = x :=
  by ring_nf


/- ## Lists -/

@[simp] theorem List.count_nil {α : Type} [BEq α] (x : α) :
    List.count x [] = 0 :=
  by rfl

@[simp] theorem List.count_cons {α : Type} [BEq α] (x a : α) (as : List α) :
    List.count x (a :: as) = (bif a == x then 1 else 0) + List.count x as :=
  by
    cases Classical.em (a == x) with
    | inl hx =>
      rw [List.count]
      simp [hx]
      ac_rfl
    | inr hx =>
      rw [List.count]
      simp [hx]

@[simp] theorem List.count_append {α : Type} [BEq α] (x : α) (as bs : List α) :
    List.count x (as ++ bs) = List.count x as + List.count x bs :=
  by
    induction as with
    | nil           => simp
    | cons a as' ih =>
      simp [ih]
      ac_rfl


/- ## Sets -/

@[aesop norm simp] theorem Set.subseteq_def {α : Type} (A B : Set α) :
    A ⊆ B ↔ ∀a, a ∈ A → a ∈ B :=
  by rfl

instance Set.PartialOrder {α : Type} : PartialOrder (Set α) :=
  { le               := fun A B ↦ A ⊆ B,
    lt               := fun A B ↦ A ⊆ B ∧ A ≠ B,
    le_refl          :=
      by
        intro A a ha
        assumption
    le_trans         :=
      by
        intro A B C hAB hBC a ha
        aesop,
    lt_iff_le_not_le :=
      by
        intro A B
        apply Iff.intro
        { intro hAB
          simp [LT.lt, LE.le] at *
          cases hAB with
          | intro hsseq hneq =>
            apply And.intro
            { assumption }
            { intro hflip
              apply hneq
              apply Set.ext
              aesop } }
        { intro hAB
          simp [LT.lt, LE.le] at *
          aesop },
    le_antisymm      :=
      by
        intro A B hAB hBA
        apply Set.ext
        aesop }

@[simp] theorem Set.le_def {α : Type} (A B : Set α) :
    A ≤ B ↔ A ⊆ B :=
  by rfl

@[simp] theorem Set.lt_def {α : Type} (A B : Set α) :
    A < B ↔ A ⊆ B ∧ A ≠ B :=
  by rfl

inductive Set.Finite {α : Type} : Set α → Prop where
  | empty                      : Set.Finite {}
  | insert (a : α) (A : Set α) : Set.Finite A → Set.Finite (insert a A)


/- ## Relations -/

def Id {α : Type} : Set (α × α) :=
  {ab | Prod.snd ab = Prod.fst ab}

@[simp] theorem mem_Id {α : Type} (a b : α) :
    (a, b) ∈ @Id α ↔ b = a :=
  by rfl

def comp {α : Type} (r₁ r₂ : Set (α × α)) : Set (α × α) :=
  {ac | ∃b, (Prod.fst ac, b) ∈ r₁ ∧ (b, Prod.snd ac) ∈ r₂}

infixl:90 " ◯ " => comp

@[simp] theorem mem_comp {α : Type} (r₁ r₂ : Set (α × α)) (a b : α) :
    (a, b) ∈ r₁ ◯ r₂ ↔ (∃c, (a, c) ∈ r₁ ∧ (c, b) ∈ r₂) :=
  by rfl

def restrict {α : Type} (r : Set (α × α)) (p : α → Prop) :Set (α × α) :=
  {ab | ab ∈ r ∧ p (Prod.fst ab)}

infixl:90 " ⇃ " => restrict

@[simp] theorem mem_restrict {α : Type} (r : Set (α × α))
      (P : α → Prop) (a b : α) :
    (a, b) ∈ r ⇃ P ↔ (a, b) ∈ r ∧ P a :=
  by rfl


/- ## Reflexive Transitive Closure -/

inductive RTC {α : Type} (R : α → α → Prop) (a : α) : α → Prop
  | refl : RTC R a a
  | tail (b c) (hab : RTC R a b) (hbc : R b c) : RTC R a c

namespace RTC

theorem trans {α : Type} {R : α → α → Prop} {a b c : α} (hab : RTC R a b)
      (hbc : RTC R b c) :
    RTC R a c :=
  by
    induction hbc with
    | refl =>
      assumption
    | tail c d hbc hcd hac =>
      apply tail <;>
        assumption

theorem single {α : Type} {R : α → α → Prop} {a b : α} (hab : R a b) :
    RTC R a b :=
  tail _ _ refl hab

theorem head {α : Type} {R : α → α → Prop} (a b c : α) (hab : R a b)
      (hbc : RTC R b c) :
    RTC R a c :=
  by
    induction hbc with
    | refl =>
      exact tail _ _ refl hab
    | tail c d hbc hcd hac =>
      apply tail <;>
        assumption

theorem head_induction_on {α : Type}
 {R : α → α → Prop} {b : α}
{P : ∀a : α, RTC R a b → Prop} {a : α} (h : RTC R a b)
      (refl : P b refl)
      (head : ∀a c (h' : R a c) (h : RTC R c b),
         P c h → P a (RTC.head _ _ _ h' h)) :
    P a h :=
  by
    induction h with
    | refl =>
      exact refl
    | tail b' c _ hb'c ih =>
      apply ih (P := fun a hab' ↦ P a (RTC.tail _ _ hab' hb'c))
      { exact head _ _ hb'c _ refl }
      { intro x y hxy hyb' hy
        exact head _ _ hxy _ hy }

theorem lift {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {a b : α}
      (f : α → β)
      (hf : ∀a b, R a b → S (f a) (f b)) (hab : RTC R a b) :
    RTC S (f a) (f b) :=
  by
    induction hab with
    | refl => apply refl
    | tail b c hab hbc ih =>
      apply tail
      apply ih
      apply hf
      exact hbc

theorem mono {α : Type} {R R' : α → α → Prop} {a b : α} :
    (∀a b, R a b → R' a b) → RTC R a b → RTC R' a b :=
  lift id

theorem RTC_RTC_eq {α : Type} {R : α → α → Prop} :
    RTC (RTC R) = RTC R :=
  funext
    (fix a : α
     funext
       (fix b : α
        propext (Iff.intro
          (assume h : RTC (RTC R) a b
           by
             induction h with
             | refl => exact refl
             | tail b c hab' hbc ih =>
               apply trans <;>
                 assumption)
          (mono
             (fix a b : α
              single)))))

end RTC


/- ## Setoids -/

attribute [simp] Setoid.refl


/- ## Metaprogramming -/

def cases (id : FVarId) : TacticM Unit :=
  do
    liftMetaTactic (fun goal ↦
      do
        let subgoals ← MVarId.cases goal id
        pure (List.map (fun subgoal ↦
            InductionSubgoal.mvarId (CasesSubgoal.toInductionSubgoal subgoal))
          (Array.toList subgoals)))


/- ## States -/

def State : Type :=
  String → ℕ

def State.update (name : String) (val : ℕ) (s : State) : State :=
  fun name' ↦ if name' = name then val else s name'

macro s:term "[" name:term "↦" val:term "]" : term =>
  `(State.update $name $val $s)

@[simp] theorem update_apply (name : String) (val : ℕ) (s : State) :
    (s[name ↦ val]) name = val :=
  by
    apply if_pos
    rfl

@[simp] theorem update_apply_neq (name name' : String) (val : ℕ) (s : State)
      (hneq : name' ≠ name) :
    (s[name ↦ val]) name' = s name' :=
  by
    apply if_neg
    assumption

@[simp] theorem update_override (name : String) (val₁ val₂ : ℕ) (s : State) :
    s[name ↦ val₂][name ↦ val₁] = s[name ↦ val₁] :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name) with
    | inl h => simp [h]
    | inr h => simp [h]

theorem update_swap (name₁ name₂ : String) (val₁ val₂ : ℕ) (s : State)
      (hneq : name₁ ≠ name₂) :
-- `hneq` should have `by decide` as an auto param, but this confuses `simp`.
-- See https://github.com/leanprover/lean4/issues/3257
    s[name₂ ↦ val₂][name₁ ↦ val₁] = s[name₁ ↦ val₁][name₂ ↦ val₂] :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name₁) with
    | inl h => simp [*]
    | inr h =>
      cases Classical.em (name' = name₁) with
      | inl h => simp [*]
      | inr h => simp [State.update, *]

@[simp] theorem update_id (name : String) (s : State) :
    s[name ↦ s name] = s :=
  by
    apply funext
    intro name'
    simp [State.update]
    intro heq
    simp [*]

@[simp] theorem update_same_const (name : String) (val : ℕ) :
    (fun _ ↦ val)[name ↦ val] = (fun _ ↦ val) :=
  by
    apply funext
    simp [State.update]

example (s : State) :
    s["a" ↦ 0]["a" ↦ 2] = s["a" ↦ 2] :=
  by simp

example (s : State) :
    (s["a" ↦ 0]) "b" = s "b" :=
  by simp

example (s : State) :
    s["a" ↦ 0]["b" ↦ 2] = s["b" ↦ 2]["a" ↦ 0] :=
  by simp [update_swap]

example (s : State) :
    s["a" ↦ s "a"]["b" ↦ 0] = s["b" ↦ 0] :=
  by simp

example (s : State) :
    (s["a" ↦ 0]["b" ↦ 0]) "c" = s "c" :=
  by simp (config := {decide := true})


variable {P Q R : Prop}


/-- 34 балла -/
theorem curry_uncurry : (P ∧ Q → R) ↔ (P → Q → R) := by
  apply Iff.intro
  { intro a a_1 a_2
    apply a
    apply And.intro
    { exact a_1 }
    { exact a_2 }
  }
  {
    intro a a_1
    apply a
    cases a_1
    { trivial }
    cases a_1
    { trivial }
  }

theorem weak_peirce (h1 : (Q → P) → P) (h2 : Q → R) (h3 : R → P) : P := by
  apply h1
  intro
  apply h3
  apply h2
  trivial

/-- 33 балла -/
theorem imp_iff_not_or' : (P → Q) ↔ (¬ P ∨ Q) := by
  apply Iff.intro
  {
    intro a
    by_cases hp : P
    {
      right
      apply a
      exact hp
    }
    {
      left
      exact hp
    }
  }
  {
    intro a a_1
    cases a
    { exfalso
      trivial
    }
    { trivial }
  }

-- 50 баллов
theorem exists_not_of_not_forall {α : Type} (P : α → Prop) : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  intro a
  by_contra h
  apply a
  intro x
  by_contra hb
  apply h
  apply Exists.intro x
  exact hb

-- 50 баллов
-- https://problems.ru/view_problem_details_new.php?id=66354
theorem func_equation (f : ℤ → ℤ) (hf : ∀ x y, f (x ^ 2 + y) = f x + f (y ^ 2)) : f (-1) = 0 := by
  -- Уравнение 1: f (-1) = f 0 + f 1
  have h1 : f (-1) = f 0 + f 1 := by
    have := hf 0 (-1)
    simp at this
    exact this

  -- Уравнение 2: f 1 = f (-1) + f 0
  have h2 : f 1 = f (-1) + f 0 := by
    have := hf (-1) 0
    simp at this
    exact this

  -- Уравнение 3: f 0 = f 1 + f 1
  have h3 : f 0 = f 1 + f 1 := by
    have := hf 1 (-1)
    simp at this
    exact this

  -- Подставляем h3 в h1 и h2
  rw [h3] at h1 h2
  -- h1 : f (-1) = f 1 + f 1 + f 1
  -- h2 : f 1 = f (-1) + (f 1 + f 1)

  -- Из h2 получаем f (-1) + f 1 = 0
  have h4 : f (-1) + f 1 = 0 := by
    rw [←add_assoc] at h2
    -- h2 : f 1 = f (-1) + f 1 + f 1
    have : f (-1) + f 1 + f 1 = f 1 + 0 := by
      rw [h2]
      simp
      norm_num at *
      rw[h2]
      simp
      exact h2
    rw[add_comm] at this

    exact add_left_cancel this


  -- f (-1) = -f 1
  have h5 : f (-1) = -f 1 := eq_neg_of_add_eq_zero_left h4


  -- Подставляем h5 в h1: -f 1 = f 1 + f 1 + f 1
  rw [h5] at h1
  -- h1 : -f 1 = f 1 + f 1 + f 1

  -- Получаем f 1 + f 1 + f 1 + f 1 = 0
  have h6 : f 1 + f 1 + f 1 + f 1 = 0 := by
    have : -f 1 + f 1 = (f 1 + f 1 + f 1) + f 1 := by rw [h1]
    rw [neg_add_cancel] at this
    -- this : 0 = f 1 + f 1 + f 1 + f 1
    exact this.symm

  -- Группируем: (f 1 + f 1) + (f 1 + f 1) = 0 !!!!!
  have h7 : (f 1 + f 1) + (f 1 + f 1) = 0 := by
    rw [add_assoc] at h6
    exact h6

  simp [← two_mul] at *
  rw[h7] at h2
  simp at h2
  apply symm
  exact h2



open Nat

-- Главная теорема: выводим сильную индукцию из обычной
theorem strong_induction_from_weak (P : ℕ → Prop)
    (step : ∀ n, (∀ k < n, P k) → P n) :
    ∀ n, P n := by
  -- 1. Вводим усиленное утверждение Q(n) := ∀ k < n, P(k)
  have Q : ∀ n, ∀ k < n, P k := by
    intro n
    -- Применяем обычную индукцию по n
    induction' n with n ih
    · -- База индукции: n = 0. Меньших чисел нет (k < 0 невозможно)
      intro k hk
      exact False.elim (Nat.not_lt_zero k hk)
    · -- Шаг индукции: предполагаем ih : ∀ k < n, P k, доказываем для n + 1
      intro k hk -- hk : k < n + 1, что эквивалентно k ≤ n
      -- Разбираем два случая: k < n или k = n
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h_lt | h_eq
      · -- Случай 1: k < n. Используем предположение индукции ih
        exact ih k h_lt
      · -- Случай 2: k = n. Подставляем k = n
        rw [h_eq]
        -- Используем условие 'step', так как ih как раз покрывает все k < n
        exact step n ih

  -- 2. Теперь из того, что Q(n+1) верно, автоматически следует P(n)
  intro n
  apply Q (n + 1) n
  exact Nat.lt_succ_self n


theorem Nat.strong_induction_from_simple {p : ℕ → Prop} (n : ℕ)
    (h : ∀ (n : ℕ), (∀ m < n, p m) → p n) : p n := by
    have Q : ∀ n, ∀ k < n, p k := by
      intro n
      induction' n with n ih
      {
        intro k
        intro a
        omega
      }
      {
        intro k
        intro hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h_lt | h_eq
        { exact ih k h_lt }
        { rw[h_eq]
          apply h
          exact ih
        }
      }

    apply Q (n + 1) n
    omega

theorem Nat.well_founded {P : ℕ → Prop} (h : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y := by
  -- Предположим противное: нет минимального элемента
  by_contra hmin
  push_neg at hmin
  -- hmin : ∀ x, P x → ∃ y, P y ∧ ¬ x ≤ y
  -- То есть для любого x, если P x, то найдётся y < x,
  -- для которого P y.
  -- Докажем, что тогда P не выполняется ни для какого числа.
  have hno : ∀ n, ¬ P n := by
    intro n
    -- Применим сильную индукцию по n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      -- Из hmin получим y < n, для которого P y
      rcases hmin n hn with ⟨y, hy, hlt⟩
      -- hlt : ¬ n ≤ y, значит y < n

      -- Применяем индукционное предположение к y
      exact ih y hlt hy
  -- Но h утверждает, что P x верно для некоторого x
  rcases h with ⟨x, hx⟩
  exact hno x hx

theorem Nat.mono_of_mono_succ {α : Type} (f : ℕ → α) [LinearOrder α] (hf : ∀ n, f n ≤ f (n + 1))
    (n m : ℕ) (h : n ≤ m) :
    f n ≤ f m := by
  induction' m with n_1 ih
  {
    cases h
    aesop
  }
  {
    rcases h with _ | a_1
    { aesop }
    { simp at a_1
      specialize hf n_1
      apply le_trans
      apply ih
      exact a_1
      exact hf }
  }

theorem Nat.surjective_of_unbounded (f : ℕ → ℕ)
    (hf₀ : f 0 = 0) (hf : ∀ n, f (n + 1) ≤ f n + 1)
    (h : ∀ C, ∃ x, f x ≥ C) : ∀ y, ∃ x, f x = y := by
  intro y
  -- Рассмотрим множество {x | f x ≥ y}
  have h_nonempty : ∃ x, f x ≥ y := h y
  -- По принципу минимального элемента существует минимальный x
  rcases Nat.well_founded h_nonempty with ⟨x, hx_ge, hx_min⟩
  -- hx_ge : f x ≥ y
  -- hx_min : ∀ z, f z ≥ y → x ≤ z

  -- Покажем, что f x = y
  -- Предположим противное: f x > y
  by_cases h_eq : f x = y
  · -- Если f x = y, то всё доказано
    exact ⟨x, h_eq⟩
  · -- Если f x ≠ y, то f x > y (так как f x ≥ y)
    have h_gt : f x > y := by omega
    -- Рассмотрим x - 1
    cases x with
    | zero =>
      -- x = 0 => f 0 = 0 ≥ y => y = 0 => f 0 = y
      simp [hf₀] at hx_ge
      have : y = 0 := by omega
      exact ⟨0, by rw [hf₀, this]⟩
    | succ x' =>
      -- x = x' + 1
      -- По условию hf: f (x' + 1) ≤ f x' + 1
      -- Значит f x' ≥ f (x' + 1) - 1 ≥ y (так как f (x'+1) > y)
      have hf_x' : f (x' + 1) ≤ f x' + 1 := hf x'
      -- f x' ≥ f (x'+1) - 1 ≥ y
      have hx'_ge : f x' ≥ y := by omega
      -- Но x' < x, а x — минимальный с f x ≥ y
      have hx'_lt_x : x' < x' + 1 := by omega
      have hx_min_x' : x' + 1 ≤ x' := hx_min x' hx'_ge
      -- Противоречие: x ≤ x' и x' < x
      omega

example (f : ℕ → ℕ) (n x : ℕ) : f^[n] (f x) = f (f^[n] x) := by
  revert x
  induction n with
  | zero =>
    simp
  | succ m ih =>
    intro x

    rw [Function.iterate_succ_apply]
    apply ih


/-! # Двоичные деревья

В этой задаче мы рассмотрим двоичные деревья как способ представлять
кусочно-постоянные функции на отрезке.
-/


noncomputable section

/-- Тип двоичных деревьев, на листьях которых написаны вещественные числа.  -/
inductive BinTree
  | leaf (value : ℝ)
  | node (left right : BinTree)

namespace BinTree

/-- Зеркальное отражение дерева -/
def reverse (t : BinTree) : BinTree :=
  match t with
  | .leaf v => .leaf v
  | .node l r => .node r.reverse l.reverse

/-- Докажите, что дважды отзеркалив дерево, мы вернем его в изначальный вид.

**(25 баллов)** -/
theorem reverse_reverse (t : BinTree) : t.reverse.reverse = t := by
  induction t <;>
  simp_all [reverse]

/-- При помощи таких деревьев можно представлять кусочно-постоянные функции на отрезке.

Двумерное обобщение (https://en.wikipedia.org/wiki/Quadtree) используется для того чтобы сжимать фотографии:
если изображение достаточно однородное -- оно представляется одноцветным квадратом, если нет -- делится на 4 квадрата
и рекурсивно вызывается на них.

`t.eval : ℝ → ℝ` это функция "аппроксимированная" бинарным деревом. Математически она определена на отрезке `[0, 1]`, но
здесь для простоты мы определяем её на всем `ℝ`. -/
def eval (t : BinTree) (x : ℝ) : ℝ :=
  match t with
  | .leaf value => value
  | .node l r =>
    if x < 2⁻¹ then
      l.eval (2 * x)
    else if 2⁻¹ < x then
      r.eval (2 * x - 1)
    else
      (l.eval 1 + r.eval 0) / 2

/-- Докажите связь между `reverse` и `eval`.

macro "my_combo" : tactic => `(tactic| intro h; exact h)

**(25 баллов)**  -/



theorem reverse_eval (t : BinTree) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    t.reverse.eval x = t.eval (1 - x) := by
    induction' t with right_ih _  _ left_ih generalizing x  <;>
    (simp_all [reverse, eval] ;
     try aesop
     try linarith;
     try (rw[right_ih]; ring_nf; linarith;linarith);
     try linarith;
     try (rw[left_ih]; ring_nf; linarith;linarith);
     try linarith;
     try linarith;
     try linarith;
     try linarith;
     try linarith
     )

 def add (x y : BinTree) : BinTree :=
  match x, y with
  | .leaf v₁, .leaf v₂ => .leaf (v₁ + v₂)
  | .node l₁ r₁, .node l₂ r₂ => .node (add l₁ l₂) (add r₁ r₂)
  | .leaf v, .node l r => .node (add (.leaf v) l) (add (.leaf v) r)
  | .node l r, .leaf v => .node (add l (.leaf v)) (add r (.leaf v))

/-
def add (x y : BinTree) : BinTree :=
  match x, y with
  | .leaf a, .leaf b => .leaf (a + b)
  | .leaf a, .node l r => .node (add (.leaf a) l) (add (.leaf a) r)
  | .node l r, .leaf b => .node (add l (.leaf b)) (add r (.leaf b))
  | .node l1 r1, .node l2 r2 => .node (add l1 l2) (add r1 r2)
  -/

 theorem add_eval (t1 t2 : BinTree) (x : ℝ) :
    (t1.add t2).eval x = t1.eval x + t2.eval x := by
  induction t1 generalizing t2 x with
  | leaf a =>
    induction t2 generalizing x with
    | leaf b => simp [add, eval]
    | node l r ihl ihr =>
      simp [add, eval, ihl, ihr]
      split_ifs <;> ring
  | node l r ihl ihr =>
    induction t2 generalizing x with
    | leaf b =>
      simp [add, eval, ihl, ihr]
      split_ifs <;> ring
    | node l2 r2 ih2l ih2r =>
      simp [add, eval, ihl, ihr, ih2l, ih2r]
      split_ifs <;> ring


theorem add_eval1 (t1 t2 : BinTree) (x : ℝ) : (t1.add t2).eval x = t1.eval x + t2.eval x := by
  induction' t1 with right_ih _  _ left_ih generalizing t2 x
  {
    simp_all[add, eval]
    induction t2 generalizing x
    { simp_all[add, eval] }
    { simp_all[add, eval]
      try aesop
      ring_nf }
  }
  {
    induction t2  generalizing x
    {
      simp_all[add, eval]
      try aesop
      ring_nf
    }
    {
      simp_all[add, eval]
      try aesop
      ring_nf
    }
  }


variable {α β γ : Type}

/-- Композиция инъективных функций инъективна.

**(25 баллов)** -/
theorem injective_comp (f : α → β) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
    simp_all

#check Int.floor        -- Int.floor : ℝ → ℤ

def g : ℕ → ℕ := fun r => Nat.floor (r/2)
def f : ℕ → ℕ := fun r => 2 * r

theorem f_injective : Function.Injective f := by
  simp_all[Function.Injective]
  intros
  simp_all[f]

theorem gf_injective : Function.Injective (g ∘ f) := by
    simp_all[Function.Injective]
    intros
    simp_all[f, g]

theorem not_g_injective : ¬ Function.Injective g := by
  rw[Not]
  intro a
  simp_all[Function.Injective, g]
  have h_div : 2 / 2 = 3 / 2 := by rfl
  have h_eq : 2 = 3 := a h_div
  aesop

theorem surjective_iff (f : α → β) :
    Function.Surjective f ↔ ∀ γ : Type, ∀ g h : β → γ, g ∘ f = h ∘ f → g = h := by
  apply Iff.intro
  {
    simp_all[Function.Surjective, Function.comp]
    intro a
    intro x
    intro g h
    intro a_1

    ext x
    specialize a x
    obtain ⟨w, hw⟩ := a
    unfold Function.comp at a_1
    have gg := congr_fun a_1 w
    aesop
  }
  {
    simp_all[Function.Surjective, Function.comp]
    intro a b
    unfold Function.comp at a
    have h_eq := a Prop (fun _ => True) (fun y => ∃a, f a = y)
    simp_all
    have gg := congr_fun h_eq b
    aesop
  }

theorem exists_surjective_nat_to_int : ∃ f : ℕ → ℤ, Function.Surjective f := by
  simp_all[Function.Surjective, Function.comp]
  exists (fun r => (if r % 2 = 0 then r/2 else -((r-1)/2)))
  simp_all[Function.Surjective, Function.comp]
  intro b
  by_cases hb : 0 ≤ b
  { exists (2 * b.natAbs)
    simp_all
  }
  {
    exists (2 * b.natAbs + 1)
    split_ifs with a
    { have gg : (2 * b.natAbs + 1) % 2 = 1 := by omega
      simp_all
    }
    {
      have gg: (b.natAbs : ℤ) = -b := by
       omega
      rw [Int.natCast_natAbs] at gg
      simp
      rw [gg]
      linarith
    }
  }



/-- Множество на плоскости выпукло,
 если для любых двух его точек `p` и `q` любая точка из отрезка
`pq` лежит в этом множестве. -/
def Convex (S : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ c ∈ Set.Icc (α := ℝ) 0 1, c • p + (1 - c) • q ∈ S

/-- **(34 балла)**

Пересечение выпуклых множеств выпукло. -/
theorem Convex.inter (A B : Set (ℝ × ℝ)) (hA : Convex A) (hB : Convex B) :
    Convex (A ∩ B) := by
  simp_all[Convex]




-- Настройка инстансов для операции • над парами (ℝ × ℝ)
instance : SMul ℝ (ℝ × ℝ) := ⟨fun c p => (c * p.1, c * p.2)⟩


/-- **Для объединения это неверно.** -/
theorem Convex.union_counterexample : ∃ A B, Convex A ∧ Convex B ∧ ¬ Convex (A ∪ B) := by
  -- В качестве контрпримера возьмем отрезки на оси X:  и
  let A : Set (ℝ × ℝ) := {p | p.2 = 0 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1}
  let B : Set (ℝ × ℝ) := {p | p.2 = 0 ∧ 2 ≤ p.1 ∧ p.1 ≤ 3}
  use A, B

  -- Докажем три утверждения: Convex A, Convex B и ¬ Convex (A ∪ B)
  have hA : Convex A := by
    intro p hp q hq c hc
    dsimp [A] at *
    rcases hc with ⟨hc0, hc1⟩
    refine ⟨by linear_combination c * hp.1 + (1 - c) * hq.1, ?_, ?_⟩
    · nlinarith
    · nlinarith

  have hB : Convex B := by
    intro p hp q hq c hc
    dsimp [B] at *
    rcases hc with ⟨hc0, hc1⟩
    refine ⟨by linear_combination c * hp.1 + (1 - c) * hq.1, ?_, ?_⟩
    · nlinarith
    · nlinarith

  refine ⟨hA, hB, ?_⟩
  -- Доказываем от противного, что объединение НЕ выпукло
  intro hUnion
  -- Берем точку p = (1, 0) из A и q = (2, 0) из B, и коэффициент c = 1/2
  have hp : (1 , 0 ) ∈ A ∪ B := Or.inl ⟨rfl, by norm_num, by norm_num⟩
  have hq : (2 , 0 ) ∈ A ∪ B := Or.inr ⟨rfl, by norm_num, by norm_num⟩
  have hc : (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

  -- Применяем гипотезу о выпуклости объединения
  have h_mid := hUnion (1, 0) hp (2, 0) hq (1/2) hc

  -- Считаем координаты средней точки: (1/2)•(1,0) + (1/2)•(2,0) = (1.5, 0)
  change ((1/2 : ℝ) * 1 + (1 - 1/2 : ℝ) * 2, (1/2 : ℝ) * 0 + (1 - 1/2 : ℝ) * 0) ∈ A ∪ B at h_mid
  norm_num at h_mid

  -- Получаем противоречие: точка (3/2, 0) не лежит ни в A, ни в B
  rcases h_mid with ⟨-, -, h32⟩ | ⟨-, h32, -⟩
  · linarith
  · linarith


/-- **(33 балла)**

Пусть множество натуральных чисел удовлетворяет двум условиям:
1. Оно содержит 0
2. Оно переходит внутрь себя при сдвиге на 2.

Докажите, что оно содержит множество чётных чисел.
-/
theorem subset_even (S : Set ℕ) (h0 : 0 ∈ S) (h_add : (fun n ↦ n + 2) '' S ⊆ S) :
    {x | x % 2 = 0} ⊆ S := by  
  simp_all[Set.subseteq_def]
  intro a
  intro ha 
  induction' a  using Nat.strong_induction_on with  n a_1
  specialize a_1 (n - 2)
  by_cases hp: 2 ≤ n
  { 
    have gg : n - 2 < n := by omega
    have rr: (n - 2) % 2 = 0 := by omega
    have dd: n - 2 ∈ S := by aesop
    have tt : n - 2 + 2 ∈ S := by
     specialize h_add (n -2)
     simp_all
    convert tt using 1
    omega 
  }
  {
    simp at hp
    rcases hp
    { simp_all }
    { simp_all }   
  }
      
open scoped Classical

/-- Теорема Кантора: не существует сюръекции α → P(α).

**(25 баллов)** -/
theorem cantor (α : Type) : ¬ ∃ f : α → Set α, Function.Surjective f := by
  -- 1. Предполагаем от противного, что сюръекция f существует
  rw[Not]
  intro a
  simp_all[Function.Surjective]
  rcases a with ⟨w, h⟩
  -- 2. Определяем диагональное множество B = {x | x ∉ f x}
  let B : Set α := {x | x ∉ w x}
  specialize h B
  unfold B at h
  rcases h with ⟨w_1, h⟩

  have h_iff : w_1 ∈ w w_1 ↔ w_1 ∈ B := by rw [h]
  unfold B at h_iff
  change w_1 ∈ w w_1 ↔ w_1 ∉ w w_1 at h_iff
  rcases h_iff with ⟨mp, mpr⟩
  by_cases hp: w_1 ∈ w w_1
  {  
    exact (mp hp) hp
  }
  {
    have tt : w_1 ∈ w w_1 := by 
      apply mpr
      trivial
    trivial  
  }

noncomputable def directIter {α β : Type*} (f : α → β) (g : β → α) : ℕ → Set α
  | 0 => (Set.range g)ᶜ
  | n + 1 => (g ∘ f) '' (directIter f g n)

noncomputable def directPoints {α β : Type*} (f : α → β) (g : β → α) : Set α :=
  ⋃ i, directIter f g i

noncomputable def h {α β : Type*} [Nonempty β] (f : α → β) (g : β → α) (x : α) : β :=
  if x ∈ directPoints f g then f x else (Function.invFun g) x

theorem sb_surjective {α β : Type*} [Nonempty β] {f : α → β} {g : β → α}
  (injg : Function.Injective g) : Function.Surjective (h f g) := by
  intro b
  simp only [h]
  by_cases gb_direct : g b ∈ directPoints f g
  · /- If g(b) is a part of a direct chain, it must have been added
    to the direct set via some a -(f)-> b -(g)-> g(b) iteration.
    By picking that a, we get h(a) = f(a) = b, proving b is reachable. -/
    simp only [directPoints, Set.mem_iUnion] at *
    rcases gb_direct with ⟨n, hn⟩
    rcases n with _ | n
    · tauto
    · rcases hn with ⟨a, a_direct, ha⟩
      use a
      rw [if_pos (by use n)]
      exact injg ha
  /- If g(b) is not a part of some direct chain [1], pick a := g(b).
  For that a, h(a) =(by [1])= inv_g(a) =(by def.)= inv_g(g(b)).
  Thus, proving inv_g(g(b)) = b would be enough to show b is reachable.
  To cancel them out, we'll wrap both sides with g (thanks, injectivity). -/
  use g b
  rw [if_neg gb_direct]
  apply injg
  apply Function.invFun_eq
  use b

theorem g_right_inv {α β : Type*} [Nonempty β] {f : α → β} {g : β → α}
    {a : α} (ha : a ∉ directPoints f g) :
    g (Function.invFun g a) = a := by
  have : ∃ b, g b = a := by
    simp only [directPoints, Set.mem_iUnion] at ha
    contrapose! ha
    use 0
    simp only [directIter, Set.mem_compl_iff, Set.mem_range]
    tauto
  apply Function.invFun_eq this

theorem heq_imp_same_directness {α β : Type*} [Nonempty β] {f : α → β} {g : β → α}
    {a1 a2 : α} (ha1 : a1 ∈ directPoints f g)
    (heq : h f g a1 = h f g a2) : a2 ∈ directPoints f g := by
  simp only [h] at *
  rw [if_pos ha1] at heq
  by_cases ha2 : a2 ∈ directPoints f g
  · tauto
  · rw [if_neg ha2] at heq
    simp only [directPoints, Set.mem_iUnion] at ha1
    rcases ha1 with ⟨i, hi⟩
    simp only [directPoints, Set.mem_iUnion]
    use i + 1, a1, hi
    rw [Function.comp_apply, heq]
    exact g_right_inv ha2
    

theorem sb_injective {α β : Type*} [Nonempty β] {f : α → β} {g : β → α}
    (injf : Function.Injective f) : Function.Injective (h f g) := by
  intro a1 a2 heq
  by_cases a1_direct : a1 ∈ directPoints f g
  · by_cases a2_direct : a2 ∈ directPoints f g
    · rw [h, h, if_pos a1_direct, if_pos a2_direct] at heq
      exact injf heq
    · have := heq_imp_same_directness  a1_direct heq
      contradiction
  · by_cases a2_direct : a2 ∈ directPoints f g
    · have := heq_imp_same_directness  a2_direct heq.symm
      contradiction
    · rw [h, h, if_neg a1_direct, if_neg a2_direct] at heq
      have ginv_a1 := g_right_inv a1_direct
      have ginv_a2 := g_right_inv a2_direct
      rw [← ginv_a1, ← ginv_a2, heq]

theorem cantor_bernstein (α β : Type) (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ f' : α → β, Function.Bijective f' := by
  by_cases hβ : Nonempty β
  · haveI : Nonempty β := hβ
    exact ⟨h f g, sb_injective hf, sb_surjective hg⟩
  · haveI : IsEmpty β := not_nonempty_iff.mp hβ
    have hα : IsEmpty α := by
      rw [← not_nonempty_iff]
      intro h
      exact hβ (h.map f)
    haveI := hα
    exact ⟨f, fun a1 a2 _ => Subsingleton.elim a1 a2, fun b => isEmptyElim b⟩


#min_imports
