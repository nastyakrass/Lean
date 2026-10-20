/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe10_HoareLogic_Demo


/- # LoVe Exercise 10: Hoare Logic

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Program Verification

1.1. The following WHILE program takes two numbers `a` and `b`
and increments
`b` until it reaches `a`: -/

def COUNT_UP : Stmt :=
  Stmt.whileDo (fun s ↦ s "b" ≠ s "a")
    (Stmt.assign "b" (fun s ↦ s "b" + 1))

/- Prove the following Hoare triple.
The main difficulty is to figure out which
invariant to use for the while loop.
The invariant should capture both the work
that has been done already (the intermediate result)
and the work that remains
to be done. Use a `show` command to
 annotate the program with a loop invariant.

Hint: If a variable `x` does not change in a program,
 it might be useful to
record this in the invariant, by adding a conjunct `s "x" = x₀`. -/
theorem COUNT_UP_correct (a₀ : ℕ) :
  {* fun s ↦ s "a" = a₀ ∧ s "b" ≤ a₀ *} (COUNT_UP) {* fun s ↦ s "a" = a₀ ∧ s "b" = a₀ *} :=
  PartialHoare.while_intro'
    (fun s ↦ s "a" = a₀ ∧ s "b" ≤ a₀)
    (by
       simp_all
       rw[PartialHoare]
       intros
       simp_all
       rcases a
       rcases left
       simp_all
       rcases right_1
       simp_all
       simp_all
       /-exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne right_1 right)
     -/)
    (by
       intros
       simp_all
     )
    (by
       intros
       simp_all
    )
/--/
theorem COUNTTT_UP_correct (a₀ : ℕ) :
{* fun s ↦ s "a" = a₀ *} (COUNT_UP) {* fun s ↦ s "a" = a₀ ∧ s "b" = a₀ *} :=
PartialHoare.while_intro'
(fun s ↦ s "a" = a₀ ∧ s "b" ≤ a₀)  -- инвариант
    (-- 1. Инвариант выполняется до цикла
     by
       intros
       simp_all
       rw[PartialHoare]
       intros
       simp_all
       rcases a
       rcases left
       simp_all
       exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne right_1 right)
     )
    (-- 2. Тело цикла сохраняет инвариант
     by
       intros
       simp_all
       sorry)

/-theorem COUNT_UP_correct (a₀ : ℕ) :
    {* fun s ↦ s "a" = a₀ *} (COUNT_UP) {* fun s ↦ s "a" = a₀ ∧ s "b" = a₀ *} :=
    PartialHoare.while_intro' (fun s ↦ s "a" = a₀ ∧ s "b" ≤ a₀)
    (by
      intros
      simp_all
      rw[PartialHoare]
      intros
      simp_all
      rcases a
      rcases left
      simp_all
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne right_1 right)
    )
    (

    )

      apply PartialHoare.seq_intro
      { apply PartialHoare.assign_intro }
      { apply PartialHoare.assign_intro'
        aesop })
    (by aesop)
    (by aesop)
-/
/- 1.2. What happens if the program is run with `b > a`? How is this captured
by the Hoare triple? -/
-/
-- enter your solution here

/- 1.3. The following WHILE program is intended to
compute the Gaussian sum up
to `n`, leaving the result in `r`. -/

def GAUSS (N : ℕ) : Stmt :=
  Stmt.assign "r" (fun s ↦ 0);
  Stmt.assign "n" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ N)
    (Stmt.assign "n" (fun s ↦ s "n" + 1);
     Stmt.assign "r" (fun s ↦ s "r" + s "n"))

/- Here is a functional implementation of the same function: -/

def sumUpTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => n + 1 + sumUpTo n

/- Invoke `vcg` on `GAUSS` using a suitable loop invariant and prove the
emerging verification conditions. -/
theorem GAUSS_correct (N : ℕ) :
    {* fun s ↦ True *} (GAUSS N) {* fun s ↦ s "r" = sumUpTo N *} :=
    by
    unfold GAUSS
    -- Преобразуем whileDo в invWhileDo с явным инвариантом
    simp [Stmt.assign, Stmt.seq]
    show {* fun s ↦ True *}
      (Stmt.assign "r" (fun s ↦ 0);
       Stmt.assign "n" (fun s ↦ 0);
       Stmt.invWhileDo (fun s ↦ s "r" = sumUpTo (s "n") ∧ s "n" ≤ N)
         (fun s ↦ s "n" ≠ N)
         (Stmt.assign "n" (fun s ↦ s "n" + 1);
          Stmt.assign "r" (fun s ↦ s "r" + s "n")))
      {* fun s ↦ s "r" = sumUpTo N *}

    vcg
    simp [sumUpTo, State.update]
    intros
    simp_all[add_assoc, add_comm]
    cases a_1 <;>
    simp_all
    simp_all
    intros
    simp_all
    simp [sumUpTo, State.update]


/- 1.4 (**optional**). The following program `MUL` is intended to compute the
product of `n` and `m`, leaving the result in `r`.
Invoke `vcg` on `MUL` using a
suitable loop invariant and prove the emerging verification conditions. -/

def MUL : Stmt :=
  Stmt.assign "r" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ 0)
    (Stmt.assign "r" (fun s ↦ s "r" + s "m");
     Stmt.assign "n" (fun s ↦ s "n" - 1))

def Mul : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _, 0 => 0
  | n + 1, m => m + Mul n m

theorem MUL_correct (n₀ m₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *} (MUL)
    {* fun s ↦ s "r" = n₀ * m₀ *} :=
  by
    unfold MUL
    -- Преобразуем whileDo в invWhileDo с явным инвариантом
    simp [Stmt.assign, Stmt.seq]
    show {* fun s => s "n" = n₀ ∧ s "m" = m₀ *}
      (Stmt.assign "r" (fun s ↦ 0);
       Stmt.invWhileDo
         (fun s ↦ s "r" +  (s "n") * (s "m") =n₀ * m₀)  -- инвариант
         (fun s ↦ s "n" ≠ 0)
         (Stmt.assign "r" (fun s ↦ s "r" + s "m");
          Stmt.assign "n" (fun s ↦ s "n" - 1)))
      {* fun s ↦ s "r" = n₀ * m₀ *}
    vcg
    intros
    simp_all [sumUpTo, State.update]
    aesop
    have cat : (s "n" - 1) * s "m" = s "n" * s "m" -  s "m" :=
    by
       rw [mul_comm, Nat.mul_sub]
       simp_all
       rw [mul_comm]
    rw[cat]
    have cat1 : s "r" + (s "n" * s "m" - s "m") = s "r" + s "n" * s "m" - s "m" :=
    by
     rw [← Nat.add_sub_assoc]
     rw [mul_comm]
     apply Nat.le_mul_of_pos_right
     exact Nat.pos_of_ne_zero right
    simp_all[add_comm, cat1, mul_comm]
    have medv : s "m" + s "r" + (s "m" * s "n" - s "m") =
    s "m" + (s "r" + (s "m" * s "n" - s "m")) :=
    by
     ring
    rw [medv]
    rw [cat1]
    simp_all
    rw [← Nat.add_sub_assoc,
          add_comm]
    simp[Nat.sub_add_cancel]
    have w: 0 < s "n" :=
    by exact Nat.pos_of_ne_zero right
    simp_all_arith!
    by_contra h
    set r := s "r"
    set m := s "m"
    set n := s "n"
    set X := n₀ * m₀
    have h_gt : X < m := Nat.gt_of_not_le h
    simp_all
    have ww : 0 ≤ r := by simp_all_arith!
    have ww1 : 0 ≤ m := by simp_all_arith!
    have h_m_le : r + m * n < m := by simp_all_arith!
    have h_ge : m ≤ r + m * n := by
      have h1 : m ≤ m * n := Nat.le_mul_of_pos_right m w
      have h2 : m * n ≤ r + m * n := Nat.le_add_left (m * n) r
      exact Nat.le_trans h1 h2
    simp_all_arith!
    omega
    intros
    simp_all
    intros
    simp_all

/- ## Question 2: Hoare Triples for Total Correctness

The following definition captures Hoare triples
 for total correctness for
deterministic languages: -/

def TotalHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s, P s → ∃t, (S, s) ⟹ t ∧ Q t

macro "[*" P:term " *] " "(" S:term ")" " [* " Q:term " *]" : term =>
  `(TotalHoare $P $S $Q)

namespace TotalHoare

/- 2.1. Prove the consequence rule. -/

theorem consequence {P P' Q Q' S}
      (hS : [* P *] (S) [* Q *]) (hP : ∀s, P' s → P s) (hQ : ∀s, Q s → Q' s) :
    [* P' *] (S) [* Q' *] :=
  by
    simp_all[TotalHoare]
    intros
    have pos : P s := by simp_all
    have qos : ∃ t, (S, s) ⟹ t ∧ Q t := by simp_all
    cases qos
    exists w
    simp_all



/- 2.2. Prove the rule for `skip`. -/

theorem skip_intro {P} :
    [* P *] (Stmt.skip) [* P *] :=
  by
    simp_all[TotalHoare]


/- 2.3. Prove the rule for `assign`. -/

theorem assign_intro {P x a} :
    [* fun s ↦ P (s[x ↦ a s]) *] (Stmt.assign x a) [* P *] :=
  by
    simp_all[TotalHoare]

/- 2.4. Prove the rule for `seq`. -/

theorem seq_intro {P Q R S T} (hS : [* P *] (S) [* Q *])
      (hT : [* Q *] (T) [* R *]) :
    [* P *] (S; T) [* R *] :=
  by
    simp_all[TotalHoare]
    intros
    have qos : ∃ t, (S, s) ⟹ t ∧ Q t := by simp_all
    cases qos
    aesop
    have mos : ∃ t, (T, w) ⟹ t ∧ R t := by simp_all
    cases mos
    aesop


/- 2.5. Complete the proof of the rule for `if`–`then`–`else`.

Hint: The proof requires a case distinction
 on the truth value of `B s`. -/

theorem if_intro {B P Q S T}
      (hS : [* fun s ↦ P s ∧ B s *] (S) [* Q *])
      (hT : [* fun s ↦ P s ∧ ¬ B s *] (T) [* Q *]) :
    [* P *] (Stmt.ifThenElse B S T) [* Q *] :=
  by
    simp_all[TotalHoare]
    intros
    have pB : B s → ∃ t, (S, s) ⟹ t ∧ Q t := by simp_all
    have nB : ¬B s → ∃ t, (T, s) ⟹ t ∧ Q t := by simp_all
    have Tr : B s ∨ ¬B s := by
         by_contra h
         apply h
         right
         rw [Not]
         intros
         apply h
         left
         simp_all
    cases Tr
    have pBB : ∃ t, (S, s) ⟹ t ∧ Q t := by simp_all
    cases pBB
    exists w
    simp_all
    have nBB : ∃ t, (T, s) ⟹ t ∧ Q t := by simp_all
    cases nBB
    exists w
    simp_all







/- 2.6 (**optional**). Try to prove the rule for `while`.

The rule is parameterized by a loop invariant `I` and
by a variant `V` that
decreases with each iteration of the loop body.

Before we prove the desired theorem, we introduce
an auxiliary theorem. Its
proof requires induction by pattern matching and recursion.
When using
`var_while_intro_aux` as induction hypothesis we recommend
 to do it directly
after proving that the argument is less than `v₀`:

    have ih : ∃u, (Stmt.whileDo B S, t) ⟹ u ∧ I u ∧ ¬ B u :=
      have _ : V t < v₀ :=
        …
      var_while_intro_aux I V h_inv (V t) …

Similarly to `if`--`then`--`else`,
the proof requires a case distinction on the
truth value of `B s`. -/

theorem var_while_intro_aux {B} (I : State → Prop) (V : State → ℕ) {S}
    (h_inv : ∀v₀,
       [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
    ∀v₀ s, V s = v₀ → I s → ∃t, (Stmt.whileDo B S, s) ⟹ t ∧ I t ∧ ¬ B t
  | v₀, s, V_eq, hs =>
    by

      by_cases h_not_B : ¬B s
      exists s
      constructor
      vcg
      simp_all
      aesop
      have pB : B s := by simp_all

      have h_inv_s : ∃t, (S, s) ⟹ t ∧ I t ∧ V t < v₀ := by
       simp_all[TotalHoare]



      cases h_inv_s
      cases h
      cases right

      have ih : ∃t, (Stmt.whileDo B S, w) ⟹ t ∧ I t ∧ ¬B t :=
          var_while_intro_aux I V h_inv (V w) w rfl left_1
      cases ih
      exists w_1
      simp_all
      exists w
      simp_all








theorem var_while_intro {B} (I : State → Prop) (V : State → ℕ) {S}
    (hinv : ∀v₀,
       [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
    [* I *] (Stmt.whileDo B S) [* fun s ↦ I s ∧ ¬ B s *] :=
  by
    intro s hs
    have h_exists := var_while_intro_aux I V hinv (V s) s rfl hs
    exact h_exists

    /-let hinv_orig := hinv  -- сохраняем исходный
    simp [TotalHoare] at hinv
    intro s hs
    exact var_while_intro_aux I V hinv_orig (V s) s rfl hs
    -/
end TotalHoare

end LoVe
