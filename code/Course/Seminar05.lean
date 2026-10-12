/-
# Seminar 5
- Products, sums, and optional results
- Recursive programs on lists
- Small list algorithms
- Membership as a specification
-/

import Mathlib

namespace Seminar05

-- ## Round 1 — data shapes

/-- Change how three values are grouped. -/
def reassociate {α β γ : Type} :
    (α × β) × γ → α × (β × γ) := by
  rintro ⟨⟨a, b⟩, c⟩
  exact ⟨a, ⟨b, c⟩⟩

/-- Both alternatives contain the same type, so either one can be returned. -/
def mergeSame {α : Type} : Sum α α → α := by
  intro h
  cases h with
  | inl a => exact a
  | inr a => exact a

/-- Return the first two elements together,
or `none` if there are fewer than two. -/
def firstTwo? {α : Type} : List α → Option (α × α)
  | [] => none
  | [_] => none
  | x :: y :: _ => some ⟨x, y⟩

-- ## Round 2 — programs that follow the shape of a list

/-- Replace every element by two adjacent copies. -/
def duplicateEach {α : Type} : List α → List α
  | [] => []
  | x :: xs => x :: x :: duplicateEach xs

/-- Homework ex01: keep the first, third, fifth, ... elements. -/
def dropEveryOther {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: dropEveryOther xs

/-- These examples should close by computation. -/
example : duplicateEach [1, 2, 3] = [1, 1, 2, 2, 3, 3] := by
  rfl

example : dropEveryOther [1, 2, 3, 4, 5] = [1, 3, 5] := by
  rfl

-- ## Round 3 — algorithms as case distinctions

/-- Remove every zero from a list. -/
def removeZeros : List Nat → List Nat
  | [] => []
  | x :: xs =>
      if x = 0 then removeZeros xs
      else x :: removeZeros xs

/-- Homework ex02: return the second-to-last element, if it exists. -/
def penultimate? {α : Type} : List α → Option α
  | [] => none
  | [_] => none
  | [x, _] => some x
  | _ :: y :: z :: ys => penultimate? (y :: z :: ys)

/-- Keep the prefix before the first zero. -/
def takeUntilZero : List Nat → List Nat
  | [] => []
  | x :: xs =>
      if x = 0 then []
      else x :: takeUntilZero xs

example : removeZeros [0, 3, 0, 2] = [3, 2] := by
  rfl

example : penultimate? [4, 7, 9] = some 7 := by
  rfl

example : takeUntilZero [3, 2, 0, 4] = [3, 2] := by
  rfl

-- ## Round 4 — trees

/-
A tree is either:

- a leaf with no stored value;
- a node containing a value and two smaller trees.
-/

inductive Tree (α : Type) where
  | leaf
  | node (left : Tree α) (value : α) (right : Tree α)
  deriving Repr, DecidableEq

/-
Build this tree:

        2
       / \
      1   3
-/
def exampleTree : Tree Nat :=
  .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)

-- ## Round 5 — membership describes the output

/-- First build one concrete membership proof. -/
example : 2 ∈ duplicateEach [1, 2, 3] := by
  repeat constructor

/-- `duplicateEach` changes multiplicity, but not which values occur. -/
theorem memDuplicateEach {α : Type} (x : α) (xs : List α) :
    x ∈ duplicateEach xs ↔ x ∈ xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [duplicateEach, List.mem_cons, ih]
    constructor
    · rintro (h | h | h)
      · left; exact h
      · left; exact h
      · right; exact h
    · rintro (h | h)
      · left; exact h
      · right; right; exact h

/-- The output of `removeZeros` never contains zero. -/
theorem zeroNotMemRemoveZeros (xs : List Nat) :
    0 ∉ removeZeros xs := by
  induction xs with
  | nil =>
    rw [removeZeros]
    intro h
    cases h
  | cons y ys ih =>
    rw [removeZeros]
    split
    · exact ih
    · rw [List.mem_cons]
      rintro (h | h)
      · rename_i hx
        exact hx h.symm
      · exact ih h

/-
Discussion: does `memDuplicateEach` say that every value occurs the same
number of times in both lists? Why not?
-/

end Seminar05
