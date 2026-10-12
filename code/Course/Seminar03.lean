/-
# Seminar 3
-/

import Mathlib.Tactic

namespace Seminar03

-- ## Round 1 — rfl or induction

inductive MyNat where
  | zero
  | succ (n : MyNat)
  deriving Repr

namespace MyNat

def add : MyNat → MyNat → MyNat
  | n, .zero => n
  | n, .succ m => .succ (add n m)

theorem add_zero (n : MyNat) : add n .zero = n := rfl

theorem add_succ (n m : MyNat) :
    add n (.succ m) = .succ (add n m) := rfl

/-- Can this be proved by computation? -/
theorem add_one (n : MyNat) :
    add n (.succ .zero) = .succ n := by
  rw [add_succ, add_zero]

/-- Try cases n, inspect the stuck goal, then restart with induction n. -/
theorem zero_add (n : MyNat) :
    add .zero n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [add_succ, ih]

/-- Choose the induction variable from the definition of add. -/
theorem succ_add (n m : MyNat) :
    add (.succ n) m = .succ (add n m) := by
  induction m with
  | zero => rfl
  | succ k ih => rw [add_succ, add_succ, ih]

-- ## Round 2 — induction as a recursor

#check @MyNat.rec
#check @congrArg

/-- Write the proof of zero_add using MyNat.rec. -/
theorem zero_add_term (n : MyNat) :
    add .zero n = n :=
  MyNat.rec
    (motive := fun k => add .zero k = k)
    (by rfl)
    (fun k ih => congrArg MyNat.succ ih)
    n

#print zero_add
#print zero_add_term

/-- Equal successors have equal predecessors. No induction needed. -/
theorem succ_injective (n m : MyNat) (h : succ n = succ m) :
    n = m := by
  apply MyNat.succ.inj
  exact h

end MyNat

-- ## Round 3 — recursive functions and specifications

/-
Define multiplication by recursion on the second argument.
-/
def mulRec : Nat → Nat → Nat
  | _, .zero => .zero
  | n, m + 1 => mulRec n m + n

theorem mulRec_eq (n m : Nat) :
    mulRec n m = n * m := by
  induction m with
  | zero => rfl
  | succ k ih => rw [mulRec, ih, Nat.mul_succ]

/-- First prove by induction on k; then prove again using mulRec_eq. -/
theorem mulRec_add (n m k : Nat) :
    mulRec n (m + k) = mulRec n m + mulRec n k := by
  induction k with
  | zero => rfl
  | succ b ih => rw [Nat.add_one, Nat.add_succ, mulRec, ih, mulRec, ← Nat.add_assoc]

theorem mulRec_add' (n m k : Nat) :
    mulRec n (m + k) = mulRec n m + mulRec n k := by
  rw [mulRec_eq, mulRec_eq, mulRec_eq, Nat.mul_add]


def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

theorem double_succ (n : Nat) :
    double (n + 1) = double n + 2 := rfl

-- Homework ex13. Prove by induction on m.
theorem double_add (n m : Nat) :
    double (n + m) = double n + double m := by
  induction m with
  | zero => rfl
  | succ k ih => rw [Nat.add_one, Nat.add_succ, double_succ, double_succ, ih, ← Nat.add_assoc]

-- Given from the lecture.
theorem double_eq_two_mul (n : Nat) :
    double n = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [double_succ, ih, Nat.mul_succ]

/-- Use double_eq_two_mul and calc, not induction. -/
theorem double_double (n : Nat) :
    double (double n) = 4 * n := by
  calc double (double n)
      = double (2 * n) := by rw [double_eq_two_mul n]
    _ = 2 * (2 * n) := by rw [double_eq_two_mul (2 * n)]
    _ = 2 * 2 * n := (Nat.mul_assoc 2 2 n).symm
    _ = 4 * n := rfl

def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

-- Homework ex15.
theorem half_double (n : Nat) :
    half (double n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_one, double_succ, half, ih]


-- ## Round 4 — generalizing the induction hypothesis

def doubleAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => doubleAcc n (acc + 2)

/--
Prove correctness for every initial accumulator.
Compare induction n with induction n generalizing acc.
-/
theorem doubleAcc_correct (n acc : Nat) :
    doubleAcc n acc = double n + acc := by
  induction n generalizing acc with
  | zero => simp [doubleAcc, double]
  | succ k ih =>
    simp only [doubleAcc]
    rw [ih (acc + 2)]
    simp only [double]
    omega


end Seminar03
