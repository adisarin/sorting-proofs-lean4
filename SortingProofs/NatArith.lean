import Mathlib
set_option linter.style.header false

/-!
# Natural Number Arithmetic: A Warmup for Lean 4 Beginners

Before diving into sorting algorithms, it helps to get comfortable
with Lean 4's proof style on familiar ground. This file proves basic
facts about natural numbers that every CS student knows — but now
we prove them formally.

This is the gentlest entry point into the project.
-/

-- ============================================
-- PART 1: Basic Arithmetic Facts
-- ============================================

-- Addition is commutative
-- Lean's omega tactic closes this instantly
theorem my_add_comm (n m : Nat) : n + m = m + n := by
  omega

-- Addition is associative
theorem add_assoc' (n m k : Nat) : n + m + k = n + (m + k) := by
  omega

-- Multiplication distributes over addition
theorem mul_distrib (n m k : Nat) : n * (m + k) = n * m + n * k := by
  ring

-- Zero is the additive identity
theorem add_zero' (n : Nat) : n + 0 = n := by
  omega

-- ============================================
-- PART 2: Induction on Natural Numbers
-- ============================================
-- These proofs require actual induction, not just omega.
-- They show the basic induction pattern in Lean 4.

-- Sum of first n natural numbers = n * (n + 1) / 2
-- We prove the doubled version to avoid division
def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp [sumTo]
    ring_nf
    linarith

-- Exponentiation: 2^n is always positive
theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Nat.pow_succ]

-- n < 2^n for all n
theorem lt_two_pow (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Nat.pow_succ]
    omega

-- ============================================
-- PART 3: Induction on Lists
-- ============================================
-- Before sorting, we need to be comfortable with
-- structural induction on lists.

-- Length of append
theorem length_append' {α : Type*} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih]
    omega

-- Reversing a list preserves length
theorem length_reverse' {α : Type*} (xs : List α) :
    xs.reverse.length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih]

-- Reversing twice gives back the original list
theorem reverse_reverse' {α : Type*} (xs : List α) :
    xs.reverse.reverse = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.reverse_append, ih]

-- Map preserves length
theorem map_length' {α β : Type*} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih]

-- ============================================
-- PART 4: Induction Patterns
-- ============================================
-- Two different ways to prove the same thing.
-- This directly motivates the structural vs
-- functional induction comparison in Comparison.lean

-- filter length: filtered list is no longer than original
theorem filter_length_le {α : Type*} (p : α → Bool) (xs : List α) :
    (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.filter]
    split
    · simp; omega
    · omega

-- takeWhile length: prefix is no longer than original
theorem takeWhile_length_le {α : Type*} (p : α → Bool) (xs : List α) :
    (xs.takeWhile p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.takeWhile]
    split
    · simp; omega
    · simp

-- ============================================
-- PART 5: Using omega and simp effectively
-- ============================================
-- These examples show when to use omega vs simp vs ring
-- and why the choice matters.

-- omega handles linear arithmetic
example (n : Nat) (h : n > 5) : n ≥ 6 := by omega

-- ring handles polynomial identities
example (n : Nat) : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring

-- simp handles definitional rewrites
example (xs : List Nat) : (xs ++ []).length = xs.length := by simp

-- combining them
theorem double_length {α : Type*} (xs : List α) :
    (xs ++ xs).length = 2 * xs.length := by
  simp
  omega
