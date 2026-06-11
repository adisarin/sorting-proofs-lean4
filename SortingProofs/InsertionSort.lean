import Mathlib
set_option linter.style.header false

-- ============================================
-- PART 2: Insertion Sort from Scratch
-- ============================================
-- Unlike mergeSort which we pulled from Mathlib,
-- we implement insertion sort ourselves and prove
-- everything ground up. This lets us compare
-- proof structure directly against mergeSort.

-- Insert an element into a sorted list
def insert' {α : Type*} (le : α → α → Bool) (a : α) : List α → List α
  | []      => [a]
  | x :: xs => if le a x then a :: x :: xs
               else x :: insert' le a xs

-- Insertion sort
def insertionSort {α : Type*} (le : α → α → Bool) : List α → List α
  | []      => []
  | x :: xs => insert' le x (insertionSort le xs)

-- ============================================
-- Lemmas about insert'
-- ============================================

-- insert' adds exactly one element
theorem insert'_length {α : Type*} (le : α → α → Bool) (a : α) (xs : List α) :
    (insert' le a xs).length = xs.length + 1 := by
  induction xs with
  | nil => simp [insert']
  | cons x xs ih =>
    simp [insert']
    split
    · simp
    · simp [ih]

-- membership after insert': y is in (insert' a xs) iff y = a or y ∈ xs
theorem insert'_mem {α : Type*} (le : α → α → Bool) (a : α) (xs : List α) (y : α) :
    y ∈ insert' le a xs ↔ y = a ∨ y ∈ xs := by
  induction xs with
  | nil => simp [insert']
  | cons x xs ih =>
    simp only [insert']
    split
    · simp [List.mem_cons]
    · simp only [List.mem_cons, ih]
      tauto

-- insert' produces a permutation of (a :: xs)
theorem insert'_perm {α : Type*} (le : α → α → Bool) (a : α) (xs : List α) :
    (insert' le a xs).Perm (a :: xs) := by
  induction xs with
  | nil => simp [insert']
  | cons x xs ih =>
    simp only [insert']
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons x ih).trans (List.Perm.swap a x xs)

-- ============================================
-- Main Theorems about insertionSort
-- ============================================

-- Theorem 1: insertionSort preserves length
-- Proof: structural induction, using insert'_length
theorem insertionSort_length {α : Type*} (le : α → α → Bool) (xs : List α) :
    (insertionSort le xs).length = xs.length := by
  induction xs with
  | nil => simp [insertionSort]
  | cons x xs ih =>
    simp only [insertionSort, List.length_cons]
    rw [insert'_length]
    omega

-- Theorem 2: insertionSort produces a permutation
-- Proof: structural induction, composing insert'_perm and induction hypothesis
theorem insertionSort_perm {α : Type*} (le : α → α → Bool) (xs : List α) :
    (insertionSort le xs).Perm xs := by
  induction xs with
  | nil => simp [insertionSort]
  | cons x xs ih =>
    simp only [insertionSort]
    exact (insert'_perm le x _).trans (List.Perm.cons x ih)

-- ============================================
-- Theorem 3: insertionSort produces a sorted list
-- ============================================

theorem insert'_pairwise {α : Type*} (le : α → α → Bool) (a : α) (xs : List α)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (hsorted : xs.Pairwise (fun a b => le a b = true)) :
    (insert' le a xs).Pairwise (fun a b => le a b = true) := by
  induction xs with
  | nil => simp [insert']
  | cons x xs ih =>
    simp only [insert']
    split
    · next h =>
      rw [List.pairwise_cons]
      refine ⟨?_, hsorted⟩
      intro y hy
      rcases List.mem_cons.mp hy with heq | hmem
      · rw [heq]; exact h
      · rw [List.pairwise_cons] at hsorted
        exact htrans a x y h (hsorted.1 y hmem)
    · next h =>
      have hax : le x a = true := by
        rcases htotal a x with hab | hba
        · simp [hab] at h
        · exact hba
      rw [List.pairwise_cons] at hsorted
      rw [List.pairwise_cons]
      refine ⟨?_, ih hsorted.2⟩
      intro y hy
      rw [insert'_mem] at hy
      rcases hy with heq | hmem
      · rw [heq]; exact hax
      · exact hsorted.1 y hmem

theorem insertionSort_sorted {α : Type*} (le : α → α → Bool) (xs : List α)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (htotal : ∀ a b, le a b = true ∨ le b a = true) :
    (insertionSort le xs).Pairwise (fun a b => le a b = true) := by
  induction xs with
  | nil => simp [insertionSort]
  | cons x xs ih =>
    simp only [insertionSort]
    exact insert'_pairwise le x _ htrans htotal ih
