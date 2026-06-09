import Mathlib
set_option linter.style.header false

-- ============================================
-- Sorting Proofs: A Learner's Case Study
-- Proof Techniques in Lean 4
-- ============================================

-- ============================================
-- PART 1: Merge Sort via Functional Induction
-- ============================================

-- Theorem 1: mergeSort preserves list length
-- We use fun_induction to follow mergeSort's own recursion structure
theorem mergeSort_length {α : Type*} (le : α → α → Bool) (xs : List α) :
    (xs.mergeSort le).length = xs.length := by
  fun_induction xs.mergeSort le
  · rfl
  · rfl
  · simp_all
    omega

-- Theorem 2: mergeSort produces a permutation of the input
theorem mergeSort_perm {α : Type*} (le : α → α → Bool) (xs : List α) :
    (xs.mergeSort le).Perm xs := by
  exact List.mergeSort_perm xs le

-- Theorem 3: mergeSort produces a sorted list
theorem mergeSort_sorted {α : Type*} (le : α → α → Bool) (xs : List α)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (htotal : ∀ a b, le a b = true ∨ le b a = true) :
    (xs.mergeSort le).Pairwise (fun a b => le a b = true) := by
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    exact htrans a b c hab hbc
  · intro a b
    cases htotal a b with
    | inl h => simp [h]
    | inr h => simp [h]
