import Mathlib
import SortingProofs.InsertionSort
set_option linter.style.header false
set_option linter.unusedSimpArgs false

/-!
# Structural vs Functional Induction: Direct Comparison

This file proves the same theorems two ways, side by side.
The goal is to make the difference concrete and runnable —
not just described in prose.

For each theorem we show:
1. The structural induction proof (induct on the data type)
2. The functional induction proof (induct on the function's recursion)

Then we comment on what was easier and why.
-/

-- ============================================
-- EXAMPLE 1: List Length after Map
-- ============================================
-- A simple warmup where both approaches are roughly equal.

def myMap' {α β : Type*} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: myMap' f xs

-- Structural induction: follow the List constructors
theorem myMap'_length_structural {α β : Type*} (f : α → β) (xs : List α) :
    (myMap' f xs).length = xs.length := by
  induction xs with
  | nil => simp [myMap']
  | cons x xs ih => simp [myMap', ih]

-- Functional induction: follow myMap's recursion
theorem myMap'_length_functional {α β : Type*} (f : α → β) (xs : List α) :
    (myMap' f xs).length = xs.length := by
  fun_induction myMap' f xs
  · simp [myMap']
  · simp [myMap', *]

/-!
**Verdict for map:** Both proofs are identical in length and complexity.
This is expected — `myMap'` recurses structurally on the list,
so structural induction and functional induction generate the same cases.
-/

-- ============================================
-- EXAMPLE 2: List Length after Filter
-- ============================================
-- Filter is also structurally recursive, but the cases
-- inside structural induction require a split.

def myFilter {α : Type*} (p : α → Bool) : List α → List α
  | []      => []
  | x :: xs => if p x then x :: myFilter p xs else myFilter p xs

-- Structural induction
theorem myFilter_length_structural {α : Type*} (p : α → Bool) (xs : List α) :
    (myFilter p xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [myFilter]
  | cons x xs ih =>
    simp only [myFilter]
    split
    · simp; omega
    · simp; omega

-- Functional induction
theorem myFilter_length_functional {α : Type*} (p : α → Bool) (xs : List α) :
    (myFilter p xs).length ≤ xs.length := by
  fun_induction myFilter p xs
  · simp [myFilter]
  · next h => simp [myFilter, h]
  · next h => simp [myFilter, h]; omega

/-!
**Verdict for filter:** Functional induction is slightly cleaner here.
The `split` in structural induction requires us to name the cases manually,
while functional induction already has the `if` cases split for us.
-/

-- ============================================
-- EXAMPLE 3: Flatten (concat)
-- ============================================
-- A function where structural induction is clearly better.

def myFlatten {α : Type*} : List (List α) → List α
  | []        => []
  | xs :: xss => xs ++ myFlatten xss

theorem myFlatten_length_structural {α : Type*} (xss : List (List α)) :
    (myFlatten xss).length = (xss.map List.length).sum := by
  induction xss with
  | nil => simp [myFlatten]
  | cons xs xss ih =>
    simp [myFlatten, List.length_append, ih]

theorem myFlatten_length_functional {α : Type*} (xss : List (List α)) :
    (myFlatten xss).length = (xss.map List.length).sum := by
  fun_induction myFlatten xss
  · simp [myFlatten]
  · simp [myFlatten, List.length_append, *]

/-!
**Verdict for flatten:** Again identical. Both follow the same nil/cons split.
-/

-- ============================================
-- EXAMPLE 4: Insert into sorted list (our own)
-- ============================================
-- Here structural induction requires careful case splitting
-- while functional induction on insert' is cleaner.

-- Recall insert' from InsertionSort.lean:
-- def insert' le a | [] => [a] | x::xs => if le a x then ... else ...

-- Structural induction on insert' length
theorem insert'_length_structural {α : Type*} (le : α → α → Bool)
    (a : α) (xs : List α) :
    (insert' le a xs).length = xs.length + 1 := by
  induction xs with
  | nil => simp [insert']
  | cons x xs ih =>
    simp only [insert']
    split
    · simp
    · simp [ih]

-- Functional induction on insert' length
theorem insert'_length_functional {α : Type*} (le : α → α → Bool)
    (a : α) (xs : List α) :
    (insert' le a xs).length = xs.length + 1 := by
  fun_induction insert' le a xs
  · simp [insert']
  · simp [insert']
  · simp [insert', *]

/-!
**Verdict for insert':** Functional induction is cleaner.
- Structural gives us `nil` and `cons`, then we have to `split` on the `if`.
- Functional gives us three cases directly: nil, le=true, le=false.
- The `split` inside structural induction is an extra cognitive step.
-/

-- ============================================
-- EXAMPLE 5: Merge Sort length (the main event)
-- ============================================
-- This is where functional induction wins decisively.

-- Structural induction attempt — this is genuinely hard because
-- mergeSort does NOT recurse structurally on the list.
-- The recursion goes xs → left_half, right_half, neither of which
-- is a structural subterm of xs. Structural induction gives us
-- no useful induction hypothesis here.

-- We can't even write a clean structural proof — this demonstrates
-- exactly why fun_induction was invented.

theorem mergeSort_length_functional {α : Type*} (le : α → α → Bool)
    (xs : List α) :
    (xs.mergeSort le).length = xs.length := by
  fun_induction xs.mergeSort le
  · rfl
  · rfl
  · simp_all; omega

/-!
**Verdict for mergeSort:** Functional induction wins completely.
Structural induction fails here — there is no way to get a useful IH
by inducting on the list structure, because mergeSort splits the list
in half, and neither half is a structural subterm.

This is the key insight of the project:
- When a function recurses structurally → both approaches work
- When a function recurses on a computed subterm → only fun_induction works cleanly

merge sort is the canonical example of the second case.
-/

-- ============================================
-- Summary Table (as Lean comments)
-- ============================================
/-!
| Function      | Recursion type  | Structural | Functional | Winner      |
|---------------|-----------------|------------|------------|-------------|
| myMap'        | structural      | 2 lines    | 2 lines    | tie         |
| myFilter      | structural+if   | 4 lines    | 3 lines    | functional  |
| myFlatten     | structural      | 2 lines    | 2 lines    | tie         |
| insert'       | structural+if   | 4 lines    | 3 lines    | functional  |
| mergeSort     | well-founded    | impossible | 4 lines    | functional  |

The pattern is clear: fun_induction matches or beats structural induction
in every case, and wins decisively when the recursion is not structural.

/-!
# Structural vs Functional Induction: Direct Comparison

This file proves the same theorems two ways, side by side.
The goal is to make the difference concrete and runnable —
not just described in prose.

For each theorem we show:
1. The structural induction proof (induct on the data type)
2. The functional induction proof (induct on the function's recursion)

Then we comment on what was easier and why.
-/

-- ============================================
-- EXAMPLE 1: List Length after Map
-- ============================================
-- A simple warmup where both approaches are roughly equal.

def myMap' {α β : Type*} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: myMap' f xs

-- Structural induction: follow the List constructors
theorem myMap'_length_structural {α β : Type*} (f : α → β) (xs : List α) :
    (myMap' f xs).length = xs.length := by
  induction xs with
  | nil => simp [myMap']
  | cons x xs ih => simp [myMap', ih]

-- Functional induction: follow myMap's recursion
theorem myMap'_length_functional {α β : Type*} (f : α → β) (xs : List α) :
    (myMap' f xs).length = xs.length := by
  fun_induction myMap' f xs
  · simp [myMap']
  · simp [myMap', *]

/-!
**Verdict for map:** Both proofs are identical in length and complexity.
This is expected — `myMap'` recurses structurally on the list,
so structural induction and functional induction generate the same cases.
-/

-- ============================================
-- EXAMPLE 2: List Length after Filter
-- ============================================
-- Filter is also structurally recursive, but the cases
-- inside structural induction require a split.

def myFilter {α : Type*} (p : α → Bool) : List α → List α
  | []      => []
  | x :: xs => if p x then x :: myFilter p xs else myFilter p xs

-- Structural induction
theorem myFilter_length_structural {α : Type*} (p : α → Bool) (xs : List α) :
    (myFilter p xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [myFilter]
  | cons x xs ih =>
    simp only [myFilter]
    split
    · simp; omega
    · omega

-- Functional induction
theorem myFilter_length_functional {α : Type*} (p : α → Bool) (xs : List α) :
    (myFilter p xs).length ≤ xs.length := by
  fun_induction myFilter p xs
  · simp [myFilter]
  · next h => simp [myFilter, h]; omega
  · next h => simp [myFilter, h]; omega

/-!
**Verdict for filter:** Functional induction is slightly cleaner here.
The `split` in structural induction requires us to name the cases manually,
while functional induction already has the `if` cases split for us.
-/

-- ============================================
-- EXAMPLE 3: Flatten (concat)
-- ============================================
-- A function where structural induction is clearly better.

def myFlatten {α : Type*} : List (List α) → List α
  | []        => []
  | xs :: xss => xs ++ myFlatten xss

theorem myFlatten_length_structural {α : Type*} (xss : List (List α)) :
    (myFlatten xss).length = (xss.map List.length).sum := by
  induction xss with
  | nil => simp [myFlatten]
  | cons xs xss ih =>
    simp [myFlatten, List.length_append, ih]

theorem myFlatten_length_functional {α : Type*} (xss : List (List α)) :
    (myFlatten xss).length = (xss.map List.length).sum := by
  fun_induction myFlatten xss
  · simp [myFlatten]
  · simp [myFlatten, List.length_append, *]

/-!
**Verdict for flatten:** Again identical. Both follow the same nil/cons split.
-/

-- ============================================
-- EXAMPLE 4: Insert into sorted list (our own)
-- ============================================
-- Here structural induction requires careful case splitting
-- while functional induction on insert' is cleaner.

-- Recall insert' from InsertionSort.lean:
-- def insert' le a | [] => [a] | x::xs => if le a x then ... else ...

-- Structural induction on insert' length
theorem insert'_length_structural {α : Type*} (le : α → α → Bool)
    (a : α) (xs : List α) :
    (insert' le a xs).length = xs.length + 1 := by
  induction xs with
  | nil => simp [insert']
  | cons x xs ih =>
    simp only [insert']
    split
    · simp
    · simp [ih]

-- Functional induction on insert' length
theorem insert'_length_functional {α : Type*} (le : α → α → Bool)
    (a : α) (xs : List α) :
    (insert' le a xs).length = xs.length + 1 := by
  fun_induction insert' le a xs
  · simp [insert']
  · simp [insert']
  · simp [insert', *]

/-!
**Verdict for insert':** Functional induction is cleaner.
- Structural gives us `nil` and `cons`, then we have to `split` on the `if`.
- Functional gives us three cases directly: nil, le=true, le=false.
- The `split` inside structural induction is an extra cognitive step.
-/

-- ============================================
-- EXAMPLE 5: Merge Sort length (the main event)
-- ============================================
-- This is where functional induction wins decisively.

-- Structural induction attempt — this is genuinely hard because
-- mergeSort does NOT recurse structurally on the list.
-- The recursion goes xs → left_half, right_half, neither of which
-- is a structural subterm of xs. Structural induction gives us
-- no useful induction hypothesis here.

-- We can't even write a clean structural proof — this demonstrates
-- exactly why fun_induction was invented.

theorem mergeSort_length_functional {α : Type*} (le : α → α → Bool)
    (xs : List α) :
    (xs.mergeSort le).length = xs.length := by
  fun_induction xs.mergeSort le
  · rfl
  · rfl
  · simp_all; omega

/-!
**Verdict for mergeSort:** Functional induction wins completely.
Structural induction fails here — there is no way to get a useful IH
by inducting on the list structure, because mergeSort splits the list
in half, and neither half is a structural subterm.

This is the key insight of the project:
- When a function recurses structurally → both approaches work
- When a function recurses on a computed subterm → only fun_induction works cleanly

merge sort is the canonical example of the second case.
-/

-- ============================================
-- Summary Table (as Lean comments)
-- ============================================
/-!
| Function      | Recursion type  | Structural | Functional | Winner      |
|---------------|-----------------|------------|------------|-------------|
| myMap'        | structural      | 2 lines    | 2 lines    | tie         |
| myFilter      | structural+if   | 4 lines    | 3 lines    | functional  |
| myFlatten     | structural      | 2 lines    | 2 lines    | tie         |
| insert'       | structural+if   | 4 lines    | 3 lines    | functional  |
| mergeSort     | well-founded    | impossible | 4 lines    | functional  |

The pattern is clear: fun_induction matches or beats structural induction
in every case, and wins decisively when the recursion is not structural.
-/
-/
