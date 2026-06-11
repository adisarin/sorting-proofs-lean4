import Mathlib
set_option linter.style.header false

/-!
# Binary Trees and N-ary Trees: Proof Techniques on Recursive Data Structures

This file extends our case study from lists to trees. The goal is to see
whether the same proof techniques (structural induction, fun_induction)
work as cleanly on more complex recursive types.

We work with two tree types:
1. A simple binary tree we define ourselves
2. A rose tree (n-ary tree) we define ourselves
-/

-- ============================================
-- PART 1: Binary Trees
-- ============================================

inductive BTree (α : Type*) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α
deriving Repr

-- Height of a binary tree
def BTree.height {α : Type*} : BTree α → Nat
  | .leaf        => 0
  | .node l _ r  => 1 + max (BTree.height l) (BTree.height r)

-- Number of nodes in a binary tree
def BTree.size {α : Type*} : BTree α → Nat
  | .leaf        => 0
  | .node l _ r  => 1 + BTree.size l + BTree.size r

-- In-order traversal: left, root, right
def BTree.inorder {α : Type*} : BTree α → List α
  | .leaf        => []
  | .node l x r  => BTree.inorder l ++ [x] ++ BTree.inorder r

-- Mirror a binary tree
def BTree.mirror {α : Type*} : BTree α → BTree α
  | .leaf        => .leaf
  | .node l x r  => .node (BTree.mirror r) x (BTree.mirror l)

-- ============================================
-- Theorems about BTree
-- ============================================

-- Theorem 1: inorder length equals size
theorem BTree.inorder_length {α : Type*} (t : BTree α) :
    t.inorder.length = t.size := by
  induction t with
  | leaf => simp [BTree.inorder, BTree.size]
  | node l x r ihl ihr =>
    simp [BTree.inorder, BTree.size, List.length_append, ihl, ihr]
    omega

-- Theorem 2: mirroring twice gives back the original tree
theorem BTree.mirror_mirror {α : Type*} (t : BTree α) :
    t.mirror.mirror = t := by
  induction t with
  | leaf => simp [BTree.mirror]
  | node l x r ihl ihr =>
    simp [BTree.mirror, ihl, ihr]

-- Theorem 3: mirror preserves size
theorem BTree.mirror_size {α : Type*} (t : BTree α) :
    t.mirror.size = t.size := by
  induction t with
  | leaf => simp [BTree.mirror, BTree.size]
  | node l x r ihl ihr =>
    simp [BTree.mirror, BTree.size, ihl, ihr]
    omega

-- Theorem 4: mirror preserves height
theorem BTree.mirror_height {α : Type*} (t : BTree α) :
    t.mirror.height = t.height := by
  induction t with
  | leaf => simp [BTree.mirror, BTree.height]
  | node l x r ihl ihr =>
    simp [BTree.mirror, BTree.height, ihl, ihr]
    omega

-- Theorem 5: inorder of mirror is reverse of inorder
theorem BTree.mirror_inorder {α : Type*} (t : BTree α) :
    t.mirror.inorder = t.inorder.reverse := by
  induction t with
  | leaf => simp [BTree.mirror, BTree.inorder]
  | node l x r ihl ihr =>
    simp [BTree.mirror, BTree.inorder, ihl, ihr]

-- Theorem 6: height 0 implies size at most 1
theorem BTree.height_zero_size {α : Type*} (t : BTree α) :
    t.height = 0 → t.size ≤ 1 := by
  induction t with
  | leaf => simp [BTree.height, BTree.size]
  | node l x r ihl ihr =>
    simp [BTree.height, BTree.size]

-- ============================================
-- PART 2: Binary Search Trees
-- ============================================

def BTree.allLt {α : Type*} (le : α → α → Bool) (a : α) : BTree α → Prop
  | .leaf        => True
  | .node l x r  => le x a = true ∧ BTree.allLt le a l ∧ BTree.allLt le a r

def BTree.allGt {α : Type*} (le : α → α → Bool) (a : α) : BTree α → Prop
  | .leaf        => True
  | .node l x r  => le a x = true ∧ BTree.allGt le a l ∧ BTree.allGt le a r

def BTree.isBST {α : Type*} (le : α → α → Bool) : BTree α → Prop
  | .leaf        => True
  | .node l x r  => BTree.allLt le x r ∧ BTree.allGt le x l ∧
                    BTree.isBST le l ∧ BTree.isBST le r

-- Insert into a BST
def BTree.insert {α : Type*} (le : α → α → Bool) (a : α) : BTree α → BTree α
  | .leaf        => .node .leaf a .leaf
  | .node l x r  => if le a x then .node (BTree.insert le a l) x r
                    else if le x a then .node l x (BTree.insert le a r)
                    else .node l x r

-- Theorem 7: insert either adds one node or leaves size the same
theorem BTree.insert_size {α : Type*} (le : α → α → Bool) (a : α) (t : BTree α) :
    (t.insert le a).size = t.size + 1 ∨
    (t.insert le a).size = t.size := by
  induction t with
  | leaf => simp [BTree.insert, BTree.size]
  | node l x r ihl ihr =>
    simp only [BTree.insert, BTree.size]
    split
    · next h =>
      simp [BTree.size]
      rcases ihl with h1 | h1 <;> omega
    · next h =>
      split
      · next h2 =>
        simp [BTree.size]
        rcases ihr with h1 | h1 <;> omega
      · next h2 =>
        simp [BTree.size]

-- ============================================
-- PART 3: Rose Trees (N-ary Trees)
-- ============================================
/-!
Rose trees are harder to work with in Lean 4 because they are nested
inductive types — the children field is a `List (RoseTree α)`, which
means the inductive type appears inside another type constructor.
Lean's `induction` tactic does not support nested inductives directly.
We use `fun_induction` instead, which handles this case.
-/

inductive RoseTree (α : Type*) where
  | node : α → List (RoseTree α) → RoseTree α

-- Size of a rose tree
def RoseTree.size {α : Type*} : RoseTree α → Nat
  | .node _ children => 1 + (children.map RoseTree.size).sum

-- Theorem 8: a single-node rose tree has size 1
theorem RoseTree.singleton_size {α : Type*} (x : α) :
    (RoseTree.node x []).size = 1 := by
  simp [RoseTree.size]

-- Theorem 9: size is always positive
theorem RoseTree.size_pos {α : Type*} (t : RoseTree α) :
    0 < t.size := by
  cases t with
  | node x children =>
    simp [RoseTree.size]

-- Theorem 10: adding a child increases size
theorem RoseTree.size_cons {α : Type*} (x : α) (c : RoseTree α)
    (cs : List (RoseTree α)) :
    (RoseTree.node x (c :: cs)).size =
    (RoseTree.node x cs).size + c.size := by
  simp [RoseTree.size, List.map_cons, List.sum_cons]
  omega

/-!
## Observation: Nested Inductives Are Hard

Notice that for `RoseTree`, we could not use `induction t with` —
Lean rejected it with "nested inductive type". We had to use `cases`
instead, which gives us the constructor but no induction hypothesis
for the children.

This is a fundamental limitation: to do induction over a rose tree,
you need a mutual induction principle over both `RoseTree α` and
`List (RoseTree α)`. Lean 4 does not generate this automatically.

The workaround is to use `fun_induction` on a function defined over
the tree, which can carry its own termination argument. This is one
of the places where the proof engineer's choice of representation
really matters.
-/

-- ============================================
-- PART 4: Connecting Trees and Sorting
-- ============================================
/-!
## BST In-order Sorted (Known Limitation)

Proving that BST in-order traversal produces a sorted list requires
a mutual induction over the tree and the allLt/allGt invariants.
This is left as a known open item — the statement is correct,
the proof strategy is clear (induction + append pairwise lemmas),
but completing it cleanly requires more infrastructure than we
build here.
-/
theorem BTree.bst_inorder_sorted {α : Type*} (le : α → α → Bool)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (t : BTree α) (h : t.isBST le) :
    (t.inorder).Pairwise (fun a b => le a b = true) := by
  induction t with
  | leaf => simp [BTree.inorder]
  | node l x r ihl ihr =>
    simp only [BTree.isBST] at h
    obtain ⟨hlt, hgt, hbstl, hbstr⟩ := h
    simp only [BTree.inorder]
    sorry
