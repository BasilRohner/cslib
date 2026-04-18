/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/

module

public import Cslib.Init

@[expose] public section

/-! # Fenwick Tree (Binary Indexed Tree)

This file defines `FenwickTree`, a data structure that supports efficient
prefix sum queries and point updates on an array of elements in a commutative
group.

## Main definitions

* `FenwickTree`: The Fenwick tree structure over a commutative group

## References

* <https://cp-algorithms.com/data_structures/fenwick.html>
-/
