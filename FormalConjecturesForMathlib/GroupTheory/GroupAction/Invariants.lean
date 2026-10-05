/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

/-!
# Numerical invariants of group actions

Invariants of an action of a group `G` on a finite set `α`, as natural numbers; for a permutation
group `G ≤ Equiv.Perm α` they are the invariants of its permutation representation.

* `MulAction.movedPoints G α`, `MulAction.numMovedPoints G α`: the points moved by some element;
* `MulAction.numOrbits G α`: the number of orbits;
* `MulAction.transitivityDegree G α`: the largest `k ≤ |α|` such that `G` is `k`-transitive;
* `MulAction.numOrbitals G α`: the number of orbits on `α × α`, the rank of a transitive action;
* `MulAction.minimalDegree G α`: the least number of points moved by an element that moves one;
* `MulAction.minInvolutionFixedPoints G α`, `MulAction.maxInvolutionFixedPoints G α`: the fixed
  points of elements of order at most `2`, resp. exactly `2`. If `G` is the Galois group of a
  real polynomial acting on its roots, complex conjugation is such an element, so the number of
  real roots is the number of fixed points of one of them.

Primitivity and `k`-transitivity are Mathlib's `MulAction.IsPreprimitive` and
`MulAction.IsMultiplyPretransitive`.
-/

namespace MulAction

variable (G α : Type*) [Group G] [MulAction G α]

/-- The points moved by some element of `G`. -/
def movedPoints : Set α := {a : α | ∃ g : G, g • a ≠ a}

/-- The number of points moved by some element of `G` (the degree of a permutation group). -/
noncomputable def numMovedPoints : ℕ := (movedPoints G α).ncard

/-- The number of orbits of `G` on `α`, fixed points included. -/
noncomputable def numOrbits : ℕ := Nat.card (orbitRel.Quotient G α)

/-- The largest `k ≤ Nat.card α` such that the action is `k`-transitive. (Every action is
`k`-transitive for `k > Nat.card α`, as there are no injections `Fin k ↪ α`.) -/
noncomputable def transitivityDegree : ℕ :=
  sSup {k : ℕ | k ≤ Nat.card α ∧ IsMultiplyPretransitive G α k}

/-- The number of orbitals, the orbits of `G` on `α × α`; for a transitive action this is its
rank, the number of orbits of a point stabiliser. -/
noncomputable def numOrbitals : ℕ := Nat.card (orbitRel.Quotient G (α × α))

/-- The minimal degree: the least number of points moved by an element that moves some point
(`0` if no element moves a point). -/
noncomputable def minimalDegree : ℕ :=
  sInf {k : ℕ | ∃ g : G, (fixedBy α g)ᶜ.Nonempty ∧ (fixedBy α g)ᶜ.ncard = k}

/-- The least number of points fixed by an element of order at most `2`; it is `Nat.card α` if
`G` has no involution, since the identity fixes every point. -/
noncomputable def minInvolutionFixedPoints : ℕ :=
  sInf {k : ℕ | ∃ g : G, g ^ 2 = 1 ∧ (fixedBy α g).ncard = k}

/-- The largest number of points fixed by an involution (`0` if `G` has none). -/
noncomputable def maxInvolutionFixedPoints : ℕ :=
  sSup {k : ℕ | ∃ g : G, orderOf g = 2 ∧ (fixedBy α g).ncard = k}

end MulAction
