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

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.RepresentationTheory.FDRep

@[expose] public section

/-!
# Numerical invariants of groups

Invariants of finite groups that are not yet in Mathlib, as natural numbers, so that they can be
compared in inequalities. Many others are already there: the order `Nat.card G`, the exponent
`Monoid.exponent G`, the number of conjugacy classes `Nat.card (ConjClasses G)`, the order of the
centre `Nat.card (Subgroup.center G)`, the abelianisation `Abelianization G`, the nilpotency class
`Group.nilpotencyClass G`, and the properties `Group.IsSolvable`, `Group.IsNilpotent`,
`Group.IsPerfect`, `IsSimpleGroup`.

* `Group.numPrimeDivisors G`, `Group.largestPrimeDivisor G`: the primes dividing `Nat.card G`;
* `Group.derivedLength G`: the length of the derived series;
* `Group.numElementOrders G`, `Group.maxElementOrder G`, `Group.numInvolutions G`;
* `Group.numRationalClasses G`: the number of conjugacy classes of cyclic subgroups;
* `Group.numGaloisStableClasses G`: the number of conjugacy classes fixed by the Galois action
  `g ↦ g ^ k`, `k` coprime to the order of `g`;
* `Group.numNormalSubgroups G`, `Group.numMaximalSubgroupClasses G`;
* `Group.maxCharacterDegree G`: the largest dimension of an irreducible complex representation.

The definitions are meant for finite groups; on infinite groups the cardinalities are `0` when
infinite, as for `Set.ncard`.
-/

open scoped Pointwise

namespace Group

variable (G : Type*) [Group G]

/-- The number of distinct primes dividing the order of `G`. -/
noncomputable def numPrimeDivisors : ℕ := (Nat.card G).primeFactors.card

/-- The largest prime dividing the order of `G`, or `0` if there is none (`G` trivial). -/
noncomputable def largestPrimeDivisor : ℕ := (Nat.card G).primeFactors.sup id

/-- The derived length of `G`: the least `k` with `derivedSeries G k = ⊥`. It is `0` if there is
none, that is, if `G` is not solvable. -/
noncomputable def derivedLength : ℕ := sInf {k : ℕ | derivedSeries G k = ⊥}

/-- The number of distinct orders of elements of `G`. -/
noncomputable def numElementOrders : ℕ := (Set.range (orderOf : G → ℕ)).ncard

/-- The largest order of an element of `G` (`0` if the orders are unbounded). -/
noncomputable def maxElementOrder : ℕ := sSup (Set.range (orderOf : G → ℕ))

/-- The number of involutions of `G`, its elements of order `2`. -/
noncomputable def numInvolutions : ℕ := {g : G | orderOf g = 2}.ncard

/-- The number of rational classes of `G`: two elements are in the same rational class if they
generate conjugate cyclic subgroups, so this is the number of conjugacy classes of cyclic
subgroups. -/
noncomputable def numRationalClasses : ℕ :=
  (Set.range fun g : G => MulAction.orbit (ConjAct G) (Subgroup.zpowers g)).ncard

/-- The number of conjugacy classes of `G` fixed by the action of `Gal(ℚ̄/ℚ)`, which maps the
class of `g` to the class of `g ^ k` for `k` coprime to the order of `g`. These are the classes on
which every complex character of `G` takes rational values. -/
noncomputable def numGaloisStableClasses : ℕ :=
  ((ConjClasses.mk : G → ConjClasses G) ''
    {g : G | ∀ k : ℕ, k.Coprime (orderOf g) → IsConj g (g ^ k)}).ncard

/-- The number of normal subgroups of `G`. -/
noncomputable def numNormalSubgroups : ℕ := {H : Subgroup G | H.Normal}.ncard

/-- The number of conjugacy classes of maximal subgroups of `G`. -/
noncomputable def numMaximalSubgroupClasses : ℕ :=
  ((fun H : Subgroup G => MulAction.orbit (ConjAct G) H) '' {H : Subgroup G | IsCoatom H}).ncard

/-- The largest degree of an irreducible complex character of `G`: the largest dimension of a
simple finite-dimensional complex representation of `G`. -/
noncomputable def maxCharacterDegree : ℕ :=
  sSup {d : ℕ | ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ Module.finrank ℂ V = d}

end Group
