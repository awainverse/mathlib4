/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.ModelTheory.Formula.Semantics

/-!
# Sentences About Binary Relations

This file defines several first-order sentences pertaining to binary relations.

## Main Definitions

If `r` is a binary relation symbol in a first-order language `L`, then
- `r.reflexive`
- `r.irreflexive`
- `r.symmetric`
- `r.antisymmetric`
- `r.transitive`
- `r.total`
are the sentences indicating that the interpretation of `r` in a given `L.Structure`
satisfies the appropriate property of binary relations.

-/

@[expose] public section

universe u v w u' v'

namespace FirstOrder.Language.Relations

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

open FirstOrder

open Structure Fin

variable (r : L.Relations 2)

/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.Sentence :=
  ∀' r.boundedFormula₂ (&0) &0

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.Sentence :=
  ∀' ∼(r.boundedFormula₂ (&0) &0)

/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.Sentence :=
  ∀' ∀' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.Sentence :=
  ∀' ∀' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)

/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.Sentence :=
  ∀' ∀' ∀' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)

/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.Sentence :=
  ∀' ∀' (r.boundedFormula₂ (&0) &1 ⊔ r.boundedFormula₂ (&1) &0)

open BoundedFormula

variable {r : L.Relations 2}

@[simp]
theorem realize_reflexive : M ⊨ r.reflexive ↔ Reflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => realize_rel₂

@[simp]
theorem realize_irreflexive : M ⊨ r.irreflexive ↔ Irreflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => not_congr realize_rel₂

@[simp]
theorem realize_symmetric : M ⊨ r.symmetric ↔ Symmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr realize_rel₂ realize_rel₂

@[simp]
theorem realize_antisymmetric :
    M ⊨ r.antisymmetric ↔ AntiSymmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ Iff.rfl)

@[simp]
theorem realize_transitive : M ⊨ r.transitive ↔ Transitive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ =>
      forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ realize_rel₂)

@[simp]
theorem realize_total : M ⊨ r.total ↔ Total fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => realize_sup.trans (or_congr realize_rel₂ realize_rel₂)

end FirstOrder.Language.Relations
