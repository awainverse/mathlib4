/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Basics on First-Order Languages and Structures

This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions

- A `FirstOrder.Language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
- A `FirstOrder.Language.Structure` interprets the symbols of a given `FirstOrder.Language` in the
  context of a given type.
- A language `IsRelational` when it lacks function symbols, and `IsAlgebraic` when it lacks
  relations.
- If `L` is a language, `L.Symbols` consists of all function and relation symbols of all arities.
  Its cardinality is `L.card`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/

@[expose] public section

universe u v u' v' w w'

open Cardinal

namespace FirstOrder

-- intended to be used with explicit universe parameters
/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
@[nolint checkUnivs]
structure Language where
  /-- For every arity, a `Type*` of functions of that arity -/
  Functions : ℕ → Type u
  /-- For every arity, a `Type*` of relations of that arity -/
  Relations : ℕ → Type v

namespace Language

variable (L : Language.{u, v})

/-- A language is relational when it has no function symbols. -/
abbrev IsRelational : Prop := ∀ n, IsEmpty (L.Functions n)

/-- A language is algebraic when it has no relation symbols. -/
abbrev IsAlgebraic : Prop := ∀ n, IsEmpty (L.Relations n)

/-- The type of constants in a given language. -/
protected abbrev Constants :=
  L.Functions 0

/-- The type of symbols in a given language. -/
abbrev Symbols :=
  (Σ l, L.Functions l) ⊕ (Σ l, L.Relations l)

/-- The cardinality of a language is the cardinality of its type of symbols. -/
def card : Cardinal :=
  #L.Symbols

variable {L} {L' : Language.{u', v'}}

theorem card_eq_card_functions_add_card_relations :
    L.card =
      (Cardinal.sum fun l => Cardinal.lift.{v} #(L.Functions l)) +
        Cardinal.sum fun l => Cardinal.lift.{u} #(L.Relations l) := by
  simp only [card, mk_sum, mk_sigma, lift_sum]

instance Countable.countable_functions [h : Countable L.Symbols] : Countable (Σ l, L.Functions l) :=
  @Function.Injective.countable _ _ h _ Sum.inl_injective

/-- Passes a `DecidableEq` instance on a type of function symbols through the  `Language`
constructor. Despite the fact that this is proven by `inferInstance`, it is still needed -
see the `example`s in `ModelTheory/Ring/Basic`. -/
instance instDecidableEqFunctions {f : ℕ → Type*} {R : ℕ → Type*} (n : ℕ) [DecidableEq (f n)] :
    DecidableEq ((⟨f, R⟩ : Language).Functions n) := inferInstance

/-- Passes a `DecidableEq` instance on a type of relation symbols through the  `Language`
constructor. Despite the fact that this is proven by `inferInstance`, it is still needed -
see the `example`s in `ModelTheory/Ring/Basic`. -/
instance instDecidableEqRelations {f : ℕ → Type*} {R : ℕ → Type*} (n : ℕ) [DecidableEq (R n)] :
    DecidableEq ((⟨f, R⟩ : Language).Relations n) := inferInstance

variable (L) (M : Type w)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(Fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
@[ext]
class Structure where
  /-- Interpretation of the function symbols -/
  funMap : ∀ {n}, L.Functions n → (Fin n → M) → M := by
    exact fun {n} => isEmptyElim
  /-- Interpretation of the relation symbols -/
  RelMap : ∀ {n}, L.Relations n → (Fin n → M) → Prop := by
    exact fun {n} => isEmptyElim

/-- Used for defining `FirstOrder.Language.Theory.ModelType.instInhabited`. -/
def Inhabited.trivialStructure {α : Type*} [Inhabited α] : L.Structure α :=
  ⟨default, default⟩

open Structure

variable {L M} [L.Structure M]

/-- Interpretation of a constant symbol -/
@[coe]
def constantMap (c : L.Constants) : M := funMap c default

instance : CoeTC L.Constants M :=
  ⟨constantMap⟩

theorem funMap_eq_coe_constants {c : L.Constants} {x : Fin 0 → M} : funMap c x = c :=
  congr rfl (funext finZeroElim)

/-- Given a language with a nonempty type of constants, any structure will be nonempty. This cannot
  be a global instance, because `L` becomes a metavariable. -/
theorem nonempty_of_nonempty_constants [h : Nonempty L.Constants] : Nonempty M :=
  h.map (↑)

end Language

end FirstOrder
