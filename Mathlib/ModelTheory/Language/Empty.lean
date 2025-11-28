/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Maps.Basic

/-!
# The Empty Language

This file defines the empty first-order language, with no function or relation symbols.

## Main Definitions

- `FirstOrder.Language.empty` is the empty first-order language, with no function or relation
  symbols. Any type can be made into a structure in this language in a unique way,
  given by `FirstOrder.Language.emptyStructure`.

-/

@[expose] public section

universe u v w u' v' w'

open Cardinal

variable {M : Type w} {N : Type w'}

namespace FirstOrder.Language

/-- The empty language has no symbols. -/
protected def empty : Language := ⟨fun _ => Empty, fun _ => Empty⟩
  deriving IsAlgebraic, IsRelational

instance : Inhabited Language :=
  ⟨Language.empty⟩

@[simp]
theorem card_empty : Language.empty.card = 0 := by simp only [card, mk_sum, mk_sigma, mk_eq_zero,
  sum_const, mk_eq_aleph0, lift_id', mul_zero, add_zero]

instance isEmpty_empty : IsEmpty Language.empty.Symbols := by
  simp only [Language.Symbols, isEmpty_sum, isEmpty_sigma]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/-- Any type can be made uniquely into a structure over the empty language. -/
def emptyStructure : Language.empty.Structure M where

instance : Unique (Language.empty.Structure M) :=
  ⟨⟨Language.emptyStructure⟩, fun a => by
    ext _ f <;> exact Empty.elim f⟩

variable [Language.empty.Structure M] [Language.empty.Structure N]

instance (priority := 100) strongHomClassEmpty {F} [FunLike F M N] :
    StrongHomClass Language.empty F M N :=
  ⟨fun _ _ f => Empty.elim f, fun _ _ r => Empty.elim r⟩

@[simp]
theorem empty.nonempty_embedding_iff :
    Nonempty (M ↪[Language.empty] N) ↔ Cardinal.lift.{w'} #M ≤ Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEmbedding, Nonempty.map StrongHomClass.toEmbedding⟩
    Cardinal.lift_mk_le'.symm

@[simp]
theorem empty.nonempty_equiv_iff :
    Nonempty (M ≃[Language.empty] N) ↔ Cardinal.lift.{w'} #M = Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEquiv, Nonempty.map fun f => { toEquiv := f }⟩
    Cardinal.lift_mk_eq'.symm

/-- Makes a `Language.empty.Hom` out of any function.
This is only needed because there is no instance of `FunLike (M → N) M N`, and thus no instance of
`Language.empty.HomClass M N`. -/
@[simps]
def _root_.Function.emptyHom (f : M → N) : M →[Language.empty] N where toFun := f

end FirstOrder.Language

open FirstOrder
