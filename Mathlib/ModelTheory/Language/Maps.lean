/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.ModelTheory.Language.Basic

/-!
# Language Maps

Maps between first-order languages in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions

- A `FirstOrder.Language.LHom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
- A `FirstOrder.Language.LEquiv`, denoted `L ≃ᴸ L'`, is an invertible language homomorphism.
- `FirstOrder.Language.withConstants` is defined so that if `M` is an `L.Structure` and
  `A : Set M`, `L.withConstants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]

-/

@[expose] public section

universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

/-- A language homomorphism maps the symbols of one language to symbols of another. -/
structure LHom where
  /-- The mapping of functions -/
  onFunction : ∀ ⦃n⦄, L.Functions n → L'.Functions n := by
    exact fun {n} => isEmptyElim
  /-- The mapping of relations -/
  onRelation : ∀ ⦃n⦄, L.Relations n → L'.Relations n :=by
    exact fun {n} => isEmptyElim

@[inherit_doc FirstOrder.Language.LHom]
infixl:10 " →ᴸ " => LHom

-- \^L
variable {L L'}

namespace LHom

variable (ϕ : L →ᴸ L')

/-- Pulls a structure back along a language map. -/
def reduct (M : Type*) [L'.Structure M] : L.Structure M where
  funMap f xs := funMap (ϕ.onFunction f) xs
  RelMap r xs := RelMap (ϕ.onRelation r) xs

/-- The identity language homomorphism. -/
@[simps]
protected def id (L : Language) : L →ᴸ L :=
  ⟨fun _n => id, fun _n => id⟩

instance : Inhabited (L →ᴸ L) :=
  ⟨LHom.id L⟩

variable (L L')

/-- The inclusion of an empty language into any other language. -/
@[simps]
protected def ofIsEmpty [L.IsAlgebraic] [L.IsRelational] : L →ᴸ L' where

variable {L L'} {L'' : Language}

@[ext]
protected theorem funext {F G : L →ᴸ L'} (h_fun : F.onFunction = G.onFunction)
    (h_rel : F.onRelation = G.onRelation) : F = G := by
  obtain ⟨Ff, Fr⟩ := F
  obtain ⟨Gf, Gr⟩ := G
  simp only [mk.injEq]
  exact And.intro h_fun h_rel

instance [L.IsAlgebraic] [L.IsRelational] : Unique (L →ᴸ L') :=
  ⟨⟨LHom.ofIsEmpty L L'⟩, fun _ => LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- The composition of two language homomorphisms. -/
@[simps]
def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
  ⟨fun _n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩

-- added ᴸ to avoid clash with function composition
@[inherit_doc]
infixl:60 " ∘ᴸ " => LHom.comp

@[simp]
theorem id_comp (F : L →ᴸ L') : LHom.id L' ∘ᴸ F = F := by
  cases F
  rfl

@[simp]
theorem comp_id (F : L →ᴸ L') : F ∘ᴸ LHom.id L = F := by
  cases F
  rfl

theorem comp_assoc {L3 : Language} (F : L'' →ᴸ L3) (G : L' →ᴸ L'') (H : L →ᴸ L') :
    F ∘ᴸ G ∘ᴸ H = F ∘ᴸ (G ∘ᴸ H) :=
  rfl

/-- A language homomorphism is injective when all the maps between symbol types are. -/
protected structure Injective : Prop where
  onFunction {n} : Function.Injective fun f : L.Functions n => onFunction ϕ f
  onRelation {n} : Function.Injective fun R : L.Relations n => onRelation ϕ R

/-- Pulls an `L`-structure along a language map `ϕ : L →ᴸ L'`, and then expands it
  to an `L'`-structure arbitrarily. -/
noncomputable def defaultExpansion (ϕ : L →ᴸ L')
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => onFunction ϕ f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => onRelation ϕ r)]
    (M : Type*) [Inhabited M] [L.Structure M] : L'.Structure M where
  funMap {n} f xs :=
    if h' : f ∈ Set.range fun f : L.Functions n => onFunction ϕ f then funMap h'.choose xs
    else default
  RelMap {n} r xs :=
    if h' : r ∈ Set.range fun r : L.Relations n => onRelation ϕ r then RelMap h'.choose xs
    else default

/-- A language homomorphism is an expansion on a structure if it commutes with the interpretation of
all symbols on that structure. -/
class IsExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] : Prop where
  map_onFunction :
    ∀ {n} (f : L.Functions n) (x : Fin n → M), funMap (ϕ.onFunction f) x = funMap f x := by
      exact fun {n} => isEmptyElim
  map_onRelation :
    ∀ {n} (R : L.Relations n) (x : Fin n → M), RelMap (ϕ.onRelation R) x = RelMap R x := by
      exact fun {n} => isEmptyElim

@[simp]
theorem map_onFunction {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (f : L.Functions n) (x : Fin n → M) : funMap (ϕ.onFunction f) x = funMap f x :=
  IsExpansionOn.map_onFunction f x

@[simp]
theorem map_onRelation {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (R : L.Relations n) (x : Fin n → M) : RelMap (ϕ.onRelation R) x = RelMap R x :=
  IsExpansionOn.map_onRelation R x

instance id_isExpansionOn (M : Type*) [L.Structure M] : IsExpansionOn (LHom.id L) M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

instance ofIsEmpty_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] [L.IsAlgebraic]
    [L.IsRelational] : IsExpansionOn (LHom.ofIsEmpty L L') M where

instance (priority := 100) isExpansionOn_reduct (ϕ : L →ᴸ L') (M : Type*) [L'.Structure M] :
    @IsExpansionOn L L' ϕ M (ϕ.reduct M) _ :=
  letI := ϕ.reduct M
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

theorem Injective.isExpansionOn_default {ϕ : L →ᴸ L'}
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => ϕ.onFunction f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => ϕ.onRelation r)]
    (h : ϕ.Injective) (M : Type*) [Inhabited M] [L.Structure M] :
    @IsExpansionOn L L' ϕ M _ (ϕ.defaultExpansion M) := by
  letI := ϕ.defaultExpansion M
  refine ⟨fun {n} f xs => ?_, fun {n} r xs => ?_⟩
  · have hf : ϕ.onFunction f ∈ Set.range fun f : L.Functions n => ϕ.onFunction f := ⟨f, rfl⟩
    refine (dif_pos hf).trans ?_
    rw [h.onFunction hf.choose_spec]
  · have hr : ϕ.onRelation r ∈ Set.range fun r : L.Relations n => ϕ.onRelation r := ⟨r, rfl⟩
    refine (dif_pos hr).trans ?_
    rw [h.onRelation hr.choose_spec]

end LHom

/-- A language equivalence maps the symbols of one language to symbols of another bijectively. -/
structure LEquiv (L L' : Language) where
  /-- The forward language homomorphism -/
  toLHom : L →ᴸ L'
  /-- The inverse language homomorphism -/
  invLHom : L' →ᴸ L
  left_inv : invLHom.comp toLHom = LHom.id L
  right_inv : toLHom.comp invLHom = LHom.id L'

@[inherit_doc] infixl:10 " ≃ᴸ " => LEquiv

-- \^L
namespace LEquiv

variable (L) in
/-- The identity equivalence from a first-order language to itself. -/
@[simps]
protected def refl : L ≃ᴸ L :=
  ⟨LHom.id L, LHom.id L, LHom.comp_id _, LHom.comp_id _⟩

instance : Inhabited (L ≃ᴸ L) :=
  ⟨LEquiv.refl L⟩

variable {L'' : Language} (e' : L' ≃ᴸ L'') (e : L ≃ᴸ L')

/-- The inverse of an equivalence of first-order languages. -/
@[simps]
protected def symm : L' ≃ᴸ L :=
  ⟨e.invLHom, e.toLHom, e.right_inv, e.left_inv⟩

/-- The composition of equivalences of first-order languages. -/
@[simps, trans]
protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
  ⟨e'.toLHom.comp e.toLHom, e.invLHom.comp e'.invLHom, by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e'.invLHom, e'.left_inv, LHom.id_comp, e.left_inv], by
    rw [LHom.comp_assoc, ← LHom.comp_assoc e.toLHom, e.right_inv, LHom.id_comp, e'.right_inv]⟩

end LEquiv

end Language

end FirstOrder
