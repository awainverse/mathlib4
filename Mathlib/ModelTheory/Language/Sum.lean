/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.ModelTheory.Language.Maps

/-!
# Sums of Languages

Sums of first-order languages in the style of the [Flypitch project](https://flypitch.github.io/).

## Main Definitions
- If `L`, `L'` are languages, then `L.sum L'` is the language combining their function and relation
  symbols. Any type that is both an `L`- and `L'`-structure is a `L.sum L'`-structure.


## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]

-/

@[expose] public section

universe u v w u' v' w'

open Cardinal

namespace FirstOrder.Language

variable (L : Language.{u, v}) (L' : Language.{u', v'})

/-- The sum of two languages consists of the disjoint union of their symbols. -/
protected def sum : Language :=
  ⟨fun n => L.Functions n ⊕ L'.Functions n, fun n => L.Relations n ⊕ L'.Relations n⟩

instance isRelational_sum [L.IsRelational] [L'.IsRelational] : IsRelational (L.sum L') :=
  fun _ => instIsEmptySum

instance isAlgebraic_sum [L.IsAlgebraic] [L'.IsAlgebraic] : IsAlgebraic (L.sum L') :=
  fun _ => instIsEmptySum

@[simp]
theorem card_functions_sum (i : ℕ) :
    #((L.sum L').Functions i)
      = (Cardinal.lift.{u'} #(L.Functions i) + Cardinal.lift.{u} #(L'.Functions i) : Cardinal) := by
  simp [Language.sum]

@[simp]
theorem card_relations_sum (i : ℕ) :
    #((L.sum L').Relations i) =
      Cardinal.lift.{v'} #(L.Relations i) + Cardinal.lift.{v} #(L'.Relations i) := by
  simp [Language.sum]

theorem card_sum :
    (L.sum L').card = Cardinal.lift.{max u' v'} L.card + Cardinal.lift.{max u v} L'.card := by
  simp only [card, mk_sum, mk_sigma, card_functions_sum, sum_add_distrib', lift_add, lift_sum,
    lift_lift, card_relations_sum, add_assoc,
    add_comm (Cardinal.sum fun i => (#(L'.Functions i)).lift)]

variable (S : Type*) [L.Structure S] [L'.Structure S]

open Structure

instance sumStructure : (L.sum L').Structure S where
  funMap := Sum.elim funMap funMap
  RelMap := Sum.elim RelMap RelMap

variable {L L' S}

@[simp]
theorem funMap_sumInl {n : ℕ} (f : L.Functions n) :
    @funMap (L.sum L') S _ n (Sum.inl f) = funMap f :=
  rfl

@[simp]
theorem funMap_sumInr {n : ℕ} (f : L'.Functions n) :
    @funMap (L.sum L') S _ n (Sum.inr f) = funMap f :=
  rfl

@[simp]
theorem relMap_sumInl {n : ℕ} (R : L.Relations n) :
    @RelMap (L.sum L') S _ n (Sum.inl R) = RelMap R :=
  rfl

@[simp]
theorem relMap_sumInr {n : ℕ} (R : L'.Relations n) :
    @RelMap (L.sum L') S _ n (Sum.inr R) = RelMap R :=
  rfl

namespace LHom

/-- The inclusion of the left factor into the sum of two languages. -/
@[simps]
protected def sumInl : L →ᴸ L.sum L' :=
  ⟨fun _n => Sum.inl, fun _n => Sum.inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
@[simps]
protected def sumInr : L' →ᴸ L.sum L' :=
  ⟨fun _n => Sum.inr, fun _n => Sum.inr⟩

variable (ϕ : L →ᴸ L')

section SumElim

variable {L'' : Language} (ψ : L'' →ᴸ L')

/-- A language map defined on two factors of a sum. -/
@[simps]
protected def sumElim : L.sum L'' →ᴸ L' where
  onFunction _n := Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

theorem sumElim_comp_inl (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInl = ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

theorem sumElim_comp_inr (ψ : L'' →ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInr = ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

theorem sumElim_inl_inr : LHom.sumInl.sumElim LHom.sumInr = LHom.id (L.sum L') :=
  LHom.funext (funext fun _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)

theorem comp_sumElim {L3 : Language} (θ : L' →ᴸ L3) :
    θ ∘ᴸ ϕ.sumElim ψ = (θ ∘ᴸ ϕ).sumElim (θ ∘ᴸ ψ) :=
  LHom.funext (funext fun _n => Sum.comp_elim _ _ _) (funext fun _n => Sum.comp_elim _ _ _)

end SumElim

section SumMap

variable {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂)

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps]
def sumMap : L.sum L₁ →ᴸ L'.sum L₂ where
  onFunction _n := Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

@[simp]
theorem sumMap_comp_inl : ϕ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

@[simp]
theorem sumMap_comp_inr : ϕ.sumMap ψ ∘ᴸ LHom.sumInr = LHom.sumInr ∘ᴸ ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

end SumMap

section

instance sumElim_isExpansionOn {L'' : Language} (ψ : L'' →ᴸ L') (M : Type*) [L.Structure M]
    [L'.Structure M] [L''.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumElim ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

instance sumMap_isExpansionOn {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂) (M : Type*) [L.Structure M]
    [L'.Structure M] [L₁.Structure M] [L₂.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumMap ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

instance sumInl_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

instance sumInr_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInr : L' →ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

end

variable (M : Type*) [L.Structure M]

@[simp]
theorem funMap_sumInl [(L.sum L').Structure M] [(LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L.sum L') M _ n (Sum.inl f) x = funMap f x :=
  (LHom.sumInl : L →ᴸ L.sum L').map_onFunction f x

@[simp]
theorem funMap_sumInr [(L'.sum L).Structure M] [(LHom.sumInr : L →ᴸ L'.sum L).IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n → M} : @funMap (L'.sum L) M _ n (Sum.inr f) x = funMap f x :=
  (LHom.sumInr : L →ᴸ L'.sum L).map_onFunction f x

theorem sumInl_injective : (LHom.sumInl : L →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inl_injective h, fun h => Sum.inl_injective h⟩

theorem sumInr_injective : (LHom.sumInr : L' →ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inr_injective h, fun h => Sum.inr_injective h⟩

end LHom

end FirstOrder.Language
