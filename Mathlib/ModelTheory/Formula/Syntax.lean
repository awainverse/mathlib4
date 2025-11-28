/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.ModelTheory.Term
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Syntax of First-Order Formulas

This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions

- A `FirstOrder.Language.Formula` is defined so that `L.Formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
- A `FirstOrder.Language.Sentence` is a formula with no free variables.
- The variables of terms and formulas can be relabelled with `FirstOrder.Language.Term.relabel`,
  `FirstOrder.Language.BoundedFormula.relabel`, and `FirstOrder.Language.Formula.relabel`.
- Given an operation on terms and an operation on relations,
  `FirstOrder.Language.BoundedFormula.mapTermRel` gives an operation on formulas.
- `FirstOrder.Language.BoundedFormula.castLE` adds more bound variables.
- `FirstOrder.Language.BoundedFormula.liftAt` raises the indexes of the bound variables above a
  particular index.
- Language maps can act on syntactic objects with functions such as
  `FirstOrder.Language.LHom.onFormula`.
- `FirstOrder.Language.BoundedFormula.constantsVarsEquiv` switches formulas between having
  constants in the language and having extra free variables indexed by the same type.

## Implementation Notes

- `BoundedFormula` uses a locally nameless representation with bound variables as well-scoped de
  Bruijn levels (the variable bounded by the outermost quantifier is indexed by `0`). Specifically,
  a `L.BoundedFormula α n` is a formula with free variables indexed by a type `α`, which cannot be
  quantified over, and bound variables indexed by `Fin n`, which can. For any
  `φ : L.BoundedFormula α (n + 1)`, we define the formula `∀' φ : L.BoundedFormula α n` by
  universally quantifying over the variable indexed by `n : Fin (n + 1)`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/

@[expose] public section


universe u v w u' v'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {L' : Language}
variable {M : Type w} {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder

open Structure Fin

variable (α)

/-- `BoundedFormula α n` is the type of formulas with free variables indexed by `α` and `n` in-scope
bound variables indexed by `Fin n`. -/
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : BoundedFormula n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : BoundedFormula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : BoundedFormula n
  /-- The implication between two bounded formulas. -/
  | imp {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
  /-- The universal quantifier over bounded formulas. -/
  | all {n} (f : BoundedFormula (n + 1)) : BoundedFormula n

/-- `Formula α` is the type of formulas with free variables indexed by `α` and no bound variables in
scope. -/
abbrev Formula :=
  L.BoundedFormula α 0

/-- A sentence is a formula with no free variables. -/
abbrev Sentence :=
  L.Formula Empty

variable {L} {α} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {l : ℕ} (R : L.Relations n) (ts : Fin n → L.Term (α ⊕ (Fin l))) :
    L.BoundedFormula α l :=
  BoundedFormula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations 1) (t : L.Term (α ⊕ (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t]

/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations 2) (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t₁, t₂]

/-- The equality of two terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂

/-- Applies a relation to terms as a formula. -/
def Relations.formula (R : L.Relations n) (ts : Fin n → L.Term α) : L.Formula α :=
  R.boundedFormula fun i => (ts i).relabel Sum.inl

/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations 1) (t : L.Term α) : L.Formula α :=
  r.formula ![t]

/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations 2) (t₁ t₂ : L.Term α) : L.Formula α :=
  r.formula ![t₁, t₂]

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

namespace BoundedFormula

instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩

instance : Bot (L.BoundedFormula α n) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
protected def ex (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  φ.not.all.not

instance : Top (L.BoundedFormula α n) :=
  ⟨BoundedFormula.not ⊥⟩

instance : Min (L.BoundedFormula α n) :=
  ⟨fun f g => (f.imp g.not).not⟩

instance : Max (L.BoundedFormula α n) :=
  ⟨fun f g => f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BoundedFormula α n) :=
  φ.imp ψ ⊓ ψ.imp φ

open Finset

/-- The `Finset` of free variables used in a given formula. -/
@[simp]
def freeVarFinset [DecidableEq α] : ∀ {n}, L.BoundedFormula α n → Finset α
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts => univ.biUnion fun i => (ts i).varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | _n, all f => f.freeVarFinset

/-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
@[simp]
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
  | _m, _n, _h, falsum => falsum
  | _m, _n, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
  | _m, _n, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
  | _m, _n, h, all f => (f.castLE (by gcongr)).all

@[simp]
theorem castLE_rfl {n} (h : n ≤ n) (φ : L.BoundedFormula α n) : φ.castLE h = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp
  | rel => simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => simp [ih3]

@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : L.BoundedFormula α k) :
    (φ.castLE km).castLE mn = φ.castLE (km.trans mn) := by
  revert m n
  induction φ with
  | falsum => intros; rfl
  | equal => simp
  | rel =>
    intros
    simp only [castLE]
    rw [← Function.comp_assoc, Term.relabel_comp_relabel]
    simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => intros; simp only [castLE, ih3]

@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedFormula.castLE mn ∘ BoundedFormula.castLE km :
        L.BoundedFormula α k → L.BoundedFormula α n) =
      BoundedFormula.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)

/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrictFreeVar [DecidableEq α] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (_f : φ.freeVarFinset → β), L.BoundedFormula β n
  | _n, falsum, _f => falsum
  | _n, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft (f ∘ Set.inclusion subset_union_left))
      (t₂.restrictVarLeft (f ∘ Set.inclusion subset_union_right))
  | _n, rel R ts, f =>
    rel R fun i => (ts i).restrictVarLeft (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => Term.varFinsetLeft (ts i)) (mem_univ i)))
  | _n, imp φ₁ φ₂, f =>
    (φ₁.restrictFreeVar (f ∘ Set.inclusion subset_union_left)).imp
      (φ₂.restrictFreeVar (f ∘ Set.inclusion subset_union_right))
  | _n, all φ, f => (φ.restrictFreeVar f).all

/-- Places universal quantifiers on all in-scope bound variables of a bounded formula. -/
def alls : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.all.alls

/-- Places existential quantifiers on all in-scope bound variables of a bounded formula. -/
def exs : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

/-- Maps bounded formulas along a map of terms and a map of relations. -/
def mapTermRel {g : ℕ → ℕ} (ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin (g n))))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1)) :
    ∀ {n}, L.BoundedFormula α n → L'.BoundedFormula β (g n)
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => equal (ft _ t₁) (ft _ t₂)
  | _n, rel R ts => rel (fr _ R) fun i => ft _ (ts i)
  | _n, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr h).imp (φ₂.mapTermRel ft fr h)
  | n, all φ => (h n (φ.mapTermRel ft fr h)).all

/-- Raises all of the bound variables of a formula greater than or equal to `m` by `n'`. -/
def liftAt : ∀ {n : ℕ} (n' _m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n + n') :=
  fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

@[simp]
theorem mapTermRel_mapTermRel {L'' : Language}
    (ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (ft' : ∀ n, L'.Term (β ⊕ Fin n) → L''.Term (γ ⊕ (Fin n)))
    (fr' : ∀ n, L'.Relations n → L''.Relations n) {n} (φ : L.BoundedFormula α n) :
    ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) =
      φ.mapTermRel (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

@[simp]
theorem mapTermRel_id_id_id {n} (φ : L.BoundedFormula α n) :
    (φ.mapTermRel (fun _ => id) (fun _ => id) fun _ => id) = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps]
def mapTermRelEquiv (ft : ∀ n, L.Term (α ⊕ (Fin n)) ≃ L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormula α n ≃ L'.BoundedFormula β n :=
  ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → β ⊕ (Fin n)) (k : ℕ) : α ⊕ (Fin k) → β ⊕ (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]
theorem sumElim_comp_relabelAux {m : ℕ} {g : α → β ⊕ (Fin n)} {v : β → M}
    {xs : Fin (n + m) → M} : Sum.elim v xs ∘ relabelAux g m =
    Sum.elim (Sum.elim v (xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n) := by
  ext x
  rcases x with x | x
  · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    rcases g x with l | r <;> simp
  · simp [BoundedFormula.relabelAux]

@[simp]
theorem relabelAux_sumInl (k : ℕ) :
    relabelAux (Sum.inl : α → α ⊕ (Fin n)) k = Sum.map id (natAdd n) := by
  ext x
  cases x <;> · simp [relabelAux]

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) : L.BoundedFormula β (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

/-- Relabels a bounded formula's free variables along a bijection. -/
def relabelEquiv (g : α ≃ β) {k} : L.BoundedFormula α k ≃ L.BoundedFormula β k :=
  mapTermRelEquiv (fun _n => Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
    fun _n => _root_.Equiv.refl _

@[simp]
theorem relabel_falsum (g : α → β ⊕ (Fin n)) {k} :
    (falsum : L.BoundedFormula α k).relabel g = falsum :=
  rfl

@[simp]
theorem relabel_bot (g : α → β ⊕ (Fin n)) {k} : (⊥ : L.BoundedFormula α k).relabel g = ⊥ :=
  rfl

@[simp]
theorem relabel_imp (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl

@[simp]
theorem relabel_not (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) :
    φ.not.relabel g = (φ.relabel g).not := by simp [BoundedFormula.not]

@[simp]
theorem relabel_all (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabel g = (φ.relabel g).all := by
  rw [relabel, mapTermRel, relabel]
  simp

@[simp]
theorem relabel_ex (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabel g = (φ.relabel g).ex := by simp [BoundedFormula.ex]

@[simp]
theorem relabel_sumInl (φ : L.BoundedFormula α n) :
    (φ.relabel Sum.inl : L.BoundedFormula α (0 + n)) = φ.castLE (ge_of_eq (zero_add n)) := by
  simp only [relabel, relabelAux_sumInl]
  induction φ with
  | falsum => rfl
  | equal => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]
  | rel => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]; rfl
  | imp _ _ ih1 ih2 => simp_all [mapTermRel]
  | all _ ih3 => simp_all [mapTermRel]

/-- Substitutes the free variables in a bounded formula with terms, leaving bound variables
unchanged. -/
def subst {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.Term β) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id

/-- A bijection sending formulas with constants to formulas with extra free variables. -/
def constantsVarsEquiv : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (γ ⊕ α) n :=
  mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _

/-- Turns all the in-scope bound variables into free variables. -/
@[simp]
def toFormula : ∀ {n : ℕ}, L.BoundedFormula α n → L.Formula (α ⊕ (Fin n))
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => t₁.equal t₂
  | _n, rel R ts => R.formula ts
  | _n, imp φ₁ φ₂ => φ₁.toFormula.imp φ₂.toFormula
  | _n, all φ =>
    (φ.toFormula.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))).all

/-- Take the disjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iSup [Finite β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊔ ·) ⊥

/-- Take the conjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iInf [Finite β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊓ ·) ⊤

end BoundedFormula

namespace LHom

open BoundedFormula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
def onBoundedFormula (g : L →ᴸ L') : ∀ {k : ℕ}, L.BoundedFormula α k → L'.BoundedFormula α k
  | _k, falsum => falsum
  | _k, equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | _k, rel R ts => (g.onRelation R).boundedFormula (g.onTerm ∘ ts)
  | _k, imp f₁ f₂ => (onBoundedFormula g f₁).imp (onBoundedFormula g f₂)
  | _k, all f => (onBoundedFormula g f).all

@[simp]
theorem id_onBoundedFormula :
    ((LHom.id L).onBoundedFormula : L.BoundedFormula α n → L.BoundedFormula α n) = id := by
  ext f
  induction f with
  | falsum => rfl
  | equal => rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  | rel => rw [onBoundedFormula, LHom.id_onTerm]; rfl
  | imp _ _ ih1 ih2 => rw [onBoundedFormula, ih1, ih2, id, id, id]
  | all _ ih3 => rw [onBoundedFormula, ih3, id, id]

@[simp]
theorem comp_onBoundedFormula {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α n → L''.BoundedFormula α n) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula := by
  ext f
  induction f with
  | falsum => rfl
  | equal => simp [Term.bdEqual]
  | rel => simp only [onBoundedFormula, comp_onRelation, comp_onTerm, Function.comp_apply]; rfl
  | imp _ _ ih1 ih2 =>
    simp only [onBoundedFormula, Function.comp_apply, ih1, ih2]
  | all _ ih3 => simp only [ih3, onBoundedFormula, Function.comp_apply]

/-- Maps a formula's symbols along a language map. -/
def onFormula (g : L →ᴸ L') : L.Formula α → L'.Formula α :=
  g.onBoundedFormula

/-- Maps a sentence's symbols along a language map. -/
def onSentence (g : L →ᴸ L') : L.Sentence → L'.Sentence :=
  g.onFormula

end LHom

namespace LEquiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps]
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α n ≃ L'.BoundedFormula α n where
  toFun := φ.toLHom.onBoundedFormula
  invFun := φ.invLHom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.left_inv,
      LHom.id_onBoundedFormula]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.right_inv,
      LHom.id_onBoundedFormula]

theorem onBoundedFormula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α n ≃ L.BoundedFormula α n) =
      φ.symm.onBoundedFormula :=
  rfl

/-- Maps a formula's symbols along a language equivalence. -/
def onFormula (φ : L ≃ᴸ L') : L.Formula α ≃ L'.Formula α :=
  φ.onBoundedFormula

@[simp]
theorem onFormula_apply (φ : L ≃ᴸ L') :
    (φ.onFormula : L.Formula α → L'.Formula α) = φ.toLHom.onFormula :=
  rfl

@[simp]
theorem onFormula_symm (φ : L ≃ᴸ L') :
    (φ.onFormula.symm : L'.Formula α ≃ L.Formula α) = φ.symm.onFormula :=
  rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps!]
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula

end LEquiv

@[inherit_doc] scoped[FirstOrder] infixl:88 " =' " => FirstOrder.Language.Term.bdEqual
-- input \~- or \simeq

@[inherit_doc] scoped[FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.BoundedFormula.imp
-- input \==>

@[inherit_doc] scoped[FirstOrder] prefix:110 "∀' " => FirstOrder.Language.BoundedFormula.all

@[inherit_doc] scoped[FirstOrder] prefix:arg "∼" => FirstOrder.Language.BoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.BoundedFormula.iff
-- input \<=>

@[inherit_doc] scoped[FirstOrder] prefix:110 "∃' " => FirstOrder.Language.BoundedFormula.ex
-- input \ex

namespace Formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.Formula α → L.Formula β :=
  @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0

/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions n) : L.Formula (Fin (n + 1)) :=
  Term.equal (var 0) (func f fun i => var i.succ)

/-- The negation of a formula. -/
protected nonrec abbrev not (φ : L.Formula α) : L.Formula α :=
  φ.not

/-- The implication between formulas, as a formula. -/
protected abbrev imp : L.Formula α → L.Formula α → L.Formula α :=
  BoundedFormula.imp

variable (β) in
/-- `iAlls f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by universally
quantifying over all variables `Sum.inr _`. -/
noncomputable def iAlls [Finite β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).alls

variable (β) in
/-- `iExs f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _`. -/
noncomputable def iExs [Finite β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).exs

variable (β) in
/-- `iExsUnique f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _` and asserting that the solution should be unique -/
noncomputable def iExsUnique [Finite β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  iExs β <| φ ⊓ iAlls β
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInf fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

/-- The biimplication between formulas, as a formula. -/
protected nonrec abbrev iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.iff ψ

/-- Take the disjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iSup [Finite α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iSup f

/-- Take the conjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iInf [Finite α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iInf f

/-- A bijection sending formulas to sentences with constants. -/
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm

theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence φ).not :=
  rfl

theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=
  rfl

end Formula

end Language

end FirstOrder
