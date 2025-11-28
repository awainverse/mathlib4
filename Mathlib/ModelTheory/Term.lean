/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.ModelTheory.Language.Constants
public import Mathlib.ModelTheory.Maps.Basic

/-!
# First-Order Terms

This file defines first-order terms in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions

- A `FirstOrder.Language.Term` is defined so that `L.Term α` is the type of `L`-terms with free
  variables indexed by `α`.
- The variables of terms can be relabelled with `FirstOrder.Language.Term.relabel`.
- `FirstOrder.Language.Term.subst` substitutes variables with given terms.
- `FirstOrder.Language.Term.substFunc` instead substitutes function definitions with given terms.
- Language maps can act on terms with `FirstOrder.Language.LHom.onTerm`.
- `FirstOrder.Language.Term.constantsVarsEquiv` switches terms between having constants in the
  language and having extra free variables indexed by the same type.
- `FirstOrder.Language.Term.realize` is defined so that `t.realize v` is the term `t` evaluated at
  variables `v`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/

@[expose] public section


universe u v w u' v'

namespace FirstOrder.Language

variable (L : Language.{u, v}) {L' : Language}
variable {M : Type w} {N : Type*} [L.Structure M] [L.Structure N]
variable {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder

open Structure Fin

/-- A term on `α` is either a variable indexed by an element of `α` or a function symbol applied to
simpler terms. -/
inductive Term (α : Type u') : Type max u u'
  | var : α → Term α
  | func : ∀ {l : ℕ} (_f : L.Functions l) (_ts : Fin l → Term α), Term α
export Term (var func)

variable {L}

namespace Term

instance instDecidableEq [DecidableEq α] [∀ n, DecidableEq (L.Functions n)] : DecidableEq (L.Term α)
  | .var a, .var b => decidable_of_iff (a = b) <| by simp
  | @Term.func _ _ m f xs, @Term.func _ _ n g ys =>
      if h : m = n then
        letI : DecidableEq (L.Term α) := instDecidableEq
        decidable_of_iff (f = h ▸ g ∧ ∀ i : Fin m, xs i = ys (Fin.cast h i)) <| by
          subst h
          simp [funext_iff]
      else
        .isFalse <| by simp [h]
  | .var _, .func _ _ | .func _ _, .var _ => .isFalse <| by simp

open Finset

/-- The `Finset` of variables used in a given term. -/
@[simp]
def varFinset [DecidableEq α] : L.Term α → Finset α
  | var i => {i}
  | func _f ts => univ.biUnion fun i => (ts i).varFinset

/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeft [DecidableEq α] : L.Term (α ⊕ β) → Finset α
  | var (Sum.inl i) => {i}
  | var (Sum.inr _i) => ∅
  | func _f ts => univ.biUnion fun i => (ts i).varFinsetLeft

/-- Relabels a term's variables along a particular function. -/
@[simp]
def relabel (g : α → β) : L.Term α → L.Term β
  | var i => var (g i)
  | func f ts => func f fun {i} => (ts i).relabel g

theorem relabel_id (t : L.Term α) : t.relabel id = t := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]
theorem relabel_id_eq_id : (Term.relabel id : L.Term α → L.Term α) = id :=
  funext relabel_id

@[simp]
theorem relabel_relabel (f : α → β) (g : β → γ) (t : L.Term α) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]
theorem relabel_comp_relabel (f : α → β) (g : β → γ) :
    (Term.relabel g ∘ Term.relabel f : L.Term α → L.Term γ) = Term.relabel (g ∘ f) :=
  funext (relabel_relabel f g)

/-- Relabels a term's variables along a bijection. -/
@[simps]
def relabelEquiv (g : α ≃ β) : L.Term α ≃ L.Term β :=
  ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩

/-- Restricts a term to use only a set of the given variables. -/
def restrictVar [DecidableEq α] : ∀ (t : L.Term α) (_f : t.varFinset → β), L.Term β
  | var a, f => var (f ⟨a, mem_singleton_self a⟩)
  | func F ts, f =>
    func F fun i => (ts i).restrictVar (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => varFinset (ts i)) (mem_univ i)))

/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrictVarLeft [DecidableEq α] {γ : Type*} :
    ∀ (t : L.Term (α ⊕ γ)) (_f : t.varFinsetLeft → β), L.Term (β ⊕ γ)
  | var (Sum.inl a), f => var (Sum.inl (f ⟨a, mem_singleton_self a⟩))
  | var (Sum.inr a), _f => var (Sum.inr a)
  | func F ts, f =>
    func F fun i =>
      (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_biUnion_of_mem
        (fun i => varFinsetLeft (ts i)) (mem_univ i)))

end Term

/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants) : L.Term α :=
  func c default

/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions 1) (t : L.Term α) : L.Term α :=
  func f ![t]

/-- Applies a binary function to two terms. -/
def Functions.apply₂ (f : L.Functions 2) (t₁ t₂ : L.Term α) : L.Term α :=
  func f ![t₁, t₂]

/-- The representation of a function symbol as a term, on fresh variables indexed by Fin. -/
def Functions.term {n : ℕ} (f : L.Functions n) : L.Term (Fin n) :=
  func f Term.var

namespace Term

/-- Sends a term with constants to a term with extra variables. -/
@[simp]
def constantsToVars : L[[γ]].Term α → L.Term (γ ⊕ α)
  | var a => var (Sum.inr a)
  | @func _ _ 0 f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => var (Sum.inl c)
  | @func _ _ (_n + 1) f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => isEmptyElim c

/-- Sends a term with extra variables to a term with constants. -/
@[simp]
def varsToConstants : L.Term (γ ⊕ α) → L[[γ]].Term α
  | var (Sum.inr a) => var a
  | var (Sum.inl c) => Constants.term (Sum.inr c)
  | func f ts => func (Sum.inl f) fun i => (ts i).varsToConstants

/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
def constantsVarsEquiv : L[[γ]].Term α ≃ L.Term (γ ⊕ α) :=
  ⟨constantsToVars, varsToConstants, by
    intro t
    induction t with
    | var => rfl
    | @func n f _ ih =>
      cases n
      · cases f
        · simp [constantsToVars, varsToConstants, ih]
        · simp [constantsToVars, varsToConstants, Constants.term, eq_iff_true_of_subsingleton]
      · obtain - | f := f
        · simp [constantsToVars, varsToConstants, ih]
        · exact isEmptyElim f, by
    intro t
    induction t with
    | var x => cases x <;> rfl
    | @func n f _ ih => cases n <;> · simp [varsToConstants, constantsToVars, ih]⟩

/-- A bijection between terms with constants and terms with extra variables. -/
def constantsVarsEquivLeft : L[[γ]].Term (α ⊕ β) ≃ L.Term ((γ ⊕ α) ⊕ β) :=
  constantsVarsEquiv.trans (relabelEquiv (Equiv.sumAssoc _ _ _)).symm

@[simp]
theorem constantsVarsEquivLeft_apply (t : L[[γ]].Term (α ⊕ β)) :
    constantsVarsEquivLeft t = (constantsToVars t).relabel (Equiv.sumAssoc _ _ _).symm :=
  rfl

@[simp]
theorem constantsVarsEquivLeft_symm_apply (t : L.Term ((γ ⊕ α) ⊕ β)) :
    constantsVarsEquivLeft.symm t = varsToConstants (t.relabel (Equiv.sumAssoc _ _ _)) :=
  rfl

instance inhabitedOfVar [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩

instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term α) :=
  ⟨(default : L.Constants).term⟩

/-- Raises all of the `Fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def liftAt {n : ℕ} (n' m : ℕ) : L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin (n + n'))) :=
  relabel (Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')

/-- Substitutes the variables in a given term with terms. -/
@[simp]
def subst : L.Term α → (α → L.Term β) → L.Term β
  | var a, tf => tf a
  | func f ts, tf => func f fun i => (ts i).subst tf

/-- Substitutes the functions in a given term with expressions. -/
@[simp]
def substFunc : L.Term α → (∀ {n : ℕ}, L.Functions n → L'.Term (Fin n)) → L'.Term α
  | var a, _ => var a
  | func f ts, tf => (tf f).subst fun i ↦ (ts i).substFunc tf

@[simp]
theorem substFunc_term (t : L.Term α) : t.substFunc Functions.term = t := by
  induction t
  · rfl
  · simp only [substFunc, Functions.term, subst, ‹∀ _, _›]

end Term

/-- `&n` is notation for the bound variable indexed by `n` in a bounded formula. -/
scoped[FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr

namespace LHom

open Term

/-- Maps a term's symbols along a language map. -/
@[simp]
def onTerm (φ : L →ᴸ L') : L.Term α → L'.Term α
  | var i => var i
  | func f ts => func (φ.onFunction f) fun i => onTerm φ (ts i)

@[simp]
theorem id_onTerm : ((LHom.id L).onTerm : L.Term α → L.Term α) = id := by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

@[simp]
theorem comp_onTerm {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α → L''.Term α) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

end LHom

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
def LEquiv.onTerm (φ : L ≃ᴸ L') : L.Term α ≃ L'.Term α where
  toFun := φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onTerm, φ.left_inv, LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onTerm, φ.right_inv, LHom.id_onTerm]


open Structure Fin

namespace Term

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
def realize (v : α → M) : ∀ _t : L.Term α, M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).realize v

@[simp]
theorem realize_var (v : α → M) (k) : realize v (var k : L.Term α) = v k := rfl

@[simp]
theorem realize_func (v : α → M) {n} (f : L.Functions n) (ts) :
    realize v (func f ts : L.Term α) = funMap f fun i => (ts i).realize v := rfl

@[simp]
theorem realize_function_term {n} (v : Fin n → M) (f : L.Functions n) :
    f.term.realize v = funMap f v := by
  rfl

@[simp]
theorem realize_relabel {t : L.Term α} {g : α → β} {v : β → M} :
    (t.relabel g).realize v = t.realize (v ∘ g) := by
  induction t with
  | var => rfl
  | func f ts ih => simp [ih]

@[simp]
theorem realize_liftAt {n n' m : ℕ} {t : L.Term (α ⊕ (Fin n))} {v : α ⊕ (Fin (n + n')) → M} :
    (t.liftAt n' m).realize v =
      t.realize (v ∘ Sum.map id fun i : Fin _ =>
        if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') :=
  realize_relabel

@[simp]
theorem realize_constants {c : L.Constants} {v : α → M} : c.term.realize v = c :=
  funMap_eq_coe_constants

@[simp]
theorem realize_functions_apply₁ {f : L.Functions 1} {t : L.Term α} {v : α → M} :
    (f.apply₁ t).realize v = funMap f ![t.realize v] := by
  rw [Functions.apply₁, Term.realize]
  refine congr rfl (funext fun i => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
theorem realize_functions_apply₂ {f : L.Functions 2} {t₁ t₂ : L.Term α} {v : α → M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ![t₁.realize v, t₂.realize v] := by
  rw [Functions.apply₂, Term.realize]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

theorem realize_con {A : Set M} {a : A} {v : α → M} : (L.con a).term.realize v = a :=
  rfl

@[simp]
theorem realize_subst {t : L.Term α} {tf : α → L.Term β} {v : β → M} :
    (t.subst tf).realize v = t.realize fun a => (tf a).realize v := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

theorem realize_restrictVar [DecidableEq α] {t : L.Term α} {f : t.varFinset → β}
    {v : β → M} (v' : α → M) (hv' : ∀ a, v (f a) = v' a) :
    (t.restrictVar f).realize v = t.realize v' := by
  induction t with
  | var => simp [restrictVar, hv']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i ((by simp [Function.comp_apply, hv'])))

/-- A special case of `realize_restrictVar`, included because we can add the `simp` attribute
to it -/
@[simp]
theorem realize_restrictVar' [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset ⊆ s)
    {v : α → M} : (t.restrictVar (Set.inclusion h)).realize (v ∘ (↑)) = t.realize v :=
  realize_restrictVar _ (by simp)

theorem realize_restrictVarLeft [DecidableEq α] {γ : Type*} {t : L.Term (α ⊕ γ)}
    {f : t.varFinsetLeft → β}
    {xs : β ⊕ γ → M} (xs' : α → M) (hxs' : ∀ a, xs (Sum.inl (f a)) = xs' a) :
    (t.restrictVarLeft f).realize xs = t.realize (Sum.elim xs' (xs ∘ Sum.inr)) := by
  induction t with
  | var a => cases a <;> simp [restrictVarLeft, hxs']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i (by simp [hxs']))

/-- A special case of `realize_restrictVarLeft`, included because we can add the `simp` attribute
to it -/
@[simp]
theorem realize_restrictVarLeft' [DecidableEq α] {γ : Type*} {t : L.Term (α ⊕ γ)} {s : Set α}
    (h : ↑t.varFinsetLeft ⊆ s) {v : α → M} {xs : γ → M} :
    (t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ (↑)) xs) =
      t.realize (Sum.elim v xs) :=
  realize_restrictVarLeft _ (by simp)

@[simp]
theorem realize_constantsToVars [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L[[α]].Term β} {v : β → M} :
    t.constantsToVars.realize (Sum.elim (fun a => ↑(L.con a)) v) = t.realize v := by
  induction t with
  | var => simp
  | @func n f ts ih =>
    cases n
    · cases f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · simp only [realize, constantsToVars, Sum.elim_inl, funMap_eq_coe_constants]
        rfl
    · obtain - | f := f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · exact isEmptyElim f

@[simp]
theorem realize_varsToConstants [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L.Term (α ⊕ β)} {v : β → M} :
    t.varsToConstants.realize v = t.realize (Sum.elim (fun a => ↑(L.con a)) v) := by
  induction t with
  | var ab => rcases ab with a | b <;> simp [Language.con]
  | func f ts ih =>
    simp only [realize, constantsOn, constantsOnFunc, ih, varsToConstants]
    -- Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sumInl]

theorem realize_constantsVarsEquivLeft [L[[α]].Structure M]
    [(lhomWithConstants L α).IsExpansionOn M] {n} {t : L[[α]].Term (β ⊕ (Fin n))} {v : β → M}
    {xs : Fin n → M} :
    (constantsVarsEquivLeft t).realize (Sum.elim (Sum.elim (fun a => ↑(L.con a)) v) xs) =
      t.realize (Sum.elim v xs) := by
  simp only [constantsVarsEquivLeft, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constantsVarsEquiv_apply, relabelEquiv_symm_apply]
  refine _root_.trans ?_ realize_constantsToVars
  congr 1; funext x -- Note: was previously rcongr x
  rcases x with (a | (b | i)) <;> simp

end Term

namespace LHom

@[simp]
theorem realize_onTerm [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
    (v : α → M) : (φ.onTerm t).realize v = t.realize v := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]

end LHom

@[simp]
theorem HomClass.realize_term {F : Type*} [FunLike F M N] [HomClass L F M N]
    (g : F) {t : L.Term α} {v : α → M} :
    t.realize (g ∘ v) = g (t.realize v) := by
  induction t
  · rfl
  · rw [Term.realize, Term.realize, HomClass.map_fun]
    refine congr rfl ?_
    ext x
    simp [*]

end FirstOrder.Language
