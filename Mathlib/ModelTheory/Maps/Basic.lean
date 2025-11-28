/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Language.Basic

/-!
# First-Order Maps

This file defines homomorphisms, embeddings, and equivalences (isomorphisms) between first-order
structures.

## Main Definitions

- A `FirstOrder.Language.Hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
- A `FirstOrder.Language.Embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
- A `FirstOrder.Language.Equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.

-/

@[expose] public section

universe u v u' v' w w'

open Cardinal

namespace FirstOrder

namespace Language

open Structure

variable (L : Language.{u, v}) (M : Type w) (N : Type w') [L.Structure M] [L.Structure N]

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
structure Hom where
  /-- The underlying function of a homomorphism of structures -/
  toFun : M → N
  /-- The homomorphism commutes with the interpretations of the function symbols -/
  -- Porting note:
  -- The autoparam here used to be `obviously`. We would like to replace it with `aesop`
  -- but that isn't currently sufficient.
  -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
  -- If that can be improved, we should change this to `by aesop` and remove the proofs below.
  map_fun' : ∀ {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    intros; trivial
  /-- The homomorphism sends related elements to related elements -/
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r x → RelMap r (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " →[" L "] " B => FirstOrder.Language.Hom L A B

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
structure Embedding extends M ↪ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ↪[" L "] " B => FirstOrder.Language.Embedding L A B

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
structure Equiv extends M ≃ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ≃[" L "] " B => FirstOrder.Language.Equiv L A B

variable {L M N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]

/-- `HomClass L F M N` states that `F` is a type of `L`-homomorphisms. You should extend this
  typeclass when you extend `FirstOrder.Language.Hom`. -/
class HomClass (L : outParam Language) (F : Type*) (M N : outParam Type*)
  [FunLike F M N] [L.Structure M] [L.Structure N] : Prop where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r x → RelMap r (φ ∘ x)

/-- `StrongHomClass L F M N` states that `F` is a type of `L`-homomorphisms which preserve
  relations in both directions. -/
class StrongHomClass (L : outParam Language) (F : Type*) (M N : outParam Type*)
  [FunLike F M N] [L.Structure M] [L.Structure N] : Prop where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r (φ ∘ x) ↔ RelMap r x

instance (priority := 100) StrongHomClass.homClass {F : Type*} [L.Structure M]
    [L.Structure N] [FunLike F M N] [StrongHomClass L F M N] : HomClass L F M N where
  map_fun := StrongHomClass.map_fun
  map_rel φ _ R x := (StrongHomClass.map_rel φ R x).2

/-- Not an instance to avoid a loop. -/
theorem HomClass.strongHomClassOfIsAlgebraic [L.IsAlgebraic] {F M N} [L.Structure M] [L.Structure N]
    [FunLike F M N] [HomClass L F M N] : StrongHomClass L F M N where
  map_fun := HomClass.map_fun
  map_rel _ _ := isEmptyElim

theorem HomClass.map_constants {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [HomClass L F M N] (φ : F) (c : L.Constants) : φ c = c :=
  (HomClass.map_fun φ c default).trans (congr rfl (funext default))

attribute [inherit_doc FirstOrder.Language.Hom.map_fun'] FirstOrder.Language.Embedding.map_fun'
  FirstOrder.Language.HomClass.map_fun FirstOrder.Language.StrongHomClass.map_fun
  FirstOrder.Language.Equiv.map_fun'

attribute [inherit_doc FirstOrder.Language.Hom.map_rel'] FirstOrder.Language.Embedding.map_rel'
  FirstOrder.Language.HomClass.map_rel FirstOrder.Language.StrongHomClass.map_rel
  FirstOrder.Language.Equiv.map_rel'

namespace Hom

instance instFunLike : FunLike (M →[L] N) M N where
  coe := Hom.toFun
  coe_injective' f g h := by cases f; cases g; cases h; rfl

instance homClass : HomClass L (M →[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

instance [L.IsAlgebraic] : StrongHomClass L (M →[L] N) M N :=
  HomClass.strongHomClassOfIsAlgebraic

@[simp]
theorem toFun_eq_coe {f : M →[L] N} : f.toFun = (f : M → N) :=
  rfl

@[ext]
theorem ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem map_fun (φ : M →[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
theorem map_constants (φ : M →[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
theorem map_rel (φ : M →[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r x → RelMap r (φ ∘ x) :=
  HomClass.map_rel φ r x

variable (L) (M)

/-- The identity map from a structure to itself. -/
@[refl]
def id : M →[L] M where
  toFun m := m

variable {L} {M}

instance : Inhabited (M →[L] M) :=
  ⟨id L M⟩

@[simp]
theorem id_apply (x : M) : id L M x = x :=
  rfl

/-- Composition of first-order homomorphisms. -/
@[trans]
def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P where
  toFun := hnp ∘ hmn
  -- Porting note: should be done by autoparam?
  map_fun' _ _ := by simp; rfl
  -- Porting note: should be done by autoparam?
  map_rel' _ _ h := map_rel _ _ _ (map_rel _ _ _ h)

@[simp]
theorem comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_id (f : M →[L] N) : f.comp (id L M) = f :=
  rfl

@[simp]
theorem id_comp (f : M →[L] N) : (id L N).comp f = f :=
  rfl

end Hom

/-- Any element of a `HomClass` can be realized as a first_order homomorphism. -/
@[simps] def HomClass.toHom {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [HomClass L F M N] : F → M →[L] N := fun φ =>
  ⟨φ, HomClass.map_fun φ, HomClass.map_rel φ⟩

namespace Embedding

instance funLike : FunLike (M ↪[L] N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    ext x
    exact funext_iff.1 h x

instance embeddingLike : EmbeddingLike (M ↪[L] N) M N where
  injective' f := f.toEmbedding.injective

instance strongHomClass : StrongHomClass L (M ↪[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

@[simp]
theorem map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
theorem map_constants (φ : M ↪[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
theorem map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- A first-order embedding is also a first-order homomorphism. -/
def toHom : (M ↪[L] N) → M →[L] N :=
  HomClass.toHom

@[simp]
theorem coe_toHom {f : M ↪[L] N} : (f.toHom : M → N) = f :=
  rfl

theorem coe_injective : @Function.Injective (M ↪[L] N) (M → N) (↑)
  | f, g, h => by
    cases f
    cases g
    congr
    ext x
    exact funext_iff.1 h x

@[ext]
theorem ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem toHom_injective : @Function.Injective (M ↪[L] N) (M →[L] N) (·.toHom) := by
  intro f f' h
  ext
  exact congr_fun (congr_arg (↑) h) _

@[simp]
theorem toHom_inj {f g : M ↪[L] N} : f.toHom = g.toHom ↔ f = g :=
  ⟨fun h ↦ toHom_injective h, fun h ↦ congr_arg (·.toHom) h⟩

theorem injective (f : M ↪[L] N) : Function.Injective f :=
  f.toEmbedding.injective

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps!]
def ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : M ↪[L] N :=
  { f with
    inj' := hf
    map_rel' := fun {_} r x => StrongHomClass.map_rel f r x }

@[simp]
theorem coeFn_ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) :
    (ofInjective hf : M → N) = f :=
  rfl

@[simp]
theorem ofInjective_toHom [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) :
    (ofInjective hf).toHom = f := by
  ext; simp

variable (L) (M)

/-- The identity embedding from a structure to itself. -/
@[refl]
def refl : M ↪[L] M where toEmbedding := Function.Embedding.refl M

variable {L} {M}

instance : Inhabited (M ↪[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of first-order embeddings. -/
@[trans]
def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where
  toFun := hnp ∘ hmn
  inj' := hnp.injective.comp hmn.injective
  -- Porting note: should be done by autoparam?
  map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
  -- Porting note: should be done by autoparam?
  map_rel' := by intros; rw [Function.comp_assoc, map_rel, map_rel]

@[simp]
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order embeddings is associative. -/
theorem comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

theorem comp_injective (h : N ↪[L] P) :
    Function.Injective (h.comp : (M ↪[L] N) →  (M ↪[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]
theorem comp_inj (h : N ↪[L] P) (f g : M ↪[L] N) : h.comp f = h.comp g ↔ f = g :=
  ⟨fun eq ↦ h.comp_injective eq, congr_arg h.comp⟩

theorem toHom_comp_injective (h : N ↪[L] P) :
    Function.Injective (h.toHom.comp : (M →[L] N) →  (M →[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]
theorem toHom_comp_inj (h : N ↪[L] P) (f g : M →[L] N) : h.toHom.comp f = h.toHom.comp g ↔ f = g :=
  ⟨fun eq ↦ h.toHom_comp_injective eq, congr_arg h.toHom.comp⟩

@[simp]
theorem comp_toHom (hnp : N ↪[L] P) (hmn : M ↪[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl

@[simp]
theorem comp_refl (f : M ↪[L] N) : f.comp (refl L M) = f := DFunLike.coe_injective rfl

@[simp]
theorem refl_comp (f : M ↪[L] N) : (refl L N).comp f = f := DFunLike.coe_injective rfl

@[simp]
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

end Embedding

/-- Any element of an injective `StrongHomClass` can be realized as a first_order embedding. -/
@[simps] def StrongHomClass.toEmbedding {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [EmbeddingLike F M N] [StrongHomClass L F M N] : F → M ↪[L] N := fun φ =>
  ⟨⟨φ, EmbeddingLike.injective φ⟩, StrongHomClass.map_fun φ, StrongHomClass.map_rel φ⟩

namespace Equiv

instance : EquivLike (M ≃[L] N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    simp only [mk.injEq]
    ext x
    exact funext_iff.1 h₁ x

instance : StrongHomClass L (M ≃[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm]
def symm (f : M ≃[L] N) : N ≃[L] M :=
  { f.toEquiv.symm with
    map_fun' := fun n f' {x} => by
      simp only [Equiv.toFun_as_coe]
      rw [Equiv.symm_apply_eq]
      refine Eq.trans ?_ (f.map_fun' f' (f.toEquiv.symm ∘ x)).symm
      rw [← Function.comp_assoc, Equiv.toFun_as_coe, Equiv.self_comp_symm, Function.id_comp]
    map_rel' := fun n r {x} => by
      simp only [Equiv.toFun_as_coe]
      refine (f.map_rel' r (f.toEquiv.symm ∘ x)).symm.trans ?_
      rw [← Function.comp_assoc, Equiv.toFun_as_coe, Equiv.self_comp_symm, Function.id_comp] }

@[simp]
theorem symm_symm (f : M ≃[L] N) :
    f.symm.symm = f :=
  rfl

theorem symm_bijective : Function.Bijective (symm : (M ≃[L] N) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a :=
  f.toEquiv.apply_symm_apply a

@[simp]
theorem symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a :=
  f.toEquiv.symm_apply_apply a

@[simp]
theorem map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
theorem map_constants (φ : M ≃[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
theorem map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- A first-order equivalence is also a first-order embedding. -/
def toEmbedding : (M ≃[L] N) → M ↪[L] N :=
  StrongHomClass.toEmbedding

/-- A first-order equivalence is also a first-order homomorphism. -/
def toHom : (M ≃[L] N) → M →[L] N :=
  HomClass.toHom

@[simp]
theorem toEmbedding_toHom (f : M ≃[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
theorem coe_toHom {f : M ≃[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl

@[simp]
theorem coe_toEmbedding (f : M ≃[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl

theorem injective_toEmbedding : Function.Injective (toEmbedding : (M ≃[L] N) → M ↪[L] N) := by
  intro _ _ h; apply DFunLike.coe_injective; exact congr_arg (DFunLike.coe ∘ Embedding.toHom) h

theorem coe_injective : @Function.Injective (M ≃[L] N) (M → N) (↑) :=
  DFunLike.coe_injective

@[ext]
theorem ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem bijective (f : M ≃[L] N) : Function.Bijective f :=
  EquivLike.bijective f

theorem injective (f : M ≃[L] N) : Function.Injective f :=
  EquivLike.injective f

theorem surjective (f : M ≃[L] N) : Function.Surjective f :=
  EquivLike.surjective f

variable (L) (M)

/-- The identity equivalence from a structure to itself. -/
@[refl]
def refl : M ≃[L] M where toEquiv := _root_.Equiv.refl M

variable {L} {M}

instance : Inhabited (M ≃[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x := by simp [refl]; rfl

/-- Composition of first-order equivalences. -/
@[trans]
def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
  { hmn.toEquiv.trans hnp.toEquiv with
    toFun := hnp ∘ hmn
    -- Porting note: should be done by autoparam?
    map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
    -- Porting note: should be done by autoparam?
    map_rel' := by intros; rw [Function.comp_assoc, map_rel, map_rel] }

@[simp]
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem comp_refl (g : M ≃[L] N) : g.comp (refl L M) = g :=
  rfl

@[simp]
theorem refl_comp (g : M ≃[L] N) : (refl L N).comp g = g :=
  rfl

@[simp]
theorem refl_toEmbedding : (refl L M).toEmbedding = Embedding.refl L M :=
  rfl

@[simp]
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

theorem injective_comp (h : N ≃[L] P) :
    Function.Injective (h.comp : (M ≃[L] N) →  (M ≃[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (congr_fun (congr_arg DFunLike.coe hfg) x)

@[simp]
theorem comp_toHom (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl

@[simp]
theorem comp_toEmbedding (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toEmbedding = hnp.toEmbedding.comp hmn.toEmbedding :=
  rfl

@[simp]
theorem self_comp_symm (f : M ≃[L] N) : f.comp f.symm = refl L N := by
  ext; rw [comp_apply, apply_symm_apply, refl_apply]

@[simp]
theorem symm_comp_self (f : M ≃[L] N) : f.symm.comp f = refl L M := by
  ext; rw [comp_apply, symm_apply_apply, refl_apply]

@[simp]
theorem symm_comp_self_toEmbedding (f : M ≃[L] N) :
    f.symm.toEmbedding.comp f.toEmbedding = Embedding.refl L M := by
  rw [← comp_toEmbedding, symm_comp_self, refl_toEmbedding]

@[simp]
theorem self_comp_symm_toEmbedding (f : M ≃[L] N) :
    f.toEmbedding.comp f.symm.toEmbedding = Embedding.refl L N := by
  rw [← comp_toEmbedding, self_comp_symm, refl_toEmbedding]

@[simp]
theorem symm_comp_self_toHom (f : M ≃[L] N) :
    f.symm.toHom.comp f.toHom = Hom.id L M := by
  rw [← comp_toHom, symm_comp_self, refl_toHom]

@[simp]
theorem self_comp_symm_toHom (f : M ≃[L] N) :
    f.toHom.comp f.symm.toHom = Hom.id L N := by
  rw [← comp_toHom, self_comp_symm, refl_toHom]

@[simp]
theorem comp_symm (f : M ≃[L] N) (g : N ≃[L] P) : (g.comp f).symm = f.symm.comp g.symm :=
  rfl

theorem comp_right_injective (h : M ≃[L] N) :
    Function.Injective (fun f ↦ f.comp h : (N ≃[L] P) → (M ≃[L] P)) := by
  intro f g hfg
  convert (congr_arg (fun r : (M ≃[L] P) ↦ r.comp h.symm) hfg) <;>
    rw [comp_assoc, self_comp_symm, comp_refl]

@[simp]
theorem comp_right_inj (h : M ≃[L] N) (f g : N ≃[L] P) : f.comp h = g.comp h ↔ f = g :=
  ⟨fun eq ↦ h.comp_right_injective eq, congr_arg (fun (r : N ≃[L] P) ↦ r.comp h)⟩

end Equiv

/-- Any element of a bijective `StrongHomClass` can be realized as a first_order isomorphism. -/
@[simps] def StrongHomClass.toEquiv {F M N} [L.Structure M] [L.Structure N] [EquivLike F M N]
    [StrongHomClass L F M N] : F → M ≃[L] N := fun φ =>
  ⟨⟨φ, EquivLike.inv φ, EquivLike.left_inv φ, EquivLike.right_inv φ⟩, StrongHomClass.map_fun φ,
    StrongHomClass.map_rel φ⟩

end FirstOrder.Language

namespace Equiv

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {L : Language} {M : Type*} {N : Type*} [L.Structure M]

/-- A structure induced by a bijection. -/
@[simps!]
def inducedStructure (e : M ≃ N) : L.Structure N :=
  ⟨fun f x => e (funMap f (e.symm ∘ x)), fun r x => RelMap r (e.symm ∘ x)⟩

/-- A bijection as a first-order isomorphism with the induced structure on the codomain. -/
def inducedStructureEquiv (e : M ≃ N) : @Language.Equiv L M N _ (inducedStructure e) := by
  letI : L.Structure N := inducedStructure e
  exact
  { e with
    map_fun' := @fun n f x => by simp [← Function.comp_assoc e.symm e x]
    map_rel' := @fun n r x => by simp [← Function.comp_assoc e.symm e x] }

@[simp]
theorem toEquiv_inducedStructureEquiv (e : M ≃ N) :
    @Language.Equiv.toEquiv L M N _ (inducedStructure e) (inducedStructureEquiv e) = e :=
  rfl

@[simp]
theorem toFun_inducedStructureEquiv (e : M ≃ N) :
    DFunLike.coe (@inducedStructureEquiv L M N _ e) = e :=
  rfl

@[simp]
theorem toFun_inducedStructureEquiv_Symm (e : M ≃ N) :
    (by
    letI : L.Structure N := inducedStructure e
    exact DFunLike.coe (@inducedStructureEquiv L M N _ e).symm) = (e.symm : N → M) :=
  rfl

end Equiv
