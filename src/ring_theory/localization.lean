/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston
-/

import data.equiv.ring
import tactic.ring_exp
import ring_theory.ideal_operations
import group_theory.monoid_localization

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R`, `f x = f y` iff there exists `c ∈ M` such that `x * c = y * c`.

Given such a localization map `f : R →+* S`, we can define the surjection
`localization.mk'` sending `(x, y) : R × M` to `f x * (f y)⁻¹`, and
`localization.lift`, the homomorphism from `S` induced by a homomorphism from `R` which maps
elements of `M` to invertible elements of the codomain. Similarly, given commutative rings
`P, Q`, a submonoid `T` of `P` and a localization map for `T` from `P` to `Q`, then a homomorphism
`g : R →+* P` such that `g(M) ⊆ T` induces a homomorphism of localizations,
`localization.map`, from `S` to `Q`.

We prove some lemmas about the `R`-algebra structure of `S`.

When `R` is an integral domain, we define `fraction_map R K` as an abbreviation for
`localization (non_zero_divisors R) K`, the natural map to `R`'s field of fractions.

We show that a `comm_ring` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A ring localization map is defined to be a localization map of the underlying `comm_monoid` (a
`submonoid.localization_map`) which is also a ring hom. To prove most lemmas about a
`localization` `f` in this file we invoke the corresponding proof for the underlying
`comm_monoid` localization map `f.to_localization_map`, which can be found in
`group_theory.monoid_localization` and the namespace `submonoid.localization_map`.

To apply a localization map `f` as a function, we use `f.to_map`, as coercions don't work well for
this structure.

We use a copy of the localization map `f`'s codomain `S` carrying the data of `f` so that the
`R`-algebra instance on `S` can 'know' the map needed to induce the `R`-algebra structure.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
          {P : Type*} [comm_ring P]

open function

set_option old_structure_cmd true

/-- The type of ring homomorphisms satisfying the characteristic predicate: if `f : R →+* S`
satisfies this predicate, then `S` is isomorphic to the localization of `R` at `M`.
We later define an instance coercing a localization map `f` to its codomain `S` so
that the `R`-algebra instance on `S` can 'know' the map needed to induce the `R`-algebra
structure. -/
@[nolint has_inhabited_instance] structure localization
extends ring_hom R S, submonoid.localization_map M S

/-- The ring hom underlying a `localization`. -/
add_decl_doc localization.to_ring_hom

/-- The `comm_monoid` `localization_map` underlying a `comm_ring` `localization`.
See `group_theory.monoid_localization` for its definition. -/
add_decl_doc localization.to_localization_map

variables {M S}

namespace ring_hom

/-- Makes a localization map from a `comm_ring` hom satisfying the characteristic predicate. -/
def to_localization (f : R →+* S) (H1 : ∀ y : M, is_unit (f y))
  (H2 : ∀ z, ∃ x : R × M, z * f x.2 = f x.1) (H3 : ∀ x y, f x = f y ↔ ∃ c : M, x * c = y * c) :
  localization M S :=
{ map_units' := H1,
  surj' := H2,
  eq_iff_exists' := H3,
  .. f }

end ring_hom

namespace localization

variables (f : localization M S)

/-- Short for `to_ring_hom`; used for applying a localization map as a function. -/
abbreviation to_map := f.to_ring_hom

lemma map_units (y : M) : is_unit (f.to_map y) := f.6 y

lemma surj (z) : ∃ x : R × M, z * f.to_map x.2 = f.to_map x.1 := f.7 z

lemma eq_iff_exists {x y} : f.to_map x = f.to_map y ↔ ∃ c : M, x * c = y * c := f.8 x y

@[ext] lemma ext {f g : localization M S}
  (h : ∀ x, f.to_map x = g.to_map x) : f = g :=
begin
  cases f, cases g,
  simp only [] at *,
  exact funext h
end

lemma ext_iff {f g : localization M S} : f = g ↔ ∀ x, f.to_map x = g.to_map x :=
⟨λ h x, h ▸ rfl, ext⟩

lemma to_map_injective : injective (@localization.to_map _ _ M S _) :=
λ _ _ h, ext $ ring_hom.ext_iff.1 h

/-- Given `a : S`, `S` a localization of `R`, `is_integer a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def is_integer (a : S) : Prop := a ∈ set.range f.to_map

variables {f}

lemma is_integer_add {a b} (ha : f.is_integer a) (hb : f.is_integer b) :
  f.is_integer (a + b) :=
begin
  rcases ha with ⟨a', ha⟩,
  rcases hb with ⟨b', hb⟩,
  use a' + b',
  rw [f.to_map.map_add, ha, hb]
end

lemma is_integer_mul {a b} (ha : f.is_integer a) (hb : f.is_integer b) :
  f.is_integer (a * b) :=
begin
  rcases ha with ⟨a', ha⟩,
  rcases hb with ⟨b', hb⟩,
  use a' * b',
  rw [f.to_map.map_mul, ha, hb]
end

lemma is_integer_smul {a : R} {b} (hb : f.is_integer b) :
  f.is_integer (f.to_map a * b) :=
begin
  rcases hb with ⟨b', hb⟩,
  use a * b',
  rw [←hb, f.to_map.map_mul]
end

variables (f)

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `localization.surj`.
-/
lemma exists_integer_multiple' (a : S) :
  ∃ (b : M), is_integer f (a * f.to_map b) :=
let ⟨⟨num, denom⟩, h⟩ := f.surj a in ⟨denom, set.mem_range.mpr ⟨num, h.symm⟩⟩

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `has_scalar` instance.
-/
lemma exists_integer_multiple (a : S) :
  ∃ (b : M), is_integer f (f.to_map b * a) :=
by { simp_rw mul_comm _ a, apply exists_integer_multiple' }


/-- Given `z : S`, `f.to_localization_map.sec z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
lemma sec_spec {f : localization M S} (z : S) :
  z * f.to_map (f.to_localization_map.sec z).2 = f.to_map (f.to_localization_map.sec z).1 :=
classical.some_spec $ f.surj z

/-- Given `z : S`, `f.to_localization_map.sec z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
lemma sec_spec' {f : localization M S} (z : S) :
  f.to_map (f.to_localization_map.sec z).1 = f.to_map (f.to_localization_map.sec z).2 * z :=
by rw [mul_comm, sec_spec]

lemma map_right_cancel {x y} {c : M} (h : f.to_map (c * x) = f.to_map (c * y)) :
  f.to_map x = f.to_map y :=
f.to_localization_map.map_right_cancel h

lemma map_left_cancel {x y} {c : M} (h : f.to_map (x * c) = f.to_map (y * c)) :
  f.to_map x = f.to_map y :=
f.to_localization_map.map_left_cancel h

lemma eq_zero_of_fst_eq_zero {z x} {y : M}
  (h : z * f.to_map y = f.to_map x) (hx : x = 0) : z = 0 :=
by rw [hx, f.to_map.map_zero] at h;
  exact (is_unit.mul_left_eq_zero_iff_eq_zero (f.map_units y)).1 h

/-- Given a localization map `f : R →+* S`, the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
noncomputable def mk' (f : localization M S) (x : R) (y : M) : S :=
f.to_localization_map.mk' x y

@[simp] lemma mk'_sec (z : S) :
  f.mk' (f.to_localization_map.sec z).1 (f.to_localization_map.sec z).2 = z :=
f.to_localization_map.mk'_sec _

lemma mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) :
  f.mk' (x₁ * x₂) (y₁ * y₂) = f.mk' x₁ y₁ * f.mk' x₂ y₂ :=
f.to_localization_map.mk'_mul _ _ _ _

lemma mk'_one (x) : f.mk' x (1 : M) = f.to_map x :=
f.to_localization_map.mk'_one _

lemma mk'_spec (x) (y : M) :
  f.mk' x y * f.to_map y = f.to_map x :=
f.to_localization_map.mk'_spec _ _

lemma mk'_spec' (x) (y : M) :
  f.to_map y * f.mk' x y = f.to_map x :=
f.to_localization_map.mk'_spec' _ _

theorem eq_mk'_iff_mul_eq {x} {y : M} {z} :
  z = f.mk' x y ↔ z * f.to_map y = f.to_map x :=
f.to_localization_map.eq_mk'_iff_mul_eq

theorem mk'_eq_iff_eq_mul {x} {y : M} {z} :
  f.mk' x y = z ↔ f.to_map x = z * f.to_map y :=
f.to_localization_map.mk'_eq_iff_eq_mul

lemma mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
  f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f.to_map (x₁ * y₂) = f.to_map (x₂ * y₁) :=
f.to_localization_map.mk'_eq_iff_eq

protected lemma eq {a₁ b₁} {a₂ b₂ : M} :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ ∃ c : M, a₁ * b₂ * c = b₁ * a₂ * c :=
f.to_localization_map.eq

lemma eq_iff_eq (g : localization M P) {x y} :
  f.to_map x = f.to_map y ↔ g.to_map x = g.to_map y :=
f.to_localization_map.eq_iff_eq g.to_localization_map

lemma mk'_eq_iff_mk'_eq (g : localization M P) {x₁ x₂}
  {y₁ y₂ : M} : f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ g.mk' x₁ y₁ = g.mk' x₂ y₂ :=
f.to_localization_map.mk'_eq_iff_mk'_eq g.to_localization_map

lemma mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * a₂ = a₁ * b₂) :
  f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
f.to_localization_map.mk'_eq_of_eq H

@[simp] lemma mk'_self {x : R} {hx : x ∈ M} : f.mk' x ⟨x, hx⟩ = 1 :=
f.to_localization_map.mk'_self' _ hx

@[simp] lemma mk'_self' {x : M} : f.mk' x x = 1 :=
f.to_localization_map.mk'_self _

@[simp] lemma mk'_self'' {x : M} : f.mk' x.1 x = 1 :=
f.mk'_self'

lemma mul_mk'_eq_mk'_of_mul (x y : R) (z : M) :
  f.to_map x * f.mk' y z = f.mk' (x * y) z :=
f.to_localization_map.mul_mk'_eq_mk'_of_mul _ _ _

lemma mk'_eq_mul_mk'_one (x : R) (y : M) :
  f.mk' x y = f.to_map x * f.mk' 1 y :=
(f.to_localization_map.mul_mk'_one_eq_mk' _ _).symm

@[simp] lemma mk'_mul_cancel_left (x : R) (y : M) :
  f.mk' (y * x) y = f.to_map x :=
f.to_localization_map.mk'_mul_cancel_left _ _

lemma mk'_mul_cancel_right (x : R) (y : M) :
  f.mk' (x * y) y = f.to_map x :=
f.to_localization_map.mk'_mul_cancel_right _ _

lemma is_unit_comp (j : S →+* P) (y : M) :
  is_unit (j.comp f.to_map y) :=
f.to_localization_map.is_unit_comp j.to_monoid_hom _

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g(M) ⊆ units P`, `f x = f y → g x = g y` for all `x y : R`. -/
lemma eq_of_eq {g : R →+* P} (hg : ∀ y : M, is_unit (g y)) {x y} (h : f.to_map x = f.to_map y) :
  g x = g y :=
@submonoid.localization_map.eq_of_eq _ _ _ _ _ _ _
  f.to_localization_map g.to_monoid_hom hg _ _ h

lemma mk'_add (x₁ x₂ : R) (y₁ y₂ : M) :
  f.mk' (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) = f.mk' x₁ y₁ + f.mk' x₂ y₂ :=
f.mk'_eq_iff_eq_mul.2 $ eq.symm
begin
  rw [mul_comm (_ + _), mul_add, mul_mk'_eq_mk'_of_mul, ←eq_sub_iff_add_eq, mk'_eq_iff_eq_mul,
      mul_comm _ (f.to_map _), mul_sub, eq_sub_iff_add_eq, ←eq_sub_iff_add_eq', ←mul_assoc,
      ←f.to_map.map_mul, mul_mk'_eq_mk'_of_mul, mk'_eq_iff_eq_mul],
  simp only [f.to_map.map_add, submonoid.coe_mul, f.to_map.map_mul],
  ring_exp,
end

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
noncomputable def lift {g : R →+* P} (hg : ∀ y : M, is_unit (g y)) : S →+* P :=
ring_hom.mk' (@submonoid.localization_map.lift _ _ _ _ _ _ _
  f.to_localization_map g.to_monoid_hom hg) $
begin
  intros x y,
  rw [f.to_localization_map.lift_spec, mul_comm, add_mul, ←sub_eq_iff_eq_add, eq_comm,
      f.to_localization_map.lift_spec_mul, mul_comm _ (_ - _), sub_mul, eq_sub_iff_add_eq',
      ←eq_sub_iff_add_eq, mul_assoc, f.to_localization_map.lift_spec_mul],
  show g _ * (g _ * g _) = g _ * (g _ * g _ - g _ * g _),
  repeat {rw ←g.map_mul},
  rw [←g.map_sub, ←g.map_mul],
  apply f.eq_of_eq hg,
  erw [f.to_map.map_mul, sec_spec', mul_sub, f.to_map.map_sub],
  simp only [f.to_map.map_mul, sec_spec'],
  ring_exp,
end

variables {g : R →+* P} (hg : ∀ y : M, is_unit (g y))

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
lemma lift_mk' (x y) :
  f.lift hg (f.mk' x y) = g x * ↑(is_unit.lift_right (g.to_monoid_hom.mrestrict M) hg y)⁻¹ :=
f.to_localization_map.lift_mk' _ _ _

lemma lift_mk'_spec (x v) (y : M) :
  f.lift hg (f.mk' x y) = v ↔ g x = g y * v :=
f.to_localization_map.lift_mk'_spec _ _ _ _

@[simp] lemma lift_eq (x : R) :
  f.lift hg (f.to_map x) = g x :=
f.to_localization_map.lift_eq _ _

lemma lift_eq_iff {x y : R × M} :
  f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
f.to_localization_map.lift_eq_iff _

@[simp] lemma lift_comp : (f.lift hg).comp f.to_map = g :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ f.to_localization_map.lift_comp _

@[simp] lemma lift_of_comp (j : S →+* P) :
  f.lift (f.is_unit_comp j) = j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ f.to_localization_map.lift_of_comp j.to_monoid_hom

lemma epic_of_localization_map {j k : S →+* P}
  (h : ∀ a, j.comp f.to_map a = k.comp f.to_map a) : j = k :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ @submonoid.localization_map.epic_of_localization_map
  _ _ _ _ _ _ _ f.to_localization_map j.to_monoid_hom k.to_monoid_hom h

lemma lift_unique {j : S →+* P}
  (hj : ∀ x, j (f.to_map x) = g x) : f.lift hg = j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ @submonoid.localization_map.lift_unique
  _ _ _ _ _ _ _ f.to_localization_map g.to_monoid_hom hg j.to_monoid_hom hj

@[simp] lemma lift_id (x) : f.lift f.map_units x = x :=
f.to_localization_map.lift_id _

/-- Given two localization maps `f : R →+* S, k : R →+* P` for a submonoid `M ⊆ R`,
the hom from `P` to `S` induced by `f` is left inverse to the hom from `S` to `P`
induced by `k`. -/
@[simp] lemma lift_left_inverse {k : localization M S} (z : S) :
  k.lift f.map_units (f.lift k.map_units z) = z :=
f.to_localization_map.lift_left_inverse _

lemma lift_surjective_iff :
  surjective (f.lift hg) ↔ ∀ v : P, ∃ x : R × M, v * g x.2 = g x.1 :=
f.to_localization_map.lift_surjective_iff hg

lemma lift_injective_iff :
  injective (f.lift hg) ↔ ∀ x y, f.to_map x = f.to_map y ↔ g x = g y :=
f.to_localization_map.lift_injective_iff hg

variables {T : submonoid P} (hy : ∀ y : M, g y ∈ T) {Q : Type*} [comm_ring Q]
          (k : localization T Q)

/-- Given a `comm_ring` homomorphism `g : R →+* P` where for submonoids `M ⊆ R, T ⊆ P` we have
`g(M) ⊆ T`, the induced ring homomorphism from the localization of `R` at `M` to the
localization of `P` at `T`: if `f : R →+* S` and `k : P →+* Q` are localization maps for `M`
and `T` respectively, we send `z : S` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : R × M` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def map : S →+* Q :=
@lift _ _ _ _ _ _ _ f (k.to_map.comp g) $ λ y, k.map_units ⟨g y, hy y⟩

variables {k}

lemma map_eq (x) :
  f.map hy k (f.to_map x) = k.to_map (g x) :=
f.lift_eq (λ y, k.map_units ⟨g y, hy y⟩) x

@[simp] lemma map_comp :
  (f.map hy k).comp f.to_map = k.to_map.comp g :=
f.lift_comp $ λ y, k.map_units ⟨g y, hy y⟩

lemma map_mk' (x) (y : M) :
  f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩ :=
@submonoid.localization_map.map_mk' _ _ _ _ _ _ _ f.to_localization_map
g.to_monoid_hom _ hy _ _ k.to_localization_map _ _

@[simp] lemma map_id (z : S) :
  f.map (λ y, show ring_hom.id R y ∈ M, from y.2) f z = z :=
f.lift_id _

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
lemma map_comp_map {A : Type*} [comm_ring A] {U : submonoid A} {W} [comm_ring W]
  (j : localization U W) {l : P →+* A} (hl : ∀ w : T, l w ∈ U) :
  (k.map hl j).comp (f.map hy k) = f.map (λ x, show l.comp g x ∈ U, from hl ⟨g x, hy x⟩) j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ @submonoid.localization_map.map_comp_map _ _ _ _ _ _ _
  f.to_localization_map g.to_monoid_hom _ hy _ _ k.to_localization_map
    _ _ _ _ _ j.to_localization_map l.to_monoid_hom hl

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
lemma map_map {A : Type*} [comm_ring A] {U : submonoid A} {W} [comm_ring W]
  (j : localization U W) {l : P →+* A} (hl : ∀ w : T, l w ∈ U) (x) :
  k.map hl j (f.map hy k x) = f.map (λ x, show l.comp g x ∈ U, from hl ⟨g x, hy x⟩) j x :=
by rw ←f.map_comp_map hy j hl; refl

/-- Given localization maps `f : R →+* S, k : P →+* Q` for submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
noncomputable def ring_equiv_of_ring_equiv (k : localization T Q) (h : R ≃+* P)
  (H : M.map h.to_monoid_hom = T) :
  S ≃+* Q :=
(f.to_localization_map.mul_equiv_of_mul_equiv k.to_localization_map H).to_ring_equiv $
(@lift _ _ _ _ _ _ _ f (k.to_map.comp h.to_ring_hom)
  (λ y, k.map_units ⟨(h y), H ▸ set.mem_image_of_mem h y.2⟩)).map_add

@[simp] lemma ring_equiv_of_ring_equiv_eq_map_apply {j : R ≃+* P}
  (H : M.map j.to_monoid_hom = T) (x) :
  f.ring_equiv_of_ring_equiv k j H x =
    f.map (λ y : M, show j.to_monoid_hom y ∈ T, from H ▸ set.mem_image_of_mem j y.2) k x := rfl

lemma ring_equiv_of_ring_equiv_eq_map {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) :
  (f.ring_equiv_of_ring_equiv k j H).to_monoid_hom =
    f.map (λ y : M, show j.to_monoid_hom y ∈ T, from H ▸ set.mem_image_of_mem j y.2) k := rfl

@[simp] lemma ring_equiv_of_ring_equiv_eq {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) (x) :
  f.ring_equiv_of_ring_equiv k j H (f.to_map x) = k.to_map (j x) :=
f.to_localization_map.mul_equiv_of_mul_equiv_eq H _

lemma ring_equiv_of_ring_equiv_mk' {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) (x y) :
  f.ring_equiv_of_ring_equiv k j H (f.mk' x y) =
    k.mk' (j x) ⟨j y, H ▸ set.mem_image_of_mem j y.2⟩ :=
f.to_localization_map.mul_equiv_of_mul_equiv_mk' H _ _

/-!
### `algebra` section

Defines the `R`-algebra instance on a copy of `S` carrying the data of the localization map
`f` needed to induce the `R`-algebra structure. -/

variables (f)
/-- We define a copy of the localization map `f`'s codomain `S` carrying the data of `f` so that
    the `R`-algebra instance on `S` can 'know' the map needed to induce the `R`-algebra
    structure. -/
@[reducible, nolint unused_arguments] def codomain (f : localization M S) := S

/-- We use a copy of the localization map `f`'s codomain `S` carrying the data of `f` so that the
    `R`-algebra instance on `S` can 'know' the map needed to induce the `R`-algebra structure. -/
instance : algebra R f.codomain := f.to_map.to_algebra

@[simp] lemma of_id (a : R) :
  (algebra.of_id R f.codomain) a = f.to_map a :=
rfl

variables (f)
/-- Localization map `f` from `R` to `S` as an `R`-linear map. -/
def lin_coe : R →ₗ[R] f.codomain :=
{ to_fun := f.to_map,
  add := f.to_map.map_add,
  smul := f.to_map.map_mul }

variables {f}

instance coe_submodules : has_coe (ideal R) (submodule R f.codomain) :=
⟨λ I, submodule.map f.lin_coe I⟩

lemma mem_coe (I : ideal R) {x : S} :
  x ∈ (I : submodule R f.codomain) ↔ ∃ y : R, y ∈ I ∧ f.to_map y = x :=
iff.rfl

@[simp] lemma lin_coe_apply {x} : f.lin_coe x = f.to_map x := rfl

end localization
variables (R)

/-- The submonoid of non-zero-divisors of a `comm_ring` `R`. -/
def non_zero_divisors : submonoid R :=
{ carrier := {x | ∀ z, z * x = 0 → z = 0},
  one_mem' := λ z hz, by rwa mul_one at hz,
  mul_mem' := λ x₁ x₂ hx₁ hx₂ z hz,
    have z * x₁ * x₂ = 0, by rwa mul_assoc,
    hx₁ z $ hx₂ (z * x₁) this }

lemma eq_zero_of_ne_zero_of_mul_eq_zero {A : Type*} [integral_domain A]
  {x y : A} (hnx : x ≠ 0) (hxy : y * x = 0) :
  y = 0 := or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma mem_non_zero_divisors_iff_ne_zero {A : Type*} [integral_domain A] {x : A} :
  x ∈ non_zero_divisors A ↔ x ≠ 0 :=
⟨λ hm hz, zero_ne_one (hm 1 $ by rw [hz, one_mul]).symm,
 λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx⟩

variables (K : Type*)

/-- Localization map from an integral domain `R` to its field of fractions. -/
@[reducible] def fraction_map [comm_ring K] := localization (non_zero_divisors R) K

namespace fraction_map
open localization
variables {R K}

lemma to_map_eq_zero_iff [comm_ring K] (φ : fraction_map R K) {x : R} :
  x = 0 ↔ φ.to_map x = 0 :=
begin
  rw ← φ.to_map.map_zero,
  split; intro h,
  { rw h },
  { cases φ.eq_iff_exists.mp h with c hc,
    rw zero_mul at hc,
    exact c.2 x hc }
end

protected theorem injective [comm_ring K] (φ : fraction_map R K) :
  injective φ.to_map :=
φ.to_map.injective_iff.2 (λ _ h, φ.to_map_eq_zero_iff.mpr h)

variables {A : Type*} [integral_domain A]

local attribute [instance] classical.dec_eq

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
def to_integral_domain [comm_ring K] (φ : fraction_map A K) : integral_domain K :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    begin
      intros z w h,
      cases φ.surj z with x hx,
      cases φ.surj w with y hy,
      have : z * w * φ.to_map y.2 * φ.to_map x.2 = φ.to_map x.1 * φ.to_map y.1, by
        rw [mul_assoc z, hy, ←hx]; ac_refl,
      erw h at this,
      rw [zero_mul, zero_mul, ←φ.to_map.map_mul] at this,
      cases eq_zero_or_eq_zero_of_mul_eq_zero (φ.to_map_eq_zero_iff.mpr this.symm) with H H,
        { exact or.inl (φ.eq_zero_of_fst_eq_zero hx H) },
      { exact or.inr (φ.eq_zero_of_fst_eq_zero hy H) },
    end,
  zero_ne_one := by erw [←φ.to_map.map_zero, ←φ.to_map.map_one];
    exact λ h, zero_ne_one (φ.injective h),
  ..(infer_instance : comm_ring K) }

/-- The inverse of an element in the field of fractions of an integral domain. -/
protected noncomputable def inv [comm_ring K] (φ : fraction_map A K) (z : K) : K :=
if h : z = 0 then 0 else
φ.mk' (φ.to_localization_map.sec z).2 ⟨(φ.to_localization_map.sec z).1,
  mem_non_zero_divisors_iff_ne_zero.2 $ λ h0, h $ φ.eq_zero_of_fst_eq_zero (sec_spec z) h0⟩

protected lemma mul_inv_cancel [comm_ring K] (φ : fraction_map A K) (x : K) (hx : x ≠ 0) :
  x * φ.inv x = 1 :=
show x * dite _ _ _ = 1, by rw [dif_neg hx,
  ←is_unit.mul_left_inj (φ.map_units ⟨(φ.to_localization_map.sec x).1,
    mem_non_zero_divisors_iff_ne_zero.2 $ λ h0, hx $ φ.eq_zero_of_fst_eq_zero (sec_spec x) h0⟩),
  one_mul, mul_assoc, mk'_spec, ←eq_mk'_iff_mul_eq]; exact (φ.mk'_sec x).symm

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is a
field. -/
noncomputable def to_field [comm_ring K] (φ : fraction_map A K) : field K :=
{ inv := φ.inv,
  mul_inv_cancel := φ.mul_inv_cancel,
  inv_zero := dif_pos rfl, ..φ.to_integral_domain }

end fraction_map
