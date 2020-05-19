/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import ring_theory.localization
import ring_theory.principal_ideal_domain

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R`, `P` the localization of `R` at `S`, and `f` the
natural ring hom from `R` to `P`.
 * `is_fractional` defines which `R`-submodules of `P` are fractional ideals
 * `fractional_ideal f` is the type of fractional ideals in `P`
 * `has_coe (ideal R) (fractional_ideal f)` instance
 * `comm_semiring (fractional_ideal f)` instance:
   the typical ideal operations generalized to fractional ideals
 * `lattice (fractional_ideal f)` instance

Let `K` be the localization of `R` at `R \ {0}` and `g` the natural ring hom from `R` to `K`.
 * `has_div (fractional_ideal g)` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `right_inverse_eq` states that `1 / I` is the inverse of `I` if one exists

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `fractional_ideal` to be the subtype of the predicate `is_fractional`,
instead of having `fractional_ideal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `I.1 + J.1 = (I + J).1` and `⊥.1 = 0.1`.

In `ring_theory.localization`, we define a copy of the localization map `f`'s codomain `P`
(`f.codomain`) so that the `R`-algebra instance on `P` can 'know' the map needed to induce
the `R`-algebra structure.

We don't assume that the localization is a field until we need it to define ideal quotients.
When this assumption is needed, we replace `S` with `non_zero_divisors R`, making the localization
a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

open localization

namespace ring

section defs

variables {R : Type*} [integral_domain R] {S : submonoid R} {P : Type*} [comm_ring P]
  (f : localization S P)

/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def is_fractional (I : submodule R f.codomain) :=
∃ a ≠ (0 : R), ∀ b ∈ I, f.is_integer (f.to_map a * b)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

  More precisely, let `P` be a localization of `R` at some submonoid `S`,
  then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
  such that there is a nonzero `a : R` with `a I ⊆ R`.
-/
def fractional_ideal :=
{I : submodule R f.codomain // is_fractional f I}

end defs

namespace fractional_ideal

open set
open submodule

variables {R : Type*} [integral_domain R] {S : submonoid R} {P : Type*} [comm_ring P]
  {f : localization S P}

instance : has_mem P (fractional_ideal f) := ⟨λ x I, x ∈ I.1⟩

/-- Fractional ideals are equal if their submodules are equal.

  Combined with `submodule.ext` this gives that fractional ideals are equal if
  they have the same elements.
-/
@[ext]
lemma ext {I J : fractional_ideal f} : I.1 = J.1 → I = J :=
subtype.ext.mpr

lemma fractional_of_subset_one (I : submodule R f.codomain)
  (h : I ≤ (submodule.span R {1})) :
  is_fractional f I :=
begin
  use [1, one_ne_zero],
  intros b hb,
  rw [f.to_map.map_one, one_mul],
  rw ←submodule.one_eq_span at h,
  obtain ⟨b', b'_mem, b'_eq_b⟩ := h hb,
  rw (show b = f.to_map b', from b'_eq_b.symm),
  exact set.mem_range_self b',
end

instance coe_to_fractional_ideal : has_coe (ideal R) (fractional_ideal f) :=
⟨ λ I, ⟨↑I, fractional_of_subset_one _ $ λ x ⟨y, hy, h⟩,
  submodule.mem_span_singleton.2 ⟨y, by rw ←h; exact mul_one _⟩⟩ ⟩

@[simp]
lemma val_coe_ideal (I : ideal R) : (I : fractional_ideal f).1 = I := rfl

@[simp]
lemma mem_coe {x : f.codomain} {I : ideal R} :
  x ∈ (I : fractional_ideal f) ↔ ∃ (x' ∈ I), f.to_map x' = x :=
⟨ λ ⟨x', hx', hx⟩, ⟨x', hx', hx⟩,
  λ ⟨x', hx', hx⟩, ⟨x', hx', hx⟩ ⟩

instance : has_zero (fractional_ideal f) := ⟨(0 : ideal R)⟩

@[simp]
lemma mem_zero_iff {x : P} : x ∈ (0 : fractional_ideal f) ↔ x = 0 :=
⟨ (λ ⟨x', x'_mem_zero, x'_eq_x⟩,
    have x'_eq_zero : x' = 0 := x'_mem_zero,
    by simp [x'_eq_x.symm, x'_eq_zero]),
  (λ hx, ⟨0, rfl, by simp [hx]⟩) ⟩

@[simp] lemma val_zero : (0 : fractional_ideal f).1 = 0 :=
submodule.ext $ λ _, mem_zero_iff

lemma nonzero_iff_val_nonzero {I : fractional_ideal f} : I.1 ≠ 0 ↔ I ≠ 0 :=
⟨ λ h h', h (by simp [h']),
  λ h h', h (ext (by simp [h'])) ⟩

instance : inhabited (fractional_ideal f) := ⟨0⟩

instance : has_one (fractional_ideal f) :=
⟨(1 : ideal R)⟩

lemma mem_one_iff {x : P} : x ∈ (1 : fractional_ideal f) ↔ ∃ x' : R, f.to_map x' = x :=
iff.intro (λ ⟨x', _, h⟩, ⟨x', h⟩) (λ ⟨x', h⟩, ⟨x', ⟨x', set.mem_univ _, rfl⟩, h⟩)

lemma coe_mem_one (x : R) : f.to_map x ∈ (1 : fractional_ideal f) :=
mem_one_iff.mpr ⟨x, rfl⟩

lemma one_mem_one : (1 : P) ∈ (1 : fractional_ideal f) :=
mem_one_iff.mpr ⟨1, f.to_map.map_one⟩

@[simp] lemma val_one : (1 : fractional_ideal f).1 = (1 : ideal R) := rfl

section lattice

/-!
### `lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/

instance : partial_order (fractional_ideal f) :=
{ le := λ I J, I.1 ≤ J.1,
  le_refl := λ I, le_refl I.1,
  le_antisymm := λ ⟨I, hI⟩ ⟨J, hJ⟩ hIJ hJI, by { congr, exact le_antisymm hIJ hJI },
  le_trans := λ _ _ _ hIJ hJK, le_trans hIJ hJK }

lemma le_iff {I J : fractional_ideal f} : I ≤ J ↔ (∀ x ∈ I, x ∈ J) := iff.refl _

lemma zero_le (I : fractional_ideal f) : 0 ≤ I :=
begin
  intros x hx,
  convert submodule.zero _,
  simpa using hx
end

instance order_bot : order_bot (fractional_ideal f) :=
{ bot := 0,
  bot_le := zero_le,
  ..fractional_ideal.partial_order }

@[simp] lemma bot_eq_zero : (⊥ : fractional_ideal f) = 0 :=
rfl

lemma eq_zero_iff {I : fractional_ideal f} : I = 0 ↔ (∀ x ∈ I, x = (0 : P)) :=
⟨ (λ h x hx, by simpa [h, mem_zero_iff] using hx),
  (λ h, le_bot_iff.mp (λ x hx, mem_zero_iff.mpr (h x hx))) ⟩

lemma fractional_sup (I J : fractional_ideal f) : is_fractional f (I.1 ⊔ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  rcases J.2 with ⟨aJ, haJ, hJ⟩,
  use aI * aJ,
  use mul_ne_zero haI haJ,
  intros b hb,
  rcases mem_sup.mp hb with
    ⟨bI, hbI, bJ, hbJ, hbIJ⟩,
  rw [←hbIJ, mul_add],
  apply is_integer_add,
  { rw [mul_comm aI, f.to_map.map_mul, mul_assoc],
    apply is_integer_smul (hI bI hbI), },
  { rw [f.to_map.map_mul, mul_assoc],
    apply is_integer_smul (hJ bJ hbJ) }
end

lemma fractional_inf (I J : fractional_ideal f) : is_fractional f (I.1 ⊓ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  use aI,
  use haI,
  intros b hb,
  rcases mem_inf.mp hb with ⟨hbI, hbJ⟩,
  exact (hI b hbI)
end

instance lattice : lattice (fractional_ideal f) :=
{ inf := λ I J, ⟨I.1 ⊓ J.1, fractional_inf I J⟩,
  sup := λ I J, ⟨I.1 ⊔ J.1, fractional_sup I J⟩,
  inf_le_left := λ I J, show I.1 ⊓ J.1 ≤ I.1, from inf_le_left,
  inf_le_right := λ I J, show I.1 ⊓ J.1 ≤ J.1, from inf_le_right,
  le_inf := λ I J K hIJ hIK, show I.1 ≤ (J.1 ⊓ K.1), from le_inf hIJ hIK,
  le_sup_left := λ I J, show I.1 ≤ I.1 ⊔ J.1, from le_sup_left,
  le_sup_right := λ I J, show J.1 ≤ I.1 ⊔ J.1, from le_sup_right,
  sup_le := λ I J K hIK hJK, show (I.1 ⊔ J.1) ≤ K.1, from sup_le hIK hJK,
  ..fractional_ideal.partial_order }

instance : semilattice_sup_bot (fractional_ideal f) :=
{ ..fractional_ideal.order_bot, ..fractional_ideal.lattice }

end lattice

section semiring

instance : has_add (fractional_ideal f) := ⟨(⊔)⟩

@[simp]
lemma sup_eq_add (I J : fractional_ideal f) : I ⊔ J = I + J := rfl

@[simp]
lemma val_add (I J : fractional_ideal f) : (I + J).1 = I.1 + J.1 := rfl

lemma fractional_mul (I J : fractional_ideal f) : is_fractional f (I.1 * J.1) :=
begin
  rcases I with ⟨I, aI, haI, hI⟩,
  rcases J with ⟨I, aJ, haJ, hJ⟩,
  use aI * aJ,
  use mul_ne_zero haI haJ,
  intros b hb,
  apply submodule.mul_induction_on hb,
  { intros m hm n hn,
    obtain ⟨n', hn'⟩ := hJ n hn,
    rw [f.to_map.map_mul, mul_comm m, ←mul_assoc, mul_assoc _ _ n],
    erw ←hn', rw mul_assoc,
    apply hI,
    exact submodule.smul_mem _ _ hm },
  { rw [mul_zero],
    exact ⟨0, f.to_map.map_zero⟩ },
  { intros x y hx hy,
    rw [mul_add],
    apply is_integer_add hx hy },
  { intros r x hx,
    show f.is_integer (_ * (f.to_map r * x)),
    rw [←mul_assoc, ←f.to_map.map_mul, mul_comm _ r, f.to_map.map_mul, mul_assoc],
    apply is_integer_smul hx },
end

instance : has_mul (fractional_ideal f) := ⟨λ I J, ⟨I.1 * J.1, fractional_mul I J⟩⟩

@[simp]
lemma val_mul (I J : fractional_ideal f) : (I * J).1 = I.1 * J.1 := rfl

lemma mul_left_mono (I : fractional_ideal f) : monotone ((*) I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul hx (h hy))

lemma mul_right_mono (I : fractional_ideal f) : monotone (λ J, J * I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul (h hx) hy)

instance add_comm_monoid : add_comm_monoid (fractional_ideal f) :=
{ add_assoc := λ I J K, sup_assoc,
  add_comm := λ I J, sup_comm,
  add_zero := λ I, sup_bot_eq,
  zero_add := λ I, bot_sup_eq,
  ..fractional_ideal.has_zero,
  ..fractional_ideal.has_add }

instance comm_monoid : comm_monoid (fractional_ideal f) :=
{ mul_assoc := λ I J K, ext (submodule.mul_assoc _ _ _),
  mul_comm := λ I J, ext (submodule.mul_comm _ _),
  mul_one := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x hx y ⟨y', y'_mem_R, y'_eq_y⟩,
      erw [←y'_eq_y, mul_comm],
      exact submodule.smul _ _ hx },
    { have : x * 1 ∈ (I * 1) := mul_mem_mul h one_mem_one,
      rwa [mul_one] at this }
  end,
  one_mul := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x ⟨x', x'_mem_R, x'_eq_x⟩ y hy,
      erw [←x'_eq_x],
      exact submodule.smul _ _ hy },
    { have : 1 * x ∈ (1 * I) := mul_mem_mul one_mem_one h,
      rwa [one_mul] at this }
  end,
  ..fractional_ideal.has_mul,
  ..fractional_ideal.has_one }

instance comm_semiring : comm_semiring (fractional_ideal f) :=
{ mul_zero := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hy])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  zero_mul := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hx])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  left_distrib := λ I J K, ext (mul_add _ _ _),
  right_distrib := λ I J K, ext (add_mul _ _ _),
  ..fractional_ideal.add_comm_monoid,
  ..fractional_ideal.comm_monoid }

end semiring

section quotient

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = non_zero_divisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/

open_locale classical

variables {K : Type*} [field K] {g : fraction_map R K}

instance : zero_ne_one_class (fractional_ideal g) :=
{ zero_ne_one := λ h,
  have this : (1 : K) ∈ (0 : fractional_ideal g) :=
    by rw ←g.to_map.map_one; convert coe_mem_one _,
  one_ne_zero (mem_zero_iff.mp this),
  ..fractional_ideal.has_one,
  ..fractional_ideal.has_zero }

lemma fractional_div_of_nonzero {I J : fractional_ideal g} (h : J ≠ 0) :
  is_fractional g (I.1 / J.1) :=
begin
  rcases I with ⟨I, aI, haI, hI⟩,
  rcases J with ⟨J, aJ, haJ, hJ⟩,
  obtain ⟨y, mem_J, not_mem_zero⟩ := exists_of_lt (bot_lt_iff_ne_bot.mpr h),
  obtain ⟨y', hy'⟩ := hJ y mem_J,
  use (aI * y'),
  split,
  { apply mul_ne_zero haI,
    intro y'_eq_zero,
    have : g.to_map aJ * y = 0 := by rw [←hy', y'_eq_zero, g.to_map.map_zero],
    obtain aJ_zero | y_zero := mul_eq_zero.mp this,
    { have : aJ = 0 := g.to_map.injective_iff.1 g.injective _ aJ_zero,
      contradiction },
    { exact not_mem_zero (mem_zero_iff.mpr y_zero) } },
  intros b hb,
  rw [g.to_map.map_mul, mul_assoc, mul_comm _ b, hy'],
  exact hI _ (hb _ (submodule.smul_mem _ aJ mem_J)),
end

noncomputable instance fractional_ideal_has_div :
  has_div (fractional_ideal g) :=
⟨ λ I J, if h : J = 0 then 0 else ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ ⟩

noncomputable instance : has_inv (fractional_ideal g) := ⟨λ I, 1 / I⟩

lemma div_nonzero {I J : fractional_ideal g} (h : J ≠ 0) :
  (I / J) = ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ :=
dif_neg h

lemma inv_nonzero {I : fractional_ideal g} (h : I ≠ 0) :
  I⁻¹ = ⟨(1 : fractional_ideal g).val / I.1, fractional_div_of_nonzero h⟩ :=
div_nonzero h

lemma val_inv_of_nonzero {I : fractional_ideal g} (h : I ≠ 0) :
  I⁻¹.val = (1 : ideal R) / I.val :=
by { rw inv_nonzero h, refl }

@[simp] lemma div_one {I : fractional_ideal g} : I / 1 = I :=
begin
  rw [div_nonzero (@one_ne_zero (fractional_ideal g) _)],
  ext,
  split; intro h,
  { convert mem_div_iff_forall_mul_mem.mp h 1
      (g.to_map.map_one ▸ coe_mem_one 1), simp },
  { apply mem_div_iff_forall_mul_mem.mpr,
    rintros y ⟨y', _, y_eq_y'⟩,
    rw [mul_comm],
    convert submodule.smul_mem _ y' h,
    rw ←y_eq_y',
    refl }
end

lemma ne_zero_of_mul_eq_one (I J : fractional_ideal g) (h : I * J = 1) : I ≠ 0 :=
λ hI, @zero_ne_one (fractional_ideal g) _ (by { convert h, simp [hI], })

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : fractional_ideal g) (h : I * J = 1) :
  J = I⁻¹ :=
begin
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h,
  suffices h' : I * (1 / I) = 1,
  { exact (congr_arg units.inv $
      @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl) },
  rw [div_nonzero hI],
  apply le_antisymm,
  { apply submodule.mul_le.mpr _,
    intros x hx y hy,
    rw [mul_comm],
    exact mem_div_iff_forall_mul_mem.mp hy x hx },
  rw [←h],
  apply mul_left_mono I,
  apply submodule.le_div_iff.mpr _,
  intros y hy x hx,
  rw [mul_comm],
  exact mul_mem_mul hx hy
end

theorem mul_inv_cancel_iff {I : fractional_ideal g} :
  I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨I⁻¹, h⟩, λ ⟨J, hJ⟩, by rwa [←right_inverse_eq I J hJ]⟩

end quotient

section principal_ideal_domain

open_locale classical

variables {K : Type*} [field K] {g : fraction_map R K}

variables {R' : Type*} [comm_ring R'] [algebra R R']

local attribute [instance] smul_set_action

open algebra

-- TODO: figure out whether we want this instance elsewhere
def submodule_has_scalar : has_scalar R' (submodule R R') :=
⟨ λ x I, { carrier := x • I.carrier,
           add := by { rintros y z ⟨y', hy', rfl⟩ ⟨z', hz', rfl⟩,
                       rw ←smul_add,
                       exact smul_mem_smul_set _ (I.add hy' hz') },
           smul := by { rintros y z ⟨z', hz', rfl⟩,
                        rw [smul_eq_mul, ←algebra.mul_smul_comm],
                        exact smul_mem_smul_set _ (I.smul y hz')},
           zero := by simpa only [smul_zero] using smul_mem_smul_set x I.zero } ⟩

local attribute [instance] submodule_has_scalar

lemma mem_smul_submodule {x y : R'} {I : submodule R R'} :
  x ∈ y • I ↔ ∃ x' ∈ I, x = y * x' :=
mem_smul_set y I.carrier x

@[simp] lemma smul_one_submodule (x : R') :
  (x • (1 : submodule R R')) = span R {x} :=
begin
  ext y,
  refine ((mem_smul_set x _ y).trans ⟨_, _⟩).trans mem_span_singleton.symm;
    simp_rw [smul_eq_mul, mul_comm x],
  { rintros ⟨y', ⟨y', ⟨⟩, rfl⟩, rfl⟩,
    exact ⟨y', smul_def y' x⟩ },
  { rintros ⟨y', rfl⟩,
    exact ⟨of_id R R' y', ⟨y', ⟨⟩, rfl⟩, smul_def y' x⟩ }
end

@[simp] lemma smul_top (x : P) :
  x • (↑(⊤ : ideal R) : submodule R f.codomain) = span R {x} :=
begin
  ext y,
  refine ((mem_smul_set x _ y).trans ⟨_, _⟩).trans mem_span_singleton.symm;
  simp_rw [smul_eq_mul, mul_comm x],
  { rintros ⟨y', ⟨y', ⟨⟩, rfl⟩, rfl⟩,
    exact ⟨y', smul_def y' x⟩ },
  { rintros ⟨y', rfl⟩,
    exact ⟨f.to_map y', ⟨y', ⟨⟩, rfl⟩, smul_def y' x⟩ }
end

lemma span_singleton_mul (x y : R') : (span R {x * y} : submodule R R') = x • span R {y} :=
begin
  ext z,
  rw [mem_smul_submodule, mem_span_singleton],
  split,
  { rintros ⟨a, rfl⟩,
    exact ⟨a • y, mem_span_singleton.mpr ⟨a, rfl⟩, (mul_smul_comm a x y).symm ⟩ },
  { rintros ⟨x', h, rfl⟩,
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp h,
    exact ⟨a, (mul_smul_comm a x y).symm⟩ }
end

lemma fractional_smul (x : K) (I : fractional_ideal g) :
  is_fractional g (x • I.1) :=
begin
  obtain ⟨s, hs⟩ := g.exists_integer_multiple x,
  obtain ⟨t, t_nonzero, ht⟩ := I.2,
  use s * t,
  use mul_ne_zero' (mem_non_zero_divisors_iff_ne_zero.mp s.2) t_nonzero,
  rintros _ ⟨y', hy', rfl⟩,
  convert is_integer_mul hs (ht y' hy') using 1,
  rw [smul_eq_mul, g.to_map.map_mul],
  ac_refl
end

instance : has_scalar K (fractional_ideal g) :=
{ smul := λ x I, ⟨ x • I.val, fractional_smul x I ⟩ }

@[simp] lemma val_smul_ideal (x : K) (I : fractional_ideal g) :
  (x • I).val = x • I.val :=
rfl

@[simp] lemma zero_smul_ideal (I : fractional_ideal g) :
  (0 : K) • I = 0 :=
begin
  ext,
  erw [val_smul_ideal, mem_smul_set, mem_zero_iff],
  simp_rw [zero_smul],
  exact ⟨ λ ⟨_, _, h⟩, h, λ h, ⟨0, I.val.zero, h⟩ ⟩
end

@[simp] lemma one_smul_ideal (I : fractional_ideal g) : (1 : K) • I = I :=
begin
  ext,
  erw [val_smul_ideal, mem_smul_set],
  simp_rw one_smul,
  exact ⟨ λ ⟨_, hy, rfl⟩, hy, λ hx, ⟨x, hx, rfl⟩ ⟩
end

@[simp] lemma mul_smul_ideal (x y : K) (I : fractional_ideal g) :
  (x * y) • I = x • y • I :=
begin
  ext z,
  simp_rw [val_smul_ideal],
  split,
  { rintros ⟨z', hz, rfl⟩,
    rw mul_smul,
    exact smul_mem_smul_set x (smul_mem_smul_set y hz) },
  { rintros ⟨z', ⟨z'', hz, rfl⟩, rfl⟩,
    rw ← mul_smul,
    exact smul_mem_smul_set (x * y) hz }
end

lemma exists_ideal_eq_smul (I : fractional_ideal g) :
  ∃ (a ≠ (0 : R)) (aI : ideal R), ↑aI = g.to_map a • I :=
begin
  obtain ⟨a, nonzero, ha⟩ := I.2,
  use [a, nonzero, (g.to_map a • I).1.comap g.lin_coe],
  ext,
  apply iff.trans mem_coe,
  split,
  { rintros ⟨x', hx', rfl⟩,
    obtain ⟨x'', hx'', hx'⟩ := mem_smul_submodule.mp hx',
    exact ⟨x'', hx'', hx'⟩ },
  { rintros ⟨x, hx, rfl⟩,
    obtain ⟨x', hx'⟩ := ha x hx,
    exact ⟨x', ⟨x, hx, hx'⟩, hx'⟩ }
end

lemma smul_one_mul_smul_one (x y : K) :
  (x • (1 : fractional_ideal g)) * (y • 1) = (x * y) • 1 :=
begin
  ext z,
  simp_rw [val_mul, val_smul_ideal, val_one, ideal.one_eq_top, smul_top, span_mul_span],
  split; refine (λ h, span_mono _ h),
  { exact (λ _ ⟨_, rfl, _, rfl, hxy⟩, hxy) },
  { exact (λ _ hxy, ⟨_, rfl, _, rfl, hxy⟩ ) },
end

open_locale classical

open submodule submodule.is_principal

lemma eq_generator_smul_one_of_principal (I : fractional_ideal g) [is_principal I.1] :
  I = (generator I.1) • 1 :=
ext (by rw [val_smul_ideal, val_one, ideal.one_eq_top, smul_top, span_singleton_generator I.1])

lemma invertible_of_principal (I : fractional_ideal g)
  [submodule.is_principal I.1] (h : I ≠ 0) :
  I * I⁻¹ = 1 :=
begin
  refine mul_inv_cancel_iff.mpr ⟨(generator I.1)⁻¹ • 1, _⟩,
  -- Rewrite only the `I` that appears alone.
  conv_lhs { congr, rw eq_generator_smul_one_of_principal I },
  rw [smul_one_mul_smul_one, mul_inv_cancel, one_smul_ideal],
  intro generator_I_eq_zero,
  apply h,
  rw [eq_generator_smul_one_of_principal I, generator_I_eq_zero, zero_smul_ideal]
end

lemma exists_eq_smul_ideal (I : fractional_ideal g) :
  ∃ (a : K) (aI : ideal R), I = a • aI :=
begin
  obtain ⟨a_inv, nonzero, aI, ha⟩ := exists_ideal_eq_smul I,
  use (g.to_map a_inv)⁻¹,
  use aI,
  rw [ha, ←mul_smul_ideal, inv_mul_cancel, one_smul_ideal],
  exact mt g.to_map_eq_zero_iff.mpr nonzero
end

instance is_principal {R} [principal_ideal_domain R] {g : fraction_map R K}
  (I : fractional_ideal g) : I.val.is_principal :=
⟨ begin
  obtain ⟨a, aI, ha⟩ := exists_eq_smul_ideal I,
  have := a * g.to_map (generator aI),
  use a * g.to_map (generator aI),
  conv_lhs { rw [ha, val_smul_ideal, val_coe_ideal, ←span_singleton_generator aI] },
  rw [span_singleton_mul],
  congr,
  ext,
  split,
  { rintros ⟨x', h, rfl⟩,
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp h,
    refine mem_span_singleton.mpr ⟨a, _⟩,
    exact (g.to_map.map_mul _ _).symm },
  { rintros h,
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp h,
    refine ⟨a * generator aI, mem_span_singleton.mpr ⟨a, rfl⟩, _⟩,
    apply g.to_map.map_mul _ _ },
end⟩

end principal_ideal_domain

end fractional_ideal

end ring
