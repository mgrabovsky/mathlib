/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
import group_theory.order_of_element
import data.polynomial
import data.equiv.ring
import data.zmod.basic
import linear_algebra.basis
import algebra.geom_sum

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, K denotes a finite field with q elements.

## Main results

1. Every finite integral domain is a field (`field_of_integral_domain`).
2. The unit group of a finite field is a cyclic group of order q - 1.
   (`finite_field.is_cyclic` and `card_units`)
3. `sum_pow_units`: The sum of x^i, where x ranges over the units of K, is
   | q-1 if q-1 ∣ i
   | 0   otherwise
4. `finite_field.card`: The cardinality q is a power of the characteristic of K.
   See `card'` for a variant.
-/

variables {K : Type*} [field K] [fintype K]
variables {R : Type*} [integral_domain R] [fintype R]
local notation `q` := fintype.card K

section

open function finset polynomial nat

variables (S : set (units R)) [is_subgroup S] [fintype S]

lemma card_nth_roots_subgroup_units [decidable_eq R] {n : ℕ} (hn : 0 < n) (a : S) :
  (univ.filter (λ b : S, b ^ n = a)).card ≤ (nth_roots n ((a : units R) : R)).card :=
card_le_card_of_inj_on (λ a, ((a : units R) : R))
  (by simp [mem_nth_roots hn, (units.coe_pow _ _).symm, -units.coe_pow, units.ext_iff.symm, subtype.coe_ext])
  (by simp [units.ext_iff.symm, subtype.coe_ext.symm])

/-- A finite subgroup of the units of an integral domain is cyclic. -/
instance subgroup_units_cyclic : is_cyclic S :=
by haveI := classical.dec_eq R; exact
is_cyclic_of_card_pow_eq_one_le
  (λ n hn, le_trans (card_nth_roots_subgroup_units S hn 1) (card_nth_roots _ _))

end

namespace finite_field
open function finset polynomial

/-- Every finite integral domain is a field. -/
def field_of_integral_domain [fintype R] [decidable_eq R] : field R :=
{ inv := λ a, if h : a = 0 then 0
    else fintype.bij_inv (show function.bijective (* a),
      from fintype.injective_iff_bijective.1 $ λ _ _, (domain.mul_right_inj h).1) 1,
  mul_inv_cancel := λ a ha, show a * dite _ _ _ = _, by rw [dif_neg ha, mul_comm];
    exact fintype.right_inverse_bij_inv (show function.bijective (* a), from _) 1,
  inv_zero := dif_pos rfl,
  ..show integral_domain R, by apply_instance }

section polynomial

open finset polynomial

/-- The cardinality of a field is at most n times the cardinality of the image of a degree n
  polynomial -/
lemma card_image_polynomial_eval [decidable_eq R] {p : polynomial R} (hp : 0 < p.degree) :
  fintype.card R ≤ nat_degree p * (univ.image (λ x, eval x p)).card :=
finset.card_le_mul_card_image _ _
  (λ a _, calc _ = (p - C a).roots.card : congr_arg card
    (by simp [finset.ext, mem_roots_sub_C hp, -sub_eq_add_neg])
    ... ≤ _ : card_roots_sub_C' hp)

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
lemma exists_root_sum_quadratic {f g : polynomial R} (hf2 : degree f = 2)
  (hg2 : degree g = 2) (hR : fintype.card R % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 :=
by letI := classical.dec_eq R; exact
suffices ¬ disjoint (univ.image (λ x : R, eval x f)) (univ.image (λ x : R, eval x (-g))),
begin
  simp only [disjoint_left, mem_image] at this,
  push_neg at this,
  rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩,
  exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_self]⟩
end,
assume hd : disjoint _ _,
lt_irrefl (2 * ((univ.image (λ x : R, eval x f)) ∪ (univ.image (λ x : R, eval x (-g)))).card) $
calc 2 * ((univ.image (λ x : R, eval x f)) ∪ (univ.image (λ x : R, eval x (-g)))).card
    ≤ 2 * fintype.card R : nat.mul_le_mul_left _ (finset.card_le_of_subset (subset_univ _))
... = fintype.card R + fintype.card R : two_mul _
... < nat_degree f * (univ.image (λ x : R, eval x f)).card +
      nat_degree (-g) * (univ.image (λ x : R, eval x (-g))).card :
    add_lt_add_of_lt_of_le
      (lt_of_le_of_ne
        (card_image_polynomial_eval (by rw hf2; exact dec_trivial))
        (mt (congr_arg (%2)) (by simp [nat_degree_eq_of_degree_eq_some hf2, hR])))
      (card_image_polynomial_eval (by rw [degree_neg, hg2]; exact dec_trivial))
... = 2 * (univ.image (λ x : R, eval x f) ∪ univ.image (λ x : R, eval x (-g))).card :
  by rw [card_disjoint_union hd]; simp [nat_degree_eq_of_degree_eq_some hf2,
    nat_degree_eq_of_degree_eq_some hg2, bit0, mul_add]

end polynomial

/-- A finite field of cardinality `q` has a unit group of cardinality `q - 1`. -/
lemma card_units : fintype.card (units K) = q - 1 :=
begin
  classical,
  rw [eq_comm, nat.sub_eq_iff_eq_add (fintype.card_pos_iff.2 ⟨(0 : K)⟩)],
  haveI := set_fintype {a : K | a ≠ 0},
  haveI := set_fintype (@set.univ K),
  rw [fintype.card_congr (equiv.units_equiv_ne_zero _),
    ← @set.card_insert _ _ {a : K | a ≠ 0} _ (not_not.2 (eq.refl (0 : K)))
    (set.fintype_insert _ _), fintype.card_congr (equiv.set.univ K).symm],
  congr; simp [set.ext_iff, classical.em]
end

/-- The units of a finite field form a cyclic group. -/
instance : is_cyclic (units K) :=
by haveI := classical.dec_eq K;
haveI := set_fintype (@set.univ (units K)); exact
let ⟨g, hg⟩ := is_cyclic.exists_generator (@set.univ (units K)) in
⟨⟨g, λ x, let ⟨n, hn⟩ := hg ⟨x, trivial⟩ in ⟨n, by rw [← is_subgroup.coe_gpow, hn]; refl⟩⟩⟩

lemma prod_univ_units_id_eq_neg_one :
  univ.prod (λ x, x) = (-1 : units K) :=
begin
  classical,
  have : ((@univ (units K) _).erase (-1)).prod (λ x, x) = 1,
  from prod_involution (λ x _, x⁻¹) (by simp)
    (λ a, by simp [units.inv_eq_self_iff] {contextual := tt})
    (λ a, by simp [@inv_eq_iff_inv_eq _ _ a, eq_comm] {contextual := tt})
    (by simp),
  rw [← insert_erase (mem_univ (-1 : units K)), prod_insert (not_mem_erase _ _),
      this, mul_one]
end

/-- In a finite field of cardinality `q`, one has `a^(q-1) = 1` for all nonzero `a`. -/
lemma pow_card_sub_one_eq_one  (a : K) (ha : a ≠ 0) :
  a ^ (q - 1) = 1 :=
calc a ^ (q - 1) = (units.mk0 a ha ^ (q - 1) : units K) :
    by rw [units.coe_pow, units.coe_mk0]
  ... = 1 : by { classical, rw [← card_units, pow_card_eq_one], refl }

variable (K)

/-- The sum of `x^i` as `x` ranges over the units of a finite field of cardinality `q`
is equal to `0` unless `(q-1) ∣ i`, in which case the sum is `q-1`. -/
lemma sum_pow_units (i : ℕ) :
  univ.sum (λ (x : units K), (x^i : K)) = if (q - 1) ∣ i then q - 1 else 0 :=
begin
  haveI : decidable_eq (units K) := by { classical, apply_instance },
  cases is_cyclic.exists_generator (units K) with a ha,
  calc univ.sum (λ (x : units K), (x^i : K)) = (range (order_of a)).sum (λ k, ((a^k)^i : K)) :
  begin
    symmetry,
    refine sum_bij (λ i hi, a^i) (λ _ _, mem_univ _) (λ _ _, by rw units.coe_pow) _ _,
    { intros i j hi hj h, rw [mem_range] at hi hj,
      exact pow_injective_of_lt_order_of a hi hj h, },
    { intros x hx, specialize ha x,
      rwa [mem_gpowers_iff_mem_range_order_of, mem_image] at ha,
      rcases ha with ⟨i, hi, rfl⟩, exact ⟨i, hi, rfl⟩ }
  end
    ... = geom_series (a^i : K) (q-1) :
  begin
    rw [order_of_eq_card_of_forall_mem_gpowers ha, card_units],
    apply sum_congr rfl, intros k hk, rw [← pow_mul, mul_comm, pow_mul]
  end
    ... = if (q - 1) ∣ i then q - 1 else 0 :
  begin
    split_ifs with H H,
    { rcases H with ⟨d, rfl⟩,
      have aux : (λ (i:ℕ), ((a : K) ^ ((q - 1) * d)) ^ i) = λ i, 1,
      { funext i, rw [pow_mul, pow_card_sub_one_eq_one _ (units.ne_zero _), one_pow, one_pow], },
      rw [geom_series_def, aux, sum_const, card_range, add_monoid.smul_one,
        nat.cast_sub, nat.cast_one],
      exact fintype.card_pos_iff.mpr ⟨0⟩ },
    { have key := geom_sum_mul (a^i : K) (q-1),
      have hai : (a^i : K) ≠ 0, { rw ← units.coe_pow, apply units.ne_zero },
      rw [pow_card_sub_one_eq_one _ hai, sub_self] at key,
      apply (eq_zero_or_eq_zero_of_mul_eq_zero key).resolve_right,
      contrapose! H,
      rw [← card_units, ← order_of_eq_card_of_forall_mem_gpowers ha],
      apply order_of_dvd_of_pow_eq_one,
      rwa [units.ext_iff, units.coe_pow, units.coe_one, ← sub_eq_zero], }
  end
end

theorem card (p : ℕ) [char_p K p] : ∃ (n : ℕ+), nat.prime p ∧ q = p^(n : ℕ) :=
begin
  haveI hp : fact p.prime := char_p.char_is_prime K p,
  have V : vector_space (zmod p) K, from { .. (zmod.cast_hom p K).to_module },
  obtain ⟨n, h⟩ := @vector_space.card_fintype _ _ _ _ V _ _,
  rw zmod.card at h,
  refine ⟨⟨n, _⟩, hp, h⟩,
  apply or.resolve_left (nat.eq_zero_or_pos n),
  rintro rfl,
  rw nat.pow_zero at h,
  have : (0 : K) = 1, { apply fintype.card_le_one_iff.mp (le_of_eq h) },
  exact absurd this zero_ne_one,
end

theorem card' : ∃ (p : ℕ) (n : ℕ+), nat.prime p ∧ q = p^(n : ℕ) :=
let ⟨p, hc⟩ := char_p.exists K in ⟨p, @finite_field.card K _ _ p hc⟩

@[simp] lemma cast_card_eq_zero : (q : K) = 0 :=
begin
  rcases char_p.exists K with ⟨p, _char_p⟩, resetI,
  rcases card K p with ⟨n, hp, hn⟩,
  simp only [char_p.cast_eq_zero_iff K p, hn],
  conv { congr, rw [← nat.pow_one p] },
  exact nat.pow_dvd_pow _ n.2,
end

/-- The sum of `x^i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q-1`. -/
lemma sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) :
  univ.sum (λ x, x^i) = (0:K) :=
begin
  by_cases hi : i = 0,
  { simp only [hi, add_monoid.smul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero], },
  have key := sum_pow_units K i,
  have not_dvd_i : ¬q - 1 ∣ i,
  { contrapose! h, exact nat.le_of_dvd (nat.pos_of_ne_zero hi) h },
  rw if_neg not_dvd_i at key,
  classical,
  conv_rhs {rw ← key}, symmetry,
  rw [← sum_sdiff (subset_univ (finset.singleton (0:K))), sum_singleton,
    zero_pow (nat.pos_of_ne_zero hi), add_zero],
  refine sum_bij (λ x _, x) (λ _ _, by simp) (λ _ _, rfl) (λ _ _ _ _, units.ext_iff.mpr) _,
  intros, refine ⟨units.mk0 b _, mem_univ _, rfl⟩,
    simpa only [true_and, mem_sdiff, mem_univ, mem_singleton] using H,
end

end finite_field

namespace zmod

open finite_field polynomial

lemma sum_two_squares (p : ℕ) [hp : fact p.prime] (x : zmod p) :
  ∃ a b : zmod p, a^2 + b^2 = x :=
begin
  cases hp.eq_two_or_odd with hp2 hp_odd,
  { unfreezeI, subst p, revert x, exact dec_trivial },
  let f : polynomial (zmod p) := X^2,
  let g : polynomial (zmod p) := X^2 - C x,
  obtain ⟨a, b, hab⟩ : ∃ a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ f g
      (degree_X_pow 2) (degree_X_pow_sub_C dec_trivial _) (by rw [zmod.card, hp_odd]),
  refine ⟨a, b, _⟩,
  rw ← sub_eq_zero,
  simpa only [eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab,
end

end zmod

namespace char_p

lemma sum_two_squares (R : Type*) [integral_domain R] (p : ℕ) [fact (0 < p)] [char_p R p] (x : ℤ) :
  ∃ a b : ℕ, (a^2 + b^2 : R) = x :=
begin
  haveI := char_is_prime_of_pos R p,
  obtain ⟨a, b, hab⟩ := zmod.sum_two_squares p x,
  refine ⟨a.val, b.val, _⟩,
  have := congr_arg (zmod.cast_hom p R) hab,
  simpa only [zmod.cast_int_cast, zmod.cast_hom_apply, zmod.cast_add,
    zmod.nat_cast_val, _root_.pow_two, zmod.cast_mul]
end

end char_p

open_locale nat
open zmod nat

/-- The Fermat-Euler totient theorem. `nat.modeq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp] lemma zmod.pow_totient {n : ℕ} [fact (0 < n)] (x : units (zmod n)) : x ^ φ n = 1 :=
by rw [← card_units_eq_totient, pow_card_eq_one]

/-- The Fermat-Euler totient theorem. `zmod.pow_totient` is an alternative statement
  of the same theorem. -/
lemma nat.modeq.pow_totient {x n : ℕ} (h : nat.coprime x n) : x ^ φ n ≡ 1 [MOD n] :=
begin
  cases n, {simp},
  rw ← zmod.eq_iff_modeq_nat,
  let x' : units (zmod (n+1)) := zmod.unit_of_coprime _ h,
  have := zmod.pow_totient x',
  apply_fun (coe : units (zmod (n+1)) → zmod (n+1)) at this,
  simpa only [-zmod.pow_totient, succ_eq_add_one, cast_pow, units.coe_one,
    nat.cast_one, cast_unit_of_coprime, units.coe_pow],
end
