/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of modules over commutative rings, indexed by a discrete type.
-/

import algebra.direct_sum
import linear_algebra.basic

universes u v w u₁

variables (R : Type u) [comm_ring R]
variables (ι : Type v) [decidable_eq ι] (β : ι → Type w)
variables [Π i, add_comm_group (β i)] [Π i, module R (β i)]
include R

namespace direct_sum

variables {R ι β}

instance : module R (direct_sum ι β) := dfinsupp.to_module

variables R ι β
def lmk : Π s : finset ι, (Π i : (↑s : set ι), β i.1) →ₗ[R] direct_sum ι β :=
dfinsupp.lmk β R
lemma single_eq_of (i : ι) (b : β i) :
  dfinsupp.single i b = of ι β i b := rfl

variables {ι β}

def lof : Π i : ι, β i →ₗ[R] direct_sum ι β :=
dfinsupp.lsingle β R
variables {R ι β}

theorem mk_smul (s : finset ι) (c : R) (x) : mk β s (c • x) = c • mk β s x :=
(lmk R ι β s).map_smul c x

theorem of_smul (i : ι) (c : R) (x) : of β i (c • x) = c • of β i x :=
(lof R ι β i).map_smul c x

lemma sum_of [Π i, decidable_pred (eq (0 : β i))] (f : direct_sum R ι β) :
  f.sum (λ i, of ι β i) = f :=
by dsimp [of, dfinsupp.lsingle]; unfold_coes; simp;
  exact @dfinsupp.sum_single ι β _ _ _ f

variables {γ : Type u₁} [add_comm_group γ] [module R γ]
variables (φ : Π i, β i →ₗ[R] γ)

variables (R ι γ φ)
def to_module : direct_sum ι β →ₗ[R] γ :=
{ to_fun := to_group (λ i, φ i),
  add := to_group_add _,
  smul := λ c x, direct_sum.induction_on x
    (by rw [smul_zero, to_group_zero, smul_zero])
    (λ i x, by rw [← of_smul, to_group_of, to_group_of, (φ i).map_smul c x])
    (λ x y ihx ihy, by rw [smul_add, to_group_add, ihx, ihy, to_group_add, smul_add]) }
variables {R ι γ φ}

@[simp] lemma to_module_lof (i) (x : β i) : to_module R ι γ φ (lof R ι β i x) = φ i x :=
to_group_of (λ i, φ i) i x

variables (ψ : direct_sum ι β →ₗ[R] γ)

theorem to_module.unique (f : direct_sum ι β) : ψ f = to_module R ι γ (λ i, ψ.comp $ lof R ι β i) f :=
to_group.unique ψ f

variables {ψ} {ψ' : direct_sum ι β →ₗ[R] γ}

theorem to_module.ext (H : ∀ i, ψ.comp (lof R ι β i) = ψ'.comp (lof R ι β i)) (f : direct_sum ι β) :
  ψ f = ψ' f :=
by rw [to_module.unique ψ, to_module.unique ψ', funext H]

def lset_to_set (S T : set ι) (H : S ⊆ T) :
  direct_sum S (β ∘ subtype.val) →ₗ direct_sum T (β ∘ subtype.val) :=
to_module R _ _ $ λ i, lof R T (β ∘ @subtype.val _ T) ⟨i.1, H i.2⟩

protected def lid (M : Type v) [add_comm_group M] [module R M] :
  direct_sum punit (λ _, M) ≃ₗ M :=
{ .. direct_sum.id M,
  .. to_module R punit M (λ i, linear_map.id) }

def component (ι : Type*) [decidable_eq ι] (β : ι → Type*)
  [Π i, add_comm_group (β i)] [Π i, module R (β i)]
  (i : ι) : direct_sum R ι β →ₗ β i :=
{ to_fun := λ f, f i,
  add := λ _ _, dfinsupp.add_apply,
  smul := λ _ _, dfinsupp.smul_apply }

lemma of_apply (i : ι) (b : β i) : ((of ι β i) b) i = b :=
by rw [of, dfinsupp.lsingle_apply, dfinsupp.single_apply, dif_pos rfl]

lemma apply_eq_component (f : direct_sum R ι β) (i : ι) :
  f i = component ι β i f := rfl

@[simp] lemma component.of_self (i : ι) (b : β i) :
  component ι β i ((of ι β i) b) = b :=
of_apply i b

lemma component.of (i j : ι) (b : β j) :
  component ι β i ((of ι β j) b) =
  if h : j = i then eq.rec_on h b else 0 :=
dfinsupp.single_apply

@[extensionality] lemma ext {f g : direct_sum R ι β}
  (h : ∀ i, component ι β i f = component ι β i g) : f = g :=
dfinsupp.ext h

lemma ext_iff {f g : direct_sum R ι β} : f = g ↔
  ∀ i, component ι β i f = component ι β i g :=
⟨λ h _, by rw h, ext⟩

end direct_sum
