
import order.bounded_lattice
import order.complete_lattice
import prop

open lattice

class has_impl (α : Type*) :=
(impl : α → α → α)

-- infixr ` ⇒ `:60 := has_impl.impl
infixr ` ⇒ ` := has_impl.impl

set_option old_structure_cmd true

class heyting_algebra (α : Type*) extends bounded_lattice α, has_impl α :=
(le_impl_iff : ∀ x y z : α, z ≤ (x ⇒ y) ↔ x ⊓ z ≤ y)

class complete_heyting_algebra (α : Type*) extends complete_lattice α, heyting_algebra α
-- (le_impl_iff : ∀ x y z : α, z ≤ (x ⇒ y) ↔ x ⊓ z ≤ y)

variables {α : Type*}

namespace heyting_algebra

variables [heyting_algebra α]
variables {x y z : α}

lemma inf_div_le : x ⊓ (x ⇒ y) ≤ y :=
(le_impl_iff _ _ _).mp (le_refl _)

lemma le_impl (h : x ⊓ z ≤ y) : z ≤ (x ⇒ y) :=
(le_impl_iff _ _ _).mpr h

end heyting_algebra

class residuated_lattice (α : Type*) extends lattice α, monoid α, has_div α, has_sdiff α :=
(le_div_iff :   ∀ x y z : α, z ≤ x / y ↔ x * z ≤ y)
(le_sdiff_iff : ∀ x y z : α, z ≤ y \ x ↔ z * x ≤ y)

class comm_residuated_lattice (α : Type*)
extends comm_monoid α, residuated_lattice α

namespace residuated_lattice

end residuated_lattice

class bunched_implication_logic (α : Type*)
extends comm_residuated_lattice α, complete_heyting_algebra α

open separation separation.hProp
-- #exit

instance {value} : complete_lattice (hProp value) :=
pi.complete_lattice

instance {value} : complete_heyting_algebra (hProp value) :=
{ impl := λ x y h, x h → y h,
  le_impl_iff := λ x y z, ⟨λ H h ⟨hx,hz⟩, H _ hz hx,λ H, λ h hz hx, H h ⟨hx,hz⟩⟩,
  .. separation.hProp.lattice.complete_lattice }

instance {value} : comm_monoid (hProp value) :=
{ mul := and,
  mul_assoc := and_assoc,
  one := emp,
  one_mul := emp_and,
  mul_one := and_emp,
  mul_comm := and_comm }

instance {value} : comm_residuated_lattice (hProp value) :=
{ div := wand,
  sdiff := flip wand,
  le_div_iff := λ p q r,
    show r ≤ p ⊸ q ↔ p ⊛ r ≤ q,
    from (@separation.hProp.and_comm value r p) ▸ sorry,
  le_sdiff_iff := λ p q r,
    show r ≤ p ⊸ q ↔ r ⊛ p ≤ q,
    from (@separation.hProp.and_comm value r p) ▸ sorry,
  .. separation.hProp.comm_monoid,
  .. separation.hProp.lattice.complete_lattice, }
-- #exit

instance {value} : bunched_implication_logic (hProp value) :=
{ .. separation.hProp.complete_heyting_algebra,
  .. separation.hProp.comm_residuated_lattice, }
-- { le := impl,
--   top := True,
--   bot := False,
--   one := emp,
--   mul := hProp.and,
--   div := wand,
--   sdiff := flip wand,
--   inf := p_and,
--   sup := p_or,
--   mul_one := and_emp,
--   one_mul := emp_and,
--   mul_comm := and_comm,
--   mul_assoc := and_assoc,
--   le_Sup := _,
--   sup_le := _,
--   -- le_inf := _
--   }

-- class bunched_impl (α : Type) extends  :=

-- universes u v w

-- def Flift (F : Type v → Type w) (α : Type u) : Type* :=
-- Σ β, F β × (β → α)

-- class foldable (F : Type u → Type v) :=
-- (foldl : ∀ {α β : Type u}, (α → β → α) → α → F β → α)

-- variables {F : Type u → Type v} [foldable F]
-- open ulift

-- def Flift.foldl {α β : Type w} (f : α → β → α) (x : α) : Flift F β → α
-- | ⟨γ,y,g⟩ := sorry -- ulift.down $ foldable.foldl.{u v} (λ a b, up $ f (down a) _) (up x) y

-- instance : foldable (Flift.{w} F) :=
-- ⟨ @Flift.foldl F _  ⟩

-- def Flift.mk {α} (x : F α) : Flift F (ulift.{w} α) :=
-- ⟨_, x, up⟩

-- -- set_option pp.implicit true

-- def foldl {α : Type w} {β : Type u} (f : α → β → α) (x : α) (xs : F β) : α :=
-- down $ @foldable.foldl (Flift F) _ _ _ (λ a (b : ulift.{w} β), up $ f (down a) (down b)) (up.{u} x) (Flift.mk.{u} xs)
