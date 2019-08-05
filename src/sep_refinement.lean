
import prop program

import data.finmap
import category_theory.category
import tactic.interactive
import tactic.tauto
import tactic.linarith
import tactic.monotonicity

namespace refinement

open category_theory
open separation separation.hProp memory

variables value : Type

-- local notation `heap` := heap value
-- local notation `hProp` := hProp value

def state := Σ t : Type*, t → hProp value

section value

variables {value}

def state.mk {s} (p : s → hProp value) : state value := ⟨s,p⟩

structure inst (x : state value) :=
 (σ : x.fst) (h : heap value)
 (shape : x.snd σ h)

end value

def hom (x y : state value) := inst x → set (inst y)

instance : category (state value) :=
{ hom := hom value,
  id := λ _, pure,
  comp := λ x y z A₀ A₁, A₀ >=> A₁,
  id_comp' := λ x y f, fish_pipe _,
  comp_id' := λ x y f, fish_pure _,
  assoc' := λ x y z w f g h, fish_assoc _ _ _ }

universes u

variables {value} {s s' α : Type u}

def sat (p : s → hProp value) (m : ST value s α) (q : α → s → hProp value) : Prop :=
∀ σ σ' h h' x, (x,σ',h') ∈ m.run (σ,h) → p σ h → q x σ' h'

variables {p : s → hProp value} {m : ST value s punit} {q : s → hProp value}
variables {p' : s' → hProp value} {m' : ST value s' punit} {q' : s' → hProp value}

open function (const)

notation `♯` := by repeat { ext : 1; try {refl} }

def attach (x : set α) : set { a // a ∈ x } :=
{ a | a.1 ∈ x }

def arrow (hm : sat p m (const _ q)) : state.mk p ⟶ state.mk q :=
show inst (state.mk p) → set (inst (state.mk q)), from
λ ⟨σ,h,hp⟩,
do ⟨⟨x₀,x₁,x₂⟩,hx⟩ ← attach (m.run (σ,h)),
   return (inst.mk x₁ x₂ (hm σ _ h _ x₀ hx hp))

def abs {s s' : Type*} (R : s → s' → Prop) {p : s → hProp value} {p' : s' → hProp value} : state.mk p ⟶ state.mk p' :=
show inst (state.mk p) → set (inst (state.mk p')), from
λ ⟨σ,h,hp⟩ ⟨σ',h',hp'⟩,
R σ σ'

def repr {s s' : Type*} (R : s → s' → Prop) {p : s → hProp value} {p' : s' → hProp value} : state.mk p' ⟶ state.mk p :=
show inst (state.mk p') → set (inst (state.mk p)), from
λ ⟨σ,h,hp⟩ ⟨σ',h',hp'⟩,
R σ' σ

def ref {X Y : state value} (a b : X ⟶ Y) : Prop :=
∀ i, a i ⊆ b i

notation `⦃` p `⦄` := inst (state.mk p)

def rel (m : ST value s punit) (x : ⦃p⦄) (y : ⦃q⦄) : Prop :=
(punit.star,y.1,y.2) ∈ m.run (x.1,x.2)

infix ` ⊑ `:50 := ref

-- #exit
-- lemma sound (R : s → s' → Prop) (hc : sat p m (const _ q)) (ha : sat p' m' (const _ q'))
--   (hh : arrow hc ≫ abs R ⊑ abs R ≫ arrow ha) :
--   ∀ (c : ⦃p⦄) (c' : ⦃q⦄) (a : ⦃p'⦄),
--     R c.1 a.1 → rel m c c' →
--     ∃ a' : ⦃q'⦄, rel m' a a' ∧ R c'.1 a'.1 :=
-- begin
--   introv hR hm,
--   let ha' := m'.run (a.1,a.2),
--   let a' : ⦃q'⦄ := ⟨ha'.2.1,ha'.2.2,ha _ _ _ _ _ ♯ a.shape⟩,
--   existsi [a'], split, repeat {ext : 1; try { refl <|> apply punit_eq }},
--   specialize @hh c a', cases c, simp [(≫),(>=>),arrow,return,abs] at hh,
--   specialize @hh a',
-- end

lemma sound' (R : s → s' → Prop) (hc : sat p m (const _ q)) (ha : sat p' m' (const _ q'))
  (hh : repr R ≫ arrow hc ⊑ arrow ha ≫ repr R) :
  ∀ (c : ⦃p⦄) (c' : ⦃q⦄) (a : ⦃p'⦄),
    R c.1 a.1 → rel m c c' →
    ∃ a' : ⦃q'⦄, rel m' a a' ∧ R c'.1 a'.1 :=
begin
  introv hR hm,
  let a' : set ⦃q'⦄ := arrow ha a,
  specialize @hh a c' ⟨_,_,hm⟩,
  casesm* ⦃ _ ⦄, -- squeeze_simp [arrow,(≫),(>=>),(>>=),attach,repr] at hh,
  simp only [category_struct.comp, fish, arrow, return, set.bUnion_singleton, and_imp, attach,
             exists_prop, set.mem_Union, set.bind_def, set.pure_def, exists_imp_distrib] at hh,
  revert hh, apply exists_imp_exists, rintros ⟨a,b,c⟩,
  simp only [repr, true_and, and_imp, subtype.val_prop, bex_imp_distrib, subtype.exists,
             set.mem_set_of_eq, exists_imp_distrib, prod.exists, rel, arrow, return, pure,
             set.mem_singleton_iff ],
  introv h₀ h₁ h₂ h₃, subst x_1, subst x_2, cases x,
  exact ⟨h₀,h₃⟩,
  simp [set.mem_singleton_iff],
  existsi c, cases c,
  apply set.ext, intro,
  simp only [arrow, set.Union, exists_prop, set.mem_Union, set.bind_def, subtype.exists, prod.exists],
  split,
  { rintro ⟨h₀,⟨⟨⟩,b,c,h₁,h₂,h₃⟩⟩, simp only [return, set.mem_singleton_iff, and_self, set.pure_def] at h₃, subst x, exact h₂, },
  { intro h, cases a, existsi [hR,punit.star,_,_,h,h],
    cases x, simp only [return, set.mem_singleton_iff, and_self, set.pure_def, eq_self_iff_true], },
end


open state_t

-- instance {α} : has_coe (option α) (ST value s α) := _

/-
 * framing
 * assignment
 * alloc
 * dealloc
 * sequencing
 * loop
-/

-- def spec_alloc (s) (free : set ptr) (p : hProp value) (m : ST value s α) (q : α → hProp value) : Prop :=
-- ∀ σ σ' h h' frame x, (x,σ',h') ∈ m.run (σ,h) → (∀ p ∈ free, ¬ p ∈ h) → holds h frame p → holds h' frame (q x)

-- lemma And_frame {α} {p : hProp value} {m : ST value s α} {q : α → hProp value}
--   (h : ) :
--   spec s p m q := _

-- lemma p_exists_one_point {α} {p : α → hProp value} (x : α)
--   (h : ∀ y, p y =*> [| x = y |] ⊛ True) :
--   p_exists p = p x :=
-- begin
--   ext; dsimp [p_exists]; split,
--   { rintros ⟨x',HH⟩, specialize h _ _ HH, admit },
--   apply @Exists.intro _ (λ x, p x h_1),
-- end


end refinement
