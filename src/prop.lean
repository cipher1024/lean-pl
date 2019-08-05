
import heap.lemmas misc
import tactic.monotonicity
import tactic.library_search
import logic.basic

namespace separation

open memory finmap

variables value : Type

def hProp := heap value → Prop

variables {value}
include value
local notation `heap` := heap value
local notation `hProp` := hProp value
local notation `tptr` := tptr value

namespace «hProp»

@[extensionality]
lemma hProp.ext {p q : hProp} (H : ∀ h, p h ↔ q h) : p = q :=
by ext; apply H

def emp : hProp := λ h, h = ∅

def and (x y : hProp) : hProp
| h := ∃ h₀ h₁, some h = add (some h₀) (some h₁) ∧ x h₀ ∧ y h₁

def lift (p : Prop) : hProp
| h := p ∧ emp h

notation `[| ` p ` |]` := lift p

lemma lift_eq_emp {p} (h : p) : [| p |] = @emp value :=
by { funext h', ext, simp [lift,h] }

infixr ` ⊛ `:55 := and

@[simp]
lemma emp_and (p : hProp) : emp ⊛ p = p :=
begin
  ext; simp [emp,and,(∈),set.mem,add]; split,
  { simp, introv h₀ h₁, subst h₁,
    simp [disjoint_empty,pure] at h₀, subst h₀, exact id },
  { intro hp, existsi [(∅ : finmap _),h],
    rw [if_pos (disjoint_empty h)], simp,
    exact ⟨rfl, hp⟩ }
end

lemma and_comm (p q : hProp) : p ⊛ q = q ⊛ p :=
funext $ λ h, by { dsimp [and], rw exists_swap, ext, repeat { apply exists_congr; intro },
                   rw [memory.add_comm,and_comm (p a_1)] }

instance and.is_commutative : is_commutative _ (@and value) := ⟨ and_comm ⟩

@[simp]
lemma and_emp (p : hProp) : p ⊛ emp = p :=
by rw [and_comm,emp_and]

def And {α} (p : α → hProp) : list α → hProp
| [] := emp
| (x :: xs) := p x ⊛ And xs

def p_exists {α} (p : α → hProp) : hProp
| h := ∃ x, p x h

notation `∃∃ ` binders `, ` r:(scoped P, p_exists P) := r

def p_forall {α} (p : α → hProp) : hProp
| h := ∀ x, p x h

notation `∀∀ ` binders `, ` r:(scoped P, p_forall P) := r

def maplets : ptr → value → hProp
-- | p [] := emp
| p v h := h = maplet p v

infix ` ↦ `:60 := maplets

open list

lemma and_assoc (p q r : hProp) : (p ⊛ q) ⊛ r = p ⊛ q ⊛ r :=
begin
  ext : 1; dsimp [and,(∈),set.mem],
  split,
  { rintros ⟨h₀,h₁,Hx,⟨h₂,h₃,HH,Hp,Hq⟩,Hr⟩,
    have : disjoint h₃ h₁,
    { by_contradiction,
      rw [HH,memory.add_assoc] at Hx, simp [add,if_neg,a] at Hx,
      exact Hx },
    refine ⟨_, h₃ ∪ h₁, _, Hp, _, _, _, Hq, Hr⟩,
    { rw [Hx,HH,memory.add_assoc,union_eq_add_of_disjoint this] },
    { rw union_eq_add_of_disjoint this } },
  { rintro ⟨h₀,h₁,Hx,Hp,h₂,h₃,Hh₁,Hq,Hr⟩,
    have : disjoint h₀ h₂,
    { by_contradiction,
      rw [Hh₁,← memory.add_assoc] at Hx, simp [add,if_neg,a] at Hx,
      exact Hx },
    refine ⟨h₀ ∪ h₂,_,_,⟨_,_,_,Hp,Hq⟩,Hr⟩,
    { rw [Hx,Hh₁,union_eq_add_of_disjoint this,memory.add_assoc] },
    { rw union_eq_add_of_disjoint this } }
end

instance and.is_associative : is_associative _ (@and value) := ⟨ hProp.and_assoc ⟩

@[simp, separation_logic]
lemma And_append {α} (p : α → hProp) (xs ys : list α) : And p (xs ++ ys) = And p xs ⊛ And p ys :=
by induction xs; dsimp [And]; [rw emp_and, rw [xs_ih,and_assoc]]

@[simp]
lemma And_map {α β} (p : α → hProp) (f : β → α) : Π (xs : list β), And p (map f xs) = And (p ∘ f) xs
| [] := rfl
| (x :: xs) := by rw [map,And,And,And_map]

open nat

-- lemma maplets_eq_And (p : ptr) (vs : list value) : (p ↦ vs) = And (λ i, p+i ↦ nth' i vs) (range vs.length) :=
-- begin
--   induction vs generalizing p,  refl,
--   simp [maplets], simp only [nat.add_comm 1,range_succ_eq_map,And,vs_ih,And_map,(∘),nth'],
--   congr' 1, ext, simp [maplets], simp [succ_eq_add_one]
-- end

def holds (h frame : heap) (p : hProp) : Prop :=
∃ h₀, some h = some h₀ ⊗ some frame ∧ p h₀

def holds' (h : heap) (p : hProp) : Prop :=
∃ h', holds h h' p

infix ` ⊨ `:60 := holds'

lemma holds_union_and {h h' frame : heap} {p q : hProp}
  (H₀ : holds h frame p) (H₁ : q h') (H₂ : disjoint h h') :
  holds (h ∪ h') frame (p ⊛ q) :=
begin
  simp [holds,and] at H₀ ⊢,
  rcases H₀ with ⟨h'', H₀, H₃⟩,
  existsi h' ∪ h'', rw [union_eq_add_of_disjoint H₂,union_eq_add_of_disjoint,H₀],
  split, ac_refl,
  refine ⟨_,_,add_comm _ _,H₃,H₁⟩,
  symmetry, apply disjoint_mono _ (le_refl h') H₂,
  apply le_of_add_eq_some _ H₀,
end

lemma holds_of_holds_union_and {h h' frame : heap} {p q : hProp}
  (H₀ : holds (h ∪ h') frame (p ⊛ q)) (H₁ : q h') (H₂ : disjoint h h') (H₃ : ∀ h'', q h'' → h'' = h') :
  holds h frame p :=
begin
  simp [holds,and] at H₀ ⊢,
  rcases H₀ with ⟨h'', H₀, h₀, h₁, H₆, H₄, H₅⟩,
  refine ⟨h₀,_,H₄⟩,
  rw [union_eq_add_of_disjoint H₂,H₆] at H₀,
  replace H₃ := H₃ _ H₅, subst h',
  have := union_eq_add_of_disjoint H₂,
  apply add_inj (some h₁) (h ∪ h₁)  (h ∪ h₁) this,
  rw [this,H₀], ac_refl, rw H₀, ac_refl,
end

lemma holds_of_holds_union_iff {h h' frame : heap} {p q : hProp}
  (H₁ : q h') (H₂ : disjoint h h') (H₃ : ∀ h'', q h'' → h'' = h') :
  holds (h ∪ h') frame (p ⊛ q) ↔ holds h frame p :=
⟨ λ H₀, holds_of_holds_union_and H₀ H₁ H₂ H₃, λ H₀,holds_union_and H₀ H₁ H₂ ⟩

lemma holds_of_holds_and (h h₀ : heap) {p q : hProp} :
  holds h h₀ (p ⊛ q) ↔ (∃ h₁, holds h₁ h₀ q ∧ holds h h₁ p) :=
begin
  split; simp only [holds, and, and_imp, exists_imp_distrib],
  { introv hh hx hp hq,
    rw hx at hh, clear hx,
    have hh : ∃ k, some k = some x_2 ⊗ some h₀,
    { apply add_eq_some _ (some x_1) h,
      rw [memory.add_comm,← memory.add_assoc,hh] },
    cases hh with k hk,
    existsi k, split,
    exact ⟨_,hk,hq⟩,
    refine ⟨_,_,hp⟩, rw [hk,hh,memory.add_assoc] },
  { introv hh hx hh' hp,
    rw hh at hh', clear hh,
    have hh : ∃ k, some k = some x_2 ⊗ some x_1,
    { apply add_eq_some _ (some h₀) h,
      rw [memory.add_assoc,hh'] },
    cases hh with k hk,
    existsi k, rw [hk,memory.add_assoc],
    existsi hh',
    refine ⟨_,_,rfl,hp,hx⟩ }
end

-- @[simp]
-- lemma maplets_nil (p : ptr) : (p ↦ nil) = @emp value := rfl

-- @[separation_logic]
-- lemma maplets_cons (p : ptr) (v : value) (vs : list value) : (p ↦ v :: vs) = (p ↦ [v]) ⊛ (p+1 ↦ vs) :=
-- by dsimp [maplets]; rw and_emp

structure impl (p q : hProp) : Prop :=
intro ::
(elim : ∀ h, p h → q h)

infixr ` =*> `:40 := impl

def wand (p q : hProp) : hProp
| h := ∀ h₀ h', some h' = some h₀ ⊗ some h → p h₀ → q h'

infixr ` ⊸ `:54 := wand

lemma and_wand {p q : hProp} : p ⊛ (p ⊸ q) =*> q :=
⟨ λ h ⟨h₀,h₁,Hh,Hp,Hpq⟩, Hpq h₀ _ Hh Hp ⟩

lemma disjoint_of_disjoint_union_left {h₀ h₁ : heap} (h₂ : heap) (H : disjoint h₀ (h₁ ∪ h₂)) :
  disjoint h₀ h₁ :=
λ x hx₀ hx₁, H x hx₀ (finmap.mem_union.mpr $ or.inl hx₁)

lemma disjoint_of_disjoint_union_right {h₀ h₁ : heap} (h₂ : heap) (H : disjoint (h₀ ∪ h₂) h₁) :
  disjoint h₀ h₁ :=
(disjoint_of_disjoint_union_left h₂ H.symm).symm

lemma wand_wand {p q r : hProp} : p ⊸ (q ⊸ r) = (p ⊛ q) ⊸ r :=
begin
  ext, simp only [wand, and, and_imp, exists_imp_distrib,@forall_swap (p _)],
  split; intros H h₀ h₁ Hhh₀ h₂ h₃ Hhh₂ Hp Hq,
  { have : some (h₂ ∪ h) = some h₂ ⊗ some h,
    { apply union_eq_add_of_disjoint, apply disjoint_of_disjoint_union_right h₃,
      apply disjoint_of_add h₁, rw union_eq_add_of_disjoint, cc,
      apply disjoint_of_add _ Hhh₂ },
    apply H _ (h₂ ∪ h) this _ _ _ Hp Hq, simp only *, cc },
  { have : some (h₀ ∪ h₂) = some h₀ ⊗ some h₂,
    { apply union_eq_add_of_disjoint, apply disjoint_of_disjoint_union_right h,
      apply disjoint_of_add h₃, rw union_eq_add_of_disjoint, cc,
      apply disjoint_of_add _ Hhh₀ },
    apply H (h₀ ∪ h₂) _ _ _ _ this Hp Hq, simp only *, cc },
end

lemma wand_deduction {p q r : hProp} : p =*> q ⊸ r ↔ p ⊛ q =*> r :=
by { split; rintro ⟨ H ⟩; constructor;
       [rintros h ⟨h₀,h₁,HH,Hp,hq⟩, intros h Hp h₀ h₁ HH Hq];
       apply H; try { assumption <|> refine ⟨h,h₀,_,Hp,Hq⟩ };
     rw [HH,memory.add_comm] }

@[refl]
lemma impl_refl (p : hProp) : p =*> p := impl.intro $ λ x, id

@[trans]
lemma impl_trans {p q r : hProp} (hpq : p =*> q) (hqr : q =*> r) : p =*> r :=
impl.intro $ λ h hp, hqr.elim _ (hpq.elim _ hp)

def True : hProp | h := true

def False : hProp | h := false

@[simp]
lemma impl_True {p : hProp} : p =*> True :=
⟨ λ _ _, trivial ⟩

@[simp, separation_logic]
lemma lift_false : [| false |] = @False value :=
funext $ λ h, by simp [lift,False]

@[simp, separation_logic]
lemma False_and (p : hProp) : False ⊛ p = False :=
by ext; simp [and,False]

@[simp, separation_logic]
lemma and_False (p : hProp) : p ⊛ False = False :=
by ext; simp [and,False]

-- @[simp]
lemma False_impl (p : hProp) : False =*> p :=
impl.intro $ λ _, false.elim

lemma holds_p_exists {α} {h h' : heap} (p : α → hProp) : holds h h' (p_exists p) ↔ ∃ x, holds h h' (p x) :=
by split; rintro ⟨_,H,H',H''⟩; [ exact ⟨_,a_w,H,H''⟩, exact ⟨H,H',_,H''⟩ ]

lemma and_p_exists_distrib_right {α} {p : α → hProp} {q : hProp} :
  p_exists p ⊛ q = ∃∃ x, p x ⊛ q :=
begin
  ext, dsimp [and,p_exists], split; simp,
  { intros h₀ h₁ H r Hp Hq, refine ⟨_,_,_,H,Hp,Hq⟩ },
  { intros r h₀ h₁ H Hp Hq,
    refine ⟨_,_,H,⟨_,Hp⟩,Hq⟩, }
end

lemma and_p_exists_distrib_left {α} {p : hProp} {q : α → hProp} :
  p ⊛ p_exists q = ∃∃ x, p ⊛ q x :=
by rw [and_comm, and_p_exists_distrib_right]; simp [and_comm]

def p_or (p q : hProp) : hProp
| h := p h ∨ q h

def p_and (p q : hProp) : hProp
| h := p h ∧ q h

infixr ` ⋁ `:53 := p_or

infixr ` ⋀ `:53 := p_and

lemma p_and_impl_p_and {p p' q q' : hProp} (hp : p =*> q) (hq : p' =*> q') :
  p ⋀ p' =*> q ⋀ q' :=
⟨ λ h, and.imp (hp.elim _) (hq.elim _) ⟩

lemma impl_and {p q q' : hProp} (H : p =*> q) (H' : p =*> q') :
  p =*> q ⋀ q' :=
⟨ λ h hp, ⟨H.elim _ hp,H'.elim _ hp⟩ ⟩

lemma impl_exists {α} {p : hProp} {q : α → hProp} (x : α) (hpq : p =*> q x) : p =*> p_exists q :=
impl.intro $ λ h hp, ⟨_,hpq.elim _ hp⟩

lemma exists_impl {α} {p : α → hProp} {q : hProp} (hpq : ∀ x, p x =*> q) : p_exists p =*> q :=
impl.intro $ λ h ⟨_, hp⟩, (hpq _).elim _ hp

lemma impl_antisymm {p q : hProp} (hpq : p =*> q) (hqp : q =*> p) : p = q :=
by ext; exact ⟨hpq.elim _,hqp.elim _⟩

open relation

lemma impl_of_eq {p q : hProp} (hpq : p = q) : p =*> q := impl.intro $ λ h, hpq.subst

lemma exists_impl_exists_of_total {α β} {p : α → hProp} {q : β → hProp}
  (R : α → β → Prop) (hl : left_total R)
  (hpq : ∀ x y, R x y → p x =*> q y) : p_exists p =*> p_exists q :=
exists_impl $ λ x, Exists.rec_on (hl x) $ λ w hw, impl_exists w (hpq _ _ hw)

lemma exists_congr_of_total {α β} {p : α → hProp} {q : β → hProp}
  (R : α → β → Prop) (hl : left_total R) (hr : right_total R)
  (hpq : ∀ x y, R x y → p x = q y) : p_exists p = p_exists q :=
impl_antisymm
  (exists_impl_exists_of_total R hl $ λ x y hR, impl_of_eq $ hpq _ _ hR)
  (exists_impl_exists_of_total (flip R) hr $ λ x y hR, impl_of_eq (hpq _ _ hR).symm)

lemma exists_impl_exists {α} {p q : α → hProp} (hpq : ∀ x, p x =*> q x) : p_exists p =*> p_exists q :=
exists_impl $ λ x, impl_exists x (hpq _)

lemma exists_impl_exists_to {α β} {p : α → hProp} {q : β → hProp}
  (f : α → β)
  (hpq : ∀ x, p x =*> q (f x)) : p_exists p =*> p_exists q :=
exists_impl $ λ x, impl_exists (f x) (hpq _)

open function

lemma exists_impl_exists_from {α β} {p : α → hProp} {q : β → hProp}
  (f : β → α) (hf : surjective f)
  (hpq : ∀ x, p (f x) =*> q x) : p_exists p =*> p_exists q :=
exists_impl $ λ x, Exists.rec_on (hf x) $ λ w hf, impl_exists w $ hf ▸ hpq w

lemma exists_congr' {α β} {p : α → hProp} {q : β → hProp}
  (f : α → β) (hf : surjective f)
  (hpq : ∀ x, p x = q (f x)) : p_exists p = p_exists q :=
impl_antisymm
  (exists_impl_exists_to f $ λ x, impl_of_eq $ hpq x)
  (exists_impl_exists_from f hf $ λ x, impl_of_eq (hpq x).symm)

lemma or_impl {p p' : hProp} {q : hProp}
  (H  : p  =*> q)
  (H' : p' =*> q) :
   p ⋁ p' =*> q :=
impl.intro $ λ h h', or.elim h' (H.elim h) (H'.elim h)

@[congr]
lemma exists_congr {α} {p q : α → hProp}
  (hpq : ∀ x, p x = q x) : p_exists p = p_exists q :=
congr_arg _ $ funext hpq

@[mono]
lemma and_impl_and {p p' q q' : hProp} (hpq : p =*> q) (hpq' : p' =*> q') : p ⊛ p' =*> q ⊛ q' :=
impl.intro $ λ h, exists_imp_exists $ λ h₀, exists_imp_exists $ λ h₁, and.imp_right $ and_implies (hpq.elim _) (hpq'.elim _)

lemma lift_impl_emp {p : Prop} : [|p|] =*> @emp value :=
⟨ λ h ⟨_,h'⟩, h' ⟩

@[mono]
lemma lift_impl_lift {p q : Prop} (h : p → q) : [|p|] =*> ([|q|] : hProp) :=
impl.intro $ λ hp, and.imp h id

lemma lift_p_and_and {p : Prop} {q : hProp} : [| p |] ⊛ q = [| p |] ⊛ True ⋀ q :=
impl_antisymm
  (impl_and (and_impl_and (impl_refl _) impl_True)
            (emp_and q ▸ and_impl_and lift_impl_emp ((emp_and q).symm ▸ impl_refl q)))
  ⟨λ h ⟨⟨h₀,h₁,h₂,h₃,h₄⟩,h'⟩,
     have h = h₁, by { dsimp [lift,emp] at h₃,
                       rw [h₃.2,empty_add,option.some.inj_eq] at h₂,
                       exact h₂ },
     ⟨h₀,h₁,h₂,h₃,this ▸ h'⟩⟩

lemma impl_or_left {p q q' : hProp} (hpq : p =*> q) : p =*> q ⋁ q' :=
impl.intro $ λ h hp, or.inl (hpq.elim h hp)

lemma impl_or_right {p q q' : hProp} (hpq : p =*> q') : p =*> q ⋁ q' :=
impl.intro $ λ h hp, or.inr (hpq.elim h hp)

lemma p_and_or_distrib_left {p q r : hProp} :
  p ⊛ (q ⋁ r) = (p ⊛ q) ⋁ (p ⊛ r) :=
impl_antisymm
  ⟨ λ h ⟨h₀,h₁,Hh,Hp,Hqr⟩,
        or.elim Hqr (λ Hq, or.inl ⟨h₀,h₁,Hh,Hp,Hq⟩)
                    (λ Hr, or.inr ⟨h₀,h₁,Hh,Hp,Hr⟩) ⟩
  (or_impl (and_impl_and (impl_refl _) (impl_or_left (impl_refl _)))
           (and_impl_and (impl_refl _) (impl_or_right (impl_refl _))) )

@[simp, separation_logic]
lemma lift_true : [| true |] = (emp : hProp) := lift_eq_emp trivial

lemma lift_and_iff_p_exists {p : Prop} {q : hProp} : [|p|] ⊛ q = ∃∃ h : p, q :=
begin
  ext, dsimp [and,p_exists,lift,emp], split,
  { rintros ⟨h₀,h₁,H₀,⟨H₁,H₂⟩,H₃⟩, subst H₂,
    rw [empty_add,option.some_inj] at H₀, exact ⟨H₁, H₀.symm ▸ H₃⟩ },
  { rintros ⟨hp,hq⟩, refine ⟨∅,h,_,⟨hp,rfl⟩,hq⟩,
    rw [empty_add,option.some_inj] }
end

@[simp]
lemma lift_and_applied {p : Prop} {q : hProp} (h : heap) : ([|p|] ⊛ q) h ↔ p ∧ q h :=
by simp [lift_and_iff_p_exists,p_exists]

lemma and_applied_union {p q : hProp} {h h' : heap} (Hp : p h) (Hq : q h') (Hdisj : disjoint h h') : (p ⊛ q) (h ∪ h') :=
⟨h, h', union_eq_add_of_disjoint Hdisj, Hp, Hq⟩

lemma lift_and_impl {p : Prop} {q r : hProp}
  (h : p → q =*> r) :
  [|p|] ⊛ q =*> r :=
suffices (∃∃ h : p, q) =*> r,
  by simpa [lift_and_iff_p_exists],
exists_impl h

lemma lift_impl {p : Prop} {r : hProp}
  (h : p → emp =*> r) :
  [|p|] =*> r :=
suffices [|p|] ⊛ emp =*> r,
  by simpa [and_emp],
lift_and_impl h

lemma impl_lift_and {p : Prop} {q r : hProp}
  (h : p)
  (h' : q =*> r) :
  q =*> [|p|] ⊛ r :=
suffices q =*> (∃∃ h : p, r),
  by simpa [lift_and_iff_p_exists],
impl_exists h h'

lemma holds_or_iff {h frame : heap} {p q : hProp} :
  holds h frame (p ⋁ q) ↔ holds h frame p ∨ holds h frame q :=
by { dsimp [holds,p_or], rw [← exists_or_distrib],
     simp [and_or_distrib_left] }

lemma holds_imp_holds_of_impl {h frame : heap} {p q : hProp}
  (Hpq : p =*> q) : holds h frame p → holds h frame q :=
exists_imp_exists (λ hp, and.imp_right $ Hpq.elim hp)

@[simp]
lemma holds_lift_and {h frame : heap} {p : Prop} {q : hProp} : holds h frame ([|p|] ⊛ q) ↔ p ∧ holds h frame q :=
begin
  simp [holds,lift,emp], rw ← exists_and_distrib_left,
  apply _root_.exists_congr, intro, cc,
end

@[simp]
lemma holds_lift {h frame : heap} {p : Prop} : holds h frame [|p|] ↔ p ∧ holds h frame emp :=
by rw [← holds_lift_and,and_emp]

lemma exists_subtype {α} {p : α → Prop} {q : α → hProp} :
  (∃∃ x : subtype p, q x.val) = (∃∃ x : α, [| p x |] ⊛ q x) :=
impl_antisymm
  (exists_impl_exists_to subtype.val (by simp; intros a ha; simp [lift_eq_emp ha]))
  (exists_impl $ λ x, lift_and_impl $ λ hp, impl_exists ⟨_,hp⟩ $ impl_refl _)

lemma exists_exists {α} {p : α → Sort*} {q : Π x, p x → hProp} :
  (∃∃ (x : α) (h : p x), q x h) = (∃∃ x : psigma p, q x.1 x.2) :=
impl_antisymm
  (exists_impl $ λ x, exists_impl $ λ h, impl_exists ⟨x,h⟩ $ impl_refl _)
  (exists_impl $ λ x, impl_exists x.1 $ impl_exists x.2 $ impl_refl _)

end «hProp»

variable (value)
class storable (α : Type*) :=
(size : α → ℕ)
(repr : tptr α → α → hProp)

export storable (size)

local notation `storable` := storable value

section

omit value
meta def check_fixed_size : tactic unit := `[intros; refl]

end

-- def typeof {α} (x : α) := α
-- #check storable.repr
infix ` ⤇ `:60 := storable.repr

class fixed_storable (α : Type*) extends storable α :=
(fixed_size : ℕ)
(is_fixed : ∀ x : α, size x = fixed_size . check_fixed_size)
(size := λ _, fixed_size)
(pos_size : fixed_size > 0)

open list function «hProp»

export fixed_storable (fixed_size)

local notation `fixed_storable` := fixed_storable value
-- local notation `fixed_size` := fixed_size value

instance : fixed_storable value :=
{ repr := λ p v, p.get ↦ v,
  -- bytes := λ v, ⟨[v], rfl⟩,
  fixed_size := 1,
  pos_size := by norm_num,
  -- abstr := λ x, value_abstr _ x.property,
  -- right_inverse := λ ⟨[x],rfl⟩, rfl,
  -- raw_bytes_conversion := λ p x, rfl
 }

def word (α) [fixed_storable α] := { bytes : list value // length bytes = fixed_size value α }

local notation `word` := word value

variables {value}

def list_repr' {α β} [storable α] : tptr (list α) → list α → tptr β → hProp
| p [] q := [| p = q.recast (list α) |]
| p (v :: vs) q := p.recast α ⤇ v ⊛ list_repr' (p +. size value v) vs q

def value_abstr : Π vs : list value, length vs = 1 → value
| [val] rfl := val

def list_repr {α} [storable α] : tptr (list α) → list α → hProp
| p [] := emp
| p (v :: vs) := p.recast α ⤇ v ⊛ list_repr (p +. size value v) vs

lemma list_repr_map {α β} [storable α] [storable β]
  (p : tptr (list α)) {f : β → α} (xs : list β)
  (h : ∀ (q : tptr α) x, q ⤇ f x = (q.recast _ ⤇ x))
  (h' : ∀ x : β, size value (f x) = size value x ):
  list_repr p (xs.map f) = (list_repr (p.recast _) xs) :=
begin
  induction xs generalizing p, refl,
  simp [list_repr,*], refl
end

@[simp, separation_logic]
lemma fixed_size_val : fixed_size value value = 1 := rfl

@[simp, separation_logic]
lemma size_val (x : value) : size value x = 1 := rfl

attribute [simp, separation_logic] fixed_storable.is_fixed

lemma list_repr'_eq_list_repr {α β} [fixed_storable α] (p : tptr (list α)) (q : tptr β) (ls : list α) :
  list_repr' p ls q = list_repr p ls ⊛ [| p +. ls.length * fixed_size value α = q.recast _ |] :=
by induction ls generalizing p; simp [list_repr',list_repr,*,right_distrib,hProp.and_assoc]; congr

instance list.storable {α} [storable α] : storable (list α) :=
{ repr := list_repr,
  size := λ vs, list.sum $ vs.map (storable.size value)
  }

variables value

class is_record (α : Type*) extends fixed_storable α :=
(abstr : word α → α)
(bytes : α → word α)
(repr := λ p v, p.recast _ ⤇ (bytes v).val)
(right_inverse : right_inverse abstr bytes)
(raw_bytes_conversion : ∀ (p : tptr α) (x : α), (p ⤇ x) = (p.recast _ ⤇ (bytes x).val : hProp))

export is_record (abstr bytes raw_bytes_conversion)

local notation `is_record` := is_record value

def bytes' {α} [is_record α] (x : α) : list value :=
(bytes value x).val

lemma length_bytes' {α} [is_record α] (x : α) : length (bytes' value x) = fixed_size value α :=
(bytes value x).property

lemma bytes_surjective (α) [is_record α] : surjective (bytes value : α → word α) :=
surjective_of_has_right_inverse ⟨abstr, is_record.right_inverse _ _⟩

variables {value}

lemma uninitialized {α} [is_record α] (p : tptr α) :
  (∃∃ bytes : list value, [|length bytes = fixed_size value α|] ⊛ (p.recast _ ⤇ bytes)) =
   ∃∃ obj : α, p ⤇ obj :=
by rw ← exists_subtype; symmetry; apply exists_congr' (bytes value) (bytes_surjective value α);
   intro x; apply raw_bytes_conversion

@[simp, separation_logic]
lemma repr_nil {α} [storable α] (p : tptr (list α)) :
  p ⤇ [] = @emp value :=
by { dsimp [storable.repr], simp [list_repr], }

@[simp, separation_logic]
lemma repr_cons {α} [storable α] (p : tptr (list α)) (x) (xs : list α) :
  p ⤇ (x :: xs) = (p.recast _ ⤇ x ⊛ p+.size value x ⤇ xs : hProp) :=
by { dsimp [storable.repr], simp [list_repr], }

lemma maplets_append' {α} [fixed_storable α] : Π (p : tptr (list α)) (us vs : list α), (p ⤇ (us ++ vs)) = (p ⤇ us) ⊛ (p+.fixed_size value α * length us ⤇ vs)
| p [] vs := by simp
| p (u::us) vs := by simp [*,hProp.and_assoc,left_distrib]

lemma maplets_append : Π (p : tptr (list value)) (us vs : list value), (p ⤇ (us ++ vs)) = (p ⤇ us) ⊛ (p+.length us ⤇ vs)
| p [] vs := by simp
| p (u::us) vs := by simp [*,hProp.and_assoc]

@[simp, separation_logic]
lemma value_repr (p : ptr) (x : value) :
  tptr.mk value value p ⤇ x = p ↦ x :=
by { dsimp [storable.repr], simp [list_repr], }

@[simp, separation_logic]
lemma get_value_repr (p : tptr value) (x : value) :
  p ⤇ x = p.get ↦ x :=
by { dsimp [storable.repr], simp [list_repr], }

@[simp, separation_logic]
lemma tptr.recast_mk {α β} : Π (p : ptr), (tptr.mk value α p).recast β = tptr.mk value β p
| p := rfl

@[simp, separation_logic]
lemma tptr.recast_get {α β} : Π (p : tptr α), (p.recast β).get = p.get
| p := rfl

@[simp]
lemma disjoint_maplet_heap_mk_of_lt {p q : ℕ} (x : value) (xs : list value) (H : p < q) : disjoint (maplet p x) (heap.mk (enum_from q xs)) :=
by intros x; simp; intros H₀ H₁; subst x; cases not_le_of_lt H H₁

@[simp]
lemma disjoint_maplet_heap_mk_one_add {p : ℕ} (x : value) (xs : list value) : disjoint (maplet p x) (heap.mk (enum_from (1 + p) xs)) :=
disjoint_maplet_heap_mk_of_lt x xs ((nat.one_add p).symm ▸ nat.lt_succ_self _)

@[simp]
lemma disjoint_maplet_heap_mk_add_one {p : ℕ} (x : value) (xs : list value) : disjoint (maplet p x) (heap.mk (enum_from (p + 1) xs)) :=
disjoint_maplet_heap_mk_of_lt x xs (nat.lt_succ_self _)

lemma maplets_eq (p : tptr _) (vs : list value) (h : heap) : (p ⤇ vs) h ↔ h = heap.mk (vs.enum_from p.get) :=
begin
  induction vs generalizing p h; simp [maplets,emp,map,enum_from],
  simp [map,to_finmap_cons,separation.hProp.and,vs_ih,maplets,(+.)], split,
  { rintro ⟨h₀,h₁,hh₀,hh₁,hh₂⟩, rw [eq_union_of_eq_add hh₀,← hh₁,← hh₂] },
  { intro hh, refine ⟨_,_,_,rfl,rfl⟩, rw [← union_eq_add_of_disjoint, ← hh],
    simp }
end

@[simp, separation_logic]
lemma tptr.recast_recast {α β γ} (p : tptr α) : (p.recast β).recast γ = (p.recast γ : tptr γ) := rfl

@[simp, separation_logic]
lemma tptr.recast_eq {α} : Π (p : tptr α), (p.recast α) = p
| ⟨ _, _,_ ⟩ := rfl

instance : is_record value :=
{ repr := λ p v, p.get ↦ v,
  bytes := λ v, ⟨[v], rfl⟩,
  fixed_size := 1,
  pos_size := by norm_num,
  abstr := λ x, value_abstr _ x.property,
  right_inverse := λ ⟨[x],rfl⟩, rfl,
  raw_bytes_conversion := λ p x, by simp; refl }

def rec_bytes {α} [is_record α] (ls : list α) : list value :=
(ls.map (bytes' value)).join

lemma rec_bytes_cons {α} [is_record α] (x) (xs : list α) : rec_bytes (x :: xs) = bytes' value x ++ rec_bytes xs := rfl

lemma length_rec_bytes {α} [is_record α] (xs : list α) :
  length (rec_bytes xs : list value) = length xs * fixed_size value α :=
begin
  simp [rec_bytes], induction xs; simp [length,*,right_distrib],
  erw (bytes value xs_hd).property,
end

open «fixed_storable» list

lemma uninitialized' {α} [is_record α] (p : tptr α) :
  (∃∃ obj : α, p ⤇ obj) = (∃∃ bytes : list value, [| length bytes = fixed_size value α |] ⊛ p.recast _ ⤇ bytes) :=
by cases p; rw uninitialized

variable (value)

structure rec_entry :=
mk' ::
{α : Type*}
[S : is_record α]
(get : α)

attribute [instance] rec_entry.S

def rec_entry.mk_ {α : Type} [I : is_record α] (x : α) : rec_entry value := ⟨_,x⟩

instance : storable (rec_entry value) :=
{ repr := λ p x, p.recast _ ⤇ x.get,
  size := λ x, storable.size value x.get, }

variables {value}

def rec_entry_bytes : rec_entry value → list value
| (@rec_entry.mk' ._ α _inst get) := @bytes' value α _inst get

def rec_bytes' (ls : list (rec_entry value)) : list value :=
(ls.map (rec_entry_bytes)).join

-- end hProp

instance fixed_storable.word {α} [fixed_storable α] : fixed_storable (word α) :=
{ repr := λ p v, p.recast _ ⤇ v.val,
  fixed_size := fixed_size value α,
  pos_size := fixed_storable.pos_size value α }

def word.bytes {α} [fixed_storable α] : word α → word (word α)
| ⟨x,hx⟩ := ⟨x,hx⟩

def word.abstr {α} [fixed_storable α] : word (word α) → word α
| ⟨x,hx⟩ := ⟨x,hx⟩

-- @[simp, separation_logic]
-- lemma val_repr {val} (p : tptr (list val)) (vs : list val) : p ⤇ vs = p.get ↦ vs :=
-- begin
--   cases p, dsimp [storable.repr,tptr.recast],
--   induction vs generalizing p, refl,
--   rw maplets_cons, simp [list_repr,tptr.add,fixed_size,*], refl
-- end

instance word.is_record {α} [fixed_storable α] : is_record (word α) :=
{ bytes := word.bytes,
  abstr := word.abstr,
  right_inverse := λ ⟨x,hx⟩, rfl,
  raw_bytes_conversion := λ ⟨_,_,p⟩ ⟨x,hx⟩,
    by { simp [tptr.recast_mk,word.bytes]; refl } }

def equiv.is_record {α β} (f : β → α) (g : α → β) (hfg : left_inverse f g) [is_record α] : is_record β :=
{ repr := λ p x, p.recast _ ⤇ f x,
  bytes := bytes value ∘ f,
  abstr := g ∘ abstr,
  fixed_size := fixed_size value α,
  pos_size := fixed_storable.pos_size value α,
  is_fixed := λ x, rfl,
  right_inverse := λ ⟨x,hx⟩, by dsimp [bytes]; rw [hfg];
                               exact (is_record.right_inverse value α ⟨x,hx⟩),
  raw_bytes_conversion := λ ⟨_,_,p⟩ x, raw_bytes_conversion ⟨value,α,p⟩ (f x)
 }

lemma repr_map_bytes {α} [is_record α] (p : tptr (list (word α))) (xs : list α) :
  p ⤇ xs.map (bytes value) = (p.recast _ ⤇ xs : hProp) :=
show list_repr p (xs.map (bytes value)) = list_repr (p.recast _) xs,
begin
  rw [list_repr_map],
  { intros, symmetry, -- erw val_repr, cases q,
    rw [raw_bytes_conversion], refl },
  intro, simp [fixed_storable.is_fixed], refl
end

lemma repr_map_abstr {α} [is_record α] (p : tptr (list α)) (xs : list (word α)) :
  p ⤇ xs.map abstr = (p.recast _ ⤇ xs) :=
begin
  have := repr_map_bytes (p.recast _) (xs.map abstr),
  simp at this, rw ← this, congr,
  transitivity xs.map id,
  { congr, ext, exact is_record.right_inverse value α x },
  { simp only [list.map_id] }
end

@[separation_logic]
lemma list_repr_recast {α β} (γ) [storable α] (vs : list α)
  (p : tptr (list α)) (q : tptr β) :
  list_repr' p vs (q.recast γ) = list_repr' p vs q :=
begin
  cases q, dsimp [tptr.recast],
  induction vs generalizing p, refl, simp [list_repr',*]
end

end separation

namespace tactic

variables {value : Type}
open separation separation.hProp

local notation `hProp` := hProp value
setup_tactic_parser

lemma shrink_impl (l m r : hProp) {p q : hProp}
  (h₀ : l ⊛ m = p) (h₁ : r ⊛ m = q) (h₂ : l =*> r) :
  p =*> q :=
h₀ ▸ (h₁ ▸ and_impl_and h₂ $ impl_refl _)

lemma split_impl (p₀ p₁ q₀ q₁ : hProp) {p q : hProp}
  (h₀ : p₀ ⊛ p₁ = p) (h₁ : q₀ ⊛ q₁ = q) (h₂ : p₀ =*> q₀) (h₃ : p₁ =*> q₁) :
  p =*> q :=
h₀ ▸ (h₁ ▸ and_impl_and h₂ h₃)

meta def parse_assert' : expr → tactic (dlist expr)
| `(%%p ⊛ %%q) := (++) <$> parse_assert' p <*> parse_assert' q
| `(emp) := pure dlist.empty
| p := pure $ dlist.singleton p

meta def parse_assert (e : expr) : tactic (list expr) :=
dlist.to_list <$> parse_assert' e

meta def mk_assert (val : expr) : list expr → expr
| [] := @expr.const tt ``emp [] val
| [x] := x
| (x::xs) :=
@expr.const tt ``hProp.and [] val x (mk_assert xs)

meta def ac_refl_aux : tactic unit :=
do `[dsimp { fail_if_unchanged := ff }],
   (lhs, rhs) ← target >>= match_eq,
   xs ← parse_assert lhs,
   with_context!"{target}" $ do
     xs.mmap' $ λ x, generalize x >> intro1,
     cc <|> fail "ac_refl_aux"

meta def ac_refl' : tactic unit :=
do try (applyc ``impl_of_eq),
   -- target >>= instantiate_mvars >>= change,
   -- `[dsimp],
   with_context!"{target}" $ do
   cc <|>
     ac_refl_aux
     -- <|>
     -- fail!"ac_refl': {target}\nmeta vars: {expr.list_meta_vars <$> target}"

meta def find_lift : list expr → tactic (option (expr × list expr))
| [] := pure none
| (x@`(separation.hProp.lift _) :: xs) := pure (some (x, xs))
| (x :: xs) :=
  do some (y, ys) ← find_lift xs | pure none,
     pure (some (y, x::ys))

@[replaceable]
meta def s_intro' (n : parse $ ident_ <|> pure `_) : tactic unit :=
do `[simp only [and_p_exists_distrib_left,and_p_exists_distrib_right]
               { fail_if_unchanged := ff }],
   `(@impl %%val %%p %%q) ← target | fail "Expecting separation logic specification",
   match p with
   | `(p_exists _) :=
     do applyc ``exists_impl,
        intro n >> pure ()
   | _ :=
   do xs ← parse_assert p,
      some (x, xs) ← find_lift xs | failed,
      let p' := mk_assert val (x :: xs),
      g ← mk_app `eq [p,p'] >>= mk_meta_var,
      gs ← get_goals, set_goals [g],
      `[simp only [and_emp,emp_and] { fail_if_unchanged := ff } ],
      done <|> ac_refl',
      set_goals gs,
      get_assignment g >>= rewrite_target,
      applyc ``lift_and_impl <|> applyc ``lift_impl,
      intro n, pure ()
   end

meta def interactive.s_intro (n : parse $ ident_ <|> pure `_) : tactic unit :=
s_intro n

@[interactive]
meta def s_intros : parse ident_* → tactic unit
| [] := repeat (s_intro `_)
| ns := ns.mmap' s_intro

@[interactive]
meta def s_existsi (wit : parse pexpr_list_or_texpr) : tactic unit :=
wit.mmap' $ λ w,
  do `(%%p =*> %%q) ← target,
     `[simp only [and_p_exists_distrib_left,and_p_exists_distrib_right] { fail_if_unchanged := ff }],
     refine ``(impl_exists %%w _) <|>
       do `[simp only [lift_and_iff_p_exists] { single_pass := tt } ],
          `[simp only [and_p_exists_distrib_left,and_p_exists_distrib_right]
                 { fail_if_unchanged := ff } ],
          refine ``(impl_exists %%w _)

lemma lin_assert {p q : hProp} (pp : Prop) (h : p =*> [| pp |] ⊛ p) (h' : pp → p =*> q) : p =*> q :=
impl_trans h
  (by s_intro h; exact h' h)

lemma lin_assert' {p q : hProp} (pp : Prop) (h : p =*> [| pp |] ⊛ True) (h' : pp → p =*> q) : p =*> q :=
begin
  transitivity [| pp |] ⊛ p,
  { rw lift_p_and_and, apply impl_and h (impl_refl _) },
  { s_intro h, exact h' h }
end

@[interactive]
meta def s_assert (h : parse $ ident? <* tk ":") (e : parse texpr) : tactic unit :=
let h := h.get_or_else `this in
refine ``(lin_assert' %%e _ _); [skip, ()<$intro h]

meta def find_frame' (e : expr) : list expr → tactic (list expr)
| [] := fail "frame not found"
| (x :: xs) :=
  xs <$ unify e x <|>
  list.cons x <$> find_frame' xs

meta def find_frame_aux : list expr → list expr → tactic (list expr)
| [] xs := pure xs
| (x::xs) ys :=
  do ys' ← find_frame' x ys,
     find_frame_aux xs ys'

meta def find_diff : list expr → list expr → tactic (list expr × list expr × list expr)
| [] xs := pure ([], [], xs)
| (x::xs) ys :=
  do (b,ys') ← prod.mk tt <$> find_frame' x ys <|> pure (ff,ys),
     (l,m,r) ← find_diff xs ys',
     if b
       then pure (l,x::m,r)
       else pure (x::l,m,r)

/--
`find_frame e e'` returns `r` and `pr` such that `pr : e ⊛ r = e'`
-/
meta def find_frame (e e' : expr) : tactic (expr × expr) :=
do `(«hProp» %%val) ← infer_type e,
   le ← parse_assert e,
   le' ← parse_assert e',
   lr ← find_frame_aux le le',
   let r := mk_assert val lr,
   t ← to_expr ``(%%e ⊛ %%r = %%e') >>= instantiate_mvars,
   (_,pr) ← solve_aux t
     (`[simp only [emp_and,and_emp] { fail_if_unchanged := ff } ]; ac_refl'),
   pure (r,pr)

@[replaceable]
meta def s_shrink' : tactic unit :=
do `(%%p =*> %%q) ← target,
   `(«hProp» %%val) ← infer_type p,
   ps ← parse_assert p,
   qs ← parse_assert q,
   (l,m,r) ← find_diff ps qs,
   guard (¬ m.empty) <|> fail "no common clauses",
   let l := mk_assert val l,
   let m := mk_assert val m,
   let r := mk_assert val r,
   to_expr ``(shrink_impl %%l %%m %%r) >>= apply,
   iterate_exactly 2 $ solve1 $ interactive.hide_meta_vars { } $ λ _, do
   { `[simp { fail_if_unchanged := ff } ],
     done <|> cc },
   try reflexivity

attribute [interactive] s_shrink

@[replaceable]
meta def entailment' : tactic unit :=
focus1 $
assumption <|>
do intros,
   target >>= instantiate_mvars >>= change,
   when_tracing `separation.failed_spec (trace "A" >> trace_state),
   with_context!"• A: {target}" $ do
     `[simp [hProp.and_p_exists_distrib_left,hProp.and_p_exists_distrib_right] with separation_logic
       { fail_if_unchanged := ff } ],
     when_tracing `separation.failed_spec (trace "B" >> trace_state),
     with_context!"• B: {try_core target}" $ do
       iterate_at_most 10 $ do
         { `(_ =*> p_exists _) ← target,
           applyc ``impl_exists },
       when_tracing `separation.failed_spec (trace "C" >> trace_state),
       with_context!"• C: {try_core target}" $ do
       done <|>
         assumption <|>
         ac_refl'
     -- s_shrink <|>
  -- (try (applyc ``impl_of_eq); ac_refl) <|>

attribute [interactive] entailment

meta def s_apply' (e : expr) : tactic unit :=
do t ← infer_type e,
   (args,`(%%p =*> %%q)) ← mk_meta_pis t,
   let e := e.mk_app args,
   `(%%p' =*> %%q') ← target,
   frp ← some <$> find_frame p p' <|> pure none,
   frq ← some <$> find_frame q q' <|> pure none,
   match frp, frq with
   | some (pr,pp), some (qr,qp) := refine ``(split_impl %%p %%pr %%q %%qr %%pp %%qp %%e _)
   | some (pr,pp), none := refine ``(impl_trans (shrink_impl %%p %%pr %%q %%pp rfl %%e) _)
   | none, some (qr,qp) := refine ``(impl_trans _ (shrink_impl %%p %%qr %%q rfl %%qp %%e))
   | none, none := fail!"No match found for `{e} : {t}`"
   end,
   try (reflexivity <|> applyc ``impl_True)

@[interactive]
meta def s_apply : parse types.pexpr_list_or_texpr → tactic unit :=
mmap' $ to_expr >=> s_apply'

@[interactive]
meta def s_assumptions : tactic unit :=
do cxt ← local_context,
   focus1 $ cxt.for_each $ λ l, try $ s_apply' l

@[interactive]
meta def s_assumption : tactic unit :=
do cxt ← local_context,
   focus1 $ cxt.any_of $ λ l, try $ s_apply' l

@[interactive]
meta def s_show (p : parse texpr) : tactic unit :=
do g ← to_expr p >>= mk_meta_var,
   s_apply' g

lemma prop_proof {p : Prop} {q : hProp} (h : p) : q =*> [| p |] ⊛ True :=
impl_lift_and h impl_True

lemma prop_proof' {p : Prop} {q : hProp} (h : p) : q =*> True ⊛ [| p |] :=
impl_trans (prop_proof h) (impl_of_eq $ hProp.and_comm _ _)

lemma prop_impl_False {q : hProp} (h : false) : q =*> False :=
impl_trans (prop_proof h) (by simp)

@[interactive]
meta def prop (ls : parse ident_*) : tactic unit :=
do s_intros ls,
   applyc ``prop_proof
   <|> applyc ``prop_proof'
   <|> applyc ``prop_impl_False

end tactic

namespace separation

open hProp list

variables {value : Type} {α : Type*} {β : Type*} {γ : Type*}
include value
local notation `hProp` := hProp value
local notation `tptr` := tptr value

lemma p_exists_one_point {q : α → hProp} (x : α)
  (h : ∀ y, q y =*> [|y = x|] ⊛ q y):
  p_exists q = q x :=
impl_antisymm
  (by { s_intros y, transitivity, apply h,
        s_intro hxy, rw hxy })
  (by { apply impl_exists x, refl } )

section storable

variables [storable value α]

lemma list_repr_and_list_repr_impl_list_repr'_concat {us vs : list α}
  (p q : tptr (list α)) (r : tptr β) :
  list_repr' p us q ⊛ list_repr' q vs r =*> list_repr' p (us ++ vs) r :=
begin
  induction us generalizing p,
  { simp [list_repr'],
    apply lift_and_impl, intro h, subst h },
  { simp [list_repr',hProp.and_assoc],
    apply and_impl_and (impl_refl _) (us_ih _) }
end

lemma list_repr_append {us vs : list α}
  (p : tptr (list α)) (r : tptr β) :
  list_repr' p (us ++ vs) r = list_repr' p us (p +. size value us) ⊛ list_repr' (p +. size value us) vs r :=
by induction us generalizing p; simp [list_repr',size,*,separation.hProp.and_assoc]

lemma list_repr_impl_le (p₀ : tptr (list α)) (p₁ : tptr β) (vs : list α) :
  list_repr' p₀ vs p₁ =*> [| p₀ ≤ p₁.recast _ |] ⊛ True :=
begin
  induction vs generalizing p₀,
  { simp [list_repr'], prop h, rw h },
  { simp [list_repr'], s_apply vs_ih, prop h,
    apply le_trans (le_offset _) h, }
end

lemma list_repr_impl_le' {p₀ p₁ : tptr (list α)} (vs : list α) :
  list_repr' p₀ vs p₁ =*> [| p₀ ≤ p₁ |] ⊛ True :=
list_repr_impl_le _ _ _

lemma list_repr_eq_of_gt {p q : tptr (list α)} {vs : list α} (h : q < p) :
  list_repr' p vs q = False :=
begin
  apply impl_antisymm _ (False_impl _),
  apply impl_trans (list_repr_impl_le' _),
  simp [not_le_of_gt h],
end

end storable

section fixed_storable

variables [fixed_storable value α]

lemma list_repr_self_impl_eq_nul (p₀ : tptr (list α)) (vs : list α) :
  list_repr' p₀ vs p₀ =*> [| vs = [] |] :=
begin
  induction vs generalizing p₀; simp [list_repr'],
  s_apply list_repr_impl_le, prop h, revert h,
  apply not_le_of_gt, simp, apply gt_offset_of_gt _ (fixed_storable.pos_size _ α),
end

lemma list_repr_self_impl_eq_nul' (p₀ : tptr (list α)) (vs : list α) :
  list_repr' p₀ vs (p₀.recast β) =*> [| vs = [] |] :=
(@list_repr_recast value _ _ β _ vs p₀ p₀).symm ▸ (list_repr_self_impl_eq_nul p₀ vs)

lemma list_repr_offset {vs : list α}
  (p : tptr (list α)) (n : ℕ) :
  list_repr' p vs (p +. n * fixed_size value α) = [| length vs = n |] ⊛ p ⤇ vs :=
begin
  induction vs generalizing n p,
  { have : p = p +. n * fixed_size value α ↔ 0 = n,
    { split; intro h,
      by_contradiction h',
      { replace h' := nat.pos_of_ne_zero (ne.symm h'),
        have h₂ : n * fixed_size value α > 0 := mul_pos h' (fixed_storable.pos_size _ _),
        exact offset_ne _ h₂ h.symm },
      { simp [h.symm] }, },
    simp [list_repr',this,*], },
  simp [list_repr',*], -- specialize vs_ih (n - 1) (p +. size value vs_hd),
  cases nat.eq_zero_or_pos n,
  { subst n,
    have : p < p +. fixed_size value α := gt_offset_of_gt _ _,
    simp [list_repr_eq_of_gt this], apply fixed_storable.pos_size },
  specialize vs_ih (n - 1) (p +. size value vs_hd),
  replace h := nat.succ_le_of_lt h,
  have := nat.mul_le_mul_right (fixed_size value α) h,
  simp at this,
  simp [nat.add_sub_cancel' this,nat.mul_sub_right_distrib] at vs_ih,
  rw [vs_ih, @eq_comm _ (length vs_tl), nat.sub_eq_iff_eq_add h, @eq_comm _ _ (length vs_tl + 1), nat.add_comm],
  ac_refl,
end

lemma recast_inj (p q : tptr α) : p.recast β = (q.recast β) ↔ p = q :=
by cases p; cases q; simp

def trashed (p : tptr α) : hProp :=
∃∃ trash : list value, [| length trash = fixed_size value α |] ⊛ p.recast _ ⤇ trash

def unused : tptr (list $ word value α) → ℕ → tptr β → hProp
| p 0 q := [| p = q.recast _ |]
| p (nat.succ n) q := trashed (p.recast α) ⊛ unused (p +. fixed_size value α) n q

@[simp, separation_logic]
lemma unused_recast (p : tptr (list $ word value α)) (q : tptr β) (n : ℕ) :
  unused p n (q.recast γ) = unused p n q :=
by induction n generalizing p; simp [unused,*]

@[simp]
lemma fixed_size_word : fixed_size value (word value α) = fixed_size value α := rfl

lemma unused_iff_exists (p : tptr (list (word value α))) (q : tptr β) (n : ℕ) :
  unused p n q = ∃∃ val : list (word value α), [| length val = n |] ⊛ list_repr' p val q :=
begin
  induction n generalizing p,
  { rw p_exists_one_point [], simp [unused,list_repr'],
    intros, s_intros h, apply impl_lift_and,
    rw ← length_eq_zero, exact h,
    apply impl_lift_and h (impl_refl _), },
  { rw [unused,n_ih,trashed,← exists_subtype],
    simp [and_p_exists_distrib_left,and_p_exists_distrib_right],
    apply impl_antisymm,
    { s_intros x xs Hxs, apply impl_exists (x :: xs),
      simp [Hxs,list_repr'], apply impl_refl _, },
    { s_intros xs Hxs, rw length_eq_succ at Hxs,
      rcases Hxs with ⟨y,ys,h,h'⟩, subst xs,
      apply impl_exists y, apply impl_exists ys, simp [list_repr',h'],
      refl } }
end

lemma unused_impl_le' {p₀ p₁ : tptr (list (word value α))} (n : ℕ) :
  unused p₀ n p₁ =*> [| p₀ ≤ p₁ |] ⊛ True :=
begin
  rw unused_iff_exists, s_intros val Hval,
  apply list_repr_impl_le
end

end fixed_storable

end separation
-- α

-- ```
-- section
-- variable [𝓛 : sep_logic]
-- include 𝓛
-- -- maintenant `hProp` et `tptr α` (le type des pointeurs typés qui pointent vers α)
-- -- réfèrent automatiquement α 𝓛 sans qu'on ait à créer de raccourcis
