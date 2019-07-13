
import data.finmap
import category_theory.category
import tactic.interactive
import tactic.tauto
import tactic.linarith
import tactic.omega
import tactic.monotonicity

namespace refinement

open category_theory

variables value : Type

@[reducible]
def ptr := ℕ

@[reducible]
def heap := finmap (λ _ : ptr, value)

def hProp := heap value → Prop

@[extensionality]
lemma hProp.ext {p q : hProp value} (H : ∀ h, p h ↔ q h) : p = q :=
by ext; apply H

-- local notation `heap` := heap value
-- local notation `hProp` := hProp value

def state := Σ t : Type*, t → hProp value

section value

variables {value}

def state.mk {t} (f : t → hProp value) : state value := ⟨t,f⟩

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

@[reducible]
def ST (s α : Type*) := state_t (s × heap value) set α

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

def maplet (x : ptr) (v : value) : heap value :=
finmap.singleton x v

def heap.mk (l : list (ptr × value)) : heap value :=
(l.map $ λ x : ptr × value, (⟨x.1,x.2⟩ : sigma $ λ _, value)).to_finmap

@[simp]
lemma heap.mk_nil : heap.mk [] = (∅ : heap value) := rfl

@[simp]
lemma heap.mk_cons (p v) (l : list (ptr × value)) : heap.mk ((p,v) :: l) = maplet p v ∪ heap.mk l := rfl

@[simp]
lemma mem_heap.mk (p) (l : list (ptr × value)) : p ∈ heap.mk l ↔ ∃ v, (p,v) ∈ l :=
iff.trans
  (finmap.mem_list_to_finmap _ _)
  (exists_congr $ λ v,
    by simp [list.mem_map]; split;
       [ { rintro ⟨a,b,h,⟨⟩,⟨⟩⟩, exact h },
         { intro h, refine ⟨_,_,h,rfl,rfl⟩ }])

open state_t

-- instance {α} : has_coe (option α) (ST value s α) := _

def read (p : ptr) : ST value s (ulift value) :=
do m ← get,
   match m.2.lookup p with
   | none := @monad_lift set _ _ _ ∅
   | (some x) := pure ⟨x⟩
   end

def assign (p : ptr) (v : value) : ST value s punit :=
modify (prod.map id $ finmap.insert p v)

def assign_vals (p : ptr) (vs : list value) : ST value s punit :=
modify $ prod.map id (∪ heap.mk (vs.enum.map $ prod.map (+p) id))

def choice (p : α → Prop) : ST value s α :=
@monad_lift set (state_t _ set) _ _ (p : set α)

def erase_all (p : ptr) (n : ℕ) (m : heap value) : heap value :=
(list.range n).foldl (λ m i, finmap.erase (p + i) m) m

@[simp] lemma erase_all_zero (p : ptr) (m : heap value) : erase_all p 0 m = m := rfl

lemma erase_all_succ (p : ptr) (n : ℕ) (m : heap value) : erase_all p n.succ m = finmap.erase (p+n) (erase_all p n m) :=
by simp [erase_all, list.foldl_eq_foldr' _ m (list.range _),list.range_concat]

lemma erase_all_one_add (p : ptr) (n : ℕ) (m : heap value) : erase_all p (1+n) m = finmap.erase (p+n) (erase_all p n m) :=
by rw add_comm; apply erase_all_succ p _ m

lemma erase_all_succ' (p : ptr) (n : ℕ) (m : heap value) : erase_all p n.succ m = finmap.erase p (erase_all (p+1) n m) :=
by { simp only [erase_all,list.range_succ_eq_map],
     rw [list.foldl_eq_of_comm',list.foldl_map],
     congr, simp only [add_zero, add_comm, add_left_comm],
     simp only [finmap.erase_erase, forall_3_true_iff, eq_self_iff_true] }

lemma erase_all_one_add' (p : ptr) (n : ℕ) (m : heap value) : erase_all p (1+n) m = finmap.erase p (erase_all (p+1) n m) :=
by rw add_comm; apply erase_all_succ' p _ m

open list nat

lemma mem_erase_all (p p' : ptr) (m : heap value) : Π {n}, p ∈ erase_all p' n m ↔ ¬ p ∈ range' p' n ∧ p ∈ m
| 0 := by simp [erase_all_zero]
| (succ n) := by { simp only [erase_all_succ, mem_cons_iff, add_comm, mem_range', finmap.mem_erase, ne.def, add_left_comm, mem_erase_all, not_and_distrib],
                   repeat { rw ← and_assoc }, apply and_congr _ (iff.refl _),
                   clear mem_erase_all, dsimp [ptr] at p p', omega nat }

def alloc (vs : list value) : ST value s (ulift ptr) :=
do ⟨_,m⟩ ← get,
   p ← choice $ λ p : ulift ptr, ∀ i < vs.length, (p.down + i : ℕ) ∉ m,
   assign_vals p.down vs,
   pure p

def dealloc (p : ptr) (n : ℕ) : ST value s punit :=
do ⟨_,m⟩ ← get,
   modify $ prod.map id $ erase_all p n

def emp : hProp value := λ h, h = ∅

open finmap

def add (x y : option (heap value)) : option (heap value) :=
do x ← x,
   y ← y,
   if disjoint x y then pure $ x ∪ y else none

def and (x y : hProp value) : hProp value
| h := ∃ h₀ h₁, some h = add (some h₀) (some h₁) ∧ x h₀ ∧ y h₁

def lift (p : Prop) : hProp value
| h := p ∧ emp h

notation `[| ` p ` |]` := lift p

lemma lift_eq_emp {p} (h : p) : [| p |] = @emp value :=
by { funext h', ext, simp [lift,h] }

infixr ` ⊛ `:55 := and

infixr ` ⊗ `:55 := add

lemma disjoint_iff {h h' : heap value} : disjoint h h' ↔ ∃ h'', some h'' = some h ⊗ some h' :=
by by_cases disjoint h h'; simp only [add, *, option.some_bind, exists_false, if_false, if_true, true_iff]; exact ⟨_,rfl⟩

lemma disjoint_of_add {h h' h'' : heap value} : some h'' = some h ⊗ some h' → disjoint h h' :=
λ HH, disjoint_iff.mpr ⟨_, HH⟩

@[simp]
lemma emp_and (p : hProp value) : emp ⊛ p = p :=
begin
  ext; simp [emp,and,(∈),set.mem,add]; split,
  { simp, introv h₀ h₁, subst h₁,
    simp [disjoint_empty,pure] at h₀, subst h₀, exact id },
  { intro hp, existsi [(∅ : finmap _),h],
    rw [if_pos (disjoint_empty h)], simp,
    exact ⟨rfl, hp⟩ }
end

lemma add_assoc (h₀ h₁ h₂ : option (heap value)) : (h₀ ⊗ h₁) ⊗ h₂ = h₀ ⊗ (h₁ ⊗ h₂) :=
begin
  simp only [add] with monad_norm; congr; ext : 1; congr; ext : 1,
  split_ifs,
  { simp, congr, ext : 1,
    split_ifs; simp [disjoint_union_left] at h_1,
    { simp, rw [if_pos,finmap.union_assoc],
      simp [disjoint_union_right],
      exact ⟨h,h_1.1⟩ },
    { exfalso, apply h_2 h_1.2 },
    simp, split_ifs,
    { exfalso, rw disjoint_union_right at h_3,
      apply h_1 h_3.2 h_2, },
    { refl },
    simp },
  simp, cases h₂,
  { refl },
  change none = pure h₂ >>= _, simp,
  split_ifs,
  { simp, split_ifs,
    exfalso, rw disjoint_union_right at h_2, apply h h_2.1,
    refl },
  refl
end

lemma add_comm (h₀ h₁ : option (heap value)) : h₀ ⊗ h₁ = h₁ ⊗ h₀ :=
begin
  cases h₀; cases h₁; try { refl },
  simp only [add, disjoint.symm_iff h₀, option.some_bind]; split_ifs,
  ext : 1, simp only [ext_iff,pure], rw finmap.union_comm_of_disjoint,
  symmetry, assumption, refl
end

instance : is_associative _ (@add value) := ⟨ add_assoc ⟩
instance : is_commutative _ (@add value) := ⟨ add_comm ⟩


lemma and_comm (p q : hProp value) : p ⊛ q = q ⊛ p :=
funext $ λ h, by { dsimp [and], rw exists_swap, ext, repeat { apply exists_congr; intro },
                   rw [add_comm,and_comm (p a_1)] }

instance and.is_commutative : is_commutative _ (@and value) := ⟨ and_comm ⟩

@[simp]
lemma and_emp (p : hProp value) : p ⊛ emp = p :=
by rw [and_comm,emp_and]

def And {α} (p : α → hProp value) : list α → hProp value
| [] := emp
| (x :: xs) := p x ⊛ And xs

def p_exists {α} (p : α → hProp value) : hProp value
| h := ∃ x, p x h

notation `∃∃ ` binders `, ` r:(scoped P, p_exists P) := r

def maplets : ptr → list value → hProp value
| p [] := emp
| p (v :: vs) := (= maplet p v) ⊛ maplets (p+1) vs

infix ` ↦ `:60 := maplets

open list

/-
 * framing
 * assignment
 * alloc
 * dealloc
 * sequencing
 * loop
-/

lemma union_eq_add_of_disjoint {h h' : heap value} (H₀ : disjoint h h') :
  some (h ∪ h') = some h ⊗ some h' :=
by simp [add,if_pos H₀]; refl

lemma eq_union_of_eq_add {h h' h'' : heap value} : some h'' = some h ⊗ some h' → h'' = h ∪ h' :=
λ HH, option.some.inj (eq.trans HH (union_eq_add_of_disjoint (disjoint_of_add HH)).symm)

@[simp]
lemma mem_maplet (p q : ptr) (v : value) : p ∈ maplet q v ↔ p = q :=
by simp only [maplet, not_mem_empty, finmap.mem_singleton, iff_self, or_false]

lemma maplets_eq (p : ptr) (vs : list value) (h : heap value) : (p ↦ vs) h ↔ h = heap.mk (vs.enum_from p) :=
begin
  induction vs generalizing p h; simp [maplets,emp,map,enum_from],
  simp [map,to_finmap_cons,and,vs_ih], split,
  { rintro ⟨h₀,h₁,hh₀,hh₁,hh₂⟩, rw [← hh₁,← hh₂], apply eq_union_of_eq_add hh₀ },
  { intro hh, refine ⟨_,_,_,rfl,rfl⟩, rw [← union_eq_add_of_disjoint, ← hh],
    rintro _ _, simp [] at H ⊢, subst x, intros v h,
    replace h := (mem_enum_from _ h).1, apply nat.not_succ_le_self _ h }
end

lemma and_assoc (p q r : hProp value) : (p ⊛ q) ⊛ r = p ⊛ q ⊛ r :=
by { ext : 1; dsimp [and,(∈),set.mem],
     split,
     { rintros ⟨h₀,h₁,Hx,⟨h₂,h₃,HH,Hp,Hq⟩,Hr⟩,
       have : disjoint h₃ h₁,
       { by_contradiction,
         rw [HH,add_assoc] at Hx, simp [add,if_neg,a] at Hx,
         exact Hx },
       refine ⟨_, h₃ ∪ h₁, _, Hp, _, _, _, Hq, Hr⟩,
       { rw [Hx,HH,add_assoc,union_eq_add_of_disjoint this] },
       { rw union_eq_add_of_disjoint this } },
     { rintro ⟨h₀,h₁,Hx,Hp,h₂,h₃,Hh₁,Hq,Hr⟩,
       have : disjoint h₀ h₂,
       { by_contradiction,
         rw [Hh₁,← add_assoc] at Hx, simp [add,if_neg,a] at Hx,
         exact Hx },
       refine ⟨h₀ ∪ h₂,_,_,⟨_,_,_,Hp,Hq⟩,Hr⟩,
       { rw [Hx,Hh₁,union_eq_add_of_disjoint this,add_assoc] },
       { rw union_eq_add_of_disjoint this } } }

instance and.is_associative : is_associative _ (@and value) := ⟨ and_assoc ⟩

@[simp]
lemma And_append {α} (p : α → hProp value) (xs ys : list α) : And p (xs ++ ys) = And p xs ⊛ And p ys :=
by induction xs; dsimp [And]; [rw emp_and, rw [xs_ih,and_assoc]]

@[simp]
lemma And_map {α β} (p : α → hProp value) (f : β → α) : Π (xs : list β), And p (map f xs) = And (p ∘ f) xs
| [] := rfl
| (x :: xs) := by rw [map,And,And,And_map]

def nth' {α} : ℕ → list α → list α
| 0 [] := []
| 0 (x :: xs) := [x]
| (succ n) [] := []
| (succ n) (x :: xs) := nth' n xs

lemma exists_nth'_eq_of_lt (vs : list α) (i : ℕ) (h : i < length vs) : ∃ x, nth' i vs = [x] :=
begin
  induction vs generalizing i, cases h, cases i; dsimp [nth'], exact ⟨_,rfl⟩,
  apply vs_ih, apply lt_of_succ_lt_succ h
end

lemma nth'_map {α β} (f : α → β) (vs : list α) (i : ℕ) : nth' i (vs.map f) = (nth' i vs).map f :=
begin
  induction vs generalizing i, cases i; refl,
  cases i; dsimp [map,nth']; [refl, exact vs_ih _]
end

lemma nth'_enum {α} (vs : list α) (i : ℕ) : nth' i vs.enum = (nth' i vs).enum_from i :=
begin
  suffices : nth' i (enum_from 0 vs) = enum_from (0 + i) (nth' i vs),
  { dsimp [enum], rw [this,zero_add] },
  generalize : 0 = k,
  induction vs generalizing i k, cases i; refl,
  cases i; dsimp [enum_from,nth'], refl, rw [vs_ih,succ_eq_add_one], ac_refl
end

lemma maplets_eq_And (p : ptr) (vs : list value) : (p ↦ vs) = And (λ i, p+i ↦ nth' i vs) (range vs.length) :=
begin
  induction vs generalizing p,  refl,
  simp [maplets], simp only [nat.add_comm 1,range_succ_eq_map,And,vs_ih,And_map,(∘),nth'],
  congr' 1, ext, simp [maplets], simp [succ_eq_add_one]
end

lemma disjoint_maplet (p) (v : value) (frame : heap value) : disjoint (maplet p v) frame ↔ ¬ p ∈ frame :=
begin
  split,
  { simp [disjoint.symm_iff], intros h h',
    specialize h _ h', simp only [maplet,finmap.mem_singleton] at h, exact h rfl },
  { intros h p' h', simp only [maplet,finmap.not_mem_empty,finmap.mem_singleton] at h',
    subst h', exact h }
end

lemma maplet_add (p : ptr) (v : value) (h : heap value) (hp : p ∉ h) :
  some (maplet p v) ⊗ some h = some (h.insert p v) :=
by rw ← union_eq_add_of_disjoint; [refl, { rw disjoint_maplet; exact hp }]

lemma empty_add (h : heap value) :
  some ∅ ⊗ some h = some h :=
by rw [← union_eq_add_of_disjoint,empty_union]; apply disjoint_empty

lemma add_empty (h : heap value) :
  some h ⊗ some ∅ = some h :=
by rw [add_comm,empty_add]

lemma add_eq_some (x y : option (heap value)) (z : heap value) : some z = x ⊗ y → ∃ x', some x' = x :=
by intro h; cases x; [ { simp [add] at h, cases h }, exact ⟨_,rfl⟩ ]

def holds (h frame : heap value) (p : hProp value) : Prop :=
∃ h₀, some h = some h₀ ⊗ some frame ∧ p h₀

def holds' (h : heap value) (p : hProp value) : Prop :=
∃ h', holds h h' p

infix ` ⊨ `:60 := holds'

-- def spec_alloc (s) (free : set ptr) (p : hProp value) (m : ST value s α) (q : α → hProp value) : Prop :=
-- ∀ σ σ' h h' frame x, (x,σ',h') ∈ m.run (σ,h) → (∀ p ∈ free, ¬ p ∈ h) → holds h frame p → holds h' frame (q x)

def spec (s) (p : hProp value) (m : ST value s α) (q : α → hProp value) : Prop :=
∀ ⦃σ σ' h h' frame x⦄, (x,σ',h') ∈ m.run (σ,h) → holds h frame p → holds h' frame (q x)

def spec' (s) (p : hProp value) (m : ST value s α) (q : hProp value) : Prop :=
spec s p m (λ _, q)

lemma punit_eq_iff (x y : punit) : x = y ↔ true := by casesm* punit; simp

@[simp]
lemma mem_run_modify (x : punit) (σ σ' : s) (h h' : heap value) (f : s → s) (g : heap value → heap value) :
  (x,σ',h') ∈ (modify (prod.map f g) : ST value s punit).run (σ,h) ↔ σ' = f σ ∧ h' = g h :=
by simp only [modify,state_t.modify,pure,state_t.run,punit_eq_iff, true_and, id.def, iff_self, set.mem_singleton_iff, prod.mk.inj_iff, prod.map]

@[simp]
lemma mem_bind_run {β} (x' : β) (σ σ' : s) (h h' : heap value) (f : ST value s α) (g : α → ST value s β) :
  (x',σ',h') ∈ (f >>= g).run (σ,h) ↔ (∃ x'' σ'' h'', (x'',σ'',h'') ∈ f.run (σ,h) ∧ (x',σ',h') ∈ (g x'').run (σ'',h'')) :=
by simp only [exists_prop, state_t.run_bind, set.mem_Union, set.bind_def, iff_self, prod.exists]

@[simp]
lemma mem_choice_run (x' : α) (σ σ' : s) (h h' : heap value) (p : α → Prop) :
  (x',σ',h') ∈ (choice p : ST value s α).run (σ,h) ↔ p x' ∧ σ' = σ ∧ h' = h :=
by simp only [choice, set.mem_Union, set.bind_def, set.mem_singleton_iff, prod.mk.inj_iff, run_monad_lift, set.pure_def];
   split; simp only [and_imp, exists_imp_distrib]; intros; try { subst x' }; repeat { split }; assumption

@[simp]
lemma mem_run_pure (x x' : α) (σ σ' : s) (h h' : heap value) :
  (x',σ',h') ∈ (pure x : ST value s α).run (σ,h) ↔  x' = x ∧ σ' = σ ∧ h' = h :=
by simp only [iff_self, set.mem_singleton_iff, prod.mk.inj_iff, set.pure_def, state_t.run_pure]

@[simp]
lemma mem_run_get (x' : s × heap value) (σ σ' : s) (h h' : heap value) :
  (x',σ',h') ∈ (get : ST value s _).run (σ,h) ↔  x' = (σ, h) ∧ σ' = σ ∧ h' = h :=
by simp only [get, monad_state.lift, pure, set.mem_singleton_iff, prod.mk.inj_iff, id.def, state_t.run_get]

@[simp]
lemma mem_run_read (x' : ulift value) (p : ptr) (σ σ' : s) (h h' : heap value) :
  (x',σ',h') ∈ (read p : ST value s _).run (σ,h) ↔ h.lookup p = some x'.down  ∧ σ' = σ ∧ h' = h :=
begin
  simp only [read, monad_state.lift, pure, exists_prop, set.mem_Union, set.bind_def, mem_run_get, prod.mk.inj_iff, run_bind, prod.exists], split,
  { rintro ⟨a,b,σ'',h'',H,H'⟩, cases h : (lookup p b); rw h at H'; simp [read] at H', cases H', casesm* _ ∧ _,
    subst_vars, rw h, exact ⟨rfl,rfl,rfl⟩ },
  { rintro ⟨h,⟨⟩,⟨⟩⟩, refine ⟨_,_,_,_,⟨⟨rfl,rfl⟩,rfl,rfl⟩,_⟩, simp [h,read], cases x', refl }
end

@[simp]
lemma heap.mem_mk (p : ptr) (vs : list (ptr × value)) : p ∈ heap.mk vs ↔ p ∈ vs.map prod.fst :=
by { simp only [heap.mk,mem_list_to_finmap,_root_.and_comm (_ ∈ vs),_root_.and_assoc,  list.mem_map,
                iff_self, exists_eq_left, exists_and_distrib_left, heq_iff_eq, list.map, prod.exists] }

instance : has_le (heap value) :=
{ le := λ x y, ∀ a b, x.lookup a = some b → y.lookup a = some b }

instance : preorder (heap value) :=
{ le_refl := λ h a b H, H,
  le_trans := λ h₀ h₁ h₂ H H' p _ HH, H' _ _ (H _ _ HH),
  .. refinement.has_le
  }

lemma le_of_add_eq_some {h₀ h₁ : heap value} (h' : heap value) (H : some h₁ = some h₀ ⊗ some h') : h₀ ≤ h₁ :=
λ p v HH,
have HH' : _, from eq_union_of_eq_add H,
by rw [HH',lookup_union_left,HH]; apply mem_of_lookup_eq_some HH

lemma erase_all_union_mk_self (p : ptr) (vs : list value) (h : heap value) (H : heap.mk (vs.enum_from p) ≤ h) :
  erase_all p (length vs) h ∪ heap.mk (vs.enum_from p) = h :=
begin
  induction vs generalizing p; simp [length,enum_from,erase_all_one_add',union_assoc],
  rw [← union_assoc,maplet,erase_union_singleton,vs_ih],
  { transitivity'; [skip, exact H], dsimp [enum_from],
    intros p' v Hp, rw [lookup_union_right,Hp],
    simp [maplet], intro Hp', subst p',
    replace Hp := mem_of_lookup_eq_some Hp,
    simp at Hp, change ℕ at p, clear_except Hp,
    replace Hp := Hp.1, omega nat, },
  clear vs_ih, replace H : h.lookup p = some vs_hd,
  { apply H, simp [enum_from,maplet,lookup_singleton_eq] },
  generalize hq : p + 1 = q,
  have : p < q,
  { rw ← hq, apply lt_add_one },
  clear hq, induction vs_tl with v vs,
  { simp [H] },
  { simp [length,erase_all_one_add], rw [lookup_erase_ne,vs_tl_ih],
    apply ne_of_lt, linarith }
end

lemma mem_of_mem_of_le {h₀ h₁ : heap value} (H : h₀ ≤ h₁) : ∀ x ∈ h₀, x ∈ h₁ :=
by intros p; rw [mem_iff,mem_iff]; apply exists_imp_exists; exact H p

lemma insert_maplet  (p) (v v' : value) : finmap.insert p v (maplet p v') = maplet p v :=
finmap.insert_singleton_eq

lemma disjoint_mono {ha hb ha' hb' : heap value} (H₀ : ha' ≤ ha) (H₁ : hb' ≤ hb) :
  disjoint ha hb → disjoint ha' hb' :=
begin
  intros H₂ x H₃ H₄,
  replace H₃ := mem_of_mem_of_le H₀ _ H₃,
  replace H₄ := mem_of_mem_of_le H₁ _ H₄,
  exact H₂ _ H₃ H₄,
end

lemma holds_union_and {h h' frame : heap value} {p q : hProp value}
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

lemma add_inj {h₀ h₁ : option (heap value)} (hh : option (heap value)) (hh₀ hh₁ : heap value)
  (H₀ : some hh₀ = h₀ ⊗ hh) (H₁ : some hh₁ = h₁ ⊗ hh) (H₂ : h₀ ⊗ hh = h₁ ⊗ hh) :
  h₀ = h₁ :=
begin
  cases h₀; [skip, cases h₁], cases H₀, cases H₁, cases hh, cases H₀,
  rw [← union_eq_add_of_disjoint (disjoint_of_add H₀),← union_eq_add_of_disjoint (disjoint_of_add H₁),option.some_inj,finmap.union_cancel] at H₂, rw H₂,
  all_goals { apply disjoint_of_add, assumption },
end

lemma holds_of_holds_union_and {h h' frame : heap value} {p q : hProp value}
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

lemma holds_of_holds_union_iff {h h' frame : heap value} {p q : hProp value}
  (H₁ : q h') (H₂ : disjoint h h') (H₃ : ∀ h'', q h'' → h'' = h') :
  holds (h ∪ h') frame (p ⊛ q) ↔ holds h frame p :=
⟨ λ H₀, holds_of_holds_union_and H₀ H₁ H₂ H₃, λ H₀,holds_union_and H₀ H₁ H₂ ⟩

lemma assign_spec (p : ptr) (v v' : value) :
      spec' s (p ↦ [v]) (assign p v') (p ↦ [v']) :=
begin
  simp [spec',spec,assign,mem_run_modify],
  introv _ hh hh', simp only [hh', holds, maplets, add, disjoint_maplet, pure, add_zero, option.some_bind, exists_eq_right, and_emp],
  split_ifs, exact id, intro hh'', simp only [hh'', insert_union, insert_maplet],
end

-- lemma And_frame {α} {p : hProp value} {m : ST value s α} {q : α → hProp value}
--   (h : ) :
--   spec s p m q := _

lemma read_spec (p : ptr) (v : value) :
  spec s (p ↦ [v]) (read p) (λ r, [|r.down = v|] ⊛ (p ↦ [v])) :=
begin
  simp [spec], introv Hrun, rintro ⟨ ⟩ ⟨ ⟩ h', rw [lift_eq_emp,emp_and], exact h',
  simp [holds,maplets_eq] at h', rw [le_of_add_eq_some _ h' p v _,option.some_inj] at Hrun,
  exact Hrun.symm, rw [heap.mk,lookup_list_to_finmap], dsimp [enum_from,map], rw lookup_cons_eq
end

lemma assign_array_spec (p : ptr) (vs : list value) (v' : value) (i : ℕ)
      (hi : i < length vs) :
      spec' s (p+i ↦ nth' i vs) (assign (p+i) v') (p+i ↦ [v']) :=
begin
  have := exists_nth'_eq_of_lt vs _ hi,
  cases this with _ h, rw h, apply assign_spec
end

lemma read_array_spec' (p : ptr) (i : ℕ) (vs : list value) (H : i < length vs) :
  spec s (p+i ↦ nth' i vs) (read (p + i)) (λ r, [| [r.down] = nth' i vs |] ⊛ (p+i ↦ nth' i vs)) :=
begin
  have := exists_nth'_eq_of_lt vs _ H,
  cases this with _ h, rw h, simp, apply read_spec
end

lemma holds_of_holds_and (h h₀ : heap value) {p q : hProp value} :
  holds h h₀ (p ⊛ q) ↔ (∃ h₁, holds h₁ h₀ q ∧ holds h h₁ p) :=
begin
  split; simp only [holds, and, and_imp, exists_imp_distrib],
  { introv hh hx hp hq,
    rw hx at hh, clear hx,
    have hh : ∃ k, some k = some x_2 ⊗ some h₀,
    { apply add_eq_some _ (some x_1) h,
      rw [add_comm,← add_assoc,hh] },
    cases hh with k hk,
    existsi k, split,
    exact ⟨_,hk,hq⟩,
    refine ⟨_,_,hp⟩, rw [hk,hh,add_assoc] },
  { introv hh hx hh' hp,
    rw hh at hh', clear hh,
    have hh : ∃ k, some k = some x_2 ⊗ some x_1,
    { apply add_eq_some _ (some h₀) h,
      rw [add_assoc,hh'] },
    cases hh with k hk,
    existsi k, rw [hk,add_assoc],
    existsi hh',
    refine ⟨_,_,rfl,hp,hx⟩ }
end

lemma frame_rule (m : ST value s α) (p frame : hProp value) (q : α → hProp value) (hm : spec s p m q) :
  spec s (p ⊛ frame) m (λ r, q r ⊛ frame) :=
begin
  intros σ σ' h h' frame' r Hrun, dsimp,
  rw [holds_of_holds_and,holds_of_holds_and],
  apply exists_imp_exists, intro h₁,
  apply and.imp_right, intro Hp,
  apply hm Hrun Hp,
end

lemma frame_rule' (m : ST value s α) (p frame : hProp value) (q : α → hProp value) (hm : spec s p m q) :
  spec s (frame ⊛ p) m (λ r, frame ⊛ q r) :=
begin
  simp [and_comm frame],
  apply frame_rule _ _ _ _ hm,
end

@[simp]
lemma maplets_nil (p : ptr) : (p ↦ nil) = @emp value := rfl

-- @[simp]
lemma maplets_cons (p : ptr) (v : value) (vs : list value) : (p ↦ v :: vs) = (p ↦ [v]) ⊛ (p+1 ↦ vs) :=
by dsimp [maplets]; rw and_emp

lemma maplets_append : Π (p : ptr) (us vs : list value), (p ↦ us ++ vs) = (p ↦ us) ⊛ (p+length us ↦ vs)
| p [] vs := by simp
| p (u::us) vs := by rw [cons_append,maplets_cons,maplets_append _ us vs,maplets_cons _ _ us,length,and_assoc,nat.add_assoc]; congr' 4; apply nat.add_comm

lemma read_array_spec (p : ptr) (i : ℕ) (vs : list value) (H : i < length vs) :
  spec s (p ↦ vs) (read (p + i)) (λ r, [| [r.down] = nth' i vs |] ⊛ (p ↦ vs)) :=
begin
  induction vs generalizing p i, cases H,
  cases i,
  { rw [maplets_cons,nth'],
    conv in (_ ⊛ _ ⊛ _) { rw ← and_assoc, },
    apply frame_rule, simp,
    apply read_spec },
  { rw [nat.add_succ,← nat.succ_add],
    rw [maplets_cons,nth'],
    conv in (_ ⊛ _ ⊛ _) { rw [← and_assoc,and_comm _ (p ↦ [vs_hd]),and_assoc], },
    apply frame_rule', apply vs_ih, apply lt_of_succ_lt_succ H }
end

lemma bind_spec {β} {p : hProp _} (q : α → hProp value) {r : β → hProp value}
    {m : ST value s α} {f : α → ST value s β}
    (h₀ : spec s p m q) (h₁ : ∀ x, spec s (q x) (f x) r) :
  spec s p (m >>= f) r :=
begin
  dsimp [spec], introv, simp [], intros y σ'' h'' hm hf hp,
  apply h₁ _ hf,
  apply h₀ hm hp,
end

lemma and_then_spec {β} {p : hProp _} (q : α → hProp value) {r : β → hProp value}
    (m : ST value s α) (f : ST value s β)
    (h₀ : spec s p m q) (h₁ : ∀ x, spec s (q x) f r) :
  spec s p (m >> f) r :=
bind_spec q h₀ h₁

lemma and_then_spec' {β} {p : hProp _} (q : hProp value) {r : β → hProp value}
    (m : ST value s α) (f : ST value s β)
    (h₀ : spec s p m (λ _, q)) (h₁ : spec s q f r) :
  spec s p (m >> f) r :=
bind_spec (λ _, q) h₀ (λ _, h₁)

inductive impl (p q : hProp value) : Prop
| intro : (∀ h, p h → q h) → impl

def impl.elim {p q : hProp value} : impl p q → (∀ h, p h → q h)
| (impl.intro h) := h

infixr ` =*> `:40 := impl

@[refl]
lemma impl_refl (p : hProp value) : p =*> p := impl.intro $ λ x, id

@[trans]
lemma impl_trans {p q r : hProp value} (hpq : p =*> q) (hqr : q =*> r) : p =*> r :=
impl.intro $ λ h hp, hqr.elim _ (hpq.elim _ hp)

def True : hProp value | h := true

def False : hProp value | h := false

@[simp]
lemma lift_false : [| false |] = @False value :=
funext $ λ h, by simp [lift,False]

@[simp]
lemma False_and (p : hProp value) : False ⊛ p = False :=
by ext; simp [and,False]

@[simp]
lemma and_False (p : hProp value) : p ⊛ False = False :=
by ext; simp [and,False]

-- @[simp]
lemma False_impl (p : hProp value) : False =*> p :=
impl.intro $ λ _, false.elim

-- lemma p_exists_one_point {α} {p : α → hProp value} (x : α)
--   (h : ∀ y, p y =*> [| x = y |] ⊛ True) :
--   p_exists p = p x :=
-- begin
--   ext; dsimp [p_exists]; split,
--   { rintros ⟨x',HH⟩, specialize h _ _ HH, admit },
--   apply @Exists.intro _ (λ x, p x h_1),
-- end

section spec_attribute

open tactic

meta def bound_var : expr → name
| (expr.lam n _ _ _) := n
| _ := `_

meta def tactic.get_spec : expr → tactic (expr × expr × expr × expr × expr)
| `(@spec %%val %%α _ %%p %%m %%q) :=
do { v ← mk_local_def (bound_var q) α,
     q ← head_beta (q v),
     pure (val, p, m, v, q) }
| `(@spec' %%val %%α _ %%p %%m %%q) :=
do { v ← mk_local_def `v α,
     pure (val, p, m, v, q) }
-- | `(%%p =*> %%q) := _
| t := (pformat!"not a specification: {t}" : pformat) >>= fail

meta def tactic.get_spec' : tactic (expr × expr × expr × expr × expr) :=
target >>= instantiate_mvars >>= tactic.get_spec

open tactic

meta def spec_target (n : name) : tactic name :=
do t ← mk_const n >>= infer_type,
   (vs,t) ← mk_local_pis t,
   (_,_,m,_,_) ← tactic.get_spec t,
   return $ m.get_app_fn.const_name

@[user_attribute]
meta def spec_attr : user_attribute (name_map (list name)) :=
{ name := `spec,
  descr := "specification lemma",
  cache_cfg := { mk_cache := mfoldl (λ m n, do proc ← spec_target n,
                                               pure $ m.insert_cons proc n)
                                    (name_map.mk _),
                 dependencies := [] },
  after_set := some $ λ n _ _, () <$ spec_target n <|> fail "ill-formed specification"
 }

meta def abstr_rewrite (n : name) : tactic name :=
do t ← mk_const n >>= infer_type,
   (vs,`(%%l = _)) ← mk_local_pis t,
   if l.get_app_fn.const_name = ``repr
     then pure l.app_arg.get_app_fn.const_name
     else pure l.get_app_fn.const_name

@[user_attribute]
meta def data_abstr_attr : user_attribute (name_map (list name)) :=
{ name := `data_abstr,
  descr := "specification lemma",
  cache_cfg := { mk_cache := mfoldl (λ m n, do proc ← abstr_rewrite n,
                                               pure $ m.insert_cons proc n)
                                    (name_map.mk _),
                 dependencies := [] },
  after_set := some $ λ n _ _, () <$ abstr_rewrite n <|> fail "ill-formed abstraction lemma"
 }

end spec_attribute


-- @[spec]
lemma pure_spec (p : hProp value) (q : α → hProp value)
  (x : α) (h : p =*> q x) :
  spec s p (pure x) q :=
begin
  introv _, simp, rintro ⟨ ⟩ ⟨ ⟩ ⟨ ⟩,
  apply exists_imp_exists, intro,
  apply and_implies id (h.elim _),
end

@[spec]
lemma pure_spec' {α} (p : α → hProp value) (x : α)  :
  spec s (p x) (pure x) p :=
pure_spec _ _ _ (impl.intro $ λ h, id)

lemma map_spec {β} {p : hProp _} {q : β → hProp value}
    {m : ST value s α} {f : α → β}
    (h₀ : spec s p m (q ∘ f))  :
  spec s p (f <$> m) q :=
by rw map_eq_bind_pure; apply bind_spec _ h₀ (λ x, _); apply pure_spec'

lemma choice_spec {β} (pp : α → Prop) (f : α → ST value s β)
  (p : hProp value) (q : β → hProp value)
  (h : ∀ x, pp x → spec s p (f x) q) :
  spec s p (choice pp >>= f) q :=
by { dsimp [spec]; intros;
     simp only [exists_prop, set.mem_Union, set.bind_def, mem_choice_run, run_bind, prod.exists] at a,
     casesm* [_ ∧ _, Exists _], subst h_1,
     apply h _ ‹ _ › ‹ _ › ‹ _ › }

lemma get_spec (p : hProp value) (q : s × heap value → hProp value)
  (h : ∀ x, p =*> q x) :
  spec s p get q :=
by { dsimp [get,monad_state.lift]; introv _ Hrun; apply exists_imp_exists,
     intro hh, simp [pure] at Hrun, casesm* _ ∧ _, subst h', subst σ',
     apply and.imp id, apply (h _).elim }

lemma get_spec' (p : hProp value) :
  spec s p get (λ _, p) :=
get_spec _ _ $ λ _, impl.intro $ λ σ, id

open list

lemma alloc_spec (vs : list value) : spec s emp (alloc vs) (λ p, p.down ↦ vs) :=
begin
  dsimp [alloc],
  intros σ σ' h h' frame _,
  simp only [mem_choice_run,mem_bind_run,assign_vals,mem_run_get,exists_imp_distrib,id,and_imp],
  intros, revert a_3, subst_vars, cases x with p,
  simp only [alloc,exists_imp_distrib,id,and_imp,mem_run_pure,enum,mem_choice_run,mem_bind_run,mem_run_get,mem_run_modify,assign_vals] at ⊢,
  intros, subst_vars,
  rw [← emp_and (p ↦ vs)],
  conv in (p ↦ vs) { rw ← nat.add_zero p },
  apply holds_union_and a_4,
  { generalize : 0 = k, clear a,
    induction vs generalizing k, simp [enum,enum_from,maplets,emp,heap.mk],
    existsi [maplet (p + k) vs_hd,heap.mk (map (prod.map (has_add.add p) id) (enum_from (k + 1) vs_tl))],
    split, { simp [enum_from,heap.mk_cons], rw union_eq_add_of_disjoint,
             simp [finmap.disjoint], introv h, replace h := mem_enum_from _ h,
             apply ne_of_gt, apply nat.lt_of_succ_le h.1 },
    split, { simp },
    simp at vs_ih, exact vs_ih (k+1) },
  symmetry, intros i, simp, introv h', replace h' := mem_enum_from _ h',
  intro, subst i, apply a x, convert h'.2.1, simp,
end

lemma dealloc_spec (p : ptr) (vs : list value) : spec' s (p ↦ vs) (dealloc p vs.length) emp :=
begin
  dsimp [dealloc],
  intros σ σ' h h' frame _,
  simp only [mem_choice_run,mem_bind_run,assign_vals,mem_run_get,exists_imp_distrib,id,and_imp],
  intros, revert a_3, subst_vars, cases x with p,
  simp only [dealloc,exists_imp_distrib,id,and_imp,mem_run_pure,enum,mem_choice_run,mem_bind_run,mem_run_get,mem_run_modify,assign_vals] at ⊢,
  intros, subst_vars,
  have : x_3 = (erase_all p (length vs) x_3) ∪ heap.mk (vs.enum_from p),
  { rw erase_all_union_mk_self, apply le_of_add_eq_some frame,
    rcases a_4 with ⟨w,hw₀,hw₁⟩, rw maplets_eq at hw₁, subst w,
    exact hw₀ },
  rw [this,← emp_and (p ↦ vs)] at a_4, clear this,
  rw holds_of_holds_union_iff at a_4, exact a_4, rw maplets_eq,
  { intros p', simp, clear a_4,
    intros, induction vs; dsimp [length] at H,
    { exact a },
    rw [erase_all_succ] at H, simp at H,
    replace vs_ih := vs_ih H.2,
    simp [mem_erase_all] at H,
    rw [length,← nat.add_assoc],
    apply succ_le_of_lt, apply lt_of_le_of_ne (H.2.1 _) (ne.symm H.1),
    apply le_trans _ vs_ih, apply nat.le_add_right },
  { introv, simp [maplets_eq] },
end

lemma holds_p_exists {α} {h h' : heap value} (p : α → hProp value) : holds h h' (p_exists p) ↔ ∃ x, holds h h' (p x) :=
by split; rintro ⟨_,H,H',H''⟩; [ exact ⟨_,a_w,H,H''⟩, exact ⟨H,H',_,H''⟩ ]

lemma and_p_exists_distrib_right {α} {p : α → hProp value} {q : hProp value} :
  p_exists p ⊛ q = ∃∃ x, p x ⊛ q :=
begin
  ext, dsimp [and,p_exists], split; simp,
  { intros h₀ h₁ H r Hp Hq, refine ⟨_,_,_,H,Hp,Hq⟩ },
  { intros r h₀ h₁ H Hp Hq,
    refine ⟨_,_,H,⟨_,Hp⟩,Hq⟩, }
end

lemma and_p_exists_distrib_left {α} {p : hProp value} {q : α → hProp value} :
  p ⊛ p_exists q = ∃∃ x, p ⊛ q x :=
by rw [and_comm, and_p_exists_distrib_right]; simp [and_comm]

lemma p_exists_intro {α β} {p : hProp value} {m : ST value s α} {q : α → β → hProp value}
  (x : β) (H : spec s p m (λ y, q y x)) :
  spec s p m (λ x, p_exists (q x)) :=
begin
  intros σ σ' h h' frame r hm hp,
  dsimp, rw holds_p_exists (q r),
  existsi x, apply H hm hp,
end

def p_or (p q : hProp value) : hProp value :=
λ h, p h ∨ q h

infixr ` ⋁ `:53 := p_or

lemma p_and_or_distrib_left {p q r : hProp value} :
  p ⊛ (q ⋁ r) = (p ⊛ q) ⋁ (p ⊛ r) :=
sorry

lemma holds_or_iff {h frame : heap value} {p q : hProp value} :
  holds h frame (p ⋁ q) ↔ holds h frame p ∨ holds h frame q :=
by { dsimp [holds], rw ← exists_or_distrib, apply exists_congr, intro h₁,
     rw ← and_or_distrib_left, refl }

lemma holds_imp_holds_of_impl {h frame : heap value} {p q : hProp value}
  (Hpq : p =*> q) : holds h frame p → holds h frame q :=
exists_imp_exists (λ hp, and.imp_right $ Hpq.elim hp)

lemma impl_exists {α} {p : hProp value} {q : α → hProp value} (x : α) (hpq : p =*> q x) : p =*> p_exists q :=
impl.intro $ λ h hp, ⟨_,hpq.elim _ hp⟩

lemma exists_impl {α} {p : α → hProp value} {q : hProp value} (hpq : ∀ x, p x =*> q) : p_exists p =*> q :=
impl.intro $ λ h ⟨_, hp⟩, (hpq _).elim _ hp

lemma impl_antisymm {p q : hProp value} (hpq : p =*> q) (hqp : q =*> p) : p = q :=
by ext; exact ⟨hpq.elim _,hqp.elim _⟩

lemma impl_of_eq {p q : hProp value} (hpq : p = q) : p =*> q := impl.intro $ λ h, hpq.subst

def left_total {α β} (R : α → β → Prop) :=
∀ x, ∃ y, R x y

def right_total {α β} (R : α → β → Prop) :=
left_total (flip R)

lemma exists_impl_exists_of_total {α β} {p : α → hProp value} {q : β → hProp value}
  (R : α → β → Prop) (hl : left_total R)
  (hpq : ∀ x y, R x y → p x =*> q y) : p_exists p =*> p_exists q :=
exists_impl $ λ x, Exists.rec_on (hl x) $ λ w hw, impl_exists w (hpq _ _ hw)

lemma exists_congr_of_total {α β} {p : α → hProp value} {q : β → hProp value}
  (R : α → β → Prop) (hl : left_total R) (hr : right_total R)
  (hpq : ∀ x y, R x y → p x = q y) : p_exists p = p_exists q :=
impl_antisymm
  (exists_impl_exists_of_total R hl $ λ x y hR, impl_of_eq $ hpq _ _ hR)
  (exists_impl_exists_of_total (flip R) hr $ λ x y hR, impl_of_eq (hpq _ _ hR).symm)

lemma exists_impl_exists {α} {p q : α → hProp value} (hpq : ∀ x, p x =*> q x) : p_exists p =*> p_exists q :=
exists_impl $ λ x, impl_exists x (hpq _)

lemma exists_impl_exists_to {α β} {p : α → hProp value} {q : β → hProp value}
  (f : α → β)
  (hpq : ∀ x, p x =*> q (f x)) : p_exists p =*> p_exists q :=
exists_impl $ λ x, impl_exists (f x) (hpq _)

open function

lemma exists_impl_exists_from {α β} {p : α → hProp value} {q : β → hProp value}
  (f : β → α) (hf : surjective f)
  (hpq : ∀ x, p (f x) =*> q x) : p_exists p =*> p_exists q :=
exists_impl $ λ x, Exists.rec_on (hf x) $ λ w hf, impl_exists w $ hf ▸ hpq w

lemma exists_congr' {α β} {p : α → hProp value} {q : β → hProp value}
  (f : α → β) (hf : surjective f)
  (hpq : ∀ x, p x = q (f x)) : p_exists p = p_exists q :=
impl_antisymm
  (exists_impl_exists_to f $ λ x, impl_of_eq $ hpq x)
  (exists_impl_exists_from f hf $ λ x, impl_of_eq (hpq x).symm)

lemma or_impl {p p' : hProp value} {q : hProp value}
  (H  : p  =*> q)
  (H' : p' =*> q) :
   p ⋁ p' =*> q :=
impl.intro $ λ h h', or.elim h' (H.elim h) (H'.elim h)

lemma exists_congr {α} {p q : α → hProp value}
  (hpq : ∀ x, p x = q x) : p_exists p = p_exists q :=
congr_arg _ $ funext hpq

@[mono]
lemma and_impl_and {p p' q q' : hProp value} (hpq : p =*> q) (hpq' : p' =*> q') : p ⊛ p' =*> q ⊛ q' :=
impl.intro $ λ h, exists_imp_exists $ λ h₀, exists_imp_exists $ λ h₁, and.imp_right $ and_implies (hpq.elim _) (hpq'.elim _)

lemma impl_or_left {p q q' : hProp value} (hpq : p =*> q) : p =*> q ⋁ q' :=
impl.intro $ λ h hp, or.inl (hpq.elim h hp)

@[simp]
lemma lift_true {α} : [| true |] = @emp α := lift_eq_emp trivial

lemma lift_and_iff_p_exists {p : Prop} {q : hProp value} : [|p|] ⊛ q = ∃∃ h : p, q :=
begin
  ext, dsimp [and,p_exists,lift,emp], split,
  { rintros ⟨h₀,h₁,H₀,⟨H₁,H₂⟩,H₃⟩, subst H₂,
    rw [empty_add,option.some_inj] at H₀, exact ⟨H₁, H₀.symm ▸ H₃⟩ },
  { rintros ⟨hp,hq⟩, refine ⟨∅,h,_,⟨hp,rfl⟩,hq⟩,
    rw [empty_add,option.some_inj] }
end

lemma lift_and_impl {p : Prop} {q r : hProp value}
  (h : p → q =*> r) :
  [|p|] ⊛ q =*> r :=
suffices (∃∃ h : p, q) =*> r,
  by simpa [lift_and_iff_p_exists],
exists_impl h

lemma impl_lift_and {p : Prop} {q r : hProp value}
  (h : p)
  (h' : q =*> r) :
  q =*> [|p|] ⊛ r :=
suffices q =*> (∃∃ h : p, r),
  by simpa [lift_and_iff_p_exists],
impl_exists h h'

lemma exists_subtype {α} {p : α → Prop} {q : α → hProp value} :
  (∃∃ x : subtype p, q x.val) = (∃∃ x : α, [| p x |] ⊛ q x) :=
impl_antisymm
  (exists_impl_exists_to subtype.val (by simp; intros a ha; simp [lift_eq_emp ha]))
  (exists_impl $ λ x, lift_and_impl $ λ hp, impl_exists ⟨_,hp⟩ $ impl_refl _)

lemma exists_exists {α} {p : α → Sort*} {q : Π x, p x → hProp value} :
  (∃∃ (x : α) (h : p x), q x h) = (∃∃ x : psigma p, q x.1 x.2) :=
impl_antisymm
  (exists_impl $ λ x, exists_impl $ λ h, impl_exists ⟨x,h⟩ $ impl_refl _)
  (exists_impl $ λ x, impl_exists x.1 $ impl_exists x.2 $ impl_refl _)

lemma p_exists_intro_left {β} {p : β → hProp value} {m : ST value s α} {q : α → hProp value}
  (H : ∀ x, spec s (p x) m q) :
  spec s (p_exists p) m q :=
by simp [spec,holds_p_exists]; introv hm; apply H _ hm

lemma lift_intro {p : Prop} {p' : hProp value} {m : ST value s α} {q : α → hProp value}
  (h : p → spec s p' m q) :
  spec s ([|p|] ⊛ p') m q :=
by rw lift_and_iff_p_exists; apply p_exists_intro_left h

lemma or_intro {p p' : hProp value} {m : ST value s α} {q : α → hProp value}
  (H  : spec s p m q)
  (H' : spec s p' m q) :
  spec s (p ⋁ p') m q :=
λ σ σ' h h' frame r hm hpp',
or.elim (holds_or_iff.mp hpp') (H hm) (H' hm)

lemma or_intro_left {p : hProp value} {m : ST value s α} {q q' : α → hProp value}
  (H' : spec s p m q) :
  spec s p m (λ r, q r ⋁ q' r) :=
λ σ σ' h h' frame r hm hp,
holds_imp_holds_of_impl (impl.intro $ λ h, or.intro_left _) (H' hm hp)

lemma or_intro_right {p : hProp value} {m : ST value s α} {q q' : α → hProp value}
  (H' : spec s p m q') :
  spec s p m (λ r, q r ⋁ q' r) :=
λ σ σ' h h' frame r hm hp,
holds_imp_holds_of_impl (impl.intro $ λ h, or.intro_right _) (H' hm hp)

lemma or_left_right_spec {p p' : hProp value} {m : ST value s α} {q q' : α → hProp value}
  (H  : spec s p  m q)
  (H' : spec s p' m q') :
  spec s (p ⋁ p') m (λ r, q r ⋁ q' r) :=
or_intro (or_intro_left H) (or_intro_right H')

def alloc' (n : ℕ) : ST value s (ulift ptr) :=
choice (λ v : ulift (list value), v.down.length = n) >>= alloc ∘ ulift.down

lemma alloc'_spec (n : ℕ) : spec s emp (alloc' n) (λ p, ∃∃ vs : list value, [|vs.length = n|] ⊛ (p.down ↦ vs)) :=
begin
  dsimp [alloc'],
  apply choice_spec, rintros ⟨vs⟩,
  dsimp, intro Hvs, apply p_exists_intro vs,
  simp [lift_eq_emp Hvs], apply alloc_spec
end

lemma precondition_impl {α} {p : hProp value} (q : hProp value) {r : α → hProp value}
  {m : ST value s α} (hpq : p =*> q) (H : spec s q m r) :
  spec s p m r :=
by dsimp [spec]; introv hm hp; apply H hm (holds_imp_holds_of_impl hpq hp)

lemma postcondition_impl {α} {p : hProp value} (q : α → hProp value) {r : α → hProp value}
  {m : ST value s α} (hqr : ∀ x, q x =*> r x) (H : spec s p m q) :
  spec s p m r :=
by dsimp [spec]; introv hm hp; apply holds_imp_holds_of_impl (hqr _) (H hm hp)

def for : Π (n : ℕ) (f : ℕ → ST value s punit), ST value s punit
| 0 f := pure punit.star
| (succ n) f := for n f >> f n

@[spec]
lemma for_spec (n : ℕ) (f : ℕ → ST value s punit) (p : ℕ → hProp value)
  (h : ∀ i, i < n → spec' s (p i) (f i) (p i.succ)) :
  spec' s (p 0) (for n f) (p n) :=
begin
  induction n,
  { simp [for], apply pure_spec' (λ _, p 0), },
  { simp [for],
    apply and_then_spec' _ _ _ (n_ih _) (h _ (lt_succ_self _)),
    introv hn, apply h, apply lt_trans hn (lt_succ_self _), }
end

lemma range_zero : range 0 = [] := rfl

lemma range'_zero (n : ℕ) : range' n 0 = [] := rfl

lemma cons_range' (n k : ℕ) : (n :: range' n.succ k : list _) = range' n k.succ := rfl

@[spec]
lemma for_spec' {n : ℕ} {f : ℕ → ST value s punit}
  {p q : ℕ → hProp value} {b : hProp value}
  (h : ∀ i, i < n → spec' s (b ⊛ p i) (f i) (b ⊛ q i)) :
  spec' s (b ⊛ And p (range n)) (for n f) (b ⊛ And q (range n)) :=
begin
  let P  := λ i, b ⊛ And q (range i) ⊛ And p (range' i (n - i)),
  let P' := λ i, And q (range i) ⊛ And p (range' i.succ (n - i.succ)),
  have h := for_spec n f P _,
  { simp only [P] at h, rw [nat.sub_zero,range_zero,And,emp_and,← range_eq_range',nat.sub_self,range'_zero,And,and_emp] at h,
    exact h },
  { intros i hn,
    have : spec' s (P' i ⊛ b ⊛ p i) (f i) (P' i ⊛ b ⊛ q i),
    { apply frame_rule', apply h _ hn },
    convert this; dsimp [P,P'],
    { rw [and_assoc], transitivity b ⊛ And q (range i) ⊛ And p (i :: range' (succ i) (n - succ i)),
      rw [cons_range',nat.sub_succ,succ_pred_eq_of_pos _],
      apply nat.lt_sub_right_of_add_lt, rw zero_add, exact hn,
      rw And, ac_refl },
    { rw [range_concat,And_append,And,And,and_emp], ac_refl } }
end

def clone (p : ptr) (n : ℕ) : ST value s (ulift ptr) :=
do q ← alloc' n,
   for n (λ i,
     do v ← read (p + i),
        assign (q.down + i) v.down),
   pure q

@[spec]
lemma clone_spec (p : ptr) (vs : list value) :
  spec s (p ↦ vs)
         (clone p vs.length)
         (λ q, (p ↦ vs) ⊛ (q.down ↦ vs) ) :=
begin
  dsimp [clone], rw ← emp_and (p ↦ vs), apply bind_spec, apply frame_rule, apply alloc'_spec,
  rintro ⟨ q ⟩, rw and_p_exists_distrib_right, apply p_exists_intro_left, intro trash,
  rw and_assoc, apply lift_intro, intro H, rw [and_comm,emp_and],
  apply bind_spec _ _ (λ _, pure_spec _ _ _ (impl_refl _)),
  rw [maplets_eq_And q,maplets_eq_And q,H], apply for_spec', intros i hi,
  apply bind_spec (λ r, [|[ulift.down r] = nth' i vs|] ⊛ ((p ↦ vs) ⊛ (q + i ↦ nth' i trash))) _ _,
  { conv in (_ ⊛ _ ⊛ _) { rw [← and_assoc] }, apply frame_rule, apply read_array_spec _ _ _ hi },
  rintro ⟨ v ⟩, apply lift_intro, dsimp, intro Hv, apply frame_rule', rw ← Hv, apply assign_array_spec,
  rw H, apply hi,
end

def map (p : ptr) (f : ℕ → value → value) (n : ℕ) : ST value s punit :=
for n (λ i,
  do v ← read (p + i),
     assign (p + i) (f i v.down) )

open function

@[spec]
lemma map_spec' (p : ptr) (f : ℕ → value → value) (vs : list value) :
  spec' s (p ↦ vs)
          (map p f vs.length)
          (p ↦ vs.enum.map (uncurry f)) :=
suffices spec' s (emp ⊛ (p ↦ vs))
                 (map p f vs.length)
                 (emp ⊛ (p ↦ vs.enum.map (uncurry f)) ),
  by simp only [emp_and] at this; exact this,
begin
  rw [maplets_eq_And,maplets_eq_And,map,list.length_map,list.length_enum],
  apply for_spec', intros i hi, rw [emp_and,emp_and],
  apply bind_spec, apply read_array_spec' _ _ _ hi,
  rintro ⟨ v ⟩, apply lift_intro, dsimp, intro Hv,
  have : nth' i (list.map (uncurry f) (enum vs)) = [f i v],
  { rw [nth'_map,nth'_enum,← Hv], refl },
  rw this, apply assign_array_spec _ _ _ _ hi,
end

@[derive decidable_eq]
structure tptr (α : Type*) :=
(get : ptr)

def tptr.recast {α β} (p : tptr α) : tptr β :=
{ get := p.get }

def tptr.add {α} (p : tptr α) (n : ℕ) : tptr α :=
{ get := p.get + n }

infixl ` +. `:65 := tptr.add

@[simp]
lemma offset_zero {α} (p : tptr α) : p +. 0 = p := by cases p; refl

@[simp]
lemma offset_offset {α} (p : tptr α) (n m : ℕ) : p +. n +. m = p +. (n + m) :=
congr_arg _ (nat.add_assoc _ _ _)

lemma offset_ne {α} (p : tptr α) {n : ℕ} (h : n > 0) : p +. n ≠ p :=
by cases p; dsimp [(+.)]; rw tptr.mk.inj_eq; apply ne_of_gt (lt_add_of_pos_right _ h)

@[simp]
lemma recast_offset {α β} (p : tptr α) (n : ℕ) : (p +. n).recast = (p.recast +. n : tptr β) := rfl

inductive vec (α : Type u) : ℕ → Type u
| nil : vec 0
| cons {n} : α → vec n → vec n.succ

class storable (val : Type) (α : Type*) :=
(size : α → ℕ)
(repr : tptr α → α → hProp val)

export storable (size)

meta def check_fixed_size : tactic unit := `[intros; refl]

infix ` ⤇ `:60 := storable.repr _

class fixed_storable (val : Type) (α : Type*) extends storable val α :=
(fixed_size : ℕ)
(is_fixed : ∀ x : α, size x = fixed_size . check_fixed_size)
(size := λ _, fixed_size)
(pos_size : fixed_size > 0)

open list

export fixed_storable (fixed_size)

def word (val α) [fixed_storable val α] := { bytes : list val // length bytes = fixed_size val α }

class is_record (val : Type) (α : Type*) extends fixed_storable val α :=
(abstr : word val α → α)
(bytes : α → word val α)
(repr := λ p v, p.get ↦ (bytes v).val)
(right_inverse : right_inverse abstr bytes)
(raw_bytes_conversion : ∀ (p : tptr α) (x : α), (p ⤇ x) = p.get ↦ (bytes x).val)

export is_record (abstr bytes raw_bytes_conversion)

def bytes' (val) {α} [is_record val α] (x : α) : list val :=
(bytes val x).val

lemma length_bytes' (val) {α} [is_record val α] (x : α) : length (bytes' val x) = fixed_size val α :=
(bytes val x).property

lemma bytes_surjective (value α) [is_record value α] : surjective (bytes value : α → word value α) :=
surjective_of_has_right_inverse ⟨abstr, is_record.right_inverse _ _⟩

lemma uninitialized {val α} [is_record val α] (p : ptr) :
  (∃∃ bytes : list val, [|length bytes = fixed_size val α|] ⊛ p ↦ bytes) =
   ∃∃ obj : α, tptr.mk α p ⤇ obj :=
by rw ← exists_subtype; symmetry; apply exists_congr' (bytes val) (bytes_surjective val α);
   intro x; apply raw_bytes_conversion

def value_abstr : Π vs : list value, length vs = 1 → value
| [val] rfl := val

instance : is_record value value :=
{ repr := λ p v, p.get ↦ [v],
  bytes := λ v, ⟨[v], rfl⟩,
  fixed_size := 1,
  pos_size := by norm_num,
  abstr := λ x, value_abstr _ x.property,
  right_inverse := λ ⟨[x],rfl⟩, rfl,
  raw_bytes_conversion := λ p x, rfl }

def list_repr {α} [storable value α] : tptr (list α) → list α → hProp value
| p [] := emp
| p (v :: vs) := p.recast ⤇ v ⊛ list_repr (p +. size value v) vs

def list_repr' (value) {α β} [storable value α] : tptr (list α) → list α → tptr β → hProp value
| p [] q := [| p = q.recast |]
| p (v :: vs) q := p.recast ⤇ v ⊛ list_repr' (p +. size value v) vs q

def rec_bytes {α} [is_record value α] (ls : list α) : list value :=
(ls.map (bytes' value)).join

lemma list_repr_map {α β} [storable value α] [storable value β]
  (p : tptr (list α)) {f : β → α} (xs : list β)
  (h : ∀ (q : tptr α) x, q ⤇ f x = (q.recast ⤇ x : hProp value))
  (h' : ∀ x : β, size value (f x) = size value x ):
  list_repr p (xs.map f) = (list_repr p.recast xs : hProp value) :=
begin
  induction xs generalizing p, refl,
  simp [list_repr,*], refl
end

lemma rec_bytes_cons {α} [is_record value α] (x) (xs : list α) : rec_bytes (x :: xs) = bytes' value x ++ rec_bytes xs := rfl

lemma length_rec_bytes {α} [is_record value α] (xs : list α) :
  length (rec_bytes xs : list value) = length xs * fixed_size value α :=
begin
  simp [rec_bytes], induction xs; simp [length,*,right_distrib],
  erw (bytes value xs_hd).property,
end

open refinement.fixed_storable list

@[simp]
lemma fixed_size_val [inhabited value] : fixed_size value value = 1 := rfl

attribute [simp] fixed_storable.is_fixed

lemma list_repr'_eq_list_repr {α β} [fixed_storable value α] (p : tptr (list α)) (q : tptr β) (ls : list α) :
  list_repr' value p ls q = list_repr p ls ⊛ [| p +. ls.length * fixed_size value α = q.recast |] :=
by induction ls generalizing p; simp [list_repr',list_repr,*,right_distrib,refinement.and_assoc]; congr

instance list.storable {α val} [storable val α] : storable val (list α) :=
{ repr := list_repr,
  size := λ vs, list.sum $ vs.map (storable.size val)
  }

lemma uninitialized' {α} [is_record value α] (p : tptr α) :
  (∃∃ obj : α, p ⤇ obj) = (∃∃ bytes : list value, [| length bytes = fixed_size value α |] ⊛ p.get ↦ bytes) :=
by cases p; rw uninitialized

structure field (val : Type) :=
mk' ::
{α : Type*}
[S : is_record val α]
(get : α)

attribute [instance] field.S

def field.mk_ (val : Type) {α : Type} [I : is_record val α] (x : α) : field val := ⟨_,x⟩

instance : storable value (field value) :=
{ repr := λ p x, p.recast ⤇ x.get,
  size := λ x, storable.size value x.get, }

def field_bytes : refinement.field value → list value
| (@field.mk' ._ α _inst get) := @bytes' value α _inst get

def rec_bytes' (ls : list (refinement.field value)) : list value :=
(ls.map (field_bytes)).join

end refinement

namespace examples

namespace circular_buffer
export refinement (ptr)
open refinement

def val := ptr
@[reducible] def IO (α : Type) := ST val punit α

open function

def equiv.is_record {α β} (f : β → α) (g : α → β) (hfg : left_inverse f g) [is_record val α] : is_record val β :=
{ repr := λ p x, p.recast ⤇ f x,
  bytes := bytes val ∘ f,
  abstr := g ∘ abstr,
  fixed_size := fixed_size val α,
  pos_size := fixed_storable.pos_size val α,
  is_fixed := λ x, rfl,
  right_inverse := λ ⟨x,hx⟩, by dsimp [bytes]; rw [hfg];
                               exact (is_record.right_inverse val α ⟨x,hx⟩),
  raw_bytes_conversion := λ ⟨_,p⟩ x, is_record.raw_bytes_conversion val ⟨α,p⟩ (f x)
 }

instance ptr.storable : is_record val ptr :=
refinement.refinement.is_record

instance tptr.storable {α} : is_record val (tptr α) :=
equiv.is_record tptr.get (tptr.mk _) (λ x, rfl)

instance unsigned.storable : is_record val ℕ :=
refinement.refinement.is_record

instance {val α} [fixed_storable val α] : fixed_storable val (word val α) :=
{ repr := λ p v, p.recast ⤇ v.val,
  fixed_size := fixed_size val α,
  pos_size := fixed_storable.pos_size val α }

def word.bytes {val α} [fixed_storable val α] : word val α → word val (word val α)
| ⟨x,hx⟩ := ⟨x,hx⟩

def word.abstr {val α} [fixed_storable val α] : word val (word val α) → word val α
| ⟨x,hx⟩ := ⟨x,hx⟩

@[simp]
lemma tptr.recast_mk {α β} : Π (p : ptr), (tptr.mk α p).recast = tptr.mk β p
| p := rfl

lemma val_repr {val} (p : tptr (list val)) (vs : list val) : p ⤇ vs = p.get ↦ vs :=
begin
  cases p, dsimp [storable.repr,tptr.recast],
  induction vs generalizing p, refl,
  rw maplets_cons, simp [list_repr,tptr.add,fixed_size,*], refl
end

instance {val α} [is_record val α] : is_record val (word val α) :=
{ bytes := word.bytes,
  abstr := word.abstr,
  right_inverse := λ ⟨x,hx⟩, rfl,
  raw_bytes_conversion := λ ⟨_,p⟩ ⟨x,hx⟩,
    by { simp [tptr.recast_mk,word.bytes,val_repr] } }

@[simp]
lemma tptr.recast_recast {α β γ} (p : tptr α) : (p.recast : tptr β).recast = (p.recast : tptr γ) := rfl

@[simp]
lemma tptr.recast_eq {α} : Π (p : tptr α), (p.recast : tptr α) = p
| ⟨ _,_ ⟩ := rfl

lemma repr_map_bytes {val α} [is_record val α] (p : tptr (list (word val α))) (xs : list α) :
  p ⤇ xs.map (bytes val) = (p.recast ⤇ xs : hProp val) :=
show list_repr p (xs.map (bytes val)) = list_repr p.recast xs,
begin
  rw [list_repr_map],
  { intros, symmetry, erw val_repr, cases q,
    rw [raw_bytes_conversion], refl },
  intro, simp [fixed_storable.is_fixed], refl
end

lemma repr_map_abstr {val α} [is_record val α] (p : tptr (list α)) (xs : list (word val α)) :
  p ⤇ xs.map abstr = (p.recast ⤇ xs : hProp val) :=
begin
  have := repr_map_bytes p.recast (xs.map abstr),
  simp at this, rw ← this, congr,
  transitivity xs.map id,
  { congr, ext, exact is_record.right_inverse val α x },
  { simp only [list.map_id] }
end

open list

lemma sizeof_eq {α} {ls : list α} : sizeof ls = length ls + 1 :=
by { dsimp [sizeof,has_sizeof.sizeof], induction ls; simp [list.sizeof,*,sizeof,has_sizeof.sizeof,default.sizeof] }

lemma sizeof_drop {α} {n : ℕ} {ls : list α} (h : n ≤ length ls) : sizeof (drop n ls) = sizeof ls - n :=
by simp [sizeof_eq,nat.add_sub_assoc h]

def trashed (val) {α} [fixed_storable val α] (p : tptr α) : hProp val :=
∃∃ trash : list val, [| length trash = fixed_size val α |] ⊛ p.recast ⤇ trash

def mk_chunk {val} (α) [fixed_storable val α] (vs : list val) (h : length vs ≥ fixed_size val α) : word val α :=
⟨take (fixed_size val α) vs,by rw [length_take,min_eq_left h]⟩

def chunks {val} (α) [fixed_storable val α] : list val → list (word val α)
| xs :=
if h : length xs ≥ fixed_size val α then
  have sizeof (drop (fixed_size val α) xs) < sizeof xs,
    by { rw sizeof_drop h, apply nat.sub_lt _ (fixed_storable.pos_size _ _),
         rw sizeof_eq, apply lt_of_le_of_lt (nat.zero_le _), apply lt_add_one, },
  mk_chunk α xs h :: chunks (drop (fixed_size val α) xs)
else []

lemma chunks_nil {val α} [fixed_storable val α] : chunks α (@nil val) = @nil (word val α) :=
by rw [chunks,dif_neg]; apply not_le_of_gt; apply fixed_storable.pos_size

lemma chunks_eq_of_length_ge {val α} [fixed_storable val α] {xs : list val} (h : length xs ≥ fixed_size val α) :
  chunks α xs = mk_chunk α xs h :: chunks α (drop (fixed_size val α) xs) :=
by rw [chunks,dif_pos h]

class {u} is_object (val : Type) (s α : Type u) extends fixed_storable val α :=
(delete : tptr α → ST val s punit)
(move : tptr α → tptr α → ST val s punit)
(delete_spec : ∀ (p : tptr α) (x : α),
                 spec' s (p ⤇ x)
                         (delete p)
                         (trashed val p))
(move_spec : ∀ (p p' : tptr α) (x : α),
                    spec' s (trashed val p ⊛ p' ⤇ x)
                            (move p p')
                            (trashed val p' ⊛ p ⤇ x))

lemma repr_cons {α} [storable val α] (p : tptr (list α)) (x) (xs : list α) :
  p ⤇ (x :: xs) = (p.recast ⤇ x ⊛ p+.size val x ⤇ xs : hProp val) :=
by { dsimp [storable.repr], simp [list_repr], }

structure buffer_node (α : Type*) [fixed_storable val α] :=
(repr tail marker : tptr (list $ word val α))
(head : tptr (list α))
(size count : ℕ)

open refinement (renaming field.mk_ -> mk_)

lemma length_eq_succ {α} (xs : list α) (n : ℕ) : xs.length = n.succ ↔ ∃ y ys, xs = y::ys ∧ ys.length = n :=
begin
  split,
  { intro h, cases xs, cases h, exact ⟨_,_,rfl,nat.succ_inj h⟩ },
  { rintro ⟨y,ys,h₀,h₁⟩, subst h₀, rw [list.length,h₁] }
end

section tactic

setup_tactic_parser
open tactic

meta def vec_cases_end (h : expr) : tactic unit :=
do rule ← mk_const ``list.length_eq_zero,
   h ← rewrite_hyp rule h,
   subst h

meta def vec_cases_aux : expr → expr → list name → tactic unit
| h `(list.length %%xs = %%n) ns :=
  do `(nat.succ %%n) ← whnf n | vec_cases_end h,
     rule ← mk_const ``length_eq_succ, -- [xs,n],
     h ← rewrite_hyp rule h,
     d ← get_unused_name `h,
     let (n,ns) := (option.get_or_else ns.head' d,ns.tail),
     [(_,[y,h],_)] ← cases_core h [n],
     [(_,[ys,h],_)] ← cases_core h [`ys],
     [(_,[h,h'],_)] ← cases_core h [`h₀,`h₁],
     subst h,
     t ← infer_type h',
     vec_cases_aux h' t ns,
     pure ()
| h _ ns := fail "expecting assumption of the form `list.length xs = n`"

meta def vec_cases (h : parse ident) (ids : parse with_ident_list) : tactic unit :=
do h ← get_local h,
   t ← infer_type h,
   vec_cases_aux h t ids

run_cmd add_interactive [``vec_cases]

end tactic

instance buffer_node.storable {α} [fixed_storable val α] : fixed_storable val (buffer_node α) :=
{ repr := λ p v, p.get ↦ rec_bytes' [mk_ val v.repr, mk_ val v.tail, mk_ val v.marker, mk_ val v.head, mk_ val v.size, mk_ val v.count],
  fixed_size := 6,
  pos_size := by norm_num }

def buffer_node.abstr {α} [fixed_storable val α] : word val (buffer_node α) → buffer_node α
| ⟨[a,b,c,d,e,f],rfl⟩ := ⟨abstr ⟨[a], rfl⟩,abstr ⟨[b], rfl⟩,abstr ⟨[c], rfl⟩,abstr ⟨[d], rfl⟩,abstr ⟨[e], rfl⟩,abstr ⟨[f], rfl⟩⟩

lemma buffer_node.abstr_list {α} [fixed_storable val α] {a b c d e f : val} (h) :
  buffer_node.abstr ⟨[a,b,c,d,e,f],h⟩ = (⟨abstr ⟨[a],rfl⟩,abstr ⟨[b],rfl⟩,abstr ⟨[c],rfl⟩,abstr ⟨[d],rfl⟩,abstr ⟨[e],rfl⟩,abstr ⟨[f],rfl⟩⟩ : buffer_node α) :=
rfl

lemma val.abstr_def {a : val} (h) : abstr ⟨[a],h⟩ = a := rfl

lemma tptr.abstr_def {α} {a : val} (h) : abstr ⟨[a],h⟩ = tptr.mk α a := rfl

instance buffer_node.is_record {α} [fixed_storable val α] : is_record val (buffer_node α) :=
{ bytes := λ v, ⟨rec_bytes' [mk_ val v.repr, mk_ val v.tail, mk_ val v.marker, mk_ val v.head, mk_ val v.size, mk_ val v.count], rfl⟩,
  abstr := buffer_node.abstr,
  right_inverse := λ ⟨a,ha⟩, by { dsimp [fixed_storable.fixed_size] at ha ⊢, congr, vec_cases ha with repr tl hd sz count, refl },
  raw_bytes_conversion := λ p a, rfl
 }

section talloc

variables (α : Type*) [fixed_storable val α] (n : ℕ)

def malloc : IO (tptr (list val)) :=
(tptr.mk _ ∘ ulift.down) <$> alloc' n

def ralloc : IO (tptr (list α)) :=
(tptr.mk _ ∘ ulift.down) <$> alloc' (n * fixed_size val α)

def ralloc1 : IO (tptr α) :=
(tptr.mk _ ∘ ulift.down) <$> alloc' (fixed_size val α)

variables {α}

def free (p : tptr (list α)) (n : ℕ) : IO unit :=
dealloc p.get (n * fixed_size val α)

def rfree (p : tptr α) : IO unit :=
dealloc p.get (fixed_size val α)

end talloc

section talloc

variables {α : Type*} [is_record val α] (n : ℕ)

open list

lemma repr_chunks {n : ℕ} (p : tptr (list (word val α))) {mem : list val}
  (Hmem : length mem = n * fixed_storable.fixed_size val α) :
  p ⤇ chunks α mem = p.get ↦ mem :=
begin
  induction n generalizing mem p; simp [nat.succ_mul,length_eq_zero] at Hmem,
  { rw [Hmem,chunks_nil], refl },
  { have : length mem ≥ fixed_size val α,
    { rw Hmem, apply nat.le_add_right, },
    rw [chunks_eq_of_length_ge this,repr_cons],
    conv { to_rhs, rw ← take_append_drop (fixed_size val α) mem, },
    rw maplets_append, congr,
    { rw [raw_bytes_conversion], refl },
    { transitivity, swap, apply @n_ih (drop (fixed_size val α) mem) (p +. length (take (fixed_size val α) mem)),
      rw [length_drop,Hmem,nat.add_sub_cancel_left],
      congr, dsimp [storable.size], simp [min_eq_left this] } }
end

lemma length_chunks {mem : list val}
  (Hmem : length mem = n * fixed_size val α) :
  length (chunks α mem) = n :=
begin
  induction n generalizing mem; simp [nat.succ_mul] at Hmem,
  { rw length_eq_zero at Hmem ⊢, subst Hmem,
    rw [chunks,dif_neg], apply not_le_of_gt,
    apply fixed_storable.pos_size },
  { rw [chunks,dif_pos,length,← nat.succ_eq_add_one], congr,
    apply n_ih, rw [length_drop,Hmem,nat.add_sub_cancel_left],
    rw Hmem, apply nat.le_add_right }
end

@[spec]
lemma malloc_spec :
  spec _
    emp
    (malloc n)
    (λ p, ∃∃ val, [| length val = n |] ⊛ p ⤇ val) :=
map_spec (by { simp only [(∘)], apply postcondition_impl _ _ (alloc'_spec n),
               rintro ⟨p⟩, simp [val_repr] })

@[spec]
lemma ralloc_spec :
  spec _
    emp
    (ralloc α n)
    (λ p, ∃∃ val, [| length val = n |] ⊛ p ⤇ val) :=
map_spec
(by { simp only [(∘)], apply postcondition_impl _ _ (alloc'_spec _),
      rintro ⟨p⟩, simp [val_repr], apply exists_impl, intro mem,
      apply lift_and_impl, intro Hmem,
      apply impl_exists ((chunks α mem).map abstr),
      rw [length_map,repr_map_abstr,tptr.recast_mk],
      apply impl_lift_and,
      { rw length_chunks _ Hmem, },
      { rw repr_chunks _ Hmem } })

@[spec]
lemma ralloc1_spec :
  spec _
    emp
    (ralloc1 α)
    (λ p, ∃∃ val, p ⤇ val) :=
map_spec (by simp only [(∘),uninitialized']; apply (alloc'_spec _ ))

@[spec]
lemma free_spec (p : tptr (list α)) (xs : list α) :
  spec' _
    (p ⤇ xs)
    (free p (length xs))
    emp :=
begin
  refine precondition_impl (p.get ↦ rec_bytes xs) _ _, -- (dealloc_spec _ _) -- (by simp [val_repr]) (dealloc_spec _ xs)
  { apply impl_of_eq, induction xs generalizing p, refl,
    rw [rec_bytes_cons,maplets_append,repr_cons,raw_bytes_conversion,xs_ih],
    erw [fixed_storable.is_fixed,(bytes val xs_hd).property], refl },
  { dsimp [free], rw ← length_rec_bytes, apply dealloc_spec }
end

@[spec]
lemma rfree_spec (p : tptr α) (x : α) :
  spec' unit
    (p ⤇ x)
    (rfree p)
    emp :=
precondition_impl (p.get ↦ (bytes' val x))
  (impl_of_eq (raw_bytes_conversion _ _ _))
  (by dsimp [rfree]; rw ← length_bytes' _ x; apply dealloc_spec)

end talloc

section setters

variables {α : Type*} [fixed_storable val α] (p : tptr (buffer_node α))

def get_repr : IO (tptr (list $ word val α)) := (tptr.mk _ ∘ ulift.down) <$> read p.get
def get_head : IO (tptr (list α)) :=   (tptr.mk _ ∘ ulift.down) <$> read (p.get+1)
def get_marker : IO (tptr (list $ word val α)) := (tptr.mk _ ∘ ulift.down) <$> read (p.get+2)
def get_tail : IO (tptr (list $ word val α)) := (tptr.mk _ ∘ ulift.down) <$> read (p.get+3)
def get_size : IO ℕ :=                 ulift.down <$> read (p.get+4)
def get_count : IO ℕ :=                ulift.down <$> read (p.get+5)

section getters

variables (x y w : tptr (list $ word val α)) (z : tptr (list α)) (sz count : ℕ)

@[spec]
lemma get_repr_spec :
  spec unit (p ⤇ ⟨x,y,w,z,sz,count⟩)
            (get_repr p)
            (λ r, [| r = x |] ⊛ p ⤇ ⟨x,y,w,z,sz,count⟩) :=
sorry

@[spec]
lemma get_head_spec :
  spec unit (p ⤇ ⟨x,y,w,z,sz,count⟩)
            (get_head p)
            (λ r, [| r = z |] ⊛ p ⤇ ⟨x,y,w,z,sz,count⟩) :=
sorry

@[spec]
lemma get_marker_spec :
  spec unit (p ⤇ ⟨x,y,w,z,sz,count⟩)
            (get_marker p)
            (λ r, [| r = w |] ⊛ p ⤇ ⟨x,y,w,z,sz,count⟩) :=
sorry

@[spec]
lemma get_tail_spec :
  spec unit (p ⤇ ⟨x,y,w,z,sz,count⟩)
            (get_tail p)
            (λ r, [| r = y |] ⊛ p ⤇ ⟨x,y,w,z,sz,count⟩) :=
sorry

@[spec]
lemma get_size_spec :
  spec unit (p ⤇ ⟨x,y,w,z,sz,count⟩)
            (get_size p)
            (λ r, [| r = sz |] ⊛ p ⤇ ⟨x,y,w,z,sz,count⟩) :=
sorry

@[spec]
lemma get_count_spec :
  spec unit (p ⤇ ⟨x,y,w,z,sz,count⟩)
            (get_count p)
            (λ r, [| r = count |] ⊛ p ⤇ ⟨x,y,w,z,sz,count⟩) :=
sorry

end getters

def set_repr (x : tptr (list $ word val α)) : IO unit := assign p.get x.get
def set_head (x : tptr (list α)) : IO unit := assign (p.get+1) x.get
def set_marker (x : tptr (list $ word val α)) : IO unit := assign (p.get+2) x.get
def set_tail (x : tptr (list $ word val α)) : IO unit := assign (p.get+3) x.get
def set_size (sz : ℕ) : IO unit := assign (p.get+4) sz
def set_count (count : ℕ) : IO unit := assign (p.get+5) count

variables (r : buffer_node α)

@[spec]
lemma set_repr_spec (x' : tptr (list $ word val α)) :
  spec' unit (p ⤇ r)
             (set_repr p x')
             (p ⤇ { repr := x', .. r }) :=
sorry

@[spec]
lemma set_tail_spec (y' : tptr (list $ word val α)) :
  spec' unit (p ⤇ r)
             (set_tail p y')
             (p ⤇ { tail := y', .. r }) :=
sorry

@[spec]
lemma set_marker_spec (w' : tptr (list $ word val α)) :
  spec' unit (p ⤇ r)
             (set_marker p w')
             (p ⤇ { marker := w', .. r }) :=
sorry

@[spec]
lemma set_head_spec (z' : tptr (list α)) :
  spec' unit (p ⤇ r)
             (set_head p z')
             (p ⤇ { head := z', .. r }) :=
sorry

@[spec]
lemma set_size_spec (sz' : ℕ) :
  spec' unit (p ⤇ r)
             (set_size p sz')
             (p ⤇ { size := sz', .. r }) :=
sorry

@[spec]
lemma set_count_spec (count' : ℕ) :
  spec' unit (p ⤇ r)
             (set_count p count')
             (p ⤇ { count := count', .. r }) :=
sorry

end setters

structure buffer_inv {α : Type} [fixed_storable val α] (b : buffer_node α) : Prop :=
(marker_loc : b.marker = b.repr +. b.size * fixed_storable.fixed_size val α)
(tail_no_lingering : b.marker ≠ b.tail)
(head_no_lingering : b.marker ≠ b.head.recast)
(pos_size : b.size > 0)

lemma marker_ne_repr {α : Type} [fixed_storable val α] {b : buffer_node α} (h : buffer_inv b) :
  b.marker ≠ b.repr :=
begin
  cases h, rw h_marker_loc,
  apply offset_ne, apply mul_pos ‹ _ › (fixed_storable.pos_size _ _),
end

def unused {α β} [fixed_storable val α] : tptr (list $ word val α) → ℕ → tptr β → hProp val
| p 0 q := [| p = q.recast |]
| p (nat.succ n) q := trashed val (p.recast : tptr α) ⊛ unused (p +. fixed_size val α) n q

def cycle {α} [fixed_storable val α] (ls : buffer_node α) (qe : list α) : hProp val :=
( ∃∃ pre post : ℕ,
     unused ls.repr pre ls.head ⊛
     list_repr' val ls.head qe ls.tail ⊛
     unused ls.tail post ls.marker ) ⋁
( ∃∃ first last (mid : ℕ),
     [| first ++ last = qe |]  ⊛
     list_repr' val ls.repr.recast last ls.tail ⊛
     unused ls.tail mid ls.head  ⊛
     list_repr' val ls.head first ls.marker )

-- instance buffer.storable {α} [fixed_storable val α] : fixed_storable val (buffer α) :=
-- { repr := λ p v, p.recast ⤇ v.to_buffer_node ⊛ cycle v.to_buffer_node v.queue,
--   fixed_size := 4,
--   pos_size := by norm_num }

def queue (α : Type) := list α

def queue.mk {α} (vs : list α) : queue α := vs

instance queue.storable {α} [fixed_storable val α] : fixed_storable val (queue α) :=
{ repr := λ p v, ∃∃ b : buffer_node α, [| buffer_inv b |] ⊛ p.recast ⤇ b ⊛ cycle b v,
  -- bytes := λ p, bytes _,
  fixed_size := 4,
  pos_size := by norm_num }

-- @[simp]
-- lemma buffer_repr {α} [fixed_storable val α] (p : tptr (buffer α)) (b : buffer α) :
--   (p ⤇ b : hProp val) = p.recast ⤇ b.to_buffer_node ⊛ cycle b.to_buffer_node b.queue :=
-- rfl

@[simp, data_abstr]
lemma queue_repr {α} [fixed_storable val α] (p : tptr (queue α)) (vs : list α) :
  (p ⤇ queue.mk vs : hProp val) = ∃∃ b : buffer_node α, [| buffer_inv b |] ⊛ p.recast ⤇ b ⊛ cycle b vs :=
rfl

def mk_buffer (α) [fixed_storable val α] (sz : ℕ) : IO (tptr $ queue α) :=
do let sz' := max 1 sz,
   p ← ralloc (word val α) sz',
   r ← ralloc1 (buffer_node α),
   set_head r p.recast,
   set_tail r p,
   set_repr r p,
   set_size r sz',
   set_marker r (p +. sz' * fixed_storable.fixed_size val α),
   set_count r 0,
   pure r.recast

section tactic

setup_tactic_parser
open tactic

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
@expr.const tt ``refinement.and [] val x (mk_assert xs)

lemma spec_congr {α s} {p p' : hProp val} {q q' : α → hProp val} {m : ST val s α}
  (hp : p = p') (hq : ∀ x, q x = q' x) (hm : spec s p m q) : spec s p' m q' :=
have hq' : q = q', from _root_.funext hq,
hq' ▸ (hp ▸ hm)

meta def first_match : list expr → list expr → tactic (expr × list expr × list expr)
| [] ys := fail "no match found"
| (x::xs) ys :=
  if x ∈ ys
  then pure (x,xs,ys.erase x)
  else do
    (a,as,bs) ← first_match xs ys,
    pure (a,x::as,bs)

meta inductive fragment
| refl : expr → fragment
| drop (n : expr) : fragment → fragment
| take (n : expr) : fragment → fragment


meta def is_fragment : expr → expr → option fragment
| e e' :=
  if e = e' then fragment.refl e
            else match e with
                 | `(drop %%n %%e₀) := do fr ← is_fragment e₀ e',
                                          fragment.drop n fr
                 | `(take %%n %%e₀) := do fr ← is_fragment e₀ e',
                                          fragment.take n fr
                 | _ := none
                 end

meta def fragment.complement' (val p ls q : expr) : expr → fragment → (expr → tactic expr) → tactic (list expr)
| n (fragment.refl e) f := pure []
| n (fragment.take n' e) f :=
  do p' ← mk_app ``refinement.tptr.add [p,n],
     let f' := λ e, f e >>= λ e, mk_app ``take [n',e],
     ls' ← mk_app ``drop [n',ls],
     ls' ← f ls',
     e' ← mk_app ``list_repr' [p',ls',q],
     cons e' <$> fragment.complement' n e f
| n (fragment.drop n' e) f :=
  do p' ← mk_app ``refinement.tptr.add [p,n],
     let f' := λ e, mk_app ``drop [n',e] >>= λ e, f e,
     ls' ← mk_app ``take [n',ls],
     ls' ← f ls',
     e' ← mk_app ``list_repr' [p',ls',q],
     n'' ← mk_app ``add [n,n'],
     cons e' <$> fragment.complement' n'' e f

meta def fragment.complement (val p ls q : expr) (fr : fragment) : tactic (list expr) :=
fragment.complement' val p ls q `(0) fr pure

meta def check_fragments (val p ls q x : expr) (xs : list expr) : list expr → tactic  (expr × list expr × list expr)
| (y@`(list_repr' _ %%p' %%ls' %%q') :: ys) :=
                  match is_fragment ls' ls with
                  | (some fr) :=
                    do trace "fragment",
                       cs ← trace_error (fr.complement val p ls q) "foo",
                       pure (y,cs ++ xs,ys)
                  | none := do (a,as,bs) ← check_fragments ys,
                               pure (a,as,y::bs)
                  end
| (y :: ys) := do (a,as,bs) ← check_fragments ys,
                  pure (a,as,y::bs)
| [] := fail "A no match found"

meta def match_fragments : list expr → list expr → tactic (expr × list expr × list expr)
| (x@`(list_repr' %%val %%p %%ls %%q) :: xs) ys :=
  check_fragments val p ls q x xs ys <|>
  do trace x,
     (a,as,bs) ← match_fragments xs ys,
     pure (a,x::as,bs)
-- | (`(list_repr %%val %%p %%ls) :: xs) ys := _
| (x :: xs) ys := do (a,as,bs) ← match_fragments xs ys,
                     pure (a,x::as,bs)
| [] ys := fail "B no match found"

meta def frame : tactic unit :=
focus1 $
do (val,p,m,v,q) ← tactic.get_spec',
   ps ← parse_assert p,
   qs ← parse_assert q,
   (a,ps,qs) ← first_match ps qs <|> match_fragments ps qs <|> match_fragments qs ps,
   -- val ← mk_mvar,
   let b := mk_assert val ps,
   let c := mk_assert val qs,
   t ← mk_mapp ``frame_rule' [val,none,none,m,b,a,expr.lambdas [v] c],
   args ← infer_type t,
   g₀ ← mk_mvar, g₁ ← mk_mvar,
   g₂ ← mk_meta_var args.binding_domain,
   refine ``(spec_congr %%g₀ %%g₁ %%(t g₂)),
   set_goals [g₀], ac_refl,
   set_goals [g₁], intro1, ac_refl,
   g₂ ← instantiate_mvars g₂,
   set_goals [g₂]

-- meta def frame' : tactic unit :=
-- focus1 $
-- do (p,m,v,q) ← get_spec,
--    `(hProp %%val) ← infer_type p,
--    ps ← parse_assert p,
--    qs ← parse_assert q,
--    (a,ps,qs) ← match_fragments ps qs,
--    trace "•",
--    trace a, trace ps, trace qs

meta def find_lift : list expr → tactic (option (expr × list expr))
| [] := pure none
| (x@`(refinement.lift _) :: xs) := pure (some (x, xs))
| (x :: xs) :=
  do some (y, ys) ← find_lift xs | pure none,
     pure (some (y, x::xs))

meta def s_intro_spec (n : name) : tactic unit :=
do (val,p,_,_,_) ← tactic.get_spec',
   match p with
   | `(p_exists _) :=
     do applyc ``p_exists_intro_left,
        intro n >> pure ()
   | _ :=
   do xs ← parse_assert p,
      some (x, xs) ← find_lift xs | failed,
      let p' := mk_assert val (x :: xs),
      g ← mk_app `eq [p,p'] >>= mk_meta_var,
      gs ← get_goals, set_goals [g],
      `[simp only [and_emp,emp_and] { fail_if_unchanged := ff } ],
      done <|> ac_refl,
      set_goals gs,
      get_assignment g >>= rewrite_target,
      applyc ``lift_intro,
      intro n, pure ()
   end

meta def s_intro (n : parse $ ident_ <|> pure `_) : tactic unit :=
do `[simp only [and_p_exists_distrib_left,and_p_exists_distrib_right]
               { fail_if_unchanged := ff }],
   `(@impl %%val %%p %%q) ← target | s_intro_spec n,
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
      done <|> ac_refl,
      set_goals gs,
      get_assignment g >>= rewrite_target,
      applyc ``lift_and_impl,
      intro n, pure ()
   end

meta def s_intros : parse ident_* → tactic unit
| [] := repeat (s_intro `_)
| ns := ns.mmap' s_intro

meta def find_frame' (e : expr) : list expr → tactic (list expr)
| [] := fail "frame not found"
| (x :: xs) :=
  xs <$ unify e x <|>
  cons x <$> find_frame' xs

meta def find_frame : list expr → list expr → tactic (list expr)
| [] xs := pure xs
| (x::xs) ys :=
  do ys' ← find_frame' x ys,
     find_frame xs ys'

meta def unify_args (e e' : expr) : tactic unit :=
do guard (e.get_app_fn.const_name = e'.get_app_fn.const_name) <|> fail format!"different calls: {e.get_app_fn} {e'.get_app_fn}",
   let args := e.get_app_args,
   let args' := e'.get_app_args,
   guard (args.length = args'.length) <|> fail "argument list mismatch",
   mzip_with' (λ a a', try (unify a a') <|> fail!"arguments `{a}` and `{a'}` do not unify\n`{e}`, `{e'}`") args args'

meta def specialize_spec (spec p call : expr) : tactic unit :=
do (args,spec') ← infer_type spec >>= mk_meta_pis,
   (val,p',m,v,q) ← tactic.get_spec spec',
   trace_state,
   unify_args call m,
   trace pformat!"• {p}\n• {p'}\n• {q}\n(end)",
   ps  ← parse_assert p,
   ps' ← parse_assert p',
   fr ← find_frame ps' ps <|> fail!"framing {ps'} {ps}",
   let fr' := mk_assert val fr,
   q' ← head_beta q >>= lambdas [v],
   e ← mk_mapp ``frame_rule [none, none, none, m, p', fr', q', spec.mk_app args],
   to_expr ``(precondition_impl _ _ %%e) >>= apply,
   `[simp only [and_emp,emp_and] { fail_if_unchanged := ff } ],
   pure ()

-- meta def apply_spec_bind : expr → tactic expr
-- | `(%%m >>= %%f) := applyc ``bind_spec >> pure m
-- | `(%%m >> %%f)  := applyc ``and_then_spec >> pure m
-- | m := pure m

meta def verify_step (rule : parse ident?) : tactic unit :=
solve1 $
do ls ← spec_attr.get_cache,
   (val,p,m,v,q) ← tactic.get_spec',
   trace pformat!"• {p} - {q} •",
   -- m' ← apply_spec_bind m,
   let proc_n := m.get_app_fn.const_name,
   specs ← ↑(list.ret <$> rule) <|> ls.find proc_n <|> fail!"no such procedure: {proc_n}",
   ps ← parse_assert p,
   specs.any_of (λ n,
   do e ← mk_const n,
      trace "\nfailure"
      trace_error (specialize_spec e p m) "msg")
   <|> fail!"no specification found. \nCandidates: {specs}"

meta def apply_spec (rule : parse ident?) : tactic unit :=
focus1 $
do s_intros [],
   (val,p,m,v,q) ← tactic.get_spec',
   match m with
   | `(%%m >>= %%f) :=
     do applyc ``bind_spec,
        verify_step rule,
        x ← intro (bound_var f),
        t ← infer_type x,
        when (t.const_name ∈ [``punit,``unit]) $ () <$ cases x,
        skip
   | `(%%m >> %%f)  :=
     do applyc ``and_then_spec,
        verify_step rule,
        x ← intro (bound_var f),
        t ← infer_type x,
        when (t.const_name ∈ [``punit,``unit]) $ () <$ cases x,
        skip
   | `(pure _) := applyc ``pure_spec
   | m :=
     do g₀ ← mk_mvar, g₁ ← mk_mvar, g₂ ← mk_mvar,
        refine ``(postcondition_impl %%g₀ %%g₁ %%g₂),
        set_goals [g₂],
        verify_step rule,
        set_goals [g₁]
   end,
   pure ()

meta def fetch_abstr_lemma (ls : name_map (list name)) : simp_lemmas → list name → tactic simp_lemmas
| s [] := pure s
| s (x::xs) :=
  do

meta def verify_proc (ids : parse using_ident) : tactic unit :=
do (val,p,m,v,q) ← tactic.get_spec',
   let proc_n := m.get_app_fn.const_name,
   let S := simp_lemmas.mk,
   simp_target simp_lemmas.mk [proc_n],
   repeat (apply_spec none),
   `[dsimp only { fail_if_unchanged := ff }]

run_cmd add_interactive [``frame,``s_intro,``s_intros, ``apply_spec, ``verify_proc]

end tactic

-- set_option trace.app_builder true
-- set_option pp.all true
-- #exit

@[spec]
lemma mk_buffer_spec {α} [is_record val α] (sz : ℕ) :
  spec _ emp
         (mk_buffer α sz)
         (λ p : tptr (queue α), p ⤇ queue.mk ([] : list α)) :=
begin
  verify_proc,
  -- dsimp [mk_buffer],
  -- -- done,
  -- -- apply bind_spec _ (ralloc_spec _), rintro p,
  -- apply_spec, dsimp,
  -- -- s_intros buffer Hbuffer,
  -- apply_spec, dsimp,
  -- s_intro x', cases x',
  -- verify_proc,
  -- repeat { apply_spec },
  -- dsimp,
  -- refine postcondition_impl _ _ _,
  -- apply pure_spec,
  -- apply_spec,
  -- -- rw ← emp_and (p ⤇ buffer),
  -- -- apply bind_spec _ (frame_rule _ _ _ _ (ralloc1_spec)), rintro q, dsimp,
  -- -- s_intros x,  apply_spec,
  -- done,
  -- apply bind_spec _ (frame_rule _ _ _ _ (ralloc1_spec)), rintro q, dsimp,
  -- simp only [and_p_exists_distrib_right,refinement.and_assoc],
  -- apply p_exists_intro_left, rintro ⟨ ⟩,
  -- apply and_then_spec _ _ _ (frame_rule _ _ _ _ (set_head_spec _ _ _ _ _ _ _ _)), dsimp, rintro ⟨ ⟩,
  -- apply and_then_spec _ _ _ (frame_rule _ _ _ _ (set_tail_spec _ _ _ _ _ _ _ _)), dsimp, rintro ⟨ ⟩,
  -- apply and_then_spec _ _ _ (frame_rule _ _ _ _ (set_repr_spec _ _ _ _ _ _ _ _)), dsimp, rintro ⟨ ⟩,
  -- apply and_then_spec _ _ _ (frame_rule _ _ _ _ (set_size_spec _ _ _ _ _ _ _ _)), dsimp, rintro ⟨ ⟩,
  -- apply and_then_spec _ _ _ (frame_rule _ _ _ _ (set_marker_spec _ _ _ _ _ _ _ _)), dsimp, rintro ⟨ ⟩,
  -- apply and_then_spec _ _ _ (frame_rule _ _ _ _ (set_count_spec _ _ _ _ _ _ _ _)), dsimp, rintro ⟨ ⟩,
  -- apply pure_spec, simp,
  have : p +. nat.mul (max 1 sz) (fixed_size val α) ≠ p,
  { cases p, dsimp [tptr.add], rw tptr.mk.inj_eq, apply ne_of_gt,
    apply nat.lt_add_of_pos_right,
    rw ← nat.mul_zero 0, apply mul_pos,
    apply lt_max_iff.mpr, left, norm_num,
    apply fixed_storable.pos_size },
  apply impl_exists,
  { apply impl_lift_and, swap,
    apply and_impl_and (impl_refl _),
    dsimp [cycle], apply impl_or_left, apply impl_exists 0, apply impl_exists x.length,
    simp [unused,queue.mk,list_repr'_eq_list_repr,Hbuffer,list_repr,storable.repr,fixed_storable.fixed_size],
    constructor,
    refl, exact this, simp, exact this,
    simp, apply lt_max_iff.mpr, norm_num },
end

def wipe_buffer {α} [storable val α] (p : tptr (queue α)) : IO unit :=
sorry

@[spec]
lemma wipe_buffer_spec {α} [fixed_storable val α] (p : tptr (queue α)) (vs : list α) :
  spec' _ (p ⤇ queue.mk vs) (wipe_buffer p) (p ⤇ queue.mk []) :=
sorry

def del_buffer {α} [fixed_storable val α] (p : tptr (queue α)) : IO unit :=
do wipe_buffer p,
   let p' : tptr $ buffer_node α := p.recast,
   r ← get_repr p',
   sz ← get_size p',
   rfree p',
   free r (sz * fixed_size val α)

lemma list_repr_recast {α β γ} [storable val α] {vs : list α}
  (p : tptr (list α)) (q : tptr β) :
  list_repr' val p vs (q.recast : tptr γ) = (list_repr' val p vs q : hProp val) :=
begin
  cases q, dsimp [tptr.recast],
  induction vs generalizing p, refl, simp [list_repr',*]
end

lemma list_repr_and_list_repr_impl_list_repr'_concat {α β} [storable val α] {us vs : list α}
  (p q : tptr (list α)) (r : tptr β) :
  list_repr' val p us q ⊛ list_repr' val q vs r =*> list_repr' val p (us ++ vs) r :=
begin
  induction us generalizing p,
  { simp [list_repr'],
    apply lift_and_impl, intro h, subst h },
  { simp [list_repr',refinement.and_assoc],
    apply and_impl_and (impl_refl _) (us_ih _) }
end

lemma list_repr_append {α β} [storable val α] {us vs : list α}
  (p : tptr (list α)) (r : tptr β) :
  list_repr' val p (us ++ vs) r = list_repr' val p us (p +. size val us) ⊛ list_repr' val (p +. size val us) vs r :=
sorry

open list

lemma list_repr_offset {α} [storable val α] {vs : list α}
  (p : tptr (list α)) (n : ℕ) :
  list_repr' val p vs (p +. n) = [| length vs = n |] ⊛ p ⤇ vs :=
sorry

lemma recast_inj {α β} (p q : tptr α) : p.recast = (q.recast : tptr β) ↔ p = q :=
sorry

lemma cycle_nil_impl_p_exists {α} [fixed_storable val α] (buf : buffer_node α)
  (Hmark : buf.marker = buf.repr +. buf.size * fixed_size val α) :
  cycle buf [] =*>
  ∃∃ trash, [| length trash = buf.size * fixed_size val α |] ⊛ buf.repr ⤇ trash :=
begin
  rcases buf with ⟨repr,tail,mark,head,size,count⟩, dsimp at *,
  simp [cycle], apply or_impl,
  { s_intros pre post,
    apply exists_impl, intro pre,
    apply exists_impl, intro post,
    -- simp
    -- apply impl_exists (pre + post),
    simp [list_repr',queue.mk], rw [refinement.and_comm, refinement.and_assoc],
    apply lift_and_impl, intro Hhd,
    rw [Hhd,refinement.and_comm,list_repr_recast],
    transitivity', apply list_repr_and_list_repr_impl_list_repr'_concat,
    rw [Hmark,list_repr_offset,length_append] },
  { apply exists_impl, intro first,
    apply exists_impl, intro last,
    apply exists_impl, intro mid,
    apply lift_and_impl, rintro ⟨H₀,H₁⟩, subst H₀, subst H₁,
    simp [list_repr',recast_inj], apply lift_and_impl, intro Htail,
    rw [← Htail,refinement.and_comm], apply lift_and_impl, intro Hhead,
    rw [Hhead,list_repr_recast,Hmark,list_repr_offset],
    apply impl_exists mid, refl },
end

-- lemma list_repr_queue {α β} [storable val α] {vs : list α}
--   (p : tptr (list α)) (q : tptr β) :
--   list_repr' p (queue.mk vs) q = list_repr' p (rec_bytes vs) q := _

lemma del_buffer_spec {α} [is_record val α] (p : tptr (queue α)) (vs : list α) :
  spec' _ (p ⤇ queue.mk vs) (del_buffer p) emp :=
begin
  verify_proc,
  dsimp [del_buffer],
  apply and_then_spec _ _ _ (wipe_buffer_spec _ _), rintro ⟨ ⟩,
  apply p_exists_intro_left, rintro ⟨repr,tl,mrk,hd,sz⟩,
  apply lift_intro, intro Hqueue,
  -- apply p_exists_intro_left, intro Hmarker,
  dsimp at *,
  apply bind_spec _ (frame_rule _ _ _ _ (get_repr_spec _ _ _ _ _ _ _)), intro repr,
  simp [refinement.and_assoc], apply lift_intro, intro h, subst h,
  apply bind_spec _ (frame_rule _ _ _ _ (get_size_spec _ _ _ _ _ _ _)), intro size,
  simp [refinement.and_assoc], apply lift_intro, intro h, subst h,
  apply and_then_spec _ _ _ (frame_rule _ _ _ _ (rfree_spec _ _)), rintro ⟨ ⟩,
  simp [queue.mk],
  apply precondition_impl _ (cycle_nil_impl_p_exists _ _),
  apply p_exists_intro_left, intro trash,
  dsimp, apply lift_intro, intro Htrash,
  rw ← Htrash, apply free_spec, apply Hqueue.marker_loc,
end

open is_object

def buffer_put {α} [is_object val punit α] (p : tptr (queue α)) (v : tptr α) : IO bool :=
do let p' : tptr (buffer_node α) := p.recast,
   count ← get_count p',
   size ← get_size p',
   if count = size then
     pure ff
   else do
     tl ← get_tail p',
     mrk ← get_marker p',
     move val punit tl.recast v,
     if tl +. 1 = mrk then
       get_repr p' >>= set_tail p'
     else set_tail p' $ tl +. 1,
     pure tt

@[simp]
lemma fixed_size_word {α} [fixed_storable val α] : fixed_size val (word val α) = fixed_size val α := rfl

lemma move_to_cycle {α} [is_object val punit α] (v : tptr α) (arg : α)
  (buf : buffer_node α) (qe : list α) :
  spec' _ (v ⤇ arg ⊛ cycle buf qe)
          (move val unit buf.tail.recast v)
          (trashed val v ⊛ cycle { tail := buf.tail +. fixed_size val α, .. buf } (qe ++ [arg])) :=
begin
  simp [cycle,p_and_or_distrib_left,and_p_exists_distrib_left],
  apply or_left_right_spec,
  { simp [list_repr_append], apply p_exists_intro_left, intro pre,
    apply p_exists_intro_left, intro post,
    apply p_exists_intro pre,
    cases post with hd post, { admit },
    apply p_exists_intro post, frame,
    dsimp [list_repr'],
    have : (buf.head +. storable.size val qe) = buf.tail.recast, admit,
    simp [this,list_repr_recast],
    frame,
    frame,
    trace "FOO",
    frame' },
end

#exit

lemma tail_wrap_around {α} [fixed_storable val α] {a c d e f} (ls : list α) :
  cycle ⟨a,c,c,d,e,f⟩ ls = cycle ⟨a,a,c,d,e,f⟩ ls :=
sorry

lemma buffer_put_spec {α} [is_object val punit α] (p : tptr (queue α)) (v : tptr α) (arg : α) (vs : list α) :
  spec _ (v ⤇ arg ⊛ p ⤇ queue.mk vs)
         (buffer_put p v)
         (λ r, if r then trashed val v ⊛ p ⤇ queue.mk (vs ++ [arg])
                    else v ⤇ arg ⊛ p ⤇ queue.mk vs ) :=
begin
  rw refinement.and_comm,
  simp [buffer_put,and_p_exists_distrib_right,refinement.and_assoc],
  apply p_exists_intro_left, rintro ⟨repr,tl,mark,hd,size,count⟩,
  dsimp at *, apply lift_intro,
  intro H,  have H' := marker_ne_repr H,
  rcases H with ⟨H₀,H₁,H₂⟩, dsimp at *,
  apply bind_spec _ (frame_rule _ _ _ _ (get_count_spec _ _ _ _ _ _ _)), intro count,
  simp [refinement.and_assoc], apply lift_intro, intro h, subst h,
  apply bind_spec _ (frame_rule _ _ _ _ (get_size_spec _ _ _ _ _ _ _)), intro size,
  simp [refinement.and_assoc], apply lift_intro, intro h, subst h,
  split_ifs,
  { apply pure_spec, simp [and_p_exists_distrib_left],
    apply impl_exists, apply impl_lift_and _, refl,
    constructor; assumption, },
  { apply bind_spec _ (frame_rule _ _ _ _ (get_tail_spec _ _ _ _ _ _ _)), intro tail,
    simp [refinement.and_assoc], apply lift_intro, intro h, subst h,
    apply bind_spec _ (frame_rule _ _ _ _ (get_marker_spec _ _ _ _ _ _ _)), intro marker,
    simp [refinement.and_assoc], apply lift_intro, intro h, subst h,
    rw refinement.and_comm _ (v ⤇ arg),
    apply and_then_spec _ _ _ (frame_rule' _ _ _ _ (move_to_cycle _ _ _ _)), intro,
    split_ifs,
    { rw bind_assoc,
      apply bind_spec _ (frame_rule _ _ _ _ (get_repr_spec p.recast _ _ _ _ _ _)), intro repr',
      simp [refinement.and_assoc], apply lift_intro, intro h, subst repr',
      apply bind_spec _ (frame_rule _ _ _ _ (set_tail_spec p.recast _ _ _ _ _ _ _)), rintro ⟨ ⟩,
      apply pure_spec, dsimp, simp [tail_wrap_around,h_1,and_p_exists_distrib_left],
      apply impl_exists, ac_mono, rw refinement.and_assoc,
      apply impl_lift_and _, refl, constructor; assumption },
    { apply bind_spec _ (frame_rule _ _ _ _ (set_tail_spec _ _ _ _ _ _ _ _)), rintro ⟨ ⟩,
      apply pure_spec, simp, ac_mono, apply impl_exists, apply impl_lift_and _, refl,
      replace h_1 := ne.symm h_1,
      constructor; try { assumption }, } }
end

def buffer_take {α} (p : tptr (queue α)) : IO (option (tptr α)) := sorry

lemma buffer_take_spec {α} [fixed_storable val α] (p : tptr (queue α)) (v : α) (vs : list α) :
  spec _ (p ⤇ queue.mk (v :: vs))
         (buffer_take p)
         (λ r, ∃∃ r', [|r = some r'|] ⊛ p ⤇ queue.mk vs) :=
sorry

lemma buffer_take_spec' {α} [fixed_storable val α] (p : tptr (queue α)) :
  spec _ (p ⤇ queue.mk [])
         (buffer_take p)
         (λ r, [| r = none |] ⊛ p ⤇ queue.mk []) :=
sorry

end circular_buffer


end examples
