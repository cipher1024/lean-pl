import category.basic
import heap.basic
import data.finmap
import tactic.omega
import tactic.linarith

namespace memory

variables value : Type

variables {value}

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

def erase_all (p : ptr) (n : ℕ) (m : heap value) : heap value :=
(list.range n).foldl (λ m i, finmap.erase (p + i) m) m

@[simp] lemma erase_all_zero (p : ptr) (m : heap value) : erase_all p 0 m = m := rfl

lemma erase_all_succ (p : ptr) (n : ℕ) (m : heap value) : erase_all p n.succ m = finmap.erase (p+n) (erase_all p n m) :=
by simp [erase_all, list.foldl_eq_foldr' _ m (list.range _),list.range_concat]

lemma erase_all_one_add (p : ptr) (n : ℕ) (m : heap value) : erase_all p (1+n) m = finmap.erase (p+n) (erase_all p n m) :=
by rw nat.add_comm; apply erase_all_succ p _ m

lemma erase_all_succ' (p : ptr) (n : ℕ) (m : heap value) : erase_all p n.succ m = finmap.erase p (erase_all (p+1) n m) :=
by { simp only [erase_all,list.range_succ_eq_map],
     rw [list.foldl_eq_of_comm',list.foldl_map],
     congr, simp only [add_zero, nat.add_comm, add_left_comm],
     simp only [finmap.erase_erase, forall_3_true_iff, eq_self_iff_true] }

lemma erase_all_one_add' (p : ptr) (n : ℕ) (m : heap value) : erase_all p (1+n) m = finmap.erase p (erase_all (p+1) n m) :=
by rw nat.add_comm; apply erase_all_succ' p _ m

open list nat

lemma mem_erase_all (p p' : ptr) (m : heap value) : Π {n}, p ∈ erase_all p' n m ↔ ¬ p ∈ range' p' n ∧ p ∈ m
| 0 := by simp [erase_all_zero]
| (succ n) := by { simp only [erase_all_succ, mem_cons_iff, add_comm, mem_range', finmap.mem_erase, ne.def, add_left_comm, mem_erase_all, not_and_distrib],
                   repeat { rw ← and_assoc }, apply and_congr _ (iff.refl _),
                   clear mem_erase_all, dsimp [ptr] at p p', omega nat }

open finmap

@[simp]
lemma mem_maplet (p q : ptr) (v : value) : p ∈ maplet q v ↔ p = q :=
by simp only [maplet, not_mem_empty, finmap.mem_singleton, iff_self, or_false]

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

@[simp]
lemma heap.mem_mk (p : ptr) (vs : list (ptr × value)) : p ∈ heap.mk vs ↔ p ∈ vs.map prod.fst :=
by { simp only [heap.mk,mem_list_to_finmap,_root_.and_comm (_ ∈ vs),_root_.and_assoc,  list.mem_map,
                iff_self, exists_eq_left, exists_and_distrib_left, heq_iff_eq, list.map, prod.exists] }

instance : has_le (heap value) :=
{ le := λ x y, ∀ a b, x.lookup a = some b → y.lookup a = some b }

instance : preorder (heap value) :=
{ le_refl := λ h a b H, H,
  le_trans := λ h₀ h₁ h₂ H H' p _ HH, H' _ _ (H _ _ HH),
  .. memory.has_le
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

lemma add_inj {h₀ h₁ : option (heap value)} (hh : option (heap value)) (hh₀ hh₁ : heap value)
  (H₀ : some hh₀ = h₀ ⊗ hh) (H₁ : some hh₁ = h₁ ⊗ hh) (H₂ : h₀ ⊗ hh = h₁ ⊗ hh) :
  h₀ = h₁ :=
begin
  cases h₀; [skip, cases h₁], cases H₀, cases H₁, cases hh, cases H₀,
  rw [← union_eq_add_of_disjoint (disjoint_of_add _ H₀),← union_eq_add_of_disjoint (disjoint_of_add _ H₁),option.some_inj,finmap.union_cancel] at H₂, rw H₂,
  all_goals { apply disjoint_of_add, assumption },
end

end memory

namespace separation
open memory

structure tptr (val : Type) (α : Type*) :=
(get : ptr)

variables {val : Type} {α : Type*} {β : Type*}
include val
local notation `tptr` := tptr val

instance : decidable_linear_order (tptr α) :=
decidable_linear_order.lift tptr.get (λ ⟨_,_,x⟩ ⟨_,_,y⟩, congr_arg _) (by apply_instance)

def tptr.recast (β) (p : tptr α) : tptr β :=
{ get := p.get }

def tptr.add (p : tptr α) (n : ℕ) : tptr α :=
{ get := p.get + n }

infixl ` +. `:65 := tptr.add

@[simp, separation_logic]
lemma offset_zero (p : tptr α) : p +. 0 = p := by cases p; refl

@[simp, separation_logic]
lemma offset_offset (p : tptr α) (n m : ℕ) : p +. n +. m = p +. (n + m) :=
congr_arg _ (nat.add_assoc _ _ _)

lemma gt_offset_of_gt {α} (p : tptr α) {n : ℕ} (h : n > 0) : p +. n > p :=
by cases p; dsimp [(+.)]; apply lt_add_of_pos_right _ h

lemma le_offset (p : tptr α) {n : ℕ} : p ≤ p +. n :=
by cases p; dsimp [(+.)]; apply nat.le_add_right

lemma offset_ne (p : tptr α) {n : ℕ} (h : n > 0) : p +. n ≠ p :=
ne_of_gt (gt_offset_of_gt _ h)

@[simp, separation_logic]
lemma recast_offset (p : tptr α) (n : ℕ) : (p +. n).recast β = (p.recast β +. n) := rfl

lemma recast_le_iff_le_recast (p : tptr α) (q : tptr β) :
  p.recast β ≤ q ↔ p ≤ q.recast α :=
by cases p; cases q; refl

@[simp]
lemma tptr.mk_offset (p : ptr) (n : ℕ) : tptr.mk val α p +. n = tptr.mk val α (p + n) := rfl

open list

lemma some_mk_enum_from_cons (p : ptr) (x : val) (xs : list val) :
  some (heap.mk (enum_from p (x :: xs))) = some (maplet p x) ⊗ some (heap.mk $ xs.enum_from $ p + 1) :=
begin
  rw ← union_eq_add_of_disjoint,
  { simp [enum_from] },
  intro p', simp, intros h h', subst p',
  cases nat.not_succ_le_self _ h'
end

end separation
