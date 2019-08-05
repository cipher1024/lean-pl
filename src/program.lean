
import heap.lemmas heap.tactic misc prop
import data.nat.basic

universes u

namespace separation
open memory finmap

variables (value : Type)

@[reducible]
def ST (α : Type) := state_t (heap value) set α

open state_t
variables {value} {α : Type}
include value
local notation `ST` := ST value

def read (p : ptr) : ST value :=
do m ← get,
   match m.lookup p with
   | none := @monad_lift set _ _ _ ∅
   | (some x) := pure x
   end

def assign (p : ptr) (v : value) : ST punit :=
modify (finmap.insert p v)

def assign_vals (p : ptr) (vs : list value) : ST punit :=
modify $ (∪ heap.mk (vs.enum_from p))

def choice (p : α → Prop) : ST α :=
@monad_lift set (state_t _ set) _ _ (p : set α)

def alloc (vs : list value) : ST ptr :=
do m ← get,
   p ← choice $ λ p : ptr, ∀ i < vs.length, (p + i) ∉ m,
   assign_vals p vs,
   pure p

section

variable value

def alloc' (n : ℕ) : ST ptr :=
choice (λ v : list value, v.length = n) >>= alloc

def dealloc (p : ptr) (n : ℕ) : ST unit :=
do m ← get,
   modify $ erase_all p n

end

def for' : Π  (k : ℕ) (n : ℕ) (f : ℕ → ST punit), ST punit
| _ 0 f := pure punit.star
| k (nat.succ n) f := f k >> for' k.succ n f

def for : Π (n : ℕ) (f : ℕ → ST punit), ST punit
| 0 f := pure punit.star
| (nat.succ n) f := for n f >> f n

-- def clone (p : tptr (list value)) (n : ℕ) : ST ptr :=
-- do q ← alloc' value n,
--    for n (λ i,
--      do v ← read (p + i),
--         assign (q + i) v),
--    pure q

-- def map (p : ptr) (f : ℕ → value → value) (n : ℕ) : ST punit :=
-- for n (λ i,
--   do v ← read (p + i),
--      assign (p + i) (f i v) )

section talloc

-- open

variables (value) (α) [fixed_storable value α] (n : ℕ)
-- local notation `ST` := ST value
local notation `tptr` := tptr value

def malloc : ST (tptr (list value)) :=
tptr.mk _ _ <$> alloc' value n

def ralloc : ST (tptr (list α)) :=
tptr.mk _ _ <$> alloc' value (n * fixed_size value α)

def ralloc1 : ST (tptr α) :=
tptr.mk _ _ <$> alloc' value (fixed_size value α)

variables {α}

variables {value}

def free (p : tptr (list α)) (n : ℕ) : ST unit :=
dealloc value p.get (n * fixed_size value α)

end talloc

@[simp]
lemma mem_run_modify (x : punit) (h h' : heap value) (g : heap value → heap value) :
  (x,h') ∈ (modify g : ST punit).run h ↔ h' = g h :=
by simp only [modify,state_t.modify,pure,state_t.run,punit.punit_eq_iff, true_and, id.def, iff_self, set.mem_singleton_iff, prod.mk.inj_iff, prod.map]

@[simp]
lemma mem_bind_run {β} (x' : β) (h h' : heap value) (f : ST α) (g : α → ST β) :
  (x',h') ∈ (f >>= g).run h ↔ (∃ x'' h'', (x'',h'') ∈ f.run h ∧ (x',h') ∈ (g x'').run h'') :=
by simp only [exists_prop, state_t.run_bind, set.mem_Union, set.bind_def, iff_self, prod.exists]

@[simp]
lemma mem_choice_run (x' : α) (h h' : heap value) (p : α → Prop) :
  (x',h') ∈ (choice p : ST α).run h ↔ p x' ∧ h' = h :=
by simp only [choice, set.mem_Union, set.bind_def, set.mem_singleton_iff, prod.mk.inj_iff, run_monad_lift, set.pure_def];
   split; simp only [and_imp, exists_imp_distrib]; intros; try { subst x' }; repeat { split }; assumption

@[simp]
lemma mem_run_pure (x x' : α) (h h' : heap value) :
  (x',h') ∈ (pure x : ST α).run h ↔  x' = x ∧ h' = h :=
by simp only [iff_self, set.mem_singleton_iff, prod.mk.inj_iff, set.pure_def, state_t.run_pure]

@[simp]
lemma mem_run_get (x' : heap value) (h h' : heap value) :
  (x',h') ∈ (get : ST _).run h ↔  x' = h ∧ h' = h :=
by simp only [get, monad_state.lift, pure, set.mem_singleton_iff, prod.mk.inj_iff, id.def, state_t.run_get]

@[simp]
lemma mem_run_read (x' : value) (p : ptr) (h h' : heap value) :
  (x',h') ∈ (read p : ST _).run h ↔ h.lookup p = some x' ∧ h' = h :=
begin
  simp only [read, monad_state.lift, pure, exists_prop, set.mem_Union, set.bind_def, mem_run_get, prod.mk.inj_iff, run_bind, prod.exists], split,
  { rintro ⟨a,b,⟨h'',H⟩,H'⟩, cases h : (lookup p b); subst_vars; rw h at H'; simp [read] at H', cases H', casesm* _ ∧ _,
    subst_vars, rw h, exact ⟨rfl,rfl⟩ },
  { rintro ⟨h,⟨⟩,⟨⟩⟩, refine ⟨_,_,⟨rfl,rfl⟩,_⟩, simp [h,read] }
end

section tactic

open tactic
omit value

meta def sane_names : tactic unit :=
do ls ← local_context,
   ls.reverse.mmap' $ λ l,
     when (l.local_pp_name.to_string.length > 5) $ do
       t ← infer_type l,
       n ← revert l,
       let fn := t.get_app_fn,
       let v := if fn.is_constant
                   then fn.const_name.update_prefix name.anonymous
                else if fn.is_local_constant
                   then fn.local_pp_name
                   else `h,
       v ← get_unused_name v,
       intro $ mk_simple_name $ (v.to_string.to_list.take 1).as_string,
       intron (n - 1),
       skip

end tactic

open list

@[simp]
lemma mem_run_alloc_cons (v : value) (vs : list value) (h h' : heap value) (p : ptr) :
  (p, h') ∈ (alloc (v :: vs)).run h ↔ ∃ h'', some h' = some h'' ⊗ some (maplet p v) ∧ p ∉ h ∧ (p+1, h'') ∈ (alloc vs).run h :=
begin
  simp [alloc,assign_vals,enum_from], split; intro h; casesm * [Exists _, _ ∧ _]; subst_vars;
  constructor_matching* [_ ∧ _, Exists _]; try { assumption <|> refl <|> sane_names },
  { have : disjoint (maplet p v) (heap.mk (enum_from (p + 1) vs)) := disjoint_maplet_heap_mk_add_one _ _,
    rw [← union_eq_add_of_disjoint,union_comm_of_disjoint this,union_assoc],
    rw disjoint_union_left, refine ⟨_,this.symm⟩,
    symmetry, simp [disjoint_maplet], apply h_1 0 (nat.zero_lt_one_add _) },
  { apply h_1 0, linarith },
  { introv hi, specialize h_1 (1 + i) (nat.add_lt_add_left hi _),
    rw ← nat.add_assoc at h_1, exact h_1, },
  { introv hi, cases i, { exact n },
    specialize h_1 i, rw [← nat.succ_eq_add_one,nat.succ_add_eq_succ_add] at h_1,
    rw [nat.add_comm,nat.succ_eq_add_one] at hi,
    apply h_1 (nat.lt_of_add_lt_add_right hi) },
  { have : disjoint (maplet p v) (heap.mk (enum_from (p + 1) vs)),
    { simp },
    rw [union_comm_of_disjoint this, ← union_assoc],
    apply eq_union_of_eq_add e }
end

@[simp]
lemma mem_run_alloc (vs : list value) (h h' : heap value) (p : ptr) :
  (p, h') ∈ (alloc vs).run h ↔ some h' = some h ⊗ some (heap.mk $ vs.enum_from p) :=
begin
  induction vs generalizing p h',
  { simp [alloc,assign_vals,list.enum_from], },
  { simp only [some_mk_enum_from_cons, mem_run_alloc_cons, vs_ih, add_zero], split,
    { simp only [and_imp, exists_imp_distrib], intros h'' H₀ H₁ H₂,
      simp only [*, memory.add_assoc, and_true, eq_self_iff_true], congr' 1,
      rw memory.add_comm, },
    { rintro H₀, existsi h ∪ heap.mk (enum_from (p + 1) vs_tl),
      rw [H₀,union_eq_add_of_disjoint,memory.add_assoc], split,
      { clear_except, congr' 1, apply memory.add_comm },
      split, {
         have : disjoint (maplet p vs_hd) h, prove_disjoint,
         apply this, simp },
      { exact rfl },
      prove_disjoint } }
end

end separation
