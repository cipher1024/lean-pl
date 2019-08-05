
import category.bitraversable.instances
import heap.basic

open memory

section disjoint

variables {val : Type}

inductive disj : list (list (heap val)) → Prop
| nil : disj []
| cons {xs : list (heap val)} {xss : list (list (heap val))} :
  (∀ (x ∈ xs) (ys ∈ xss) (y ∈ ys), finmap.disjoint x y) →
  disj xss → disj (xs :: xss)

def union' : list (heap val) → heap val
| [] := ∅
| [x] := x
| (x :: xs) := x ∪ union' xs

def {u} all_pairs' {α : Type u} : list α → list (list α) → list (α × α)
| xs [] := []
| xs (y::ys) := xs.product y ++ all_pairs' (y ++ xs) ys

def {u} all_pairs {α : Type u} : list (list α) → list (α × α) :=
all_pairs' []

variables (x x' : heap val)
variables (xs : list (heap val))
variables (xss : list (list (heap val)))

open finmap

def disj_all := (∀ (x ∈ xs) (ys ∈ xss) (y ∈ ys), disjoint x y)

variables {x' x xs xss}

def all_pairs_disjoint (xs : list (heap val × heap val)) :=
∀ x y, (x,y) ∈ xs → disjoint x y

lemma all_pairs_disjoint_of_all_pairs_disjoint_cons {x : heap val × heap val} {xs : list $ heap val × heap val} :
  all_pairs_disjoint (x :: xs) → all_pairs_disjoint xs
| H x y Hxy := H _ _ (or.inr Hxy)

lemma disjoint_of_all_pairs_disjoint_cons {x y : heap val} {xs : list $ heap val × heap val} :
  all_pairs_disjoint ((x,y) :: xs) → disjoint x y
| H := H _ _ (or.inl rfl)

lemma all_pairs_disjoint_of_disj' : Π {xss : list (list (heap val))} (ys : list (heap val)), disj_all ys xss → disj xss → ∀ x y, (x,y) ∈ all_pairs' ys xss → disjoint x y
| (xs :: xss) ys Hys (disj.cons h h') a b h'' :=
have a ∈ ys ∧ b ∈ xs ∨ (a, b) ∈ all_pairs' (xs ++ ys) xss, by simpa [all_pairs',list.mem_append] using h'',
or.cases_on this
  (λ ⟨h,h'⟩, Hys _ h xs (or.inl rfl) _ h')
  (λ h₂,
    have h₃ : disj_all (xs ++ ys) xss,
      from (λ a' Ha' zs Hzs y Hy,
        by { simp at Ha', cases Ha';
             [ apply h _ Ha' _ Hzs _ Hy,
               apply Hys _ Ha' zs (or.inr Hzs) _ Hy] }),
    all_pairs_disjoint_of_disj' (xs ++ ys) h₃ h' _ _ (h₂ ))


lemma all_pairs_disjoint_of_disj : Π {xss : list (list (heap val))}, disj xss → all_pairs_disjoint (all_pairs xss)
| xss h a b h'' :=
all_pairs_disjoint_of_disj' [] (λ x, false.elim) h _ _ h''

lemma disj_of_disj_cons_cons : disj ((x :: xs) :: xss) → disj (xs :: xss)
| (disj.cons h' h) := disj.cons (λ y hy ys hys z hz, h' _ (or.inr hy) ys hys _ hz) h

lemma disj_of_disj_nil_cons : disj ([] :: xss) → disj xss
| (disj.cons _ h) := h

@[simp]
lemma union_nil : @union' val [] = ∅ :=
rfl

@[simp]
lemma union_cons : union' (x :: xs) = x ∪ union' xs :=
by { cases xs with x' xs; simp [union'] }

def sum' : list (list (heap val)) → option (heap val)
| [] := some ∅
| [x] := some (union' x)
| (x :: xs) := some (union' x) ⊗ sum' xs

@[simp]
lemma sum_cons : sum' (xs :: xss) = some (union' xs) ⊗ sum' xss :=
by cases xss; simp [sum']

variables {x xs xss}

section finmap

variables {α : Type*} {β : α → Type*}

lemma sub_union_left [decidable_eq α] {x y z : finmap β} (h : x ⊆ y) : x ⊆ y ∪ z :=
λ a hx, finmap.mem_union.mpr $ or.inl (h _ hx)

lemma sub_union_right [decidable_eq α] {x y z : finmap β} (h : x ⊆ z) : x ⊆ y ∪ z :=
λ a hx, finmap.mem_union.mpr $ or.inr (h _ hx)

lemma sub_union_self_left [decidable_eq α] {x y : finmap β} : x ⊆ x ∪ y :=
λ a hx, finmap.mem_union.mpr $ or.inl hx

lemma sub_union_self_right [decidable_eq α] {x y : finmap β} : x ⊆ y ∪ x :=
λ a hx, finmap.mem_union.mpr $ or.inr hx

@[refl]
lemma sub_refl (x : finmap β) : x ⊆ x :=
λ a, id

@[trans]
lemma sub_trans {x y z : finmap β} (h₀ : x ⊆ y) (h₁ : y ⊆ z) : x ⊆ z :=
λ a hx, h₁ _ (h₀ _ hx)

end finmap

lemma sub_union'_of_mem {x : heap val} {xs : list (heap val)} (h : x ∈ xs) :
  x ⊆ union' xs :=
begin
  induction xs; cases h,
  { subst xs_hd, simp, apply sub_union_self_left },
  { transitivity', apply xs_ih h,
    simp, apply sub_union_self_right }
end

lemma eq_union'_of_eq_sum {x : heap val} {xss : list $ list (heap val)}
  (H : some x = sum' xss) :
  x = union' (xss.map union') :=
begin
  induction xss generalizing x,
  { simp [union',sum'] at *, exact H },
  { simp [sum'] at *,
    rcases add_eq_some' _ _ _ H with ⟨ y, Hy ⟩,
    rw ← Hy at H,
    replace H := eq_union_of_eq_add H,
    replace Hy := xss_ih Hy, cc },
end

lemma disj_of_some_eq_sum :
  some x = sum' xss → disj xss :=
begin
  introv Hxy,
  induction xss with xs xss generalizing x, constructor,
  simp at Hxy,
  rcases add_eq_some' _ _ _ Hxy with ⟨y, Hy⟩,
  constructor,
  { introv Hx Hys Hy', rw ← Hy at Hxy,
    replace Hxy := disjoint_of_add _ Hxy,
    apply memory.disjoint_mono' (sub_union'_of_mem Hx) _ Hxy,
    rw eq_union'_of_eq_sum Hy,
    transitivity' union' ys,
    apply sub_union'_of_mem Hy',
    apply sub_union'_of_mem, rw list.mem_map,
    existsi [_,Hys], refl },
  { apply xss_ih Hy }
end

lemma all_pairs_disj_of_some_eq_sum (h : some x = sum' xss) :
  all_pairs_disjoint (all_pairs xss) :=
all_pairs_disjoint_of_disj $ disj_of_some_eq_sum h

def all_subset (x : heap val) (xs : list (heap val)) :=
∀ y ∈ xs, y ⊆ x

lemma all_subset_of_some_eq_sum (h : some x = sum' xss) :
  all_subset x xss.join :=
begin
  induction xss generalizing x,
  { rintro _ ⟨ ⟩ },
  { simp at h,
    rcases add_eq_some' _ _ _ h with ⟨w,hw⟩,
    rw ← hw at h,
    simp [all_subset],
    rw eq_union_of_eq_add h,
    rintro y (h'|⟨l,h₀,h₁⟩),
    { apply sub_union_left (sub_union'_of_mem h'), },
    { apply sub_union_right,
      apply xss_ih hw y, rw list.mem_join,
      exact ⟨_,h₀,h₁⟩ }, }
end

lemma all_subset_of_all_subset_cons (h : all_subset x (x' :: xs)) : all_subset x xs :=
λ a Ha, h _ (or.inr Ha)

lemma subset_of_all_subset_cons (h : all_subset x (x' :: xs)) : x' ⊆ x :=
h _ (or.inl rfl)

end disjoint

namespace tactic

@[reducible]
meta def graph := expr_map (list (expr × expr))

meta def parse_union : expr → tactic (list expr)
| `(%%x ∪ %%y) := (++) <$> parse_union x <*> parse_union y
| e := pure [e]
-- | _ := failed

meta def parse_sum : expr → tactic (list (list expr))
| `(some %%x) := list.ret <$> parse_union x
| `(%%x ⊗ %%y) := (++) <$> parse_sum x <*> parse_sum y
| _ := failed

lemma heap.rotate {α} (h : heap α) (h' h'' : option (heap α)) :
  h' ⊗ h'' = some h ↔ some h = h' ⊗ h'' :=
⟨ eq.symm, eq.symm ⟩

meta def add_disj_edge (d : graph) (pr n n' : expr) : tactic graph :=
do pr' ← mk_mapp ``finmap.disjoint.symm [none,none,none,none,pr],
   pure $ (d.insert_cons n (n', pr)).insert_cons n' (n,pr')

open function

meta def add_disjoint (xs : list (expr × expr × expr)) (d : graph) : tactic graph :=
xs.mfoldl (λ d ⟨x,y,h⟩,
  do h' ← mk_mapp ``finmap.disjoint.symm [none,none,none,none,h],
     pure $ (d.insert_cons x (y,h)).insert_cons y (x,h') ) d

meta def add_subset (xs : list (expr × expr × expr)) (d : graph) : graph :=
xs.foldl (λ d ⟨x,y,h⟩, d.insert_cons x (y,h) ) d

meta def reachable' (g : graph) (root : expr) : expr → expr_map expr → expr × expr → tactic (expr_map expr)
| pr s n :=
  if s.contains n.1 then pure s
  else do
    pr' ← to_expr ``(sub_trans %%pr %%(n.2)),
    (g.find_def [] n.1).mfoldl (reachable' pr') (s.insert n.1 pr')

meta def reachable (g : graph) (v : expr) : tactic (expr_map expr) :=
do pr ← mk_mapp ``sub_refl [none,none,v],
   reachable' g v pr (mk_expr_map ) (v, pr)


setup_tactic_parser

meta def to_pair : expr × expr → tactic expr
| (x,y) := mk_app ``prod.mk [x,y]

meta def to_list (t : expr) : list expr → tactic expr
| [] := mk_app ``list.nil [t]
| (x :: xs) :=
  do xs' ← to_list xs,
     mk_app ``list.cons [x,xs']

meta def to_sum (t : expr) (xs : list (list expr)) : tactic expr :=
do ts ← mk_app ``list [t],
   xs' ← xs.mmap (to_list t) >>= to_list ts,
   mk_app ``sum' [xs']

meta def replace' (h : expr) (p : option expr) (e : expr) : tactic expr :=
note h.local_pp_name p e <* clear h

meta def mk_disj_hyps : list (expr × expr) → expr → tactic (list (expr × expr × expr))
| [] h := clear h *> pure []
| ((x,y) :: xss) h :=
  do Hxy ← mk_mapp ``disjoint_of_all_pairs_disjoint_cons [none,none,none,none,h],
     Hxy ← note (`h ++ x.local_pp_name ++ y.local_pp_name <.> "disj") none Hxy,
     h ← mk_mapp ``all_pairs_disjoint_of_all_pairs_disjoint_cons [none,none,none,h] >>=
       replace' h none,
     list.cons (x,y,Hxy) <$> mk_disj_hyps xss h

meta def mk_sub_hyps (s : expr) : list expr → expr → tactic (list (expr × expr × expr))
| [] h := clear h *> pure []
| (x :: xss) h :=
  do Hxy ← mk_mapp ``subset_of_all_subset_cons [none,none,none,none,h],
     Hxy ← note (`h ++ x.local_pp_name ++ s.local_pp_name <.> "sub") none Hxy,
     h ← mk_mapp ``all_subset_of_all_subset_cons [none,none,none,none,h] >>=
       replace' h none,
     -- trace!"sub: s: {s}; x: {x}; h: {infer_type h}",
     list.cons (x,s,Hxy) <$> mk_sub_hyps xss h

meta def mk_sum_form (h : expr) : tactic (expr × expr × expr × list (list expr)) :=
do `(%%l = %%r) ← infer_type h,
   `(some %%l') ← pure l,
   `(option %%v) ← infer_type l,
   r ← parse_sum r,
   r' ← to_sum v r,
   ht ← mk_app `eq [l,r'],
   h ← assertv (h.local_pp_name ++ `sum) ht h,
   pure (v,h,l',r)

meta def mk_disjointness_hyps (v h : expr) (r : list (list expr)) : tactic (list $ expr × expr × expr) :=
do p ← mk_mapp ``all_pairs_disj_of_some_eq_sum [none,none,none,h],
   h ← note h.local_pp_name none p,
   prod_t ← mk_app ``prod [v,v],
   let r := all_pairs r,
   x ← r.mmap to_pair >>= to_list prod_t,
   x ← mk_app ``all_pairs_disjoint [x],
   h ← replace' h (some x) h,
   mk_disj_hyps r h

meta def mk_subset_hyps (v h l : expr) (r : list (list expr)) : tactic (list $ expr × expr × expr) :=
do p ← mk_mapp ``all_subset_of_some_eq_sum [none,none,none,h],
   h ← note h.local_pp_name none p,
   let r := r.join,
   r' ← to_list v r,
   ht ← mk_app ``all_subset [l,r'],
   h ← replace' h (some ht) h,
   mk_sub_hyps l r h

meta def parse_asm (s d : graph) : expr → expr → tactic (graph × graph)
| pr `(finmap.disjoint %%x %%y) :=
  if x.is_local_constant ∧ y.is_local_constant
    then do
      d' ← add_disj_edge d pr x y,
      pure (s,d')
    else pure (s,d)
| pr `(%%x = %%y) :=
  do [[x]] ← parse_sum x | pure (s,d),
     (v,h,x,r) ← mk_sum_form pr,
     ys ← mk_disjointness_hyps v h r,
     d ← add_disjoint ys d,
     zs ← mk_subset_hyps v h x r,
     let s := add_subset zs s,
     pure (s,d)
| _ _ := pure (s,d)

meta def mk_graph (t : expr) : tactic (graph × graph) :=
do let s : graph := expr_map.mk (list (expr × expr)),
   let d : graph := expr_map.mk (list (expr × expr)),
   ls ← local_context,
   ht ← mk_app ``heap [t],
   ls.mfoldl (λ ⟨s,d⟩ l,
     do t ← infer_type l,
        if t = ht then
          pure (s.insert_if_absent l [],d.insert_if_absent l [])
        else
          parse_asm s d l t ) (s, d)

meta def split_asm : expr → expr → tactic unit
| h `(some %%h₀ = some %%h₁ ⊗ some %%h₂ ⊗ %%h₃) :=
  do h' ← mk_app ``add_eq_some' [h],
     h' ← note `h none h',
     [(_, ([w,h'],_))] ← cases_core h',
     ht ← infer_type h',
     h ← mk_eq_symm h' >>= flip rewrite_hyp h,
     split_asm h' ht
| _ _ := skip

meta def preprocess : tactic unit :=
do `[simp only [option.some_inj,tactic.heap.rotate,memory.add_assoc,finmap.union_assoc] at * { fail_if_unchanged := ff }],
   subst_vars,
   ls ← local_context,
   ls.mmap' $ λ l,
     infer_type l >>= split_asm l

meta def interactive.prove_disjoint : tactic unit :=
do preprocess,
   `(finmap.disjoint %%x %%y) ← target,
   `(heap %%v) ← infer_type x,
   (s,d) ← mk_graph v,
   mx ← reachable s x,
   my ← reachable s y,
   mx.to_list.any_of $ λ ⟨a,pa⟩,
     (d.find_def [] a).any_of $ λ ⟨b,pb⟩,
       do pc ← my.find b,
          refine ``(disjoint_mono' %%pa %%pc %%pb)

end tactic

open memory tactic native

variables
  h₀ h₁ h₂ h₃ h₄ h₅
  h₆ h₇ h₈ h₉ : heap ℕ

example (H₂ : some h₂ = some h₁ ⊗ some h₀)
        (H₅ : some h₅ = some h₄ ⊗ some h₃)
        -- (H₈ : some h₈ = some h₇ ⊗ some h₆)
        (H₈ : some h₈ = some (h₇ ∪ h₄) ⊗ some h₆ ⊗ some h₄ ⊗ some (h₃ ∪ h₀ ∪ h₂))
        (H₈ : some h₈ = some (h₇ ∪ h₄) ⊗ some (h₃ ∪ h₀ ∪ h₂))
        -- (H₉ : some h₉ = some h₂ ⊗ some h₅)
        (H : finmap.disjoint h₅ h₂)
        (H₁₀ : some h₀ = some h₁)  :
  finmap.disjoint h₀ h₄ :=
begin
  prove_disjoint,
end
