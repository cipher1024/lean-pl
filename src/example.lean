
import spec

namespace examples

namespace circular_buffer
export memory (ptr)
open separation separation.hProp

def val := ptr
@[reducible] def IO (α : Type) := ST val punit α

open function list

instance ptr.storable : is_record val ptr :=
separation.separation.is_record

instance tptr.storable {α} : is_record val (tptr α) :=
equiv.is_record tptr.get (tptr.mk _) (λ x, rfl)

instance unsigned.storable : is_record val ℕ :=
separation.separation.is_record

structure buffer_node (α : Type*) [fixed_storable val α] :=
(repr tail marker : tptr (list $ word val α))
(head : tptr (list α))
(size count : ℕ)

open separation (renaming rec_entry.mk_ -> mk_)

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

section setters
open separation
variables {α : Type*} [fixed_storable val α] (p : tptr (buffer_node α))

def get_repr : IO (tptr (list $ word val α)) := (tptr.mk _) <$> read p.get
def get_head : IO (tptr (list α)) :=   (tptr.mk _) <$> read (p.get+1)
def get_marker : IO (tptr (list $ word val α)) := (tptr.mk _) <$> read (p.get+2)
def get_tail : IO (tptr (list $ word val α)) := (tptr.mk _) <$> read (p.get+3)
def get_size : IO ℕ :=                 read (p.get+4)
def get_count : IO ℕ :=                read (p.get+5)

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

run_cmd mk_simp_attr `abstr

@[abstr]
lemma queue_repr {α} [fixed_storable val α] (p : tptr (queue α)) (vs : list α) :
  (p ⤇ queue.mk vs : hProp val) = ∃∃ b : buffer_node α, [| buffer_inv b |] ⊛ p.recast ⤇ b ⊛ cycle b vs :=
rfl

def mk_buffer (α) [fixed_storable val α] (sz : ℕ) : IO (tptr $ queue α) :=
do let sz' := max 1 sz,
   p ← ralloc val (word val α) sz',
   r ← ralloc1 val (buffer_node α),
   set_head r p.recast,
   set_tail r p,
   set_repr r p,
   set_size r sz',
   set_marker r (p +. sz' * fixed_storable.fixed_size val α),
   set_count r 0,
   pure r.recast

-- set_option trace.app_builder true
-- set_option pp.all true
-- #exit

@[spec]
lemma mk_buffer_spec {α} [is_record val α] (sz : ℕ) :
  spec _ emp
         (mk_buffer α sz)
         (λ p : tptr (queue α), p ⤇ queue.mk ([] : list α)) :=
begin
  simp only with abstr,
  verify_proc!,
  have : p +. nat.mul (max 1 sz) (fixed_size val α) ≠ p,
  { cases p, dsimp [tptr.add], rw tptr.mk.inj_eq, apply ne_of_gt,
    apply nat.lt_add_of_pos_right,
    rw ← nat.mul_zero 0, apply mul_pos,
    apply lt_max_iff.mpr, left, norm_num,
    apply fixed_storable.pos_size },
  { apply impl_lift_and, swap,
    { dsimp [cycle], apply impl_or_left, apply impl_exists 0, apply impl_exists x.length,
      simp [a,unused,queue.mk,list_repr',storable.repr,fixed_storable.fixed_size],
      rw [unused_iff_exists], apply impl_exists x, apply impl_lift_and a,
      simp [list_repr'_eq_list_repr,a] },
    constructor,
    refl, exact this, simp, exact this,
    simp, apply lt_max_iff.mpr, norm_num },
end

#check @get_size

def buffer_size {α} [fixed_storable val α] (p : tptr (queue α)) : IO ℕ :=
get_size (p.recast : tptr (buffer_node α))

@[spec]
lemma buffer_size_spec {α} [fixed_storable val α] (p : tptr (queue α)) (vs : list α) :
  spec _ (p ⤇ queue.mk vs)
         (buffer_size p)
         (λ r, [| r = length vs |] ⊛ p ⤇ queue.mk vs) :=
sorry

open separation.is_object

instance {α} : decidable_eq (tptr α)
| ⟨_,p⟩ ⟨_,q⟩ := decidable_of_iff (p = q) (by rw tptr.mk.inj_eq)

def remove {α} [is_object val unit α] (p : tptr (queue α)) : IO unit :=
do let p' : tptr (buffer_node α) := p.recast,
   sz ← buffer_size p,
   if sz = 0 then pure ()
   else do
     hd ← get_head p',
     mark ← get_marker p',
     delete val _ (hd.recast : tptr α),
     set_head p' (hd +. fixed_size val α),
     hd ← get_head p',
     repr ← get_repr p',
     when (mark = hd.recast) (set_head p' repr.recast)

section tactic
open tactic

@[tactic.entailment]
meta def entailment' : tactic unit :=
do trace_state,
focus1 $
assumption <|>
do intros,
   `[simp [hProp.and_p_exists_distrib_left,hProp.and_p_exists_distrib_right]
     { fail_if_unchanged := ff } ],
   iterate_at_most 10 $ do
     { `(_ =*> p_exists _) ← target,
       applyc ``impl_exists },
   done <|>
     ac_refl' <|>
     s_shrink <|>
     assumption
  -- (try (applyc ``impl_of_eq); ac_refl) <|>

end tactic

@[spec]
lemma delete_cycle_spec {α} [is_object val unit α] (v : α) (vs : list α)
  (b : buffer_node α) (H : buffer_inv b) :
  spec' _ (cycle b (v :: vs))
          (delete val punit (b.head.recast : tptr α))
          (cycle { head := b.head +. fixed_size val α, .. b } vs) :=
begin
  dsimp [cycle],
  apply or_left_right_spec,
  { s_intros, dsimp [list_repr'],
    verify_proc,
    simp [fixed_storable.is_fixed],
    s_shrink,
    rintro ⟨ ⟩,  },
end

-- set_option trace.separation.failed_spec true

@[spec]
lemma remove_spec {α} [is_object val unit α] (p : tptr (queue α)) (v : α) (vs : list α) :
  spec' _ (p ⤇ queue.mk (v :: vs)) (remove p) (p ⤇ queue.mk vs) :=
begin
  verify_proc!,
  { simp only [queue_repr,when],
    s_intros x Hsz Hx, rw if_neg,
    verify_proc,
    split_ifs ; verify_proc,
    { have H := marker_ne_repr Hx, cases Hx,
      apply impl_lift_and,
      constructor; try { assumption }, dsimp,
      simp only [tptr.recast_eq], exact H, simp only [cycle],
      apply or_impl,
      { s_intros pre post,
        -- apply hProp.impl_or_right,
        -- simp only [unused_iff_exists],
        s_intros,
        s_assert : x.marker = x.tail,
        { s_apply [list_repr_impl_le' x_3,list_repr_impl_le _ _ vs],
          prop h₀ h₁, apply le_antisymm _ h₁, rw [h,recast_le_iff_le_recast],
          apply h₀ },
        contradiction },
      { s_intros first last mid Hvs,
        rw h,
        s_assert : first = [],
        { s_apply list_repr_self_impl_eq_nul', },
        subst first, rw ← Hvs,
        apply hProp.impl_or_left,
        s_existsi [0,mid], simp [unused,list_repr',- recast_offset] } },
    { rw lift_eq_emp,
      have H := marker_ne_repr Hx, cases Hx,
      constructor; dsimp; try { assumption } },
    rw [Hsz,length,nat.add_one], contradiction },
end

def wipe_buffer {α} [is_object val unit α] (p : tptr (queue α)) : IO unit :=
do sz ← buffer_size p,
   for' 0 sz $ λ i, remove p

@[spec]
lemma wipe_buffer_spec {α} [is_object val unit α] (p : tptr (queue α)) (vs : list α) :
  spec' _ (p ⤇ queue.mk vs) (wipe_buffer p) (p ⤇ queue.mk []) :=
begin
  verify_proc!, s_intro h, generalize : 0 = k,
  induction sz generalizing vs k; dsimp [for'],
  { cases vs, verify_proc, cases h },
  { cases vs, cases h, specialize sz_ih vs_tl,
    verify_proc, apply nat.succ_inj h }
end

def del_buffer {α} [is_object val unit α] (p : tptr (queue α)) : IO unit :=
do wipe_buffer p,
   let p' : tptr $ buffer_node α := p.recast,
   r ← get_repr p',
   sz ← get_size p',
   rfree _ p',
   free _ r (sz * fixed_size val α)

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

lemma del_buffer_spec {α} [is_object val unit α] (p : tptr (queue α)) (vs : list α) :
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

open separation.is_object

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
