
import program prop misc
-- import tactic.tidy
import tactic.monotonicity

universes u

declare_trace separation.failed_spec

open memory separation.hProp finmap list

variables {value : Type} {s s' α : Type}
include value
local notation `ST` := separation.ST value
local notation `heap` := memory.heap value
local notation `hProp` := separation.hProp value
local notation `tptr` := separation.tptr value

namespace separation

def spec (p : hProp) (m : ST α) (q : α → hProp) : Prop :=
∀ ⦃h h' frame x⦄, (x,h') ∈ m.run h → holds h frame p → holds h' frame (q x)

def spec' (p : hProp) (m : ST α) (q : hProp) : Prop :=
spec p m (λ _, q)

lemma frame_rule (m : ST α) (p frame : hProp) (q : α → hProp) (hm : spec p m q) :
  spec (p ⊛ frame) m (λ r, q r ⊛ frame) :=
begin
  intros h h' frame' r Hrun, dsimp,
  rw [holds_of_holds_and,holds_of_holds_and],
  apply exists_imp_exists, intro h₁,
  apply and.imp_right, intro Hp,
  apply hm Hrun Hp,
end

lemma frame_rule' (m : ST α) (p frame : hProp) (q : α → hProp) (hm : spec p m q) :
  spec (frame ⊛ p) m (λ r, frame ⊛ q r) :=
begin
  simp [and_comm frame],
  apply frame_rule _ _ _ _ hm,
end

lemma pure_spec (p : hProp) (q : α → hProp)
  (x : α) (h : p =*> q x) :
  spec p (pure x) q :=
begin
  introv _, simp, rintro ⟨ ⟩ ⟨ ⟩,
  apply exists_imp_exists, intro,
  apply and_implies id (h.elim _),
end

lemma pure_spec' {α} (p : α → hProp) (x : α)  :
  spec (p x) (pure x) p :=
pure_spec _ _ _ (impl.intro $ λ h, id)

lemma bind_spec {β} {p : hProp} (q : α → hProp) {r : β → hProp}
    {m : ST α} {f : α → ST β}
    (h₀ : spec p m q) (h₁ : ∀ x, spec (q x) (f x) r) :
  spec p (m >>= f) r :=
begin
  dsimp [spec], introv, simp [], intros y h'' hm hf hp,
  apply h₁ _ hf,
  apply h₀ hm hp,
end

lemma and_then_spec {β} {p : hProp} (q : α → hProp) {r : β → hProp}
    (m : ST α) (f : ST β)
    (h₀ : spec p m q) (h₁ : ∀ x, spec (q x) f r) :
  spec p (m >> f) r :=
bind_spec q h₀ h₁

lemma p_exists_intro {α β} {p : hProp} {m : ST α} {q : α → β → hProp}
  (x : β) (H : spec p m (λ y, q y x)) :
  spec p m (λ x, p_exists (q x)) :=
begin
  intros h h' frame r hm hp,
  dsimp, rw holds_p_exists (q r),
  existsi x, apply H hm hp,
end

lemma p_exists_intro_left {β} {p : β → hProp} {m : ST α} {q : α → hProp}
  (H : ∀ x, spec (p x) m q) :
  spec (p_exists p) m q :=
by simp [spec,holds_p_exists]; introv hm; apply H _ hm

lemma lift_intro {p : Prop} {p' : hProp} {m : ST α} {q : α → hProp}
  (h : p → spec p' m q) :
  spec ([|p|] ⊛ p') m q :=
by rw lift_and_iff_p_exists; apply p_exists_intro_left h

lemma or_intro {p p' : hProp} {m : ST α} {q : α → hProp}
  (H  : spec p m q)
  (H' : spec p' m q) :
  spec (p ⋁ p') m q :=
λ h h' frame r hm hpp',
or.elim (holds_or_iff.mp hpp') (H hm) (H' hm)

lemma or_intro_left {p : hProp} {m : ST α} {q q' : α → hProp}
  (H' : spec p m q) :
  spec p m (λ r, q r ⋁ q' r) :=
λ h h' frame r hm hp,
holds_imp_holds_of_impl (impl.intro $ λ h, or.intro_left _) (H' hm hp)

lemma or_intro_right {p : hProp} {m : ST α} {q q' : α → hProp}
  (H' : spec p m q') :
  spec p m (λ r, q r ⋁ q' r) :=
λ h h' frame r hm hp,
holds_imp_holds_of_impl (impl.intro $ λ h, or.intro_right _) (H' hm hp)

lemma or_left_right_spec {p p' : hProp} {m : ST α} {q q' : α → hProp}
  (H  : spec p  m q)
  (H' : spec p' m q') :
  spec (p ⋁ p') m (λ r, q r ⋁ q' r) :=
or_intro (or_intro_left H) (or_intro_right H')

lemma precondition_impl {α} {p : hProp} (q : hProp) {r : α → hProp}
  {m : ST α} (hpq : p =*> q) (H : spec q m r) :
  spec p m r :=
by dsimp [spec]; introv hm hp; apply H hm (holds_imp_holds_of_impl hpq hp)

lemma postcondition_impl {α} {p : hProp} (q : α → hProp) {r : α → hProp}
  {m : ST α} (hqr : ∀ x, q x =*> r x) (H : spec p m q) :
  spec p m r :=
by dsimp [spec]; introv hm hp; apply holds_imp_holds_of_impl (hqr _) (H hm hp)

end separation

namespace tactic

omit value
section spec_attribute

open separation

meta def bound_var : expr → name
| (expr.lam n _ _ _) := n
| _ := `_

meta def get_spec : expr → tactic (expr × expr × expr × expr × expr)
| `(@spec %%val %%α %%p %%m %%q) :=
do { v ← mk_local_def (bound_var q) α,
     q ← head_beta (q v),
     pure (val, p, m, v, q) }
| `(@spec' %%val %%α %%p %%m %%q) :=
do { v ← mk_local_def `v α,
     pure (val, p, m, v, q) }
-- | `(%%p =*> %%q) := _
| t := (pformat!"not a specification: {t}" : pformat) >>= fail

meta def get_spec' : tactic (expr × expr × expr × expr × expr) :=
target >>= instantiate_mvars >>= get_spec

open tactic

meta def spec_target (n : name) : tactic name :=
do t ← mk_const n >>= infer_type,
   (vs,t) ← mk_local_pis t,
   (_,_,m,_,_) ← get_spec t,
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

setup_tactic_parser

meta def vec_cases_end (h : expr) : tactic unit :=
do rule ← mk_const ``list.length_eq_zero,
   h ← rewrite_hyp rule h,
   subst h

meta def vec_cases_aux : expr → expr → list name → tactic unit
| h `(list.length %%xs = %%n) ns :=
  do `(nat.succ %%n) ← whnf n | vec_cases_end h,
     rule ← mk_const ``list.length_eq_succ, -- [xs,n],
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
setup_tactic_parser
open tactic

open separation

lemma spec_congr {α} {p p' : hProp} {q q' : α → hProp} {m : ST α}
  (hp : p = p') (hq : ∀ x, q x = q' x) (hm : spec p m q) : spec p' m q' :=
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

-- meta inductive fragment
-- | refl : expr → fragment
-- | drop (n : expr) : fragment → fragment
-- | take (n : expr) : fragment → fragment


-- meta def is_fragment : expr → expr → option fragment
-- | e e' :=
--   if e = e' then fragment.refl e
--             else match e with
--                  | `(drop %%n %%e₀) := do fr ← is_fragment e₀ e',
--                                           fragment.drop n fr
--                  | `(take %%n %%e₀) := do fr ← is_fragment e₀ e',
--                                           fragment.take n fr
--                  | _ := none
--                  end

-- meta def fragment.complement' (val p ls q : expr) : expr → fragment → (expr → tactic expr) → tactic (list expr)
-- | n (fragment.refl e) f := pure []
-- | n (fragment.take n' e) f :=
--   do p' ← mk_app ``tptr.add [p,n],
--      let f' := λ e, f e >>= λ e, mk_app ``take [n',e],
--      ls' ← mk_app ``drop [n',ls],
--      ls' ← f ls',
--      e' ← mk_app ``list_repr' [p',ls',q],
--      cons e' <$> fragment.complement' n e f
-- | n (fragment.drop n' e) f :=
--   do p' ← mk_app ``tptr.add [p,n],
--      let f' := λ e, mk_app ``drop [n',e] >>= λ e, f e,
--      ls' ← mk_app ``take [n',ls],
--      ls' ← f ls',
--      e' ← mk_app ``list_repr' [p',ls',q],
--      n'' ← mk_app ``add [n,n'],
--      cons e' <$> fragment.complement' n'' e f

-- meta def fragment.complement (val p ls q : expr) (fr : fragment) : tactic (list expr) :=
-- fragment.complement' val p ls q `(0) fr pure

-- meta def check_fragments (val p ls q x : expr) (xs : list expr) : list expr → tactic  (expr × list expr × list expr)
-- | (y@`(list_repr' _ %%p' %%ls' %%q') :: ys) :=
--                   match is_fragment ls' ls with
--                   | (some fr) :=
--                     do trace "fragment",
--                        cs ← fr.complement val p ls q,
--                        pure (y,cs ++ xs,ys)
--                   | none := do (a,as,bs) ← check_fragments ys,
--                                pure (a,as,y::bs)
--                   end
-- | (y :: ys) := do (a,as,bs) ← check_fragments ys,
--                   pure (a,as,y::bs)
-- | [] := fail "A no match found"

-- meta def match_fragments : list expr → list expr → tactic (expr × list expr × list expr)
-- | (x@`(list_repr' %%val %%p %%ls %%q) :: xs) ys :=
--   check_fragments val p ls q x xs ys <|>
--   do trace x,
--      (a,as,bs) ← match_fragments xs ys,
--      pure (a,x::as,bs)
-- -- | (`(list_repr %%val %%p %%ls) :: xs) ys := _
-- | (x :: xs) ys := do (a,as,bs) ← match_fragments xs ys,
--                      pure (a,x::as,bs)
-- | [] ys := fail "B no match found"

@[interactive]
meta def frame : tactic unit :=
focus1 $
do (val,p,m,v,q) ← tactic.get_spec',
   ps ← parse_assert p,
   qs ← parse_assert q,
   (a,ps,qs) ← first_match ps qs,
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

-- meta def find_lift : list expr → tactic (option (expr × list expr))
-- | [] := pure none
-- | (x@`(separation.hProp.lift _) :: xs) := pure (some (x, xs))
-- | (x :: xs) :=
--   do some (y, ys) ← find_lift xs | pure none,
--      pure (some (y, x::ys))

open tactic

@[tactic.s_intro]
meta def s_intro_spec (n : parse (ident_ <|> pure (name.mk_string "_" name.anonymous))) (tac : tactic unit) : tactic unit :=
do `[simp only [and_p_exists_distrib_left,and_p_exists_distrib_right]
               { fail_if_unchanged := ff }],
   some (val,p,_,_,_) ← try_core $ get_spec' | tac,
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

-- meta def ac_refl_aux : tactic unit :=
-- do `[dsimp { fail_if_unchanged := ff }],
--    (lhs, rhs) ← target >>= match_eq,
--    xs ← parse_assert lhs,
--    xs.mmap' $ λ x, generalize x >> intro1,
--    cc <|> fail "ac_refl_aux"

-- meta def ac_refl' : tactic unit :=
-- do try (applyc ``impl_of_eq),
--    -- target >>= instantiate_mvars >>= change,
--    -- `[dsimp],
--    cc <|>
--      ac_refl_aux
--      -- <|>
--      -- fail!"ac_refl': {target}\nmeta vars: {expr.list_meta_vars <$> target}"

-- @[interactive]
-- meta def s_intro (n : parse $ ident_ <|> pure `_) : tactic unit :=
-- do `[simp only [and_p_exists_distrib_left,and_p_exists_distrib_right]
--                { fail_if_unchanged := ff }],
--    `(@impl %%val %%p %%q) ← target | s_intro_spec n,
--    match p with
--    | `(p_exists _) :=
--      do applyc ``exists_impl,
--         intro n >> pure ()
--    | _ :=
--    do xs ← parse_assert p,
--       some (x, xs) ← find_lift xs | failed,
--       let p' := mk_assert val (x :: xs),
--       g ← mk_app `eq [p,p'] >>= mk_meta_var,
--       gs ← get_goals, set_goals [g],
--       `[simp only [and_emp,emp_and] { fail_if_unchanged := ff } ],
--       done <|> ac_refl',
--       set_goals gs,
--       get_assignment g >>= rewrite_target,
--       applyc ``lift_and_impl,
--       intro n, pure ()
--    end

-- @[interactive]
-- meta def s_intros : parse ident_* → tactic unit
-- | [] := repeat (s_intro `_)
-- | ns := ns.mmap' s_intro

-- meta def find_frame' (e : expr) : list expr → tactic (list expr)
-- | [] := fail "frame not found"
-- | (x :: xs) :=
--   xs <$ unify e x <|>
--   cons x <$> find_frame' xs

-- meta def find_frame_aux : list expr → list expr → tactic (list expr)
-- | [] xs := pure xs
-- | (x::xs) ys :=
--   do ys' ← find_frame' x ys,
--      find_frame_aux xs ys'

-- meta def find_diff : list expr → list expr → tactic (list expr × list expr × list expr)
-- | [] xs := pure ([], [], xs)
-- | (x::xs) ys :=
--   do (b,ys') ← prod.mk tt <$> find_frame' x ys <|> pure (ff,ys),
--      (l,m,r) ← find_diff xs ys',
--      if b
--        then pure (l,x::m,r)
--        else pure (x::l,m,r)

-- /--
-- `find_frame e e'` returns `r` and `pr` such that `pr : e ⊛ r = e'`
-- -/
-- meta def find_frame (e e' : expr) : tactic (expr × expr) :=
-- do `(hProp %%val) ← infer_type e,
--    le ← parse_assert e,
--    le' ← parse_assert e',
--    lr ← find_frame_aux le le',
--    let r := mk_assert val lr,
--    t ← to_expr ``(%%e ⊛ %%r = %%e') >>= instantiate_mvars,
--    (_,pr) ← solve_aux t
--      (`[simp only [emp_and,and_emp] { fail_if_unchanged := ff } ]; ac_refl'),
--    pure (r,pr)

@[replaceable]
meta def unify_args' (e e' : expr) : tactic unit :=
do guard (e.get_app_fn.const_name = e'.get_app_fn.const_name) <|> fail format!"different calls: {e.get_app_fn} {e'.get_app_fn}",
   s ← cc_state.mk_using_hs,
   let args := e.get_app_args,
   let args' := e'.get_app_args,
   guard (args.length = args'.length) <|> fail "argument list mismatch",
   mzip_with' (λ a a', try (unify a a') <|> fail!"arguments `{a}` and `{a'}` do not unify\n`{e}`, `{e'}`") args args',
   -- s.eqv_proof e e'
   skip

meta def selected_goals (p : tactic bool) (tac : tactic unit) : tactic unit :=
all_goals (mcond p tac skip)

meta def is_spec (t : expr) : tactic bool :=
do (_,t) ← mk_local_pis t,
   pure (t.is_app_of ``spec ∨ t.is_app_of ``spec')

meta def all_spec_goals : tactic unit → tactic unit :=
selected_goals $ target >>= is_spec

meta def all_entails_goals : tactic unit → tactic unit :=
selected_goals $ do
  (_,t) ← target >>= mk_local_pis,
  pure (t.is_app_of ``impl)

meta def all_side_conditions : tactic unit → tactic unit :=
selected_goals $ do
  (_,t) ← target >>= mk_local_pis,
  pure $ ¬ (t.is_app_of ``spec ∨ t.is_app_of ``spec' ∨ t.is_app_of ``impl)

meta def cc_prove_eq (e e' : expr) : tactic expr :=
do s ← cc_state.mk_using_hs,
   e ← instantiate_mvars e,
   e' ← instantiate_mvars e',
   s ← s.internalize e,
   s ← s.internalize e',
   s.eqv_proof e e'

@[replaceable]
meta def specialize_spec'' (spec p call : expr) : tactic unit :=
do when_tracing `separation.failed_spec trace!"try {spec}",
   (args,spec') ← infer_type spec >>= mk_meta_pis,
   (val,p',m,v,q) ← get_spec spec',
   unify_args call m,
   ps  ← parse_assert p,
   ps' ← parse_assert p',
   let (vs,ps'') := ps'.partition $ λ e : expr, e.is_meta_var,
   fr ← find_frame_aux ps'' ps <|> fail!"framing {ps'} {ps}",
   let fr' := mk_assert val fr,
   q' ← head_beta q >>= lambdas [v],
   cc_prove_eq call m >>= rewrite_target <|> fail!"spec: {spec}\ncannot prove that {call} and {m} are equal",
   e ← if vs.empty then
     mk_mapp ``frame_rule [none, none, m, p', fr', q', spec.mk_app args]
     else do
       { [v] ← pure vs | fail "only one abstract predicate can be supported",
         unify v fr',
         return $ spec.mk_app args },
   to_expr ``(precondition_impl _ _ %%e) >>= apply,
   pure ()

-- lemma shrink_impl (l m r : hProp) {p q : hProp}
--   (h₀ : l ⊛ m = p) (h₁ : r ⊛ m = q) (h₂ : l =*> r) :
--   p =*> q :=
-- h₀ ▸ (h₁ ▸ and_impl_and h₂ $ impl_refl _)

-- lemma split_impl (p₀ p₁ q₀ q₁ : hProp) {p q : hProp}
--   (h₀ : p₀ ⊛ p₁ = p) (h₁ : q₀ ⊛ q₁ = q) (h₂ : p₀ =*> q₀) (h₃ : p₁ =*> q₁) :
--   p =*> q :=
-- h₀ ▸ (h₁ ▸ and_impl_and h₂ h₃)

@[replaceable]
meta def try_unfold' (attr_names : list name) (hs : list simp_arg_type) (tac : tactic unit) (cfg : simp_config) : tactic unit :=
tac <|> do
  (lmms, ids) ← mk_simp_set tt (`separation_logic :: attr_names) hs,
  simp_target lmms ids { fail_if_unchanged := ff, .. cfg },
  tac

meta def combine (tac_a tac_b : tactic (list α)) : tactic (list α) :=
do a ← try_core tac_a,
   b ← try_core tac_b,
   match a, b with
   | none, none := failed
   | some a, none := pure a
   | none, some b := pure b
   | some a, some b := pure $ a ++ b
   end

meta def clear_specs (local_specs : expr_map (list expr)) : tactic unit :=
local_specs.to_list.mmap' $ λ ⟨_,x⟩, x.mmap clear


@[replaceable]
meta def verify_step' (ids : list simp_arg_type) (rule : option expr) (local_specs : expr_map (list expr)) : tactic unit :=
focus1 $
do ls ← spec_attr.get_cache,
   (val,p,m,v,q) ← tactic.get_spec',
   let proc_e := m.get_app_fn,
   let proc_n := proc_e.const_name,
   specs ← ↑(list.ret <$> rule) <|>
     combine (↑(local_specs.find proc_e))
             (↑(ls.find proc_n) >>= list.mmap mk_const) <|>
     fail!"no such procedure: {proc_n}",
   ps ← parse_assert p,
   when (is_trace_enabled_for `separation.failed_spec = tt)
     (trace!"• verify step" >> trace_state),
   when (is_trace_enabled_for `separation.failed_spec = tt)
     (trace!"candidate specs: {specs}"),
   -- sl ← ids.mmap (resolve_name >=> pure ∘ simp_arg_type.expr),
   specs.any_of (λ e,
     if is_trace_enabled_for `separation.failed_spec = tt
         then trace_error "msg" (specialize_spec e p m)
         else specialize_spec e p m)
     <|> fail!"no specification found. \nCandidates: {specs}",
   when (is_trace_enabled_for `separation.failed_spec = tt)
     (trace "• prove side conditions" >> trace_state),
   all_entails_goals (try $ do
      clear_specs local_specs,
      if is_trace_enabled_for `separation.failed_spec = tt
         then trace_error "msg" entailment
         else entailment),
   when (is_trace_enabled_for `separation.failed_spec = tt)
     (trace "• propositional" >> trace_state),
   all_side_conditions (try $ do clear_specs local_specs,
                                 assumption <|> cc <|>
                                   linarith' none none none ),
   when (is_trace_enabled_for `separation.failed_spec = tt)
     (trace "• next" >> trace_state)


open interactive

meta def with_simp_arg_list := (tk "with" *> simp_arg_list) <|> pure []

@[interactive]
meta def apply_spec (rule : parse texpr?) (ids : parse with_simp_arg_list)
  (local_specs : option (expr_map (list expr)) := none)
  (cfg : simp_config := {}) : tactic unit :=
focus1 $
try_unfold [] ids
(do intros,
   s_intros [],
   subst_vars,
   when_tracing `separation.failed_spec $ do
   { trace "\nBEGIN - apply_spec",
     trace_state,
     trace "END - apply_spec\n" },
   let local_specs := local_specs.get_or_else (expr_map.mk _),
   (val,p,m,v,q) ← get_spec',
   match m with
   | `(%%m >>= %%f) :=
     do applyc ``bind_spec,
        g::gs ← get_goals, set_goals [g],
        rule ← traverse to_expr rule,
        verify_step ids rule local_specs,
        gs' ← get_goals,
        set_goals (gs ++ gs'),
        x ← intro (bound_var f),
        t ← infer_type x,
        when (t.const_name ∈ [``punit,``unit]) $ () <$ cases x,
        all_entails_goals $ try entailment,
        skip
   | `(%%m >> %%f)  :=
     do applyc ``and_then_spec,
        g::gs ← get_goals, set_goals [g],
        rule ← traverse to_expr rule,
        verify_step ids rule local_specs,
        gs' ← get_goals,
        set_goals (gs ++ gs'),
        x ← intro (bound_var f),
        t ← infer_type x,
        when (t.const_name ∈ [``punit,``unit]) $ () <$ cases x,
        all_entails_goals $ try entailment,
        skip
   | `(pure _) := applyc ``pure_spec; try entailment
   | m :=
     do g₀ ← mk_mvar, g₁ ← mk_mvar, g₂ ← mk_mvar,
        refine ``(postcondition_impl %%g₀ %%g₁ %%g₂),
        set_goals [g₂],
        rule ← traverse to_expr rule,
        verify_step ids rule local_specs,
        gs ← get_goals,
        set_goals $ g₁ :: gs,
        -- trace "\n• Z", trace_state,
        all_entails_goals $ try entailment
   end,
   try `[dsimp only { fail_if_unchanged := ff }])
cfg

open native

@[interactive]
meta def verify_proc (unfold : parse (tk "!")?)
  (ids : parse simp_arg_list) (cfg : simp_config := {}) : tactic unit :=
do intros,
   cxt ← local_context,
   local_specs ← cxt.mfoldl
     (λ (m : rb_map expr (list expr)) l,
       do { (_,t) ← infer_type l >>= mk_local_pis,
            (val,p,cmd,_) ← get_spec t,
            pure $ m.insert_cons cmd.get_app_fn l } <|> pure m )
     (expr_map.mk (list expr)),
   when unfold.is_some $ do
   { (val,p,m,v,q) ← tactic.get_spec',
     let proc_n := m.get_app_fn.const_name,
     ns ← get_eqn_lemmas_for ff proc_n,
     let S := simp_lemmas.mk,
     S ← ns.mmap mk_const >>= S.append,
     simp_target S [``function.comp] },
   repeat1 (
   fail_if_unchanged $
     all_spec_goals (
       do -- trace "begin",
          apply_spec none ids (some local_specs) cfg))
          -- trace "end"))

-- @[interactive]
-- meta def s_existsi (wit : parse pexpr_list_or_texpr) : tactic unit :=
-- wit.mmap' $ λ w,
--   do `(%%p =*> %%q) ← target,
--      `[simp only [and_p_exists_distrib_left,and_p_exists_distrib_right] { fail_if_unchanged := ff }],
--      refine ``(impl_exists %%w _) <|>
--        do `[simp only [lift_and_iff_p_exists] { single_pass := tt } ],
--           `[simp only [and_p_exists_distrib_left,and_p_exists_distrib_right]
--                  { fail_if_unchanged := ff } ],
--           refine ``(impl_exists %%w _)

-- lemma lin_assert {p q : hProp} (pp : Prop) (h : p =*> [| pp |] ⊛ p) (h' : pp → p =*> q) : p =*> q :=
-- impl_trans h
--   (by s_intro h; exact h' h)

-- lemma lin_assert' {p q : hProp} (pp : Prop) (h : p =*> [| pp |] ⊛ True) (h' : pp → p =*> q) : p =*> q :=
-- begin
--   transitivity [| pp |] ⊛ p,
--   { rw lift_p_and_and, apply impl_and h (impl_refl _) },
--   { s_intro h, exact h' h }
-- end

-- @[interactive]
-- meta def s_assert (h : parse $ ident? <* tk ":") (e : parse texpr) : tactic unit :=
-- let h := h.get_or_else `this in
-- refine ``(lin_assert' %%e _ _); [skip, ()<$intro h]

-- meta def s_apply' (e : expr) : tactic unit :=
-- do t ← infer_type e,
--    (args,`(%%p =*> %%q)) ← mk_meta_pis t,
--    let e := e.mk_app args,
--    `(%%p' =*> %%q') ← target,
--    frp ← some <$> find_frame p p' <|> pure none,
--    frq ← some <$> find_frame q q' <|> pure none,
--    match frp, frq with
--    | some (pr,pp), some (qr,qp) := refine ``(split_impl %%p %%pr %%q %%qr %%pp %%qp %%e _)
--    | some (pr,pp), none := refine ``(impl_trans (shrink_impl %%p %%pr %%q %%pp rfl %%e) _)
--    | none, some (qr,qp) := refine ``(impl_trans _ (shrink_impl %%p %%qr %%q rfl %%qp %%e))
--    | none, none := fail!"No match found for `{e} : {t}`"
--    end,
--    try (reflexivity <|> applyc ``impl_True)

-- @[interactive]
-- meta def s_apply : parse types.pexpr_list_or_texpr → tactic unit :=
-- mmap' $ to_expr >=> s_apply'

-- @[interactive]
-- meta def s_assumptions : tactic unit :=
-- do cxt ← local_context,
--    focus1 $ cxt.for_each $ λ l, try $ s_apply' l

-- @[interactive]
-- meta def s_assumption : tactic unit :=
-- do cxt ← local_context,
--    focus1 $ cxt.any_of $ λ l, try $ s_apply' l

-- @[interactive]
-- meta def s_show (p : parse texpr) : tactic unit :=
-- do g ← to_expr p >>= mk_meta_var,
--    s_apply' g

-- lemma prop_proof {p : Prop} {q : hProp} (h : p) : q =*> [| p |] ⊛ True :=
-- impl_lift_and h impl_True

-- lemma prop_proof' {p : Prop} {q : hProp} (h : p) : q =*> True ⊛ [| p |] :=
-- impl_trans (prop_proof h) (impl_of_eq $ hProp.and_comm _ _)

-- @[interactive]
-- meta def prop (ls : parse ident_*) : tactic unit :=
-- do s_intros ls,
--    applyc ``prop_proof
--    <|> applyc ``prop_proof'

-- example {p q : hProp} : p =*> q :=
-- begin
--   s_assert h : 1 ≤ 2,
--   -- check_hyp
-- end

-- meta def fetch_abstr_lemma (ls : name_map (list name)) : simp_lemmas → list name → tactic simp_lemmas
-- | s [] := pure s
-- | s (x::xs) := _

-- run_cmd add_interactive [``frame,``s_intro,``s_intros, ``apply_spec, ``verify_proc, ``entailment]

end tactic

namespace separation

attribute [spec] pure_spec'

@[spec]
lemma assign_spec (p : tptr value) (v v' : value) :
      spec' (p ⤇ v) (assign p.get v') (p ⤇ v') :=
begin
  cases p,
  simp [spec',spec,assign,mem_run_modify],
  introv hh hh', simp only [hh', holds, maplets, add, disjoint_maplet, pure, add_zero, option.some_bind, exists_eq_right, and_emp],
  split_ifs, exact id, intro hh'', simp only [hh'', insert_union, insert_maplet],
end

lemma holds_maplet {h frame : heap} {p : ptr} {v : value} : holds h frame (p ↦ v) → h.lookup p = some v :=
begin
  simp [holds,maplets], intros Hh',
  rw [eq_union_of_eq_add Hh',maplet,singleton_union,lookup_insert],
end

@[spec]
lemma read_spec (p : ptr) (v : value) :
  spec (p ↦ v) (read p) (λ r, [|r = v|] ⊛ p ↦ v) :=
begin
  simp [spec], introv Hrun, rintro ⟨ ⟩ H,
  rw [holds_maplet H,option.some_inj] at Hrun,
  exact ⟨ Hrun.symm, H ⟩,
end

@[spec]
lemma read_spec' (p : tptr value) (v : value) :
  spec (p ⤇ v) (read p.get) (λ r, [|r = v|] ⊛ p ⤇ v) :=
by cases p; simp [read_spec]

@[spec]
lemma assign_array_spec (p : tptr (list value)) (vs : list value) (v' : value) (i : ℕ)
      (hi : i < length vs) :
      spec' (p+.i ⤇ nth' i vs) (assign (p+.i).get v') (p+.i ⤇ [v']) :=
begin
  have := exists_nth'_eq_of_lt vs _ hi,
  cases this with _ h,
  simp [h], apply assign_spec
end

@[spec]
lemma read_array_spec' (p : tptr (list value)) (i : ℕ) (vs : list value) (H : i < length vs) :
  spec (p+.i ⤇ nth' i vs) (read (p +. i).get) (λ r, [| [r] = nth' i vs |] ⊛ p+.i ⤇ nth' i vs) :=
begin
  have := exists_nth'_eq_of_lt vs _ H,
  cases this with _ h, rw h, simp [value_repr], apply read_spec
end

-- set_option pp.implicit true
-- set_option pp.notation false
-- set_option trace.separation.failed_spec true

section tactic

open tactic

-- @[interactive]
-- meta def with_tracing (tac : interactive.itactic) : tactic unit :=
-- save_options $ do
--   o ← get_options,
--   trace $ o.fold [] (::),
--   set_options $ o.set_bool `trace.separation.failed_spec tt,
--   tac
-- `separation.failed_spec

-- @[tactic.try_unfold]
-- meta def try_unfold' (attr_names : list name) (hs : list simp_arg_type) (tac : tactic unit) (cfg : simp_config) : tactic unit :=
-- tac <|> do
--   -- trace "• A",
--   (lmms, ids) ← mk_simp_set tt (`separation_logic :: attr_names) hs,
--   -- let _ := _,
--   -- trace!"• C: {hs}",
--   simp_target lmms ids { fail_if_unchanged := ff, .. cfg },
--   -- trace!"• B: {hs}",
--   tac

-- @[tactic.unify_args]
-- meta def unify_args' (e e' : expr) : tactic unit :=
-- do guard (e.get_app_fn.const_name = e'.get_app_fn.const_name) <|> fail format!"different calls: {e.get_app_fn} {e'.get_app_fn}",
--    s ← cc_state.mk_using_hs,
--    let args := e.get_app_args,
--    let args' := e'.get_app_args,
--    guard (args.length = args'.length) <|> fail "argument list mismatch",
--    mzip_with' (λ a a', (unify a a') <|> fail!"arguments `{a}` and `{a'}` do not unify\n`{e}`, `{e'}`") args args',
--    -- s.eqv_proof e e'
--    skip

-- @[tactic.specialize_spec]
-- meta def specialize_spec'' (spec p call : expr) : tactic unit :=
-- do (args,spec') ← infer_type spec >>= mk_meta_pis,
--    (val,p',m,v,q) ← get_spec spec',
--    trace m,
--    unify_args call m,
--    trace!"{m}, {call}, \np: {p}, \np': {p'}, \nq: {q}",
--    ps  ← parse_assert p,
--    ps' ← parse_assert p',
--    let (vs,ps'') := ps'.partition $ λ e : expr, e.is_meta_var,
--    fr ← find_frame_aux ps'' ps <|> fail!"framing {ps''} {ps}",
--    let fr' := mk_assert val fr,
--    q' ← head_beta q >>= lambdas [v],
--    cc_prove_eq call m >>= rewrite_target <|> fail!"spec: {spec}\ncannot prove that {call} and {m} are equal",
--    e ← if vs.empty then
--      mk_mapp ``frame_rule [none, none, none, m, p', fr', q', spec.mk_app args]
--      else do
--        { [v] ← pure vs | fail "only one abstract predicate can be supported",
--          unify v fr',
--          return $ spec.mk_app args },
--    to_expr ``(precondition_impl _ _ %%e) >>= apply,
--    pure ()

end tactic

lemma offset_succ {α} (p : tptr α) (n : ℕ) : p +. n.succ = p +. 1 +. n :=
by cases p; simp [(+.),nat.succ_eq_add_one]

-- set_option trace.separation.failed_spec true
-- set_option pp.implicit true
-- -- set_option pp.universes true
-- set_option trace.app_builder true

@[spec]
lemma read_array_spec (p : tptr (list value)) (i : ℕ) (vs : list value) (H : i < length vs) :
  spec (p ⤇ vs) (read (p +. i).get) (λ r, [| [r] = nth' i vs |] ⊛ (p ⤇ vs)) :=
begin
  induction vs generalizing p i, cases H,
  cases i; verify_proc [offset_succ] { single_pass := tt },
end

lemma and_then_spec' {β} {p : hProp} (q : hProp) {r : β → hProp}
    (m : ST α) (f : ST β)
    (h₀ : spec p m (λ _, q)) (h₁ : spec q f r) :
  spec p (m >> f) r :=
bind_spec (λ _, q) h₀ (λ _, h₁)

@[spec]
lemma map_spec {β} {p : hProp} {q : β → hProp}
    {m : ST α} {f : α → β}
    (h₀ : spec p m (q ∘ f))  :
  spec p (f <$> m) q :=
by rw map_eq_bind_pure; apply bind_spec _ h₀ (λ x, _); apply pure_spec'

@[spec]
lemma choice_spec (p : α → Prop) :
  spec emp (@choice value _ p) (λ r, [| p r |]) :=
by simp [spec]; introv h₀ h₁ h₂; exact ⟨h₀,h₁.symm ▸ h₂⟩

lemma choice_spec' {β} (pp : α → Prop) (f : α → ST β)
  (p : hProp) (q : β → hProp)
  (h : ∀ x, pp x → spec p (f x) q) :
  spec p (choice pp >>= f) q :=
by { dsimp [spec]; intros;
     simp only [exists_prop, set.mem_Union, set.bind_def, mem_choice_run, state_t.run_bind, prod.exists] at a,
     casesm* [_ ∧ _, Exists _], subst h_1,
     apply h _ ‹ _ › ‹ _ › ‹ _ › }

lemma get_spec (p : hProp) (q : heap → hProp)
  (h : ∀ x, p =*> q x) :
  spec p get q :=
by { dsimp [get,monad_state.lift]; introv _ Hrun; apply exists_imp_exists,
     intro hh, simp [pure] at Hrun, casesm* _ ∧ _, subst h',
     apply and.imp id, apply (h _).elim }

@[spec]
lemma get_spec' (p : hProp) :
  spec p get (λ _, p) :=
get_spec _ _ $ λ _, impl.intro $ λ σ, id

open list

@[spec]
lemma alloc_spec (vs : list value) : spec emp (alloc vs) (λ p, tptr.mk _ _ p ⤇ vs) :=
begin
  simp [spec],
  intros h h' frame p,
  -- simp only [mem_choice_run,mem_bind_run,assign_vals,mem_run_get,exists_imp_distrib,id,and_imp],
  intros H₀ H₁,
  -- simp only [alloc,exists_imp_distrib,id,and_imp,mem_run_pure,enum,mem_choice_run,mem_bind_run,mem_run_get,mem_run_modify,assign_vals] at ⊢,
  -- intros, subst_vars, simp,
  rw [← emp_and ({get := p} ⤇ vs)],
  -- conv in (x ↦ vs) { rw ← nat.add_zero x },
  rw eq_union_of_eq_add H₀,
  apply holds_union_and H₁ _ _,
  { simp!, clear H₀,
    induction vs generalizing p; simp [enum_from,maplets,emp,to_finmap_cons],
    apply and_applied_union, exact rfl, apply vs_ih,
    simp [disjoint_maplet], },
  prove_disjoint,
end

@[spec]
lemma alloc'_spec (n : ℕ) : spec emp (alloc' value n) (λ p, ∃∃ vs : list value, [|vs.length = n|] ⊛ (tptr.mk _ _ p ⤇ vs)) :=
by { verify_proc! }

open nat

@[spec]
lemma dealloc_spec (p : ptr) (vs : list value) : spec' (tptr.mk _ _ p ⤇ vs) (dealloc value p vs.length) emp :=
begin
  dsimp [dealloc],
  intros h h' frame _,
  simp only [mem_choice_run,mem_bind_run,assign_vals,mem_run_get,exists_imp_distrib,id,and_imp,mem_run_modify],
  introv H₀ H₁ H₂ H₃, subst x_1, subst x_2, subst h', cases x with p,
  -- simp only [dealloc,exists_imp_distrib,id,and_imp,mem_run_pure,enum,mem_choice_run,mem_bind_run,mem_run_get,mem_run_modify,assign_vals] at ⊢,
  -- intros, subst_vars,
  have : h = (erase_all p (length vs) h) ∪ heap.mk (vs.enum_from p),
  { rw erase_all_union_mk_self, apply le_of_add_eq_some frame,
    rcases H₃ with ⟨w,hw₀,hw₁⟩, simp [maplets_eq] at hw₁, subst w,
    exact hw₀ },
  rw [this,← emp_and (tptr.mk _ _ p ⤇ vs)] at H₃, clear this,
  rw holds_of_holds_union_iff at H₃, exact H₃, rw maplets_eq,
  { intros p', simp, clear H₃,
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

-- set_option trace.separation.failed_spec true

-- section tactic
-- open tactic

-- #check @tactic.entailment

-- -- @[tactic.entailment]
-- -- meta def entailment' (tac : tactic unit) : tactic unit :=
-- -- focus1 $
-- -- assumption <|>
-- -- do intros,
-- --    target >>= instantiate_mvars >>= change,
-- --    when_tracing `separation.failed_spec (trace "A"),
-- --    with_context!"• A: {target}" $ do
-- --      `[simp [hProp.and_p_exists_distrib_left,hProp.and_p_exists_distrib_right] with separation_logic
-- --        { fail_if_unchanged := ff } ],
-- --      with_context!"• B: {try_core target}" $ do
-- --        iterate_at_most 10 $ do
-- --          { `(_ =*> p_exists _) ← target,
-- --            applyc ``impl_exists },
-- --        with_context!"• C: {try_core target}" $ do
-- --        done <|>
-- --          assumption <|>
-- --          ac_refl'

-- end tactic

-- #check tactic.verify_step'
-- #check tactic.specialize_spec
-- #check tactic.entailment

@[spec]
lemma for_spec (n : ℕ) (f : ℕ → ST punit) (p : ℕ → hProp)
  (h : ∀ i, i < n → spec' (p i) (f i) (p i.succ)) :
  spec' (p 0) (for n f) (p n) :=
begin
  induction n,
  { verify_proc! },
  { verify_proc! },
end

@[spec]
lemma for_spec' {n : ℕ} {f : ℕ → ST punit}
  {p q : ℕ → hProp} (b : hProp)
  (h : ∀ i, i < n → spec' (b ⊛ p i) (f i) (b ⊛ q i)) :
  spec' (b ⊛ And p (range n))
          (for n f)
          (b ⊛ And q (range n)) :=
begin
  let P  := λ i, b ⊛ And q (range i) ⊛ And p (range' i (n - i)),
  let P' := λ i, And q (range i) ⊛ And p (range' i.succ (n - i.succ)),
  have h := for_spec n f P _,
  { simp only [P] at h, rw [nat.sub_zero,range_zero,And,emp_and,← range_eq_range',nat.sub_self,range'_zero,And,and_emp] at h,
    exact h },
  { intros i hn,
    have : spec' (P' i ⊛ b ⊛ p i) (f i) (P' i ⊛ b ⊛ q i),
    { apply frame_rule', apply h _ hn },
    convert this; dsimp [P,P'],
    { rw [hProp.and_assoc], transitivity b ⊛ And q (range i) ⊛ And p (i :: range' (succ i) (n - succ i)),
      rw [cons_range',nat.sub_succ,succ_pred_eq_of_pos _],
      apply nat.lt_sub_right_of_add_lt, rw zero_add, exact hn,
      rw And, ac_refl },
    { rw [range_concat,And_append,And,And,and_emp], ac_refl } }
end



-- @[spec]
-- lemma clone_spec (p : tptr (list value)) (vs : list value) :
--   spec (p ⤇ vs)
--          (clone p vs.length)
--          (λ q, (p ⤇ vs) ⊛ (q ⤇ vs) ) :=
-- begin
--   verify_proc!,

--   s_intros trash H,
--   simp [hProp.maplets_eq_And q,H],
--   verify_proc, rw ← hProp.maplets_eq_And,
--   entailment,
-- end

-- #exit

open function

local notation `fixed_storable` := fixed_storable value

-- @[spec]
-- lemma map_spec' (p : ptr) (f : ℕ → value → value) (vs : list value) :
--   spec' (tptr.mk _ _ p ⤇ vs)
--           (map p f vs.length)
--           (tptr.mk _ _ p ⤇ vs.enum.map (uncurry f)) :=
-- begin
--   rw hProp.maplets_eq_And,
--   verify_proc!,
--   { rw hProp.maplets_eq_And, simp },
--   { rw ← a_1, simp [enum_from,uncurry] },
-- end

variables (value)

class is_object (α : Type) extends fixed_storable α :=
(delete : tptr α → ST punit)
(move : tptr α → tptr α → ST punit)
(delete_spec : ∀ (p : tptr α) (x : α),
                 spec' (p ⤇ x)
                         (delete p)
                         (trashed p))
(move_spec : ∀ (p p' : tptr α) (x : α),
                    spec' (trashed p ⊛ p' ⤇ x)
                            (move p p')
                            (trashed p' ⊛ p ⤇ x))

attribute [spec] is_object.delete_spec is_object.move_spec

local notation `is_object` := is_object value

class copyable (α : Type) extends is_object α :=
(copy : tptr α → tptr α → ST punit)
(copy_spec : ∀ (p p' : tptr α) (x : α),
                    spec' (trashed p ⊛ p' ⤇ x)
                            (copy p p')
                            (p ⤇ x ⊛ p' ⤇ x))

local notation `copyable` := copyable value
attribute [spec] copyable.copy_spec

variables {value}
open «copyable»
omit value
lemma sizeof_eq {α} {ls : list α} : sizeof ls = length ls + 1 :=
by { dsimp [sizeof,has_sizeof.sizeof], induction ls; simp [list.sizeof,*,sizeof,has_sizeof.sizeof,default.sizeof] }

lemma sizeof_drop {α} {n : ℕ} {ls : list α} (h : n ≤ length ls) : sizeof (drop n ls) = sizeof ls - n :=
by simp [sizeof_eq,nat.add_sub_assoc h]
include value

section chunks

variables (α) [fixed_storable α]

def mk_chunk (vs : list value) (h : length vs ≥ fixed_size value α) : word value α :=
⟨take (fixed_size value α) vs,by rw [length_take,min_eq_left h]⟩

def chunks : list value → list (word value α)
| xs :=
if h : length xs ≥ fixed_size value α then
  have sizeof (drop (fixed_size value α) xs) < sizeof xs,
    by { rw sizeof_drop h, apply nat.sub_lt _ (fixed_storable.pos_size _ _),
         rw sizeof_eq, apply lt_of_le_of_lt (nat.zero_le _), apply lt_add_one, },
  mk_chunk α xs h :: chunks (drop (fixed_size value α) xs)
else []

variables {α}

lemma chunks_nil : chunks α (@nil value) = @nil (word value α) :=
by rw [chunks,dif_neg]; apply not_le_of_gt; apply fixed_storable.pos_size

lemma chunks_eq_of_length_ge {xs : list value} (h : length xs ≥ fixed_size value α) :
  chunks α xs = mk_chunk α xs h :: chunks α (drop (fixed_size value α) xs) :=
by rw [chunks,dif_pos h]

variables  {n : ℕ}

lemma repr_chunks (p : tptr (list (word value α))) {mem : list value}
  (Hmem : length mem = n * fixed_storable.fixed_size value α) :
  p ⤇ chunks α mem = p.recast _ ⤇ mem :=
begin
  induction n generalizing mem p; simp [nat.succ_mul,length_eq_zero] at Hmem,
  { rw [Hmem,chunks_nil], refl },
  { have : length mem ≥ fixed_size value α,
    { rw Hmem, apply nat.le_add_right, },
    rw [chunks_eq_of_length_ge this,repr_cons],
    conv { to_rhs, rw ← take_append_drop (fixed_size value α) mem, },
    rw [maplets_append], congr' 1,
    { transitivity, swap, apply @n_ih (drop (fixed_size value α) mem) (p +. length (take (fixed_size value α) mem)),
      rw [length_drop,Hmem,nat.add_sub_cancel_left],
      congr, dsimp [storable.size], simp [min_eq_left this] } },
end

lemma length_chunks {mem : list value}
  (Hmem : length mem = n * fixed_size value α) :
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

end chunks

section talloc

variables [fixed_storable α] (n : ℕ)

open list

@[spec]
lemma malloc_spec :
  spec
    emp
    (malloc value n)
    (λ p, ∃∃ val : list value, [| length val = n |] ⊛ p ⤇ val) :=
by { verify_proc! }

@[spec]
lemma ralloc1_spec :
  spec
    emp
    (ralloc1 value α)
    (λ p, trashed p) :=
by verify_proc!; intro; simp [trashed]

end talloc

section talloc

open list «is_object»
variables [is_object α]

variables (value)
-- include S

def rfree (p : tptr α) : ST unit :=
do delete p,
   dealloc value p.get (fixed_size value α)

variables {value}

section tactic

open tactic


-- @[tactic.verify_step]
-- meta def verify_step'' (ids : list simp_arg_type) (rule : option expr) (local_specs : expr_map (list expr)) : tactic unit :=
-- focus1 $
-- do ls ← spec_attr.get_cache,
--    trace_state,
--    (val,p,m,v,q) ← tactic.get_spec',
--    let proc_e := m.get_app_fn,
--    let proc_n := proc_e.const_name,
--    specs ← ↑(list.ret <$> rule) <|>
--      local_specs.find proc_e <|>
--      (↑(ls.find proc_n) >>= list.mmap mk_const) <|>
--      fail!"no such procedure: {proc_n}",
--    trace "foo bar",
--    ps ← parse_assert p,
--    -- sl ← ids.mmap (resolve_name >=> to_expr) >>= simp_lemmas.append simp_lemmas.mk,
--    trace!"foo {specs}",
--    specs.any_of (λ e,
--    try_unfold [] ids $
--    do trace e,
--       if is_trace_enabled_for `separation.failed_spec = tt
--          then trace_error "msg" (specialize_spec e p m) >> trace "bar"
--          else specialize_spec e p m >> trace "bar")
--      <|> fail!"no specification found. \nCandidates: {specs}",
--    all_entails_goals (try entailment),
--    all_side_conditions (try cc)

-- @[tactic.try_unfold]
-- meta def try_unfold'' (attr_names : list name) (hs : list simp_arg_type) (tac : tactic unit) : tactic unit :=
-- -- do trace "foo",
-- tac <|> do
--   trace!"A - {hs}",
--   (lmms, ids) ← mk_simp_set tt (`separation_logic :: attr_names) hs,
--   simp_target lmms ids { fail_if_unchanged := ff },
--   trace_state,
--   tac

-- @[tactic.unify_args]
-- meta def unify_args' (e e' : expr) : tactic unit :=
-- do guard (e.get_app_fn.const_name = e'.get_app_fn.const_name) <|> fail format!"different calls: {e.get_app_fn} {e'.get_app_fn}",
--    let args := e.get_app_args,
--    let args' := e'.get_app_args,
--    guard (args.length = args'.length) <|> fail "argument list mismatch",
--    mzip_with' (λ a a', (unify a a') <|> trace!"arguments `{a}` and `{a'}` do not unify\n`{e}`, `{e'}`") args args',
--    -- e ← instantiate_mvars e,
--    -- e' ← instantiate_mvars e',
--    -- trace (to_fmt e), trace (to_fmt e'),
--    -- -- s.is_eqv
--    -- s ← s.internalize e,
--    -- s ← s.internalize e',
--    -- s.is_eqv e e' >>= trace,
--    -- s.eqv_proof e e',
--    skip

-- @[tactic.specialize_spec]
-- meta def specialize_spec'' (spec p call : expr) : tactic unit :=
-- do (args,spec') ← infer_type spec >>= mk_meta_pis,
--    (val,p',m,v,q) ← tactic.get_spec spec',
--    pr  ← unify_args call m,
--    ps  ← parse_assert p,
--    ps' ← parse_assert p',
--    let (vs,ps'') := ps'.partition $ λ e : expr, e.is_meta_var,
--    fr ← find_frame_aux ps'' ps <|> fail!"framing {ps'} {ps}",
--    let fr' := mk_assert val fr,
--    q' ← head_beta q >>= lambdas [v],
--    s ← cc_state.mk_using_hs,
--    call ← instantiate_mvars call,
--    m ← instantiate_mvars m,
--    s ← s.internalize m,
--    s ← s.internalize call,
--    trace! "{to_fmt call}\n{to_fmt m}",
--    pr ← s.eqv_proof call m,
--    rewrite_target pr,
--    trace!"{infer_type pr}",
--    e ← if vs.empty then
--      mk_mapp ``frame_rule [none, none, none, m, p', fr', q', spec.mk_app args]
--      else do
--        { [v] ← pure vs | fail "only one abstract predicate can be supported",
--          unify v fr',
--          return $ spec.mk_app args },
--    to_expr ``(precondition_impl _ _ %%e) >>= apply,
--    pure ()

end tactic

-- set_option trace.separation.failed_spec true

@[spec]
lemma rfree_spec (p : tptr α) (x : α) :
  spec'
    (p ⤇ x)
    (rfree value p)
    emp :=
-- precondition_impl (trashed value p)
--   (impl_of_eq (raw_bytes_conversion _ _ _))
--   (by dsimp [rfree]; rw ← length_bytes' _ x; apply dealloc_spec)
by { verify_proc! [trashed] }

end talloc

section talloc_isrecord

variables [is_record value α] (n : ℕ)

open list

@[spec]
lemma ralloc_spec :
  spec
    emp
    (ralloc value α n)
    (λ p, ∃∃ val : list α, [| length val = n |] ⊛ p ⤇ val) :=
(by { verify_proc!, intro, simp [],
      apply exists_impl, intro mem,
      apply lift_and_impl, intro Hmem,
      apply impl_exists ((chunks α mem).map abstr),
      rw [length_map,repr_map_abstr,tptr.recast_mk],
      apply impl_lift_and,
      { rw length_chunks Hmem, },
      { simp [repr_chunks _ Hmem], } })

@[spec]
lemma ralloc1_spec' :
  spec
    emp
    (ralloc1 value α)
    (λ p, ∃∃ val, p ⤇ val) :=
by { verify_proc, intro, simp [(∘),uninitialized',trashed] }

#check lattice.has_sup

@[spec]
lemma free_spec (p : tptr (list α)) (xs : list α) :
  spec'
    (p ⤇ xs)
    (free p (length xs) )
    emp :=
begin
  refine precondition_impl (p.recast (list value) ⤇ rec_bytes xs) _ _, -- (dealloc_spec _ _) -- (by simp [val_repr]) (dealloc_spec _ xs)
  { apply impl_of_eq, induction xs generalizing p, refl,
    -- have := maplets_append,
    rw [rec_bytes_cons,maplets_append',repr_cons,raw_bytes_conversion,xs_ih],
    simp [fixed_storable.is_fixed,length_bytes'], refl },
  { dsimp [free], rw ← length_rec_bytes, apply dealloc_spec }
end

end talloc_isrecord

namespace «copyable»

variables [copyable α]

def clone (p : tptr α) : ST (tptr α) :=
do p' ← ralloc1 _ α,
   copy p' p,
   pure p'

open separation.is_object

lemma clone_spec (p : tptr α) (x : α) :
  spec (p ⤇ x) (clone p) (λ r, r ⤇ x ⊛ p ⤇ x) :=
by verify_proc!

def replace (p p' : tptr α) : ST unit :=
do delete p,
   copy p p'

lemma replace_spec (p p' : tptr α) (x y : α) :
  spec' (p ⤇ x ⊛ p' ⤇ y) (replace p p') (p ⤇ y ⊛ p' ⤇ y) :=
by verify_proc!

end «copyable»

end separation
