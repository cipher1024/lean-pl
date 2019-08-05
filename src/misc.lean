
import data.list.basic
import tactic.linarith

namespace relation

def left_total {α β} (R : α → β → Prop) :=
∀ x, ∃ y, R x y

def right_total {α β} (R : α → β → Prop) :=
left_total (flip R)

end relation

namespace punit

lemma punit_eq_iff (x y : punit) : x = y ↔ true := by casesm* punit; simp

end punit

namespace nat

@[simp]
lemma not_add_one_le_self {p : ℕ} : ¬ p + 1 ≤ p := nat.not_succ_le_self _

@[simp]
lemma not_one_add_le_self {p : ℕ} : ¬ 1 + p ≤ p := (one_add p).symm ▸ nat.not_succ_le_self _

end nat


namespace list
open nat

variables {α : Type*} {β : Type*}

@[simp]
def nth' : ℕ → list α → list α
| 0 [] := []
| 0 (x :: xs) := [x]
| (succ n) [] := []
| (succ n) (x :: xs) := nth' n xs

lemma exists_nth'_eq_of_lt (vs : list α) (i : ℕ) (h : i < length vs) : ∃ x, nth' i vs = [x] :=
begin
  induction vs generalizing i, cases h, cases i; dsimp [nth'], exact ⟨_,rfl⟩,
  apply vs_ih, apply lt_of_succ_lt_succ h
end

@[simp]
lemma nth'_map (f : α → β) (vs : list α) (i : ℕ) : nth' i (vs.map f) = (nth' i vs).map f :=
begin
  induction vs generalizing i, cases i; refl,
  cases i; dsimp [map,nth']; [refl, exact vs_ih _]
end

@[simp]
lemma nth'_enum (vs : list α) (i : ℕ) : nth' i vs.enum = (nth' i vs).enum_from i :=
begin
  suffices : nth' i (enum_from 0 vs) = enum_from (0 + i) (nth' i vs),
  { dsimp [enum], rw [this,zero_add] },
  generalize : 0 = k,
  induction vs generalizing i k, cases i; refl,
  cases i; dsimp [enum_from,nth'], refl, rw [vs_ih,succ_eq_add_one], ac_refl
end

lemma range_zero : range 0 = [] := rfl

lemma range'_zero (n : ℕ) : range' n 0 = [] := rfl

lemma cons_range' (n k : ℕ) : (n :: range' n.succ k : list _) = range' n k.succ := rfl

attribute [simp] length_enum

lemma length_eq_succ {α} (xs : list α) (n : ℕ) : xs.length = n.succ ↔ ∃ y ys, xs = y::ys ∧ ys.length = n :=
begin
  split,
  { intro h, cases xs, cases h, exact ⟨_,_,rfl,nat.succ_inj h⟩ },
  { rintro ⟨y,ys,h₀,h₁⟩, subst h₀, rw [list.length,h₁] }
end

end list

section logic

lemma exists_one_point {α} {p : α → Prop} (x : α) (h : ∀ y, p y → x = y) : (∃ y, p y) ↔ p x :=
⟨λ ⟨x',h'⟩, (h _ h').symm ▸ h', λ h', ⟨x,h'⟩ ⟩

end logic

@[user_attribute]
meta def interactive_attr : user_attribute :=
{ name := `interactive,
  descr := "inject definition into the `tactic.interactive` namespace",
  after_set := some $ λ n _ _, add_interactive [n]  }

namespace name

def drop_prefix : name → name
| anonymous := anonymous
| (mk_string s _) := mk_string s anonymous
| (mk_numeral n _) := mk_numeral n anonymous

end name


namespace tactic

meta def fail_if_unchanged {α} (tac : tactic α) : tactic α :=
do gs ← get_goals,
   r ← tac,
   gs' ← get_goals,
   r <$ guard (gs ≠ gs')

setup_tactic_parser
open list

@[interactive]
meta def duplicate_goal (n : parse small_nat) : tactic unit :=
focus1 $
do t ← target,
   gs ← (iota n).mmap (λ _, mk_meta_var t),
   [g] ← get_goals,
   set_goals (g :: gs)

-- meta def mk_instance_binder : expr → expr
-- | (expr.pi n _ d b) := expr.pi `_inst binder_info.inst_implicit d b
-- | e := e

-- meta def to_inst_implicit : expr → expr
-- | (expr.local_const uniq n bi t) := expr.local_const uniq n binder_info.inst_implicit t
-- | e := e

-- meta def cache_local_instances : tactic unit :=
-- do cxt ← local_context,
--    ns ← cxt.reverse.mmap $ λ l,
--      do { t ← infer_type l,
--           mcond (is_class t.get_app_fn) (revert l <* (target >>= unsafe_change ∘ mk_instance_binder)) (pure 0) },
--    intron ns.sum

-- #print partial_order
-- #check add_inductive

-- meta def force_local_type : expr → tactic expr
-- | e@`

-- meta def get_local_pis : ℕ → expr → tactic (list expr)
-- | 0 _ := pure []
-- | (nat.succ n) (pi nn bi )

-- meta def mk_le (n le_n : name) (ls : list name) (ps : list expr) : tactic expr :=
-- do cxt ← local_context,
--    env ← get_env,
--    -- let paramn := env.inductive_num_params n,
--    let cs := env.constructors_of n,
--    let cs' := do { (x,ys) ← cs.zip cs.tails,
--                    y ← ys,
--                    let c := le_n <.>
--                      (x.drop_prefix.to_string ++ "_le_" ++ y.drop_prefix.to_string),
--                    pure (x,y,c) },
--    let ps' := ps.map some,
--    cxt ← cxt.mmap $ λ l,
--      do { t ← infer_type l,
--           mcond (is_class t)
--             (pure $ to_inst_implicit l)
--             (pure $ to_implicit l) },
--    c ← mk_mapp n ps',
--    t ← pis cxt (c.imp $ c.imp `(Prop)),
--    let decl : expr := expr.const le_n $ ls.map level.param,
--    cs'' ← cs'.mmap $ λ ⟨c₀,c₁,cc⟩,
--    do { x ← mk_mapp c₀ ps',
--         y ← mk_mapp c₁ ps',
--         (xs, _) ← infer_type x >>= mk_local_pis,
--         (ys, _) ← infer_type y >>= mk_local_pis,
--         let hd := (decl.mk_app cxt (x.mk_app xs) (y.mk_app ys)),
--         t ← if c₀ = c₁
--           then do
--             hs ← mzip_with (λ x y : expr,
--               do t ← infer_type x,
--                  h ← mk_mapp `has_le.le [t,none,x,y],
--                  mk_local_def `h h) xs ys,
--             -- t ← pis hs hd,
--             pis (cxt ++ xs ++ ys ++ hs) hd
--           else pis (cxt ++ xs ++ ys) hd,
--         -- trace!"{t}, {t.list_local_consts}",
--         pure (cc,t) },
--    trace t,
--    trace "•",
--    add_inductive le_n ls cxt.length t cs'',
--    trace "•",
--    pure $ (expr.const le_n (ls.map level.param)).mk_app cxt

-- meta def prove_refl (t R : expr) : tactic expr :=
-- do x ← mk_local_def `x t,
--    t ← pis [x] (R x x),
--    prod.snd <$> solve_aux t (do
--      { x ← intro1, cs ← cases x,
--        all_goals (constructor >> applyc ``le_refl),
--        skip })

-- meta def prove_trans (t R : expr) : tactic expr :=
-- do env ← get_env,
--    let n := R.get_app_fn.const_name,
--    let rec_n := n <.> "rec",

--    x ← mk_local_def `x t,
--    y ← mk_local_def `y t,
--    z ← mk_local_def `z t,
--    h₀ ← mk_local_def `h₀ (R x y),
--    h₁ ← mk_local_def `h₁ (R y z),
--    t ← pis [x,y,z,h₀,h₁] (R x z),
--    prod.snd <$> solve_aux t (do
--      { [x,y,z,h₀,h₁] ← intros, cs ← induction h₀ [] rec_n,
--        gs ← get_goals,
--        trace "• A",
--        gs ← mzip_with (λ (g) c : name × list expr × list (name × expr),
--          do let ⟨a,b,c⟩ := c,
--             set_goals [g],
--             trace_state,
--             trace!"{h₁.to_raw_fmt} - {(h₁.instantiate_locals c).to_raw_fmt}\n{c}",
--             () <$ induction (h₁.instantiate_locals c) [] rec_n,
--             trace "• A",
--             get_goals ) gs cs,
--        trace "• A",
--        set_goals gs.join,
--        all_goals (constructor >> applyc ``le_refl),
--        skip })

-- meta def mk_linear_order_instance : tactic unit :=
-- do `(linear_order %%t) ← target,
--    let fn := t.get_app_fn,
--    let ps := t.get_app_args,
--    -- cache_local_instances,
--    guard (fn.is_constant) <|> fail "expecting a type applied to arguments: `fn a b c`",
--    let n := fn.const_name,
--    let le_n := n <.> "le",
--    env ← get_env,
--    let cs := env.constructors_of n,
--    let paramn := env.inductive_num_params n,
--    let cs' := do { (x,ys) ← cs.zip cs.tails,
--                    y ← ys,
--                    let c := le_n <.>
--                      (x.drop_prefix.to_string ++ "_le_" ++ y.drop_prefix.to_string),
--                    pure (x,y,c) },
--    d ← get_decl n,
--    let ls := d.univ_params,
--    guard (env.inductive_num_indices n = 0),
--    le ← mk_le n le_n ls ps,
--    le_refl ← prove_refl t le,
--    le_trans ← prove_trans t le,
--    refine ``( { linear_order .  le := %%le,
--                 le_refl := %%le_refl,
--                 le_trans := %%le_trans } )

-- -- #print instances decidable_linear_order

-- @[derive_handler]
-- meta def linear_order_derive_handler : derive_handler :=
-- instance_derive_handler ``linear_order mk_linear_order_instance

-- @[derive_handler]
-- meta def decidable_linear_order_derive_handler : derive_handler :=
-- instance_derive_handler ``decidable_linear_order mk_decidable_linear_order_instance

meta def simp_arg_type.to_tactic_format : simp_arg_type → tactic format
| simp_arg_type.all_hyps := pure "all_hyps"
| (simp_arg_type.except a) := (pformat!"- {a}" : pformat)
| (simp_arg_type.expr a) := pp a

meta instance simp_arg_type.has_to_tactic_format : has_to_tactic_format simp_arg_type :=
⟨ simp_arg_type.to_tactic_format ⟩

open interactive tactic.interactive

meta def interactive.repeat1 (tac : itactic) : tactic unit :=
let tac : tactic unit := tac in
tac ; repeat tac

meta def enclosing_def : tactic unit :=
do n ← decl_name,
   exact `(n)

meta def with_context (msg : format) (tac : itactic) (caller : name . enclosing_def) : tactic unit
| s := match tac s with
       | (result.success a a_1) := result.success a a_1
       | (result.exception (some msg') p s) :=
         (do result.exception (some $ λ _, format!"> {caller}\n{msg}\n\nPreviously:\n{msg' ()}") p) s
       | (result.exception none p s) :=
         (do result.exception (some $ λ _, format!"> {caller}\n{msg}") p) s
       end

precedence `with_context!`:0

@[user_notation]
meta def with_context_macro (_ : parse $ tk "with_context!") (xs : string) : lean.parser pexpr :=
do msg ← pformat_macro () xs,
   pure ``(λ tac, do x ← %%msg, tactic.with_context x tac)

run_cmd mk_simp_attr `linarith

@[interactive]
meta def linarith'
  (red : parse (tk "!")?)
  (restr : parse (tk "only")?) (hyps : parse pexpr_list?)
  (cfg : linarith.linarith_config := {}) : tactic unit :=
do `[simp only with linarith at * { fail_if_unchanged := ff } ],
   done <|> do
     intros,
     casesm (some ()) [``(Exists _), ``(_ ∧ _)],
     linarith red restr hyps cfg

attribute [linarith] nat.succ_eq_add_one list.length

end tactic

-- @[linarith]
-- lemma dvd_iff_exists {α} [comm_semiring α] (x y : α) : x ∣ y ↔ ∃ z, y = x * z := iff.refl _

-- open list

-- example {x y : ℕ}
--   -- (h : x ∣ y)
--   (h' : x = length [x,y])
--   (h'' : y > 0) :
--   x > 0 :=
-- begin
--   -- dsimp [has_dvd.dvd] at h,
--   linarith',
-- end

-- set_option trace.app_builder true

-- open tactic tactic.interactive

-- meta def other_def : tactic unit :=
-- with_context ↑"other" (tactic.fail "bar error")

-- meta def foo_def : tactic unit :=
-- by with_context ↑"foo" other_def

-- attribute [derive linear_order] sum

-- @[derive linear_order]
-- inductive foo (α : Type)
-- | left : α → ℕ → foo
-- | mid : foo
-- | right : ℕ → foo

-- attribute [derive decidable_linear_order] sum
