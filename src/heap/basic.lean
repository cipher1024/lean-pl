
import data.finmap

run_cmd mk_simp_attr `separation_logic

open finmap

namespace memory

variables value : Type

@[reducible]
def ptr := ℕ

@[reducible]
def heap := finmap (λ _ : ptr, value)

variables {value}

def add (x y : option (heap value)) : option (heap value) :=
do x ← x,
   y ← y,
   if disjoint x y then pure $ x ∪ y else none

infixr ` ⊗ `:55 := add

instance {α : Type*} {β : α → Type*} : has_subset (finmap β) :=
⟨ λ x y, ∀ a, a ∈ x → a ∈ y ⟩

lemma disjoint_mono' {ha hb ha' hb' : heap value} (H₀ : ha' ⊆ ha) (H₁ : hb' ⊆ hb) :
  disjoint ha hb → disjoint ha' hb' :=
λ H₂ x H₃ H₄,  H₂ x (H₀ _ H₃) (H₁ _ H₄)

lemma union_eq_add_of_disjoint {h h' : heap value} (H₀ : disjoint h h') :
  some (h ∪ h') = some h ⊗ some h' :=
by simp [add,if_pos H₀]; refl

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
  simp only [add, @disjoint.symm_iff _ _ h₀, option.some_bind]; split_ifs,
  ext : 1, simp only [ext_iff,pure], rw finmap.union_comm_of_disjoint,
  symmetry, assumption, refl
end

instance : is_associative _ (@add value) := ⟨ add_assoc ⟩
instance : is_commutative _ (@add value) := ⟨ add_comm ⟩

@[simp]
lemma empty_add (h : option (heap value)) :
  some ∅ ⊗ h = h :=
by cases h; [ simp [add], { rw [← union_eq_add_of_disjoint,empty_union]; apply disjoint_empty }]

@[simp]
lemma add_empty (h : option (heap value)) :
  h ⊗ some ∅ = h :=
by cases h; [ simp [add], { rw [← union_eq_add_of_disjoint,union_empty]; apply empty_disjoint }]

lemma add_eq_some (x y : option (heap value)) (z : heap value) : some z = x ⊗ y → ∃ x', some x' = x :=
by intro h; cases x; [ { simp [add] at h, cases h }, exact ⟨_,rfl⟩ ]

lemma add_eq_some' (x y : option (heap value)) (z : heap value) : some z = x ⊗ y → ∃ y', some y' = y :=
assume h, add_eq_some y x z (@add_comm _ x y ▸ h)

lemma disjoint_iff {h h' : heap value} : disjoint h h' ↔ ∃ h'', some h'' = some h ⊗ some h' :=
by by_cases disjoint h h'; simp only [add, *, option.some_bind, exists_false, if_false, if_true, true_iff]; exact ⟨_,rfl⟩

lemma disjoint_of_add {h h' : heap value} (h'' : heap value) : some h'' = some h ⊗ some h' → disjoint h h' :=
λ HH, disjoint_iff.mpr ⟨_, HH⟩

lemma eq_union_of_eq_add {h h' h'' : heap value} : some h'' = some h ⊗ some h' → h'' = h ∪ h' :=
λ HH, option.some.inj (eq.trans HH (union_eq_add_of_disjoint (disjoint_of_add _ HH)).symm)

end memory
