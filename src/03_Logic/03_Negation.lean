import data.real.basic

section
variables a b : ℝ

example (h : a < b) : ¬ b < a :=
begin
  intro h',
  have : a < a,
    from lt_trans h h',
  apply lt_irrefl a this
end

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intros fnub,
  cases fnub with a fnuba,
  cases h a with x hx,
  have : f x ≤ a,
    from fnuba x,
  linarith
end

example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f := begin
  intros flb,
  cases flb with a flba,
  cases h a with x hx,
  have: f x >= a, from flba x,
  linarith,
end

example : ¬ fn_has_ub (λ x, x) := begin
  intros fub,
  rcases fub with ⟨y, fuby⟩,
  have: y + 1 <= y, from fuby (y + 1),
  linarith,
end

#check (not_le_of_gt : a > b → ¬ a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬ a < b)
#check (lt_of_not_ge : ¬ a ≥ b → a < b)
#check (le_of_not_gt : ¬ a > b → a ≤ b)

example (h : monotone f) (h' : f a < f b) : a < b := begin
  apply lt_of_not_ge,
  intros agtb,
  have: f a >= f b, from h agtb,
  linarith,
end

example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f := begin
  intros mf,
  have: f a <= f b, from mf h,
  linarith,
end

example :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f,
  {
    intros a b aleb,
    linarith,
  },
  have h' : f 1 ≤ f 0,
    from le_refl _,
  have: (1 : ℝ) <= 0, from h monof h',
  linarith,
end

#check le_of_not_gt
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := begin
  apply le_of_not_gt,
  intros xgt,
  have: x > x, from h x xgt,
  linarith,
end

end

section
variables {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x := begin
  intro x,
  intro px,
  have: ∃ (x: α), P x, {
    use x,
    apply px,
  },
  apply h this,
end

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x := begin
  intro npx,
  cases npx with x px,
  apply h x,
  apply px,
end

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
sorry

example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x := begin
  intro apx,
  cases h with x npx,
  apply npx (apx x),
end

open_locale classical

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin
  by_contradiction h',
  apply h,
  intro x,
  show P x,
  by_contradiction h'',
  exact h' ⟨x, h''⟩
end

example (h : ¬ ¬ Q) : Q := begin
  by_contradiction h',
  apply h h',
end

example (h : Q) : ¬ ¬ Q := begin
  intro h',
  apply h' h,
end

end

open_locale classical
section
variable (f : ℝ → ℝ)

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a := begin
  intro a,
  by_contradiction g,
  apply h,
  use a,
  intros x,
  by_contradiction h',
  apply g,
  use x,
  linarith,
end

example (h : ¬ ∀ a, ∃ x, f x > a) : fn_has_ub f :=
begin
  push_neg at h,
  exact h
end

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  simp only [fn_has_ub, fn_ub] at h,
  push_neg at h,
  exact h
end

example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x := begin
  simp only [monotone] at h,
  push_neg at h,
  apply h,
end

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  contrapose! h,
  exact h
end

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
begin
  contrapose! h,
  use x / 2,
  split; linarith
end

end

section
variable a : ℕ

example (h : 0 < 0) : a > 37 :=
begin
  exfalso,
  apply lt_irrefl 0 h
end

example (h : 0 < 0) : a > 37 :=
absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 :=
begin
  have h' : ¬ 0 < 0,
    from lt_irrefl 0,
  contradiction
end

end
