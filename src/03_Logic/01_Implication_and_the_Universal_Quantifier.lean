import data.real.basic

#check ∀ x : ℝ, 0 ≤ x → abs x = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε

lemma my_lemma : ∀ x y ε : ℝ,
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
sorry

section
  variables a b δ : ℝ
  variables (h₀ : 0 < δ) (h₁ : δ ≤ 1)
  variables (ha : abs a < δ) (hb : abs b < δ)

  #check my_lemma a b δ
  #check my_lemma a b δ h₀ h₁
  #check my_lemma a b δ h₀ h₁ ha hb
end

lemma my_lemma2 : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
sorry

section
  variables a b δ : ℝ
  variables (h₀ : 0 < δ) (h₁ : δ ≤ 1)
  variables (ha : abs a < δ) (hb : abs b < δ)

  #check my_lemma2 h₀ h₁ ha hb
end

lemma my_lemma3 : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  sorry
end

#check mul_le_mul
#check mul_lt_mul_right
#check (mul_lt_mul_right _).mpr
lemma my_lemma4 : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  calc
    abs (x * y) = abs x * abs y : by apply abs_mul
    ... ≤ abs x * ε             : by
      apply mul_le_mul (le_refl (abs x)) (le_of_lt ylt) (abs_nonneg y) (abs_nonneg x)
    ... < 1 * ε                 : by
      apply (mul_lt_mul_right epos).mpr (lt_of_lt_of_le xlt ele1)
    ... = ε                     : by rw one_mul
end

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

section
variables (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
begin
  intro x,
  dsimp,
  apply add_le_add,
  apply hfa,
  apply hgb
end

example (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) :=
begin
  intro x,
  dsimp,
  apply add_le_add,
  apply hfa,
  apply hgb,
end

example (nnf : fn_lb f 0) (nng : fn_lb g 0) :
  fn_lb (λ x, f x * g x) 0 :=
begin
  intro x,
  dsimp,
  apply mul_nonneg,
  apply nnf,
  apply nng,
end

example (hfa : fn_ub f a) (hfb : fn_ub g b)
    (nng : fn_lb g 0) (nna : 0 ≤ a) :
  fn_ub (λ x, f x * g x) (a * b) :=
begin
  intro x,
  dsimp,
  -- rw <-mul_zero,
  apply mul_le_mul,
  apply hfa,
  apply hfb,
  apply nng,
  apply nna,
end

end

section
variables {α : Type*} {R : Type*} [ordered_cancel_add_comm_monoid R]

#check @add_le_add

def fn_ub' (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

theorem fn_ub_add {f g : α → R} {a b : R}
    (hfa : fn_ub' f a) (hgb : fn_ub' g b) :
  fn_ub' (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)
end

example (f : ℝ → ℝ) (h : monotone f) :
  ∀ {a b}, a ≤ b → f a ≤ f b := h

section
variables (f g : ℝ → ℝ)

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
begin
  intros a b aleb,
  apply add_le_add,
  apply mf aleb,
  apply mg aleb
end

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
λ a b aleb, add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) := begin
  intros a b aleb,
  dsimp,
  apply mul_le_mul_of_nonneg_left,
  apply mf aleb,
  apply nnc,
end

example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
λ a b aleb, mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
begin
  intros a b aleb,
  dsimp,
  apply mf,
  apply mg,
  apply aleb,
end

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
λ a b aleb, mf (mg aleb)

def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def fn_odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (ef : fn_even f) (eg : fn_even g) : fn_even (λ x, f x + g x) :=
begin
  intro x,
  calc
    (λ x, f x + g x) x = f x + g x       : rfl
                    ... = f (-x) + g (-x) : by rw [ef, eg]
end

example (of : fn_odd f) (og : fn_odd g) : fn_even (λ x, f x * g x) := begin
  intro x,
  dsimp,
  rw [of, og],
  linarith,
end

example (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x, f x * g x) := begin
  intro x,
  dsimp,
  rw [ef, og],
  linarith,
end

example (ef : fn_even f) (og : fn_odd g) : fn_even (λ x, f (g x)) := begin
  intro x,
  dsimp,
  rw og,
  rw <-ef,
end

end

section
variables {α : Type*} (r s t : set α)

example : s ⊆ s :=
by { intros x xs, exact xs }

theorem subset.refl : s ⊆ s := λ x xs, xs

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := begin
  intros rs st,
  intros x xr,
  apply st,
  apply rs,
  apply xr,
end

end

section

variables {α : Type*} [partial_order α]
variables (s : set α) (a b : α)

def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b := begin
  intros x xs,
  apply le_trans,
  apply h x,
  apply xs,
  apply h',
end

end

section
open function

example (c : ℝ) : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  exact (add_left_inj c).mp h',
end

example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) := begin
  intros x₁ x₂,
  dsimp,
  intros h',
  apply (mul_left_inj' h).mp,
  linarith,
end

variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (injg : injective g) (injf : injective f) :
  injective (λ x, g (f x)) := begin
  intros x₁ x₂,
  dsimp,
  intros h',
  apply injf,
  apply injg,
  apply h',
end

end
