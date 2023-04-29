import data.set.lattice
import data.set.function
import analysis.special_functions.log.basic

section

variables {α β : Type*}
variable  f : α → β
variables s t : set α
variables u v : set β
open function
open set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y, split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left, use [x, xs] },
    right, use [x, xt] },
  rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
  { use [x, or.inl xs] },
  use [x, or.inr xt]
end

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs]
end

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := begin
  split,
  { show f '' s ⊆ v → s ⊆ f ⁻¹' v,
    rintros h x xs,
    have : f x ∈ f '' s, from ⟨x, xs, rfl⟩,
    have : f x ∈ v, from h this,
    use this
  },
  { show s ⊆ f ⁻¹' v → f '' s ⊆ v,
    -- rintros s_ss_primg_v y y_mem_img_f_s,
    rintros s_ss_primg_v y ⟨x, xs, rfl⟩,
    have : x ∈  f ⁻¹' v, from s_ss_primg_v xs,
    show f x ∈ v, from this, 
  },
end

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s := begin
  intros x x_mem_primg_f_s,
  have : f x ∈ f '' s, from x_mem_primg_f_s,
  rcases this with ⟨y, y_mem_s, fxeqfy⟩,
  have : y = x, from h fxeqfy,
  rw ←this,
  exact y_mem_s, 
end

example : f '' (f⁻¹' u) ⊆ u := begin
  intros y h, -- ⟨aa, bb⟩  ,
  rcases h with ⟨x, x_mem_primg_f_u, fxeqy⟩,
  rw ←fxeqy,
  exact x_mem_primg_f_u,
end

-- ∀ b, ∃ a, f a = b
example (h : surjective f) : u ⊆ f '' (f⁻¹' u) := begin
  rintros y y_mem_u,
  let hj := f ⁻¹' u,

  -- fail: intro, 
  simp,
  rcases h y with ⟨x, fxeqy⟩,
  use x,
  split,
  { rw fxeqy, exact y_mem_u },
  { exact fxeqy },
end

example (h : s ⊆ t) : f '' s ⊆ f '' t := begin
  rintros y ⟨x, xs, f_x_eq_y⟩,
  have : x ∈ t, exact h xs,
  use ⟨ x, this, f_x_eq_y⟩ ,
end

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := begin
  rintros x x_mem_f_preimg_u,
  -- have : f x ∈ u, by x_mem_f_preing_u,
  have : f x ∈ u, exact mem_preimage.mp x_mem_f_preimg_u,
  have : f x ∈ v, exact h this,
  use this,
end

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := begin
  ext,
  split,
  { show x ∈ f ⁻¹' (u ∪ v) → x ∈ f ⁻¹' u ∪ f ⁻¹' v,
    rintros x_mem_pre_img_u_or_v,
    simp,
    have : f x ∈ (u ∪ v), exact mem_preimage.mp x_mem_pre_img_u_or_v,
    -- rcases mem_or_mem_of_mem_union this with ⟨ z, zz ⟩ ,
    -- {},
    -- {},

        sorry },
  { 
    sorry },
  -- let h := f ⁻¹' (u ∪ v),
  -- have : ∃ x, f x ∈ (u ∪ v), sorry,

  -- have :  f ⁻¹' (u ∪ v) = 
-- sorry
end

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
sorry

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
sorry

variables {I : Type*} (A : I → set α) (B : I → set β)

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  rintros ⟨i, x, xAi, fxeq⟩,
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
end

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

example (i : I) (injf : injective f) :
  (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  exact fxeq
end

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }

end

section
open set real

example : inj_on log { x | x > 0 } :=
begin
  intros x xpos y ypos,
  intro e,   -- log x = log y
  calc
    x   = exp (log x) : by rw exp_log xpos
    ... = exp (log y) : by rw e
    ... = y           : by rw exp_log ypos
end

example : range exp = { y | y > 0 } :=
begin
  ext y, split,
  { rintros ⟨x, rfl⟩,
    apply exp_pos },
  intro ypos,
  use log y,
  rw exp_log ypos
end

example : inj_on sqrt { x | x ≥ 0 } := begin
  intros x x_ge_0 y y_ge_0 sqrt_x_eq_sqrt_y,
  have : x = sqrt x * sqrt x, { rw mul_self_sqrt x_ge_0 },
  rw this,
  have : y = sqrt y * sqrt y, { rw mul_self_sqrt y_ge_0},
  rw this,
  rw sqrt_x_eq_sqrt_y,
end

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } := begin
  intros x x_ge_0 y y_ge_0 x_sq_eq_y_sq,
  dsimp at *,
  have : x = sqrt (x^2), { rw sqrt_sq x_ge_0 },
  rw this,
  have : y = sqrt (y^2), { rw sqrt_sq y_ge_0 },
  rw this,
  rw x_sq_eq_y_sq,
end

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} := begin
  ext y, simp, split,
  { show (∃ (x : ℝ), 0 ≤ x ∧ sqrt x = y) → 0 ≤ y,
    rintros  ⟨x, x_ge_0, rfl⟩,
    exact sqrt_nonneg x,
  },
  { show 0 ≤ y → (∃ (x : ℝ), 0 ≤ x ∧ sqrt x = y),
    intro y_ge_0,
    -- split,
    use (y * y),
    split,
    { exact mul_nonneg y_ge_0 y_ge_0},
    { rw sqrt_mul_self y_ge_0 },
  },
end

example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} := begin
  ext,
  simp,
  split,
  { show (∃ (y : ℝ), y ^ 2 = x) → 0 ≤ x,
    rintros ⟨y, rfl⟩,
    exact sq_nonneg y,
  },
  {
    rintros x_ge_0,
    use sqrt x,
    have : sqrt x ^ 2 = sqrt x * sqrt x, { ring },
    rw this,
    exact mul_self_sqrt x_ge_0,
  },
end

end

section
variables {α β : Type*} [inhabited α]

#check (default : α)

variables (P : α → Prop) (h : ∃ x, P x)

#check classical.some h

example : P (classical.some h) := classical.some_spec h

noncomputable theory
open_locale classical

def inverse (f : α → β) : β → α :=
λ y : β, if h : ∃ x, f x = y then classical.some h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y :=
begin
  rw inverse, dsimp, rw dif_pos h,
  exact classical.some_spec h
end

variable  f : α → β
open function

/-
def function.left_inverse : Π {α : Sort u₁} {β : Sort u₂}, (β → α) → (α → β) → Prop :=
λ {α : Sort u₁} {β : Sort u₂} (g : β → α) (f : α → β), ∀ (x : α), g (f x) = x
-/

#print left_inverse 
-- 
/-
left_inverse : (?M_2 → ?M_1) → (?M_1 → ?M_2) → Prop
-/

#check left_inverse
-- g (f x) = x

/-
def function.injective : Π {α : Sort u₁} {β : Sort u₂}, (α → β) → Prop :=
λ {α : Sort u₁} {β : Sort u₂} (f : α → β), ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
-/

#print injective


example : injective f ↔ left_inverse (inverse f) f  := begin
  split,
  { show injective f → left_inverse (inverse f) f,
    rintros injective_f,  
    rintros x,
    rw inverse,
    dsimp,
    have : ∃ x', f x' = f x, exact Exists.intro x rfl,
    rw dif_pos this,
    have : f (classical.some this) = f x, from classical.some_spec this,
    apply injective_f this,
   },
  { show left_inverse (inverse f) f → injective f,
    rintros left_inverse_inverse_f_f,
    rintros x y fx_eq_fy,
    have fxx: (inverse f) (f x) = x, from left_inverse_inverse_f_f x,
    have fyy: (inverse f) (f y) = y, from left_inverse_inverse_f_f y,
    rw fx_eq_fy at fxx,
    rw [← fyy, ← fxx],
  },
end

/-
def right_inverse : Π {α : Type u}, (α → α → α) → (α → α) → α → Prop :=
λ {α : Type u} (f : α → α → α) (inv : α → α) (one : α), ∀ (a : α), f a (inv a) = one

def function.right_inverse : Π {α : Sort u₁} {β : Sort u₂}, (β → α) → (α → β) → Prop :=
λ {α : Sort u₁} {β : Sort u₂} (g : β → α) (f : α → β), left_inverse f g
-/

-- f (g x) = x

#print right_inverse
-- #check right_inverse

example : surjective f ↔ right_inverse (inverse f) f := begin
  split,
  { show surjective f → right_inverse (inverse f) f,
    rintros subjective_f,
    rintros x, rw inverse, dsimp,
    have : ∃ x', f x' = x, exact subjective_f x,
    rw dif_pos this,
    exact classical.some_spec this,
  },
  { show right_inverse (inverse f) f → surjective f,
    rintros right_inverse_inverse_f_f,
    rintros y,
    have : f (inverse f y) = y, from right_inverse_inverse_f_f y,
    use inverse f y,
    exact this,
  },
end

end

section
variable {α : Type*}
open function

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with ⟨j, h⟩,
  have h₁ : j ∉ f j,
  {
    intro h',
    have : j ∉ f j,
      {
         by rwa h at h' },
    contradiction },
  have h₂ : j ∈ S,
    {
      simp, exact h₁,

    },
  have h₃ : j ∉ S,
    {
      rwa h at h₁,
    },
  contradiction
end

end
