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

example : inj_on sqrt { x | x ≥ 0 } :=
sorry

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
sorry

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
sorry

example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} :=
sorry

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

example : injective f ↔ left_inverse (inverse f) f  :=
sorry

example : surjective f ↔ right_inverse (inverse f) f :=
sorry

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
  { intro h',
    have : j ∉ f j,
      { by rwa h at h' },
    contradiction },
  have h₂ : j ∈ S,
    sorry,
  have h₃ : j ∉ S,
    sorry,
  contradiction
end

end
