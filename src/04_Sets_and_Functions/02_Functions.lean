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

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
begin
  split,
  intros h x xs,
  apply h,
  use [x, xs],
  intros h y,
  rintros ⟨x, xs, fxeq⟩,
  rw ← fxeq,
  exact h xs,
end

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
begin
  rintros x ⟨y, ys, fxeq⟩,
  rw ← h fxeq,
  exact ys
end

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, xfeq, rfl⟩,
  exact xfeq
end

-- The obtain tactic is used to introduce new variables and hypotheses 
-- based on an existential statement or a constructive proof. 
-- It is often used in conjunction with the have or suffices tactics. 
example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
begin
  intros x hu,
  obtain ⟨y, hy⟩ := h x,
  use y,
  split,
  dsimp [set.preimage],
  rw hy,
  exact hu,
  exact hy,
end



example (h : s ⊆ t) : f '' s ⊆ f '' t :=
begin
  rintros y ⟨x, xs, fxeq⟩,
  use [x, h xs, fxeq]
end

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros x hu,
  apply h,
  exact hu,
end

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x, 
  split,
  rintros (h | h),
  left, 
  exact h,
  right, 
  exact h,
  rintros (h | h),
  left, 
  exact h,
  right, 
  exact h,
end

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  rintros y ⟨x, ⟨xs, xt⟩, fxeq⟩,
  split,
  use [x, xs, fxeq],
  use [x, xt, fxeq],
end

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  -- 요거 이해가 안됨 rfl을 넣으면 뭐가 다른거지?
  rintros y ⟨⟨x, xs, rfl⟩, ⟨x', xt, fxeq'⟩⟩,
  use [x, xs],
  rw ← h fxeq',
  exact xt
end

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  -- 요거도 이해가 잘...
  rintros y ⟨⟨x, xs, rfl⟩, h⟩,
  use [x, xs],
  intro h',
  apply h,
  use [x, h', rfl],
end

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  rintros x ⟨h, h'⟩,
  split,
  exact h,
  intro h'',
  apply h',
  exact h'',
end

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  apply set.ext,
  intro y,
  split,
  rintros ⟨⟨x, xs, rfl⟩, xv⟩,
  use [x, xs, xv],
  rintros ⟨x, xs, xv⟩,
  split,
  simp,
  rw ← xv,
  apply set.mem_image_of_mem,
  exact xs.1,
  dsimp at *,
  rw ← xv,
  exact xs.2,
end


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
begin
  rintros y ⟨x, ⟨xs, fxu⟩, rfl⟩,
  left, 
  use [x, xs]
end

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin
  rintros x ⟨xs, fxu⟩,
  use [x, xs, fxu],
end

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  rintros x (xs | fxu),
  use [x, xs],
  right,
  exact fxu,
end

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
  intro e,  
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
begin
  intros x xpos y ypos,
  intro e,
  have h': sqrt (x^2) = sqrt (y^2),
    begin
      rw ←sq_sqrt xpos, 
      rw ←sq_sqrt ypos,
      rw e,
    end,
  have : x = y :=
    begin
      dsimp at xpos ypos,
      rw ← sqrt_sq xpos,
      rw ← sqrt_sq ypos,
      exact h',
    end,
  assumption,
end

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
begin
    intros x xnonneg y ynonneg,
    intro e,
    dsimp at e,
    have : x = y := 
      begin
        dsimp at xnonneg ynonneg,
        rw ← sqrt_sq xnonneg, 
        rw ← sqrt_sq ynonneg,
        rw e,
      end,
    rw this,
end

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
begin
  ext y, split,
  rintros ⟨x, xs, rfl⟩,
  apply sqrt_nonneg,
  dsimp,
  intro ypos,
  use y^2,
  split,
  apply pow_two_nonneg,
  rw pow_two,
  rw sqrt_mul_self ypos
end


example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} :=
begin
  ext y, 
  split,
  rintros ⟨x, rfl⟩,
  dsimp,
  apply pow_two_nonneg,
  intro ypos,
  use sqrt y,
  dsimp,
  rw pow_two,
  have : sqrt y * sqrt y = y :=
    by { rw mul_self_sqrt ypos },
  rw this,
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

example : injective f ↔ left_inverse (inverse f) f  :=
begin
  split,
  intros h y,
  apply h,
  apply inverse_spec,
  use y,
  intro h,
  intro x1,
  intro x2,
  intro e,
  rw ←h x1,
  rw ←h x2,
  rw e,
end

example : surjective f ↔ right_inverse (inverse f) f :=
begin
  split,
  intro h,
  intro y,
  rcases h y with ⟨x, fxeq⟩,
  apply inverse_spec,
  use x,
  exact fxeq,
  intro h,
  intro y,
  use inverse f y,
  exact h y,
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
  { intro h',
    have : j ∉ f j,
      { by rwa h at h' },
    contradiction },
  have h₂ : j ∈ S,
    by exact h₁,
  have h₃ : j ∉ S,
    by rwa h at h₁,
  contradiction
end

end
