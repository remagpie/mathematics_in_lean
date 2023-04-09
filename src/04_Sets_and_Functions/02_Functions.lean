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
  split; intros ssv x xs,
  {
    apply ssv,
    use [x, xs],
  },
  rcases xs with ⟨x', xs', rfl⟩,
  let h := ssv xs',
  use h,
end

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s := begin
  intros x,
  simp,
  intros y ys fyx,
  let g := h fyx,
  rw <-g,
  apply ys,
end

example : f '' (f⁻¹' u) ⊆ u := begin
  intros x,
  simp,
  intros y fyu fyx,
  rw fyx at fyu,
  apply fyu,
end
-- ??
example : f '' (f⁻¹' u) ⊆ u := begin
  simp,
end

example (h : surjective f) : u ⊆ f '' (f⁻¹' u) := begin
  intros x xu,
  simp,
  rcases h x with ⟨y, fyx⟩,
  use y,
  rw <-fyx at xu,
  exact ⟨xu, fyx⟩
end

example (h : s ⊆ t) : f '' s ⊆ f '' t := begin
  simp,
  intros x xs,
  simp,
  use x,
  exact ⟨h xs, rfl⟩
end

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := begin
  intros x,
  simp,
  intros fxu,
  apply h fxu,
end

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := begin
  ext x,
  dsimp,
  refl,
end
-- ??
example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := begin
  simp,
end

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := begin
  simp,
  split; rintros x ⟨xs, xt⟩; simp; use x,
  { exact ⟨xs, rfl⟩ },
  { exact ⟨xt, rfl⟩ },
end

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := begin
  intros x,
  rintros ⟨xfs, xft⟩,
  rcases xfs with ⟨y, ⟨ys, fyx⟩⟩,
  rcases xft with ⟨y', ⟨y't, fy'x⟩⟩,
  simp,
  use y,
  split,
  {
    rw <-fy'x at fyx,
    let g := h fyx,
    rw <-g at y't,
    exact ⟨ys, y't⟩
  },
  exact fyx,
end

example : f '' s \ f '' t ⊆ f '' (s \ t) := begin
  rintros x ⟨xfs, xnft⟩,
  rcases xfs with ⟨y, ⟨ys, fyx⟩⟩,
  simp,
  use y,
  split,
  {
    split,
    { exact ys },
    contrapose! xnft,
    simp,
    use y,
    exact ⟨xnft, fyx⟩,
  },
  exact fyx,
end

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := begin
  intros x,
  simp,
  intros fxu fxnv,
  exact ⟨fxu, fxnv⟩
end
-- ??
example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := begin
  simp,
end

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := begin
  ext x,
  split,
  {
    rintros ⟨⟨y, ⟨ys, fyx⟩⟩, xv⟩,
    simp,
    use y,
    rw <-fyx at xv,
    exact ⟨⟨ys, xv⟩, fyx⟩
  },
  rintros ⟨y, ⟨⟨ys, yfv⟩, fyx⟩⟩,
  simp at yfv,
  split,
  {
    use y,
    exact ⟨ys, fyx⟩,
  },
  rw fyx at yfv,
  exact yfv,
end

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u := begin
  intros x,
  rintros ⟨y, ⟨⟨ys, h⟩, yfx⟩⟩,
  simp at h,
  left,
  use y,
  exact ⟨ys, yfx⟩,
end

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := begin
  intros x,
  rintros ⟨xs, h⟩,
  simp at h,
  split,
  {
    simp,
    use x,
    exact ⟨xs, rfl⟩,
  },
  apply h,
end

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := begin
  intros x,
  rintros (xs | h); simp,
  {
    left,
    use x,
    exact ⟨xs, rfl⟩
  },
  simp at h,
  right,
  exact h,
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
  intros x xpos y ypos,
  intro h,
  calc
    x   = sqrt x ^ 2 : by rw sq_sqrt xpos
    ... = sqrt y ^ 2 : by rw h
    ... = y          : by rw sq_sqrt ypos
end

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } := begin
  intros x xpos y ypos,
  intro h,
  simp at h,
  calc
    x   = sqrt (x ^ 2) : by rw sqrt_sq xpos
    ... = sqrt (y ^ 2) : by rw h
    ... = y            : by rw sqrt_sq ypos
end

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} := begin
  ext x,
  split,
  {
    simp,
    intros y ypos,
    intro h,
    rw <-h,
    apply sqrt_nonneg,
  },
  simp,
  intros xpos,
  use (x ^ 2),
  exact ⟨sq_nonneg x, sqrt_sq xpos⟩,
end

example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} := begin
  ext x,
  simp,
  split,
  {
    rintros ⟨y, h⟩,
    rw <-h,
    apply sq_nonneg y,
  },
  intros xpos,
  use (sqrt x),
  apply sq_sqrt xpos,
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

#print left_inverse
example : injective f ↔ left_inverse (inverse f) f  := begin
  split,
  {
    intros h,
    rw left_inverse,
    intros x,
    rw inverse,
    dsimp,
    rw dif_pos,
    sorry,
    sorry,
  },
  {
    rw left_inverse,
    intros h,
    intros x y,
    intros g,
    let h':= h x,
    rw g at h',
    rw inverse at h',
    simp at h',
    sorry,
  }
end

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
  have h₂ : j ∈ S, {
    rw h at h₁,
    simp at h₁,
    rw <-h,
    apply h₁,
  },
  have h₃ : j ∉ S, {
    contrapose! h₁,
    rw h,
    apply h₁,
  },
  contradiction
end

end
