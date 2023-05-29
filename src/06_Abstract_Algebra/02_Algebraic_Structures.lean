import data.real.basic

structure group₁ (α : Type*) :=
(mul: α → α → α)
(one: α)
(inv: α → α)
(mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z))
(mul_one: ∀ x : α, mul x one = x)
(one_mul: ∀ x : α, mul x one = x)
(mul_left_inv : ∀ x : α, mul (inv x) x = one)

structure Group₁ :=
(α : Type*)
(str : group₁ α)

section
variables (α β γ : Type*)
variables (f : α ≃ β) (g : β ≃ γ)

#check equiv α β
#check (f.to_fun : α → β)
#check (f.inv_fun : β → α)
#check (f.right_inv: ∀ x : β, f (f.inv_fun x) = x)
#check (f.left_inv: ∀ x : α, f.inv_fun (f x) = x)

#check (equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

example (x : α) : (f.trans g).to_fun x = g.to_fun (f.to_fun x) := rfl

example (x : α) : (f.trans g) x = g (f x) := rfl

example : (f.trans g : α → γ) = g ∘ f := rfl

end

example (α : Type*) : equiv.perm α = (α ≃ α) := rfl

def perm_group {α : Type*} : group₁ (equiv.perm α) :=
{ mul          := λ f g, equiv.trans g f,
  one          := equiv.refl α,
  inv          := equiv.symm,
  mul_assoc    := λ f g h, (equiv.trans_assoc _ _ _).symm,
  one_mul      := equiv.trans_refl,
  mul_one      := equiv.refl_trans,
  mul_left_inv := equiv.self_trans_symm }

structure add_group₁ (α : Type*) :=
(add : α → α → α)
(zero : α)
(neg : α -> α)
(add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z))
(add_zero : ∀ x : α, add x zero = x)
(zero_add : ∀ x : α, add zero x = x)
(add_left_neg : ∀ x : α, add (neg x) x = zero)

@[ext] structure point := (x : ℝ) (y : ℝ) (z : ℝ)

namespace point

def add (a b : point) : point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a: point) : point := ⟨-a.x, -a.y, -a.z⟩

def zero : point := ⟨0, 0, 0⟩

def add_group_point : add_group₁ point := {
  add := point.add,
  zero := point.zero,
  neg := point.neg,
  add_assoc := by {
    intros x y z,
    repeat { rw add },
    ext; dsimp; linarith,
  },
  add_zero := by {
    intro x,
    rw add,
    rw zero,
    ext; dsimp; linarith,
  },
  zero_add := by {
    intro x,
    rw add,
    rw zero,
    ext; dsimp; linarith,
  },
  add_left_neg := by {
    intro x,
    rw add,
    rw zero,
    rw neg,
    ext; dsimp; linarith,
  },
}

end point

section
variables {α : Type*} (f g : equiv.perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g^n

example : f * g * (g⁻¹) = f :=
by { rw [mul_assoc, mul_right_inv, mul_one] }

example : f * g * (g⁻¹) = f := mul_inv_cancel_right f g

example {α : Type*} (f g : equiv.perm α) : g.symm.trans (g.trans f) = f :=
mul_inv_cancel_right f g

end

class group₂ (α : Type*) :=
(mul: α → α → α)
(one: α)
(inv: α → α)
(mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z))
(mul_one: ∀ x : α, mul x one = x)
(one_mul: ∀ x : α, mul x one = x)
(mul_left_inv : ∀ x : α, mul (inv x) x = one)

instance {α : Type*} : group₂ (equiv.perm α) :=
{ mul          := λ f g, equiv.trans g f,
  one          := equiv.refl α,
  inv          := equiv.symm,
  mul_assoc    := λ f g h, (equiv.trans_assoc _ _ _).symm,
  one_mul      := equiv.trans_refl,
  mul_one      := equiv.refl_trans,
  mul_left_inv := equiv.self_trans_symm }

#check @group₂.mul

def my_square {α : Type*} [group₂ α] (x : α) := group₂.mul x x

#check @my_square

section
variables {β : Type*} (f g : equiv.perm β)

example : group₂.mul f g = g.trans f := rfl

example : my_square f = f.trans f := rfl

end

instance : inhabited point := { default := ⟨0, 0, 0⟩ }

#check (default : point)

example : ([] : list point).head = default := rfl

instance : has_add point := { add := point.add }

section
variables x y : point

#check x + y

example : x + y = point.add x y := rfl

end

instance has_mul_group₂ {α : Type*} [group₂ α] : has_mul α := ⟨group₂.mul⟩

instance has_one_group₂ {α : Type*} [group₂ α] : has_one α := ⟨group₂.one⟩

instance has_inv_group₂ {α : Type*} [group₂ α] : has_inv α := ⟨group₂.inv⟩

section
variables {α : Type*} (f g : equiv.perm α)

#check f * 1 * g⁻¹

def foo: f * 1 * g⁻¹ = g.symm.trans ((equiv.refl α).trans f) := rfl

end

class add_group₂ (α : Type*) :=
(add : α → α → α)
(zero: α)
(neg: α → α)
(add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z))
(add_zero: ∀ x : α, add x zero = x)
(zero_add: ∀ x : α, add zero x = x)
(add_left_neg : ∀ x : α, add (neg x) x = zero)

instance has_add_add_group₂ {α : Type*} [add_group₂ α] : has_add α := ⟨add_group₂.add⟩

instance has_zero_add_group₂ {α : Type*} [add_group₂ α] : has_zero α := ⟨add_group₂.zero⟩

instance has_neg_add_group₂ {α : Type*} [add_group₂ α] : has_neg α := ⟨add_group₂.neg⟩

instance {α : Type*} : add_group₂ point :=
{ add          := point.add,
  zero         := point.zero,
  neg          := point.neg,
  add_assoc := by {
    intros x y z,
    repeat { rw point.add },
    ext; dsimp; linarith,
  },
  add_zero := by {
    intro x,
    rw point.add,
    rw point.zero,
    ext; dsimp; linarith,
  },
  zero_add := by {
    intro x,
    rw point.add,
    rw point.zero,
    ext; dsimp; linarith,
  },
  add_left_neg := by {
    intro x,
    rw point.add,
    rw point.zero,
    rw point.neg,
    ext; dsimp; linarith,
  },
}
