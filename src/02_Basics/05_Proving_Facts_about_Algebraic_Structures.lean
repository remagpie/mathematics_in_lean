import topology.metric_space.basic

section
variables {α : Type*} [partial_order α]
variables x y z : α

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬ x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
lt_iff_le_and_ne

end

section
variables {α : Type*} [lattice α]
variables x y z : α

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right: y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x :=
begin
  apply le_antisymm,
  {
    show x ⊓ y ≤ y ⊓ x,
    apply le_inf,
    apply inf_le_right,
    apply inf_le_left,
  },
  {
    show y ⊓ x ≤ x ⊓ y,
    apply le_inf,
    apply inf_le_right,
    apply inf_le_left,
  },
end
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) :=
begin
  apply le_antisymm,
  {
    show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z),
    apply le_inf,
    {
      show x ⊓ y ⊓ z ≤ x,
      apply le_trans,
      apply inf_le_left,
      apply inf_le_left,
    },
    apply le_inf,
    {
      show x ⊓ y ⊓ z ≤ y,
      apply le_trans,
      apply inf_le_left,
      apply inf_le_right,
    },
    {
      show x ⊓ y ⊓ z ≤ z,
      apply le_trans,
      apply inf_le_right,
      apply le_refl,
    },
  },
  {
    show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z,
    apply le_inf,
    apply le_inf,
    {
      show x ⊓ (y ⊓ z) ≤ x,
      apply le_trans,
      apply inf_le_left,
      apply le_refl,
    },
    {
      show x ⊓ (y ⊓ z) ≤ y,
      apply le_trans,
      apply inf_le_right,
      apply inf_le_left,
    },
    {
      show x ⊓ (y ⊓ z) ≤ z,
      apply le_trans,
      apply inf_le_right,
      apply inf_le_right,
    }
  },
end
example : x ⊔ y = y ⊔ x :=
begin
  apply le_antisymm,
  {
    show x ⊔ y ≤ y ⊔ x,
    apply sup_le,
    apply le_sup_right,
    apply le_sup_left,
  },
  {
    show y ⊔ x ≤ x ⊔ y,
    apply sup_le,
    apply le_sup_right,
    apply le_sup_left,
  },
end
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
begin
  apply le_antisymm,
  {
    show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z),
    apply sup_le,
    {
      show x ⊔ y ≤ x ⊔ (y ⊔ z),
      apply sup_le,
      apply le_sup_left,
      apply le_trans,
      apply le_sup_left,
      exact z,
      apply le_sup_right,
    },
    {
      show z ≤ x ⊔ (y ⊔ z),
      apply le_trans,
      apply le_sup_right,
      exact y,
      apply le_sup_right,
    },
  },
  {
    show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z,
    apply sup_le,
    {
      show x ≤ x ⊔ y ⊔ z,
      apply le_trans,
      apply le_sup_left,
      exact y,
      apply le_sup_left,
    },
    apply sup_le,
    {
      show y ≤ x ⊔ y ⊔ z,
      apply le_trans,
      apply le_sup_right,
      exact x,
      apply le_sup_left,
    },
    {
      show z ≤ x ⊔ y ⊔ z,
      apply le_sup_right,
    },
  },
end

theorem absorb1 : x ⊓ (x ⊔ y) = x :=
begin
  apply le_antisymm,
  {
    show x ⊓ (x ⊔ y) ≤ x,
    apply inf_le_left,
  },
  {
    show x ≤ x ⊓ (x ⊔ y),
    apply le_inf,
    apply le_refl,
    apply le_sup_left,
  },
end

theorem absorb2 : x ⊔ (x ⊓ y) = x :=
begin
  apply le_antisymm,
  {
    show x ⊔ x ⊓ y ≤ x,
    apply sup_le,
    apply le_refl,
    apply inf_le_left,
  },
  {
    show x ≤ x ⊔ x ⊓ y,
    apply le_sup_left,
  },
end

end

section
variables {α : Type*} [distrib_lattice α]
variables x y z : α

#check (inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
#check (inf_sup_right : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z))
#check (sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

end

section
variables {α : Type*} [lattice α]
variables a b c : α

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
sorry

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) :=
sorry

end

section
variables {R : Type*} [ordered_ring R]
variables a b c : R

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example : a ≤ b → 0 ≤ b - a :=
begin
  assume h: a ≤ b,
  rw ←sub_self a,
  rw [sub_eq_add_neg, add_comm],
  rw [sub_eq_add_neg, add_comm b],
  apply add_le_add_left,
  exact h,
end

example : 0 ≤ b - a → a ≤ b :=
begin
  assume h: 0 ≤ b - a,
  rw ←add_zero a,
  rw ←add_zero b,
  nth_rewrite 1 ←sub_self a,
  rw add_sub,
  nth_rewrite 1 add_comm,
  rw ←add_sub,
  apply add_le_add_left,
  exact h,
end

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c :=
begin
  have h2 : 0 ≤ b - a,
  {
    rw ←sub_self a,
    rw [sub_eq_add_neg, add_comm],
    rw [sub_eq_add_neg, add_comm b],
    apply add_le_add_left,
    exact h,
  },
  have h3 : 0 ≤ (b - a) * c,
  {
    apply mul_nonneg,
    exact h2,
    exact h',
  },
  rw ←add_zero (b * c),
  rw ←sub_self (a * c),
  rw add_sub,
  rw add_comm,
  nth_rewrite 0 ←add_zero (a * c),
  rw ←add_sub,
  apply add_le_add_left,
  rw ←sub_mul,
  exact h3,
end

end

section
variables {X : Type*} [metric_space X]
variables x y z : X

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y :=
begin
  have h1 : dist x x ≤ dist x y + dist y x,
  {
    apply dist_triangle,
  },
  nth_rewrite 2 dist_comm at h1,
  rw dist_self at h1,
  rw ←two_mul at h1,
  rw ←zero_mul (dist x y) at h1,
  linarith,
end

end

