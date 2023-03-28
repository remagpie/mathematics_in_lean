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
    { apply le_inf,
      { apply inf_le_right, },
      { apply inf_le_left, }, },
    { apply le_inf,
      { apply inf_le_right, },
      { apply inf_le_left, }, },
end

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := 
begin
  apply le_antisymm,
  { apply le_inf,
    { apply le_trans,
      apply inf_le_left,
      apply inf_le_left },
    apply le_inf,
    { apply le_trans,
      apply inf_le_left,
      apply inf_le_right },
    apply inf_le_right  },
  apply le_inf,
  { apply le_inf,
    { apply inf_le_left },
    apply le_trans,
    apply inf_le_right,
    apply inf_le_left },
  apply le_trans,
  apply inf_le_right,
  apply inf_le_right
end

example : x ⊔ y = y ⊔ x := sorry
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := sorry

theorem absorb1 : x ⊓ (x ⊔ y) = x := sorry
theorem absorb2 : x ⊔ (x ⊓ y) = x := sorry

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
begin
  sorry
end


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
  intro h,
  rw ←sub_self a,
  rw sub_eq_add_neg,
  rw sub_eq_add_neg,
  rw add_comm,
  rw add_comm b,
  apply add_le_add_left h,
end

example : 0 ≤ b - a → a ≤ b := 
begin
  intro h,
  rw [←add_zero a, ←sub_add_cancel b a, add_comm (b - a)],
  apply add_le_add_left h,
end


example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := begin
  rw <-add_zero (b * c),
  rw add_comm,
  rw <-add_zero (a * c),
  nth_rewrite 1 <-sub_self (a * c),
  rw sub_eq_add_neg,
  rw add_assoc,
  apply add_le_add_left,
  rw add_comm,
  rw <-neg_mul,
  rw <-add_mul,
  apply mul_nonneg,
  {
    rw <-sub_self a,
    rw sub_eq_add_neg a a,
    rw add_comm a (-a),
    rw add_comm b (-a),
    apply add_le_add_left,
    apply h,
  },
  apply h',
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
  have : 0 ≤ dist x y + dist y x,
    { rw [←dist_self x],
      apply dist_triangle, },
    linarith [dist_comm x y],
end

end

