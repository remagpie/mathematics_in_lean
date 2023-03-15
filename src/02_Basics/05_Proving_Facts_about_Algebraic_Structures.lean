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

example : x ⊓ y = y ⊓ x := begin
  apply le_antisymm,
  repeat {
    apply le_inf,
    apply inf_le_right,
    apply inf_le_left,
  }
end
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := begin
  apply le_antisymm,
  {
    apply le_inf,
    {
      apply le_trans,
      apply inf_le_left,
      apply inf_le_left,
    },
    {
      apply le_inf,
      {
        apply le_trans,
        apply inf_le_left,
        apply inf_le_right,
      },
      {
        apply inf_le_right,
      }
    },
  },
  {
    apply le_inf,
    {
      apply le_inf,
      {
        apply inf_le_left,
      },
      {
        apply le_trans,
        apply inf_le_right,
        apply inf_le_left,
      }
    },
    {
      apply le_trans,
      apply inf_le_right,
      apply inf_le_right,
    },
  },
end
example : x ⊔ y = y ⊔ x := begin
  apply ge_antisymm,
  repeat {
    apply sup_le,
    apply le_sup_right,
    apply le_sup_left,
  }
end
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := begin
  sorry
end

theorem absorb1 : x ⊓ (x ⊔ y) = x := begin
  apply le_antisymm,
  {
    apply inf_le_left,
  },
  {
    apply le_inf,
    refl,
    apply le_sup_left,
  }
end
theorem absorb2 : x ⊔ (x ⊓ y) = x := begin
  apply le_antisymm,
  {
    apply sup_le,
    refl,
    apply inf_le_left,
  },
  apply le_sup_left,
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
begin
  apply le_antisymm,
  {
    apply le_inf,
    {
      apply sup_le,
      { apply le_sup_left },
      {
        apply le_trans,
        apply inf_le_left,
        apply le_sup_right,
      },
    },
    {
      apply sup_le,
      { apply le_sup_left },
      {
        apply le_trans,
        apply inf_le_right,
        apply le_sup_right,
      },
    },
  },
  {
    rw h,
    apply sup_le,
    {
      rw inf_comm,
      rw h,
      apply sup_le,
      repeat {
        apply le_trans,
        { apply inf_le_left },
        { apply le_sup_left },
      },
    },
    {
      rw inf_comm,
      rw h,
      apply sup_le,
      {
        rw inf_comm,
        apply le_trans,
        { apply inf_le_left, },
        { apply le_sup_left, },
      },
      {
        rw inf_comm,
        apply le_sup_right,
      },
    }
  }
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

example : a ≤ b → 0 ≤ b - a := begin
  intros h,
  rw <-sub_self a,
  rw sub_eq_add_neg a a,
  rw sub_eq_add_neg b a,
  rw add_comm a (-a),
  rw add_comm b (-a),
  apply add_le_add_left,
  apply h,
end

example : 0 ≤ b - a → a ≤ b := begin
  intros h,
  rw <-add_zero b,
  rw add_comm,
  rw <-add_zero a,
  nth_rewrite 1 <-sub_self a,
  rw sub_eq_add_neg,
  rw add_assoc,
  apply add_le_add_left,
  rw add_comm,
  rw <-sub_eq_add_neg,
  exact h,
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

#check nonneg_of_mul_nonneg_left
example (x y : X) : 0 ≤ dist x y := begin
  have h : 0 <= 2 * dist x y, {
    rw two_mul,
    nth_rewrite 1 dist_comm,
    rw <-dist_self x,
    apply dist_triangle,
  },
  apply nonneg_of_mul_nonneg_left,
  { apply h },
  { apply zero_lt_two },
end

end
