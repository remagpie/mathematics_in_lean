import data.real.basic

section
variables {x y : ℝ}

example (h : y > x^2) : y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

example (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }

example (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h

example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h h,
  { rw abs_of_nonneg h,
    intro h, left, exact h },
  rw abs_of_neg h,
  intro h, right, exact h
end

namespace my_abs

theorem le_abs_self (x : ℝ) : x ≤ abs x :=
begin
  by_cases h : 0 ≤ x,
  { rw abs_of_nonneg h },
  { rw abs_of_neg (lt_of_not_ge h),
    linarith }
end

theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x :=
begin
  by_cases h : 0 ≤ x,
  { rw abs_of_nonneg h,
    linarith },
  { rw abs_of_neg (lt_of_not_ge h)}
end

theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y :=
begin
  by_cases h : 0 ≤ x + y,
  { rw abs_of_nonneg h,
    linarith [le_abs_self x, le_abs_self y] },
  { rw abs_of_neg (lt_of_not_ge h),
    linarith [neg_le_abs_self x, neg_le_abs_self y] }
end

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
begin
  split,
  { intro h,
    by_cases h' : 0 ≤ y,
    { left, rwa abs_of_nonneg h' at h },
    { right, rwa abs_of_neg (lt_of_not_ge h') at h } },
  { intro h,
    cases h with h h,
    { apply lt_of_lt_of_le h (my_abs.le_abs_self y) },
    { apply lt_of_lt_of_le h (my_abs.neg_le_abs_self y) }}
end



theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
begin
  split,
  { intro h,
    split,
    { have h1 := my_abs.neg_le_abs_self x,
      linarith },
    { apply lt_of_le_of_lt (my_abs.le_abs_self x),
      exact h }},
  { rintros ⟨h1, h2⟩,
    by_cases h0 : 0 ≤ x,
    { rw abs_of_nonneg h0,
      exact h2 },
    { rw abs_of_neg (lt_of_not_ge h0),
      linarith }}
end

end my_abs
end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, exact xlt },
  { contradiction },
  right, exact xgt
end

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right },
  rw [mul_comm, mul_assoc],
  apply dvd_mul_right
end

example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
begin
  obtain ⟨x, y, hz⟩ := h,
  cases hz,
  { rw hz,
    have hx2_nonneg : 0 ≤ x^2 := sq_nonneg x,
    have hy2_nonneg : 0 ≤ y^2 := sq_nonneg y,
    linarith },
  { rw hz,
    have hx2_nonneg : 0 ≤ x^2 := sq_nonneg x,
    have hy2_nonneg : 0 ≤ y^2 := sq_nonneg y,
    linarith }
end


example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
  have h' : x^2 - 1 = 0,
  { rw h, rw sub_self },
  have h'' : (x - 1) * (x + 1) = 0,
   { rw ← h',
    ring },
  cases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 h1,
  { left,
    exact eq_of_sub_eq_zero h1 },
  { right,
    exact eq_neg_iff_add_eq_zero.mpr h1 }
end


example {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
begin
  have h' : x^2 - y^2 = 0,
  { rw h, rw sub_self },
  have h' : (x - y) * (x + y) = 0,
  { rw [←sub_mul, h, sub_self] },
  cases eq_zero_or_eq_zero_of_mul_eq_zero h' with h1 h1,
  { left,
    exact eq_of_sub_eq_zero h1 },
  { right,
    exact eq_neg_of_add_eq_zero h1 }
end

section
variables {R : Type*} [comm_ring R] [is_domain R]
variables (x y : R)

example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

example (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry

end

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end

section
open_locale classical

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction
end

example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
sorry

end
