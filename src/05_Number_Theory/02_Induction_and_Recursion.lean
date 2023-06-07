import data.nat.prime
import algebra.big_operators
import tactic

example (n : nat) : n.succ ≠ nat.zero := nat.succ_ne_zero n

example (m n : nat) (h : m.succ = n.succ) : m = n := nat.succ.inj h

def fac : ℕ → ℕ
| 0       := 1
| (n + 1) := (n + 1) * fac n

example : fac 0 = 1 := rfl
example : fac 0 = 1 := by rw fac
example : fac 0 = 1 := by simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := rfl
example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rw fac
example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by simp [fac]

theorem fac_pos (n : ℕ) : 0 < fac n :=
begin
  induction n with m ih,
  { rw fac, exact zero_lt_one },
  rw fac,
  exact mul_pos m.succ_pos ih,
end

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n :=
begin
  induction n with n ih,
  { exact absurd ipos (not_lt_of_ge ile) },
  rw fac,
  cases nat.of_le_succ ile with h h,
  { apply dvd_mul_of_dvd_right (ih h) },
  rw h,
  apply dvd_mul_right
end

theorem pow_two_le_fac (n : ℕ) : 2^(n-1) ≤ fac n :=
begin
  cases n with n,
  { simp [fac] },
  induction n with n ih,
  { rw fac, rw fac, norm_num, },
  { rw fac,
    -- ih: 2 ^ (n.succ - 1) ≤ fac n.succ
    have ih'₀: 2 * 2 ^ (n.succ - 1) ≤ 2 * fac n.succ, {
      exact mul_le_mul_left' ih 2,
    },
    have ih'₁: 2 ^ (n.succ - 1 + 1) ≤ 2 * fac n.succ, {
      have : 2 * 2 ^ (n.succ - 1) = 2 ^ (n.succ - 1 + 1), {
        rw add_comm,
        rw pow_add,
        by norm_num,
      },
      rw ← this,
      exact ih'₀,
    },
    have ih': 2 ^ (n.succ.succ - 1) ≤ 2 * fac n.succ, {
      have : n.succ - 1 + 1 = n.succ.succ - 1, {
        by norm_num,
      },
      rw this at ih'₁,
      exact ih'₁,
    },
    have ih'': 2 * fac n.succ ≤ (n.succ + 1) * fac n.succ, {
      have : 2 ≤ n.succ + 1, {
        have : 1 ≤ n.succ, {
          exact nat.succ_pos n,
        },
        exact nat.succ_le_succ this,
      },
      exact mul_le_mul_right' this (fac n.succ),
    },
    apply le_trans ih' ih'',
  },
end

section

variables {α : Type*} (s : finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check finset.sum s f
#check finset.prod s f

open_locale big_operators
open finset

example : s.sum f = ∑ x in s, f x := rfl
example : s.prod f = ∏ x in s, f x := rfl

example : (range n).sum f = ∑ x in range n, f x := rfl
example : (range n).prod f = ∏ x in range n, f x := rfl

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ): ∑ x in range n.succ, f x = (∑ x in range n, f x) + f n :=
finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ): ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
finset.prod_range_succ f n


example (n : ℕ) : fac n = ∏ i in range n, (i + 1) :=
begin
  induction n with n ih,
  { simp [fac] },
  simp [fac, ih, prod_range_succ, mul_comm]
end

example (a b c d e f : ℕ) : a * ((b * c) * f * (d * e)) = d * (a * f * e) * (c * b) :=
by simp [mul_assoc, mul_comm, mul_left_comm]

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 :=
begin
-- ∑ (i : ℕ) in range (n + 1), i = n * (n + 1) / 2
  symmetry,
  -- n * (n + 1) / 2 = ∑ (i : ℕ) in range (n + 1), i
  apply nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2),
  -- n * (n + 1) = 2 * ∑ (i : ℕ) in range (n + 1), i
  induction n with n ih,
  { simp },
  -- n.succ * (n.succ + 1) = 2 * ∑ (i : ℕ) in range (n.succ + 1), i
  --     rw [finset.sum_range_succ, mul_add 2, ←ih, nat.succ_eq_add_one],
  rw finset.sum_range_succ,
  -- n.succ * (n.succ + 1) = 2 * (∑ (x : ℕ) in range n.succ, x + n.succ)
  rw mul_add 2, 
  -- n.succ * (n.succ + 1) = 2 * ∑ (x : ℕ) in range n.succ, x + 2 * n.succ
  rw ←ih, 
  -- n.succ * (n.succ + 1) = n * (n + 1) + 2 * n.succ
  rw nat.succ_eq_add_one,
  -- (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1)
  ring
end

-- example (f : ℕ → ℕ) (n : ℕ): ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
-- finset.prod_range_succ f n
theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i^2 = n * (n + 1) * (2 *n + 1) / 6 := begin
  symmetry,
  apply nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6),
  induction n with n ih,
  { simp },
  -- ih: n * (n + 1) * (2 * n + 1) = 6 * ∑ (i : ℕ) in range (n + 1), i ^ 2
  -- n.succ * (n.succ + 1) * (2 * n.succ + 1) = 6 * ∑ (i : ℕ) in range (n.succ + 1), i ^ 2
  rw finset.sum_range_succ _ (n.succ),
  -- n.succ * (n.succ + 1) * (2 * n.succ + 1) = 6 * (∑ (x : ℕ) in range n.succ, x ^ 2 + n.succ ^ 2)
  rw mul_add 6,
  -- n.succ * (n.succ + 1) * (2 * n.succ + 1) = 6 * ∑ (x : ℕ) in range n.succ, x ^ 2 + 6 * n.succ ^ 2
  rw ←ih,
  -- n.succ * (n.succ + 1) * (2 * n.succ + 1) = n * (n + 1) * (2 * n + 1) + 6 * n.succ ^ 2
  rw nat.succ_eq_add_one,
  ring,
end

end

inductive my_nat
| zero : my_nat
| succ : my_nat → my_nat

namespace my_nat

def add : my_nat → my_nat → my_nat
| x zero     := x
| x (succ y) := succ (add x y)

def mul : my_nat → my_nat → my_nat
| x zero     := zero
| x (succ y) := add (mul x y) x

theorem zero_add (n : my_nat) : add zero n = n :=
begin
  induction n with n ih,
  { refl },
  rw [add, ih]
end

theorem succ_add (m n : my_nat) : add (succ m) n = succ (add m n) :=
begin
  induction n with n ih,
  { refl },
  rw [add, ih],
  refl
end

theorem add_comm (m n : my_nat) : add m n = add n m :=
begin
  induction n with n ih,
  { rw zero_add, refl },
  rw [add, succ_add, ih]
end

theorem add_assoc (m n k : my_nat) : add (add m n) k = add m (add n k) := begin
  induction n with n ih,
  { rw zero_add, refl },
  { -- (m.add n.succ).add k = m.add (n.succ.add k) 
  rw add,
  rw succ_add,
  rw ih,
  rw succ_add,
  rw add,
  },
end

theorem mul_add  (m n k : my_nat) : mul m (add n k) = add (mul m n) (mul m k) :=
sorry

theorem zero_mul (n : my_nat) : mul zero n = zero :=
sorry

theorem succ_mul (m n : my_nat) : mul (succ m) n = add (mul m n) n :=
sorry

theorem mul_comm (m n : my_nat) : mul m n = mul n m :=
sorry

end my_nat
