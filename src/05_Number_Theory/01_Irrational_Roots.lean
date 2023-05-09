import data.nat.gcd
import data.real.irrational

#print nat.coprime

example (m n : nat) (h : m.coprime n) : m.gcd n = 1 := h

example (m n : nat) (h : m.coprime n) : m.gcd n = 1 :=
by { rw nat.coprime at h, exact h }

example : nat.coprime 12 7 := by norm_num
example : nat.gcd 12 8 = 4 := by norm_num

#check @nat.prime_def_lt

example (p : ℕ) (prime_p : nat.prime p) : 2 ≤ p ∧ ∀ (m : ℕ), m < p → m ∣ p → m = 1 :=
by rwa nat.prime_def_lt at prime_p

#check nat.prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : nat.prime p) : ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p :=
prime_p.eq_one_or_self_of_dvd

example : nat.prime 17 := by norm_num

-- commonly used
example : nat.prime 2 := nat.prime_two
example : nat.prime 3 := nat.prime_three

#check @nat.prime.dvd_mul
#check nat.prime.dvd_mul nat.prime_two
#check nat.prime_two.dvd_mul

lemma even_of_even_sqr {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
begin
  rw [pow_two, nat.prime_two.dvd_mul] at h,
  cases h; assumption
end

example {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
nat.prime.dvd_of_dvd_pow nat.prime_two h

example (a b c : nat) (h : a * b = a * c) (h' : a ≠ 0) :
  b = c :=
begin
  -- library_search suggests the following:
  exact (mul_right_inj' h').mp h
end

example {m n : ℕ} (coprime_mn : m.coprime n) : m^2 ≠ 2 * n^2 :=
begin
  intro sqr_eq,
  have : 2 ∣ m,
    by {apply even_of_even_sqr, rw sqr_eq, norm_num},
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,
  have : 2 * (2 * k^2) = 2 * n^2,
  { rw [←sqr_eq, meq], ring },
  have : 2 * k^2 = n^2,
    by {norm_num at this, assumption},
  have : 2 ∣ n,
    by {apply even_of_even_sqr, rw ← this, norm_num},
  have : 2 ∣ m.gcd n,
    by { apply nat.dvd_gcd, assumption, assumption },
  have : 2 ∣ 1,
    by { rw coprime_mn.gcd_eq_one at this, assumption },
  norm_num at this
end

example {m n p : ℕ} (coprime_mn : m.coprime n) (prime_p : p.prime) : m^2 ≠ p * n^2 :=
begin
  intro sqr_eq,
  have pdivm2 : p ∣ m,
    by {apply prime_p.dvd_of_dvd_pow, rw sqr_eq, norm_num},
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp pdivm2,
  have : p * (p * k^2) = p * n^2,
    by { rw [←sqr_eq, meq], ring },
  have : p * k^2 = n^2,
    by { apply nat.eq_of_mul_eq_mul_left prime_p.pos, rw this },
  have : p ∣ n,
    by {apply nat.prime.dvd_of_dvd_pow prime_p, rw ← this, norm_num},
  have pdivmgcdn: p ∣ m.gcd n,
    by { apply nat.dvd_gcd, assumption, assumption },
  have : p ∣ 1,
    by { rw coprime_mn.gcd_eq_one at pdivmgcdn, assumption },
  have : 2 ≤ 1,
    by { apply prime_p.two_le.trans,
    exact nat.le_of_dvd zero_lt_one this },
  norm_num at this
end

#check nat.factors
#check nat.prime_of_mem_factors
#check nat.prod_factors
#check nat.factors_unique


theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
  (m * n).factorization p = m.factorization p + n.factorization p :=
by { rw nat.factorization_mul mnez nnez, refl }

theorem factorization_pow' (n k p : ℕ) :
  (n^k).factorization p = k * n.factorization p :=
by { rw nat.factorization_pow, refl }

theorem nat.prime.factorization' {p : ℕ} (prime_p : p.prime) :
  p.factorization p = 1 :=
by { rw prime_p.factorization, simp }


example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.prime) : m^2 ≠ p * n^2 :=
begin
  intro sqr_eq,
  have nsqr_nez : n^2 ≠ 0,
    by simpa,
  have eq1 : nat.factorization (m^2) p = 2 * m.factorization p,
    by { rw factorization_pow' },
  have eq2 : (p * n^2).factorization p = 2 * n.factorization p + 1,
    by {
      rw factorization_mul',
      rw factorization_pow',
      rw prime_p.factorization',
      ring,
      exact nat.prime.ne_zero prime_p,
      exact nsqr_nez
    },
  have : (2 * m.factorization p) % 2 = (2 * n.factorization p + 1) % 2,
  { rw [←eq1, sqr_eq, eq2] },
  rw [add_comm, nat.add_mul_mod_self_left, nat.mul_mod_right] at this,
  norm_num at this
end

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m^k = r * n^k)
  {p : ℕ} (prime_p : p.prime) : k ∣ r.factorization p :=
begin
  cases r with r,
  { simp },
  have npow_nz : n^k ≠ 0 := λ npowz, nnz (pow_eq_zero npowz),
  have eq1 : (m^k).factorization p = k * m.factorization p,
    by { rw factorization_pow' },
  have eq2 : (r.succ * n^k).factorization p =
      k * n.factorization p + r.succ.factorization p,
    by {
      rw factorization_mul',
      rw factorization_pow',
      ring,
      exact r.succ_ne_zero,
      exact npow_nz
    },
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p,
  { rw [←eq1, pow_eq, eq2, add_comm, nat.add_sub_cancel] },
  rw this,
  apply nat.dvd_sub',
  apply nat.dvd_mul_right,
  -- ??
  exact dvd.intro ((nat.factorization n) p) rfl
end

#check multiplicity
#check @irrational_nrt_of_n_not_dvd_multiplicity
#check irrational_sqrt_two

