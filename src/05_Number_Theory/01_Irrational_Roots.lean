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
  have m_dvd_2 : 2 ∣ m, {
    have : 2 ∣ m^2, exact dvd.intro (n ^ 2) (eq.symm sqr_eq),
    apply nat.prime.dvd_of_dvd_pow nat.prime_two this,
  },
  -- obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,
  rcases dvd_iff_exists_eq_mul_left.mp m_dvd_2 with ⟨ k, meq ⟩,
  have : 2 * (2 * k^2) = 2 * n^2,
  { rw [←sqr_eq, meq], ring },
  have : 2 * k^2 = n^2, begin
    apply mul_left_cancel₀ _ this,
    norm_num,
  end,
  have n_dvd_2 : 2 ∣ n, begin
    have : 2 ∣ n^2, exact dvd.intro (k ^ 2) this,
    apply nat.prime.dvd_of_dvd_pow nat.prime_two this,
  end,
  have m_gcd_n_dvd_2 : 2 ∣ m.gcd n, begin
    apply (dvd_gcd_iff 2 m n).mpr,
    exact ⟨m_dvd_2, n_dvd_2⟩,
  end,
  have : 2 ∣ 1, {
    have : m.gcd n = 1, from coprime_mn,
    rwa this at m_gcd_n_dvd_2,
  },
  norm_num at this
end

example {m n p : ℕ} (coprime_mn : m.coprime n) (prime_p : p.prime) : m^2 ≠ p * n^2 := begin
  intro sqr_eq,
  have m_dvd_p : p ∣ m, {
    have : p ∣ m^2, exact dvd.intro (n ^ 2) (eq.symm sqr_eq),
    apply nat.prime.dvd_of_dvd_pow prime_p this,
  },
  -- obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,
  rcases dvd_iff_exists_eq_mul_left.mp m_dvd_p with ⟨ k, meq ⟩,
  have : p * (p * k^2) = p * n^2,
  { rw [←sqr_eq, meq], ring },
  have : p * k^2 = n^2, begin
    apply mul_left_cancel₀ _ this,
    norm_num,
    intro p_neq_zero,
    have : p >= 2, from nat.prime.two_le prime_p,
    linarith only [this, p_neq_zero],
  end,
  have n_dvd_p : p ∣ n, begin
    have : p ∣ n^2, exact dvd.intro (k ^ 2) this,
    apply nat.prime.dvd_of_dvd_pow prime_p this,
  end,
  have m_gcd_n_dvd_p : p ∣ m.gcd n, begin
    apply (dvd_gcd_iff p m n).mpr,
    exact ⟨m_dvd_p, n_dvd_p⟩,
  end,
  have : p ∣ 1, {
    have : m.gcd n = 1, from coprime_mn,
    rwa this at m_gcd_n_dvd_p,
  },
  have p_le_one : p <= 1, {
    apply nat.le_of_dvd _ this,
    by norm_num,
  },
  have p_ge_two : p >= 2, from nat.prime.two_le prime_p,
  linarith only [p_le_one, p_ge_two],
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
    begin
      apply factorization_pow' m 2 p,
    end,
  have p_nonzero : p ≠ 0, exact nat.prime.ne_zero prime_p, 
  have eq2 : (p * n^2).factorization p = 2 * n.factorization p + 1,
    begin
      calc (p * n^2).factorization p
        = p.factorization p + (n^2).factorization p
          : by apply factorization_mul' p_nonzero nsqr_nez p
        ... = 1 + (n^2).factorization p
          : by rw nat.prime.factorization' prime_p
        ... = (n^2).factorization p + 1 : by ring
        ... = 2 * n.factorization p + 1 : by rw factorization_pow' n 2 p,
    end,
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
    sorry,
  have eq2 : (r.succ * n^k).factorization p =
      k * n.factorization p + r.succ.factorization p,
    sorry,
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p,
  { rw [←eq1, pow_eq, eq2, add_comm, nat.add_sub_cancel] },
  rw this,
  sorry
end

#check multiplicity
#check @irrational_nrt_of_n_not_dvd_multiplicity
#check irrational_sqrt_two

