import data.set.lattice
import data.nat.parity
import tactic

section
variable {α : Type*}
variables (s t u : set α)

open set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  rw subset_def at h,
  dsimp,
  rintros x ⟨xs, xu⟩,
  -- exact ⟨h _ xs, xu⟩,
  exact ⟨h x xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  -- ∀ (x : α), x ∈ s ∧ x ∈ u → x ∈ t ∧ x ∈ u
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩
end

theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by exact λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  right,
  show x ∈ s ∩ u,
  exact ⟨xs, xu⟩
end

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left, exact ⟨xs, xt⟩ },
  right, exact ⟨xs, xu⟩
end

-- 합집합을 rintros로 풀어내는 방법을 모르겠네
example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):= begin
  -- rintros x,
  rintros x z, -- z : x ∈ (s ∩ t) ∪ (s ∩ u)
  rcases z with ⟨xs, xt⟩  | ⟨xs, xu⟩ ,
  -- rintros x ⟨ ⟨xs, xt⟩  ⟩,
  { show x ∈ s ∩ (t ∪ u), -- xs and xt
    split,
    {  exact xs, },
    { left, exact xt, },
  },
  { show x ∈ s ∩ (t ∪ u), -- x ∈ s ∩ u
    split,
    { exact xs, },
    { right, exact xu, },
  },
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs }, dsimp,
  intro xtu, -- x ∈ t ∨ x ∈ u
  cases xtu with xt xu,
  { show false, from xnt xt },
  show false, from xnu xu
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

example : s \ (t ∪ u) ⊆ s \ t \ u := begin
  rintros x ⟨ xs, x_notin_t_and_u⟩,
  use xs,
  { show x ∉ t,
    by_contradiction xt,
    apply x_notin_t_and_u,
    left, exact xt,
  },
  { show x ∉ u,
    by_contradiction xt,
    apply x_notin_t_and_u,
    right, exact xt,
  },
end

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
set.ext $ λ x, ⟨λ ⟨xs, xt⟩, ⟨xt, xs⟩, λ ⟨xt, xs⟩, ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

example : s ∩ t = t ∩ s :=
begin
  apply subset.antisymm,
  { rintros x ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros x ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
by apply subset.antisymm; simp [and.comm]

example : s ∩ (s ∪ t) = s := begin
ext x,
split,
{
  rintros ⟨ xs, _ ⟩,
  exact xs, 
},
{
  intro xs,
  split,
  { exact xs, },
  { left, exact xs, },
}
end

example : s ∪ (s ∩ t) = s := begin
  ext x,
  split,
  { rintros (xs | ⟨xs, _⟩); exact xs, },
  { intro xs, left, exact xs, },
end

example : (s \ t) ∪ t = s ∪ t := begin
  ext x,
  split,
  { dsimp, rintros (⟨xs, nxt⟩ | xt),
    { left, exact xs },
    { right, exact xt },
  },
  { dsimp, rintros (xs | xt),
    {  
      cases classical.em (x ∈ t) with xt xnotint,
      { right, exact xt, },
      { left, exact ⟨ xs, xnotint ⟩ , },
     },
    { right, exact xt },
  },
end

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) := begin
  ext x,
  split; dsimp,
  { rintros (⟨ xs, nxt ⟩  | ⟨ xt, nxs ⟩ ); push_neg,
    { have l:  x ∈ s ∨ x ∈ t, exact or.inl xs,
      have r: x ∈ s → x ∉ t, {
        intro _, exact nxt,
      },
      exact ⟨ l, r ⟩,
      },
    { 
      have l: x ∈ s ∨ x ∈ t, exact or.inr xt,
      have r: x ∈ s → x ∉ t, by contradiction,
      exact ⟨l, r⟩,
    }
  },
  { push_neg,
    rintros ⟨(xs | xt), (xs_than_nxt)⟩, -- (nxs | nxt)⟩  ,
    { left, exact ⟨xs, xs_than_nxt xs⟩, },
    { --  x ∈ s ∧ x ∉ t ∨ x ∈ t ∧ x ∉ s
      right,
      contrapose! xs_than_nxt,
      exact ⟨xs_than_nxt xt, xt⟩,
    },
  },
end


def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em
end

example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
h

example (x : ℕ) : x ∈ (univ : set ℕ) :=
trivial

#check nat.prime.eq_two_or_odd -- p = 2 ∨ p % 2 = 1
#check nat.even_iff  -- even n ↔ n % 2 = 0 

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } := begin
  intro n,
  simp,
  intros prime_n gt_2,
  have : n = 2 ∨ n % 2 = 1, exact nat.prime.eq_two_or_odd prime_n,
  cases this with n_eq_2 n_mod_2,
  { exfalso, linarith, },
  { by_contradiction even_n,
    have : n % 2 = 0, exact nat.even_iff.mp even_n,
    linarith,
   },
end

#print prime
#print nat.prime

example (n : ℕ) : prime n ↔ nat.prime n := nat.prime_iff.symm

example (n : ℕ) (h : prime n) : nat.prime n :=
by { rw nat.prime_iff, exact h }

example (n : ℕ) (h : prime n) : nat.prime n :=
by rwa nat.prime_iff

end
section
variables (s t : set ℕ)

example (h₀ : ∀ x ∈ s, ¬ even x) (h₁ : ∀ x ∈ s, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x xs },
  apply h₁ x xs
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ s, prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use [x, xs, prime_x]
end

section
variable (ssubt : s ⊆ t)

include ssubt

example (h₀ : ∀ x ∈ t, ¬ even x) (h₁ : ∀ x ∈ t, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x := begin
  intros x xs,
  have xt: x ∈ t, exact ssubt xs,
  exact ⟨ h₀ x xt, h₁ x xt ⟩,  
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ t, prime x := begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  have xt: x ∈ t, exact ssubt xs,
  use x,
  exact ⟨xt, prime_x⟩,
end

end

end

section
variables {α I : Type*}
variables A B : I → set α
variable  s : set α
open set

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  rintros ⟨i, xAi, xs⟩,
  exact ⟨xs, ⟨i, xAi⟩⟩
end

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    intro i,
    exact (h i).2 },
  rintros ⟨h1, h2⟩ i,
  split,
  { exact h1 i },
  exact h2 i
end

open_locale classical

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) := begin
  ext x,
  simp only [mem_union_eq, mem_Inter],
  split,
  { show (x ∈ s ∨ ∀ (i : I), x ∈ A i) → ∀ (i : I), x ∈ A i ∨ x ∈ s,
    rintros (xs | alli_x_in_ai ) i,
    { show x ∈ A i ∨ x ∈ s, right, exact xs },
    { show x ∈ A i ∨ x ∈ s, left, exact alli_x_in_ai i },
  },
  { show  (∀ (i : I), x ∈ A i ∨ x ∈ s) → (x ∈ s ∨ ∀ (i : I), x ∈ A i),
    intro h,
    cases em (x ∈ s) with xs nxs,
    { left, exact xs, },
    { right,  intro i, 
      have xai_or_xs : x ∈ A i ∨ x ∈ s, by apply h i,
      have : x ∈ A i, begin
        cases xai_or_xs with xai xs,
        { exact xai },
        { exfalso, exact nxs xs }
      end,
      exact this,
    },
  },
end

def primes : set ℕ := {x | nat.prime x}

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, rw mem_Union₂, refl }

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, simp }

example : (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x = 1} :=
begin
  intro x,
  contrapose!,
  simp,
  apply nat.exists_prime_and_dvd
end

#check eq_univ_of_forall 
-- {s : set α} : (∀ x, x ∈ s) → s = univ
#check nat.exists_infinite_primes
-- (n : ℕ) : ∃ p, n ≤ p ∧ prime p

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ := begin
  ext,
  simp only [mem_Union],
  split,
  { intro h,
    rcases h with ⟨p, p_prime, x_le_p⟩,
    simp at x_le_p,
    -- dsimp at x_le_p,
    -- rw ← eq_univ_of_forall,
    -- use x_le_p,
    -- simp at x_le_p,
  },  
  { sorry },
end

end

section
open set

variables {α : Type*} (s : set (set α))

example : ⋃₀ s = ⋃ t ∈ s, t :=
begin
  ext x,
  rw mem_Union₂,
  refl
end

example : ⋂₀ s = ⋂ t ∈ s, t :=
begin
  ext x,
  rw mem_Inter₂,
  refl
end

end

