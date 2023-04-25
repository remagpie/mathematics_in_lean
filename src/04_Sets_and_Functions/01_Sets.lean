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
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
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

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  rintros x (⟨xs, xt⟩ | ⟨xs, xu⟩),
  split, 
  exact xs, 
  left, 
  exact xt,
  split, 
  exact xs, 
  right, 
  exact xu,
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

example : s \ (t ∪ u) ⊆ s \ t \ u :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1,
  have xnt : x ∉ t := λ xt, xstu.2 (or.inl xt), 
  have xnu : x ∉ u := λ xu, xstu.2 (or.inr xu),
  split,
  split,
  exact xs,
  exact xnt,
  exact xnu,
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
subset.antisymm (λ x ⟨xs, xt⟩, ⟨xt, xs⟩) (λ x ⟨xt, xs⟩, ⟨xs, xt⟩)

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  simp only [mem_inter_eq, mem_union_eq],
  split,
  rintros ⟨xs, xst⟩, 
  exact xs,
  rintros xs, exact ⟨xs, or.inl xs⟩,
end

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  simp only [mem_union_eq, mem_inter_eq],
  split,
  rintros (xs | ⟨xs, xt⟩),
  exact xs,
  exact xs,
  intro xs,
  left,
  exact xs,
end

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext x,
  split,
  intro hx,
  cases hx,
  left,
  exact hx.1,
  right,
  exact hx,
  intro hx,
  cases hx,
  by_cases hxt : x ∈ t,
  right,
  exact hxt,
  left,
  exact ⟨hx, hxt⟩,
  right,
  exact hx,
end


example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  intro hx,
  cases hx,
  cases hx with xs xt,
  split,
  left, exact xs,
  intro hst, apply xt, 
  exact hst.2,
  cases hx with xt xs,
  split,
  right, 
  exact xt,
  intro hst, apply xs, 
  exact hst.1,
  intro hx,
  cases hx with xst xnt,
  cases xst,
  left,
  split, 
  exact xst,
  intro xt, 
  apply xnt,
  exact ⟨xst, xt⟩,
  right,
  split,
  exact xst,
  intro xs,
  apply xnt,
  exact ⟨xs, xst⟩,
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

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
begin
  intro n,
  simp,
  intro nprime,
  cases nat.prime.eq_two_or_odd nprime with h h,
  rw h, 
  intro, 
  linarith,
  rw nat.even_iff, 
  rw h,
  norm_num,
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
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  apply h₀ x, 
  apply ssubt xs,
  apply h₁ x, apply ssubt xs,
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ t, prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use x,
  use ssubt xs, 
  use prime_x,
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

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union_eq, mem_Inter],
  split,
  rintros (xs | xAi),
  intro i,
  right,
  exact xs,
  intro i,
  left,
  exact xAi i,
  intro h,
  by_cases hxs : x ∈ s,
  left,
  exact hxs,
  right,
  intro i,
  cases h i,
  assumption,
  contradiction,
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

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
begin
  sorry
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

