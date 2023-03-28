import data.real.basic

section
variables a b : ℝ

-- lt_irrefl states that no element can be less than itself.
-- lt_asymm is a lemma in Lean that states the asymmetry property of the "less than" relation for linear orders. In other words, it asserts that for any two elements a and b in a linear order, if a < b, then it is not the case that b < a.
example (h : a < b) : ¬ b < a :=
begin
  intro h',
  have : a < a,
    from lt_trans h h',
  apply lt_irrefl a this
end

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intros fnub,
  cases fnub with a fnuba,
  cases h a with x hx,
  have : f x ≤ a,
    from fnuba x,
  linarith
end

example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
begin
  intros fnlb,
  cases fnlb with a fnlba,
  cases h a with x hx,
  have : a ≤ f x,
    from fnlba x,
  linarith,
end

example : ¬ fn_has_ub (λ x, x) :=
begin
  intro fnub,
  cases fnub with a fnuba,
  have : a ≤ a,
    from fnuba a,
  have : a < a + 1,
    from lt_add_one a,
  have : a + 1 ≤ a,
    from fnuba (a + 1),
  linarith,
end


#check (not_le_of_gt : a > b → ¬ a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬ a < b)
#check (lt_of_not_ge : ¬ a ≥ b → a < b)
#check (le_of_not_gt : ¬ a > b → a ≤ b)


-- absurd is a tactic in Lean that is used to prove a goal when a contradiction is found.
-- by_contradiction is a tactic in Lean that is used to prove a goal by assuming its negation and then deriving a contradiction from that assumption.
-- contradiction is a tactic in Lean that is used to prove a goal when you have contradictory hypotheses in your context.
-- exfalso is a tactic in Lean that helps you prove a goal by showing that a contradiction exists in your current hypotheses. 

-- absurd requires you to provide the specific contradictory hypotheses as arguments.
-- contradiction automatically searches for contradictory pairs of hypotheses.
-- exfalso changes the goal to false, leaving you to find and prove the contradiction.

example (h : monotone f) (h' : f a < f b) : a < b :=
begin
  by_contradiction h_contra,
  have : b ≤ a, from le_of_not_gt h_contra,
  have : f b ≤ f a := h this,
  have : false := not_lt_of_ge this h',
  contradiction,
end


example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
begin
  intro h_mono,
  have : f a ≤ f b := h_mono h,
  have : false := not_le_of_gt h' this,
  contradiction,
end

example :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f,
  {  
    intros a b hab,
    exact le_refl 0,
  },
  have h' : f 1 ≤ f 0,
    from le_refl _,
  -- h가 ℝ -> ℝ -> Prop이므로, h'가 ℝ -> ℝ -> Prop이어야 함.
  have : (1 : ℝ) ≤ (0 : ℝ) := 
    h monof h',
  linarith,
end

-- specialize is a tactic in Lean that is used to apply a given hypothesis or function to specific arguments.
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 :=
begin
  apply le_of_not_gt,
  intro h',
  specialize h x h',
  linarith,
end

end

section
variables {α : Type*} (P : α → Prop) (Q : Prop)

-- The left and right angle brackets, which can be entered as \< and \> respectively, tell Lean to put together the given data using whatever construction is appropriate for the current goal.
example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
begin
  intros x h',
  have : ∃ x, P x := ⟨x, h'⟩,
  contradiction,
end

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
begin
  intro h',
  cases h' with x hx,
  have : ¬ P x := h x,
  contradiction,
end

-- push_neg : "pushes negations inwards" by applying De Morgan's laws and 
-- other logical equivalences to rewrite negations in a formula.
-- be used to simplify a logical statement by moving negations from 
-- the outside of the formula to the inside, or vice versa.
example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin
  push_neg at h,
  exact h,
end

example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
begin
  intro h',
  cases h with x hx,
  apply hx,
  apply h',
end

open_locale classical

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin
  by_contradiction h',
  apply h,
  intro x,
  show P x,
  by_contradiction h'',
  exact h' ⟨x, h''⟩
end

example (h : ¬ ¬ Q) : Q :=
begin
  by_contradiction h',
  contradiction,
end

example (h : Q) : ¬ ¬ Q :=
begin
  intro h',
  contradiction,
end

end

open_locale classical
section
variable (f : ℝ → ℝ)

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  intros a,
  by_contradiction hn,
  have h' : fn_has_ub f :=
  begin
    use a,
    intros x,
    by_contradiction hn',
    have : f x > a := lt_of_not_ge hn',
    exact hn ⟨x, this⟩,
  end,
  contradiction,
end

example (h : ¬ ∀ a, ∃ x, f x > a) : fn_has_ub f :=
begin
  push_neg at h,
  exact h
end

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  simp only [fn_has_ub, fn_ub] at h,
  push_neg at h,
  exact h
end

example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
begin
  rw [monotone] at h,
  push_neg at h,
  exact h
end

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  contrapose! h,
  exact h
end

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
begin
  contrapose! h,
  use x / 2,
  split; linarith
end

end

section
variable a : ℕ

example (h : 0 < 0) : a > 37 :=
begin
  exfalso,
  apply lt_irrefl 0 h
end

example (h : 0 < 0) : a > 37 :=
absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 :=
begin
  have h' : ¬ 0 < 0,
    from lt_irrefl 0,
  contradiction
end


end

