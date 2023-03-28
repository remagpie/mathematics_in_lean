import data.real.basic

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 5 / 2,
  norm_num
end

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
    by norm_num,
  exact ⟨5 / 2, h⟩
end

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5 / 2, by norm_num⟩

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a


theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

section
variables {f g : ℝ → ℝ}

-- The cases tactic in Lean is used to perform case analysis on inductive data types,
-- hypothesis, or goal. It is particularly useful when you want to analyze different cases
-- or constructors of an inductive data type in your proof. When using the cases tactic, 
-- Lean generates new subgoals for each constructor or case, 
-- allowing you to reason about them individually.
example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin
  cases ubf with a ubfa,
  cases ubg with b ubfb,
  use a + b,
  apply fn_ub_add ubfa ubfb
end

-- specialize로 x를 사용할 수 있네
-- The specialize tactic in Lean is used to instantiate a universally quantified hypothesis
-- or lemma with specific terms. It replaces a general statement with a more specific version,
-- which can be useful when you want to apply the statement to a particular case in your proof.
example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) :=
begin
  cases lbf with a hlf,
  cases lbg with b hlg,
  use a + b,
  intros x,
  specialize hlf x,
  specialize hlg x,
  have fg_sum_ge : f x + g x ≥ a + b,
  {
    apply add_le_add,
    exact hlf,
    exact hlg,
  },
  exact fg_sum_ge,
end

-- 요건 sepcialize 예제
example (h : ∀ x : ℕ, x > 0 → x + 1 > x) : 2 + 1 > 2 :=
begin
  specialize h 2,
  apply h,
  norm_num,
end

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
begin
  cases ubf with a ubfa,
  use c * a,
  intros x,
  specialize ubfa x,
  have cfa_ge : c * f x ≤ c * a,
  {
    apply mul_le_mul_of_nonneg_left,
    exact ubfa,
    exact h,
  },
  exact cfa_ge,
end

example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin
  rcases ubf with ⟨a, ubfa⟩,
  rcases ubg with ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩
end

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
begin
  rintros ⟨a, ubfa⟩ ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩
end

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
λ ⟨a, ubfa⟩ ⟨b, ubfb⟩, ⟨a + b, fn_ub_add ubfa ubfb⟩

end

section
variables {α : Type*} [comm_ring α]

def sum_of_squares (x : α) := ∃ a b, x = a^2 + b^2

theorem sum_of_squares_mul {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq⟩,
  rcases sosy with ⟨c, d, yeq⟩,
  rw [xeq, yeq],
  use [a*c - b*d, a*d + b*c],
  ring
end
theorem sum_of_squares_mul' {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, rfl⟩,
  rcases sosy with ⟨c, d, rfl⟩,
  use [a*c - b*d, a*d + b*c],
  ring
end

end
section
variables {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c :=
begin
  cases divab with d beq,
  cases divbc with e ceq,
  rw [ceq, beq],
  use (d * e), ring
end

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin 
  cases divab with d beq,
  cases divac with e ceq,
  rw [beq, ceq],
  use (d + e), ring,
end

end

section
open function

example {c : ℝ} : surjective (λ x, x + c) :=
begin
  intro x,
  use x - c,
  dsimp, ring
end

-- The field_simp tactic in Lean is used to simplify expressions involving fields, 
-- which are mathematical structures that have addition, subtraction, multiplication, and division operations.
example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro x,
  use x / c,
  dsimp, 
  field_simp [h],
  ring
end

example (x y : ℝ) (h : x - y ≠ 0) : (x^2 - y^2) / (x - y) = x + y :=
by { field_simp [h], ring }

example {f : ℝ → ℝ} (h : surjective f) : ∃ x, (f x)^2 = 4 :=
begin
  cases h 2 with x hx,
  use x,
  rw hx,
  norm_num
end

end

section
open function
variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
begin
  intro y,
  cases surjg y with b hb,
  cases surjf b with a ha,
  use a,
  dsimp,
  rw ha,
  exact hb,
end

end

