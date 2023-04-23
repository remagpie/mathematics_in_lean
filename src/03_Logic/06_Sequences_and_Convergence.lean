import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
by { ext, ring }

example (a b : ℝ) : abs a = abs (a - b + b) :=
by  { congr, ring }

example {a : ℝ} (h : 1 < a) : a < a * a :=
begin
  convert (mul_lt_mul_right _).2 h,
  { rw [one_mul] },
  exact lt_trans zero_lt_one h
end

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin
  intros ε εpos,
  use 0,
  intros n nge, dsimp,
  rw [sub_self, abs_zero],
  apply εpos
end

theorem converges_to_add {s t : ℕ → ℝ} {a b : ℝ}
  (cs : converges_to s a) (ct : converges_to t b):
converges_to (λ n, s n + t n) (a + b) :=
begin
  intros ε εpos, dsimp,
  have ε2pos : 0 < ε / 2,
  { linarith },
  cases cs (ε / 2) ε2pos with Ns hs,
  cases ct (ε / 2) ε2pos with Nt ht,
  use max Ns Nt,
  intros n ns_nt_le,
  have sna: |s n - a| < ε / 2, {
    convert hs n _,
    apply le_of_max_le_left ns_nt_le,
  },
  have tnb: |t n - b| < ε / 2, {
    convert ht n _,
    apply le_of_max_le_right ns_nt_le,
  },
  have h: |s n + t n - (a + b)| <= |s n - a| + |t n - b|, {
    rw add_sub_add_comm,
    apply abs_add,
  },
  have h': |s n - a| + |t n - b| < ε, {
    rw <-half_add_self ε,
    rw add_div,
    apply add_lt_add,
    apply sna,
    apply tnb,
  },
  cases lt_or_eq_of_le h with hlt heq,
  { apply lt_trans hlt h' },
  rw heq,
  apply h',
end

theorem converges_to_mul_const {s : ℕ → ℝ} {a : ℝ}
    (c : ℝ) (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    { ext, rw [h, zero_mul] },
    rw [h, zero_mul] },
  have acpos : 0 < abs c,
    from abs_pos.mpr h,
  intros ε εpos,
  have c_εpos: ε / |c| > 0, from div_pos εpos acpos,
  dsimp,
  cases cs (ε / |c|) c_εpos with N h',
  use N,
  intros n nge,
  rw <-mul_sub,
  rw abs_mul,
  rw mul_comm,
  apply (lt_div_iff acpos).mp,
  exact (h' n nge),
end

theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, abs a + 1],
  intros n nge,
  have g: |s n| <= |s n - a| + |a|, calc
    |s n| = |(s n - a) + a| : by ring
    ... <= |s n - a| + |a| : by apply abs_add,
  have g': |s n - a| + |a| < |a| + 1, {
    nth_rewrite 1 add_comm,
    apply (add_lt_add_iff_right (|a|)).mpr,
    exact h n nge,
  },
  apply lt_of_le_of_lt g g',
end

lemma aux {s t : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) (ct : converges_to t 0) :
  converges_to (λ n, s n * t n) 0 :=
begin
  intros ε εpos, dsimp,
  rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩,
  have Bpos : 0 < B,
    from lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _)),
  have pos₀ : ε / B > 0,
    from div_pos εpos Bpos,
  cases ct _ pos₀ with N₁ h₁,
  use max N₀ N₁,
  intros n NNle,
  rw sub_zero,
  rw abs_mul,
  rw <-div_mul_cancel ε (ne_of_gt Bpos),
  rw mul_comm,
  let sn_lt := h₀ n (max_le_iff.mp NNle).left,
  let tn_lt := h₁ n (max_le_iff.mp NNle).right,
  rw sub_zero at tn_lt,
  apply mul_lt_mul'' tn_lt sn_lt,
  apply abs_nonneg,
  apply abs_nonneg,
end

theorem converges_to_mul {s t : ℕ → ℝ} {a b : ℝ}
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n * t n) (a * b) :=
begin
  have h₁ : converges_to (λ n, s n * (t n - b)) 0,
  { apply aux cs,
    convert converges_to_add ct (converges_to_const (-b)),
    ring },
  convert (converges_to_add h₁ (converges_to_mul_const b cs)),
  { ext, ring },
  ring
end

theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : converges_to s a) (sb : converges_to s b) :
  a = b :=
begin
  by_contradiction abne,
  have : abs (a - b) > 0, {
    refine abs_pos.mpr _, -- ???
    -- apply abs_pos.mpr,
    contrapose! abne,
    linarith,
  },
  let ε := abs (a - b) / 2,
  have εpos : ε > 0,
  { change abs (a - b) / 2 > 0, linarith },
  cases sa ε εpos with Na hNa,
  cases sb ε εpos with Nb hNb,
  let N := max Na Nb,
  have absa : abs (s N - a) < ε, {
    apply hNa N (le_max_left Na Nb),
  },
  have absb : abs (s N - b) < ε, {
    apply hNb N (le_max_right Na Nb),
  },
  have : abs (a - b) < abs (a - b), calc
    |a - b| = |(s N - b) - (s N - a)| : by ring
    ...     <= |s N - b| + |s N - a|  : by apply abs_sub
    ...     < ε + ε                   : by apply add_lt_add absb absa
    ...     = |a - b|                 : add_halves (|a - b|),
  exact lt_irrefl _ this
end

section
variables {α : Type*} [linear_order α]

def converges_to' (s : α → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

end
