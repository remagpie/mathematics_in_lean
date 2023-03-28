import data.real.basic

/- An example. -/

import data.real.basic
example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc b a c
end

/- Try these.-/

example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  rw mul_assoc b c a,
  rw mul_comm c a
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ← mul_assoc a b c,
  rw mul_comm a b,
  rw mul_assoc b a c
end

/- An example. -/

example (a b c : ℝ) : a * b * c = b * c * a :=
begin
  rw mul_assoc,
  rw mul_comm
end

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/

example (a b c : ℝ) : a * (b * c) = b * (c * a) :=
begin
  rw mul_comm,
  rw mul_assoc
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ← mul_assoc a b c,
  rw mul_comm a b,
  rw mul_assoc b a c
end

/- Using facts from the local context. -/

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
begin
  rw h',
  rw ←mul_assoc,
  rw h,
  rw mul_assoc
end

/- Try these. For the second one, use the theorem `sub_self`. -/

example (a b c d e f : ℝ) (h : b * c = e * f) :
  a * b * c * d = a * e * f * d :=
begin
  rw mul_assoc a,
  rw h,
  rw ← mul_assoc a
end

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  rw hyp,
  rw mul_comm b a,
  rw hyp',
  rw sub_self 
end

/- Examples. -/

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
by rw [h', ←mul_assoc, h, mul_assoc]

section

variables a b c d e f g : ℝ

example (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
by rw [h', ←mul_assoc, h, mul_assoc]

end

section
variables a b c : ℝ

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
#check @mul_comm

end

section
variables a b : ℝ

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin
  rw [mul_add, add_mul, add_mul],
  rw [←add_assoc, add_assoc (a * a)],
  rw [mul_comm b a, ←two_mul]
end

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
          by rw [mul_add, add_mul, add_mul]
  ... = a * a + (b * a + a * b) + b * b :
          by rw [←add_assoc, add_assoc (a * a)]
  ... = a * a + 2 * (a * b) + b * b     :
          by rw [mul_comm b a, ←two_mul]


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
    begin
      rw mul_add,
      rw add_mul,
      rw add_mul
    end
  ... = a * a + (b * a + a * b) + b * b : 
    begin 
      rw ←add_assoc,
      rw add_assoc (a * a)
    end
  ... = a * a + 2 * (a * b) + b * b     : 
    begin 
      rw mul_comm b a, 
      rw ←two_mul
    end
end

/- Try these. For the second, use the theorems listed underneath. -/

section
variables a b c d : ℝ

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d) 
    = a * c + a * d + b * c + b * d :
  begin
    rw mul_add,
    rw add_mul,
    rw add_mul,
    rw ← add_assoc,
    rw add_assoc (a * c),
    rw add_comm (b * c),
    rw ← add_assoc,
  end


example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
begin
  rw add_mul,
  rw mul_sub,
  rw mul_sub,
  rw mul_comm b,
  rw add_comm,
  rw ← add_sub_assoc,
  rw ← pow_two a,
  rw ← pow_two b,
  rw sub_add, 
  rw sub_sub,
  rw add_comm,
  rw ← sub_sub,
  rw ← sub_add,
  rw ← sub_mul,
  rw sub_self,
  rw zero_mul,
  rw add_comm,
  rw zero_sub,
  rw add_comm,
  rw neg_add_eq_sub, 
end

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

/- Examples. -/

section
variables a b c d : ℝ

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw hyp' at hyp,
  rw mul_comm d a at hyp,
  rw ← two_mul (a * d) at hyp,
  rw ← mul_assoc 2 a d at hyp,
  exact hyp
end

example : (c * b) * a = b * (a * c) :=
by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw [hyp, hyp'],
  ring
end

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c :=
begin
  nth_rewrite 1 h,
  rw add_mul
end

example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
  conv
  begin          -- | a * (b * c) = a * (c * b)
    to_lhs,      -- | a * (b * c)
    congr,       -- 2 goals : | a and | b * c
    skip,        -- | b * c
    rw mul_comm, -- | c * b
  end
end

example : (λ x : ℕ, 0 + x) = (λ x, x) :=
begin
  conv
  begin           -- | (λ (x : ℕ), 0 + x) = λ (x : ℕ), x
    to_lhs,       -- | λ (x : ℕ), 0 + x
    funext,       -- | 0 + x
    rw zero_add,  -- | x
  end
end

example : (λ x : ℕ, 0+x) = (λ x, x) :=
by funext ; rw zero_add 

example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
conv in (b*c)
begin          -- | b * c
  rw mul_comm, -- | c * b
end
end

example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
by conv in (b*c) { rw mul_comm }

example (a b c : ℕ) : a + (b * c) = a + (c * b) :=
by conv in (_ * c) { rw mul_comm }

example (a b c : ℕ) : (b * c) * (b * c) * (b * c) = (b * c) * (c * b)  * (c * b):=
by conv { for (b * c) [2, 3] { rw mul_comm } }
