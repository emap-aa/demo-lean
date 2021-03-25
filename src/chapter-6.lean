import tactic
import data.list
import data.real.basic 
import init.function
open function

-- def exp (a : Type) (x : a) (n : ℕ) : a := x * (exp x (n - 1))

-- def exp1 {a : Type} [has_mul a] : a → ℕ → a  
--  | x 0            := 1
--  | x (nat.succ n) := x * exp1 x n

def exp : ℕ → ℕ → ℕ   
 | x 0            := 1
 | x (nat.succ n) := x * exp x n


example {x m n : ℕ} : exp x (m + n) = exp x m * exp x n := 
begin
 induction m with a ha,
 -- coluna 1
 rw zero_add,
 -- coluna 2
 rw exp,
 rw one_mul,
 -- norm_num,

 -- coluna 1
 rw nat.succ_add,
 rw exp, rw ha,

 -- coluna 2
 rw exp,
 rw mul_assoc,
end


example {a : Type} {xs ys zs : list a} : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
begin
 induction xs with b hb,
 apply list.append.equations._eqn_1,
 
 sorry
end


-- page 112

def reverse { a : Type } : list a -> list a
| []      := []
| (x::xs) := (reverse xs) ++ [x]

def map {a b : Type} : (a → b) → list a → list b
| f [] := []
| f (x :: xs) := f x :: map f xs

def foldr {a b: Type} : (a → b → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := f x (foldr f e xs)

#reduce foldr (λ x y, x + y) 0 [1,2,3]
#reduce map (λ x : ℕ, x + 1) [1,2,3]
#reduce reverse [1,2,3]

theorem map_distr_comp₁ (a b c : Type) (f : b → c) (g : a → b) (xs : list a) : 
 (map f ∘ map g) xs = map (f ∘ g) xs :=
begin
 unfold comp,
 induction xs with xa xha xhi,
 repeat { rw map },
 simp, 
 rw ← xhi,
end

theorem map_distr_comp₂ (a b c : Type) (f : b → c) (g : a → b) : 
 (map f ∘ map g) = map (f ∘ g) :=
begin
 unfold comp,
 funext,
 induction x with xa xha xhi,
 repeat { rw map },
 { simp, 
   rw ← xhi, },
end

#print list.cons_append


lemma rev_aux {a : Type } (x : a) (ys : list a) : reverse (ys ++ [x]) = x :: reverse ys :=
begin
 induction ys with b bs hi,
 simp [reverse, append],

 rw list.cons_append,
 rw reverse, 
 rw hi,
 rw reverse.equations._eqn_2, 
 rw list.cons_append,
end


theorem rev_rev_eq {a : Type} (xs : list a) : reverse (reverse xs) = xs :=
begin
 induction xs with b bs hi,
 simp [reverse,append],
 
 rw reverse,
 rw rev_aux,
 rw hi,
end


theorem rev_rev_id {a : Type} : (reverse ∘ reverse) = (id : list a → list a) :=
begin
 unfold comp, 
 funext,
 induction x with b bs hi,

 simp [reverse,append],
 
 rw reverse,
 rw rev_aux,
 rw hi, 
 unfold id, -- or simp
end
 
