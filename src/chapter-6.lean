import tactic
import data.list
import data.real.basic 
import init.function
open function


-- constant mynat : Type (versus)

inductive mynat : Type
 | z : mynat 
 | s : mynat → mynat

#check mynat.s $ mynat.s mynat.z


/--
def exp1 (a : Type) (x : a) (n : ℕ) : a := x * (exp x (n - 1))

def exp2 {a : Type} [has_mul a] : a → ℕ → a  
 | x 0            := 1
 | x (nat.succ n) := x * exp1 x n
--/

def exp : ℕ → ℕ → ℕ   
 | x 0            := 1
 | x (nat.succ n) := x * exp x n


-- #print prefix exp

-- Exercicio A
-- https://leanprover-community.github.io/mathematics_in_lean/basics.html
example (x y z : ℕ) : (x + y) * z = (x * z) + (y * z) :=
begin
 ring,
end


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

section Fusion

def reverse { a : Type } : list a -> list a
| []      := []
| (x::xs) := (reverse xs) ++ [x]

def map {a b : Type} : (a → b) → list a → list b
| f [] := []
| f (x :: xs) := f x :: map f xs

def foldr {a b: Type} : (a → b → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := f x (foldr f e xs)

def foldl {a b: Type} : (b → a → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := foldl f (f e x) xs

def sum' : list ℕ → ℕ 
 | []        := 0
 | (x :: xs) := x + sum' xs 

def concat {a : Type} : list (list a) → list a 
 | []          := []
 | (xs :: xss) := xs ++ concat xss 

-- using foldr

def sum'' : list ℕ → ℕ  := foldr (+) 0
def map2 {a b :Type} (g : a → b) : list a → list b := foldr ((::) ∘ g) []

-- tests

#reduce concat [[1,2],[3,4],[5]]
#reduce sum'' [0,1,2,3]
#reduce foldr (λ x y, x + y) 0 [1,2,3]
#reduce map (λ x : ℕ, x + 1) [1,2,3]
#reduce reverse [1,2,3]


theorem sum'_eq_sum'' {xs : list ℕ} : sum' xs = sum'' xs := sorry

theorem sum_of_append {xs ys : list ℕ} : sum' (xs ++ ys) = sum' xs + sum' ys := sorry

theorem concat_of_apend { a : Type} {xss yss : list (list a)} : 
  concat (xss ++ yss) = concat xss ++ concat yss := sorry

theorem foldr_law {a b : Type} (f : a → b → b) (g : b → b → b) (e : b) (xs ys : list a) 
  (h1 : ∀ x, g e x = x) 
  (h2 : ∀ x y z, f x (g y z) = g (f x y) z) : 
  foldr f e (xs ++ ys) = g (foldr f e xs) (foldr f e ys) := sorry


theorem funsion_law {a b : Type} (f : a → b) (g : b → a → a) (h : b → b → b) 
  (xa : a) (xb : b)
  (h1 : f xa = xb) 
  (h2 : ∀ x y, f (g x y) = h x (f y)) : 
  f ∘ foldr g xa = foldr h xb := 
begin
 funext xs,
 induction xs with d hd, 
 rw foldr, rw comp, dsimp, rw foldr, exact h1, 
 sorry
end


lemma funsion1 {α β : Type} (a : α) 
 (f :  β → α → α) (h : α → α → α) (g : α → β) 
 (h1 : foldr f a [] = a)
 (h2 : ∀ x y, foldr f a (((::) ∘ g) x y) = h x (foldr f a y))
 : foldr f a ∘ map2 g = foldr h a := sorry


end Fusion



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

-- #print list.cons_append

-- Exercicio B

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


-- Exercicio C 

example {a b : Type} (f : a → b) [inhabited a] [inhabited b] : 
  list.head ∘ map f = f ∘ list.head :=
begin
 unfold comp,
 funext, 
 induction x with b bs hi, 
 rw list.head,
 rw map, rw list.head,
 sorry -- aparece que nao podemos provar sem saber mais sobre F
end

