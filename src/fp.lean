import tactic
import data.list
import data.real.basic 
import init.function
open function


def splitAt1 {a : Type} : ℕ → (list a) → (list a × list a)
 |              0 xs := ([], xs)
 |              _ [] := ([], [])
 | (n + 1) (x :: xs) := (x :: (splitAt1 n xs).1, (splitAt1 n xs).2)

def splitAt2 {a : Type} : ℕ → (list a) → (list a × list a) 
 |                   0 xs := ([], xs)
 |                   _ [] := ([], [])
 | (nat.succ n) (x :: xs) := let (ys,zs) := splitAt2 n xs in (x :: ys, zs)

#reduce splitAt2 2 [1,2,3,4]
#reduce splitAt1 2 [1,2,3,4]

example : splitAt1 2 [1,2,3,4] = ([1,2],[3,4]) :=
begin
  rw splitAt1,
  rw splitAt1, 
  rw splitAt1, -- como fazer passo-a-passo
end

example (a : Type) (n : ℕ) (xs : list a) :
 (λ x, (prod.fst x) ++ (prod.snd x) = xs) (splitAt1 n xs) :=
begin
  induction xs with d hd IH generalizing n,
  { induction n with m hm;
    simp [splitAt1], },
  { induction n with m hm,
    { simp [splitAt1], },
    { simp [splitAt1, IH, hm], } }
end

-- #print prefix splitAt1

example : splitAt2 2 [1,2,3,4] = ([1,2],[3,4]) := 
begin
 rw splitAt2, 
 rw splitAt2, 
 rw splitAt2,
 rw splitAt2._match_1,
 rw splitAt2._match_1,
end

  
example (a : Type) (n : ℕ) (xs : list a) : 
 (λ x, (prod.fst x) ++ (prod.snd x) == xs) (splitAt2 n xs) :=
begin
 induction xs with d hd ih generalizing n,
 induction n with m hm,
 simp [splitAt2],
 simp [splitAt2],
 
 induction n with m hm,
 simp [splitAt2],
 have h2 := ih m,
 simp [splitAt2, hm, h2, splitAt2._match_1], 
 sorry
end


def map {a b : Type} : (a → b) → list a → list b
| f [] := []
| f (x :: xs) := f x :: map f xs

def foldr {a b: Type} : (a → b → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := f x (foldr f e xs)

def reverse { a : Type } : list a -> list a
| []      := []
| (x::xs) := (reverse xs) ++ [x]

#reduce reverse [1,2,3]
#reduce foldr (λ x y, x + y) 0 [1,2,3]
#reduce map (λ x : ℕ, x + 1) [1,2,3]

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


#print prefix reverse
#print list.cons_append


-- page 112

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

theorem rev_rev_eq {a : Type } (xs : list a) : reverse (reverse xs) = xs :=
begin
 induction xs with b bs hi,
 simp [reverse,append],
 
 rw reverse,
 rw rev_aux,
 rw hi,
end

theorem rev_rev_id {a : Type } : (reverse ∘ reverse) = (id : list a → list a) :=
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
 
