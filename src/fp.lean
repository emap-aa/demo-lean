import tactic
import data.list
import data.real.basic 
import init.function

open function


@[inline, reducible]
def splitAt {a : Type} : ℕ → (list a) → (list a × list a) 
 |                  0 xs  := ([], xs)
 |                   _ [] := ([], [])
 | (nat.succ n) (x :: xs) := let (ys,zs) := splitAt n xs in (x :: ys, zs)

#reduce splitAt 2 [1,2,3,4]


example : splitAt 2 [1,2,3,4] = ([1,2],[3,4]) := 
begin
 rw splitAt, 
 rw splitAt, 
 rw splitAt,
 rw splitAt._match_1,
 rw splitAt._match_1,
end
  
example (a : Type) (n : ℕ) (xs : list a) : 
 (λ x, (prod.fst x) ++ (prod.snd x) == xs) (splitAt n xs) :=
begin
 induction xs with d hd,
 sorry 
end


def map {a b : Type} : (a → b) → list a → list b
| f [] := []
| f (x :: xs) := f x :: map f xs

def foldr {a b: Type} : (a → b → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := f x (foldr f e xs)

#reduce foldr (λ x y, x + y) 0 [1,2,3]

#reduce map (λ x : ℕ, x + 1) [1,2,3]

example (a b c : Type) (f : b → c) (g : a → b) (xs : list a) : 
 (map f ∘ map g) xs = map (f ∘ g) xs :=
begin
 unfold comp,
 induction xs with xa xha xhi,
 repeat { rw map },

 simp, 
 rw ← xhi,
end

theorem map_distr_comp (a b c : Type) (f : b → c) (g : a → b) : 
 (map f ∘ map g) = map (f ∘ g) :=
begin
 unfold comp,
 funext,
 induction x with xa xha xhi,
 repeat { rw map },
 { simp, 
   rw ← xhi, },
end

#check map_distr_comp
