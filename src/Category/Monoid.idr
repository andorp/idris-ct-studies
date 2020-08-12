module Category.Monoid

import Category.Definition
import Data.Nat
import Data.List

MONOID
  : {m : Type}
  -> (e : m)
  -> (a : m -> m -> m)
  -> ((x : m) -> a e x = x)
  -> ((x : m) -> a x e = x)
  -> ((x, y, z : m) -> x `a` (y `a` z) = (x `a` y) `a` z)
  -> Category
MONOID {m} e a l r c = MkCategory Unit (\_ , _ => m) e a l r c

FREE_MONOID : (e : Type) -> Category
FREE_MONOID e = MONOID {m=List e} [] (++) (\x => Refl {x=x}) appendNilRightNeutral appendAssociative

SUM_MONOID : Category
SUM_MONOID = MONOID {m=Nat} 0 (+) (\x => Refl) plusZeroRightNeutral plusAssociative

-- TODO: Improve the readability of the proof
freeToSumComp
   : (f : List Nat) -> (g : List Nat)
  -> sum (f ++ g) = (sum f + sum g)
freeToSumComp []        g = Refl
freeToSumComp (x :: xs) g with (freeToSumComp xs g)
  freeToSumComp (x :: xs) g | xsg
    = rewrite (sym (plusAssociative x (sum xs) (sum g)))           -- x + (sum (xs ++ g)) = (x + sum xs) + sum g
      in (plusConstantLeft (sum (xs ++ g)) (sum xs + sum g) x xsg) -- x + (sum (xs ++ g)) = x + (sum xs + sum g)

FREE_TO_SUM_FUNCTOR : Functor (FREE_MONOID Nat) SUM_MONOID
FREE_TO_SUM_FUNCTOR = MkFunctor id sum Refl freeToSumComp


