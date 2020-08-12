module Category.TTExample

import Category.Definition
import Category.Discrete
import Category.SET


public export
data TType
  = TInt
  | TDouble
  | TString
  | TList TType

public export
TDiscrete : Category
TDiscrete = DISCRETE TType

public export
iFObj : TType -> Type
iFObj TInt      = Int
iFObj TDouble   = Double
iFObj TString   = String
iFObj (TList t) = List (iFObj t)

public export
iFmap : s = t -> iFObj s -> iFObj t
iFmap Refl = id

public export
iLawComp : {x, y, z : TType} -> (f : x = y) -> (g : y = z) -> iFmap (discreteComp f g) = \x => (iFmap g (iFmap f x))
iLawComp Refl Refl = Refl

public export
ImplementationFunctor : Functor TDiscrete SET
ImplementationFunctor = MkFunctor
  iFObj
  iFmap
  Refl
  (\f , g => iLawComp f g)

