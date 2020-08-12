module Category.Discrete

import Category.Definition

public export
DiscreteMorphism : (x , y : a) -> Type
DiscreteMorphism x y = (x = y)

public export
discreteComp
  : {x , y , z : a} -> DiscreteMorphism x y -> DiscreteMorphism y z -> DiscreteMorphism x z
discreteComp Refl Refl = Refl

public export
discreteIdentity : {x : a} -> DiscreteMorphism x x
discreteIdentity = Refl

public export
discreteLawLeftId : {x , y : a} -> (f : DiscreteMorphism x y) -> discreteComp Refl f = f
discreteLawLeftId Refl = Refl

public export
discreteLawRightId : {x , y : a} -> (f : DiscreteMorphism x y) -> discreteComp f Refl = f
discreteLawRightId Refl = Refl

public export
discreteLawComp : {x , y , z , w : a}
  -> (f : DiscreteMorphism x y)
  -> (g : DiscreteMorphism y z)
  -> (h : DiscreteMorphism z w)
  -> f `discreteComp` (g `discreteComp` h) = (f `discreteComp` g) `discreteComp` h
discreteLawComp Refl Refl Refl = Refl

public export
DISCRETE : (a : Type) -> Category
DISCRETE a = MkCategory
  a
  DiscreteMorphism
  discreteIdentity
  discreteComp
  discreteLawLeftId
  discreteLawRightId
  discreteLawComp
