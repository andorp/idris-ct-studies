module Category.Definition

public export
record Category where
  constructor MkCategory
  Obj : Type
  Arr : Obj -> Obj -> Type -- TODO: Rename this to Hom

  id   : {T : Obj} -> (Arr T T)
  comp : {R , S , T : Obj} -> (Arr R S) -> (Arr S T) -> (Arr R T)

  lawLeftId    : {S , T : Obj} -> (f : Arr S T) -> (id `comp` f) = f
  lawRightId   : {S , T : Obj} -> (f : Arr S T) -> (f `comp` id) = f
  lawCompAssoc
    : {Q , R , S , T : Obj}
    -> (f : Arr Q R) -> (g : Arr R S) -> (h : Arr S T)
    -> (f `comp` (g `comp` h)) = ((f `comp` g) `comp` h)

public export
record Functor (C : Category) (D : Category) where
  constructor MkFunctor
  FObj : Obj C -> Obj D
  Fmap : {S , T : Obj C} -> Arr C S T -> Arr D (FObj S) (FObj T)

  lawFmapId : {X : Obj C} -> (Fmap {S=X} {T=X} (id C {T=X})) = (id D {T=(FObj X)})
  lawFmapComposition
    : {X , Y , Z : Obj C}
    -> (f : Arr C X Y) -> (g : Arr C Y Z)
    -> Fmap {S=X} {T=Z} (comp C {R=X} {S=Y} {T=Z} f g)
       = comp D {R=FObj X} {S=FObj Y} {T=FObj Z} (Fmap {S=X} {T=Y} f) (Fmap {S=Y} {T=Z} g)

public export
record NatTrans {C , D : Category} (F , G : Functor C D) where
  constructor MkNatTrans
  eta : {O : Obj C} -> Arr D (FObj F O) (FObj G O)

  lawNaturality
    : {X , Y : Obj C}
    -> (f : Arr C X Y)  
    -> comp D {R=FObj F X} {S=FObj F Y} {T=FObj G Y} (Fmap F {S=X} {T=Y} f) (eta {O=Y})
     = comp D {R=FObj F X} {S=FObj G X} {T=FObj G Y} (eta {O=X}) (Fmap G {S=X} {T=Y} f)

public export
record Isomorphism {C : Category} {A , B : Obj C} (f : Arr C A B) where
  constructor MkIsomorphism
  inverse : Arr C B A
  lawLeft  : comp C {R=A} {S=B} {T=A} f inverse = id C {T=A}
  lawRight : comp C {R=B} {S=A} {T=B} inverse f = id C {T=B}

public export
record NatIso {C , D : Category} (F , G : Functor C D) where
  constructor MkNatIso
  eta    : {O : Obj C} -> Arr D (FObj F O) (FObj G O)
  etaInv : {O : Obj C} -> Isomorphism {C=D} {A=FObj F O} {B=FObj G O} (eta {O=O})

  lawNaturality
    : {X, Y : Obj C}
    -> (f : Arr C X Y)
    -> comp D {R=FObj F X} {S=FObj F Y} {T=FObj G Y} (Fmap F {S=X} {T=Y} f) (eta {O=Y})
     = comp D {R=FObj F X} {S=FObj G X} {T=FObj G Y} (eta {O=X}) (Fmap G {S=X} {T=Y} f)



{-
Hom set
Adjunction
Yoneda embedding
Yoneda lemma
-}

