-- TODO: Rename this to Fun
module Category.SET

import Category.Definition

extensionality : (f : a -> b) -> (g : a -> b) -> ((x : a) -> f x = g x) -> f = g
extensionality f g = believe_me $ Refl {x=f}

leftId : (f : a -> b) -> (Prelude.id . f = f)
leftId f = extensionality (Prelude.id . f) f (leftIdPoint f)
  where
    leftIdPoint : (f : a -> b) -> (x : a) -> Prelude.id (f x) = f x
    leftIdPoint f x = Refl

rightId : (f : a -> b) -> (f . Prelude.id = f)
rightId f = extensionality (f . Prelude.id) f (rightIdPoint f)
  where
    rightIdPoint : (f : a -> b) -> (x : a) -> f (Prelude.id x) = f x
    rightIdPoint f x = Refl

public export
SET : Category
SET = MkCategory
  Type
  (\a , b => a -> b)
  Prelude.id
  (flip (.))
  rightId
  leftId
  (\f , g , h => Refl)


