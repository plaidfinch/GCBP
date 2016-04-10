
gcbc :: (Either a c -> Either b c) -> a -> b
gcbc iso a = case iso (Left a) of
  Left b -> b
  Right c -> fixEither (iso . Right) c

fixEither :: (a -> Either b a) -> a -> b
fixEither f a0 =
  case f a0 of
    Left b -> b
    Right a -> fixEither f a

swapEither :: Either a b -> Either b a
swapEither = either Right Left
