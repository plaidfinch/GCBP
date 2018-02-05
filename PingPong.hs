{-# LANGUAGE TypeOperators #-}
type (+) = Either

pingpong :: (a + b -> a' + b') -> (b' -> b) -> (a -> a')
pingpong h ginv = untilLeft (h . Right . ginv) . h . Left

untilLeft :: (b' -> a' + b') -> (a' + b' -> a')
untilLeft step ab = case ab of
  Left  a' -> a'
  Right b' -> untilLeft step (step b')

untilLeft' :: (b' -> a' + b') -> (a' + b' -> a')
untilLeft' step = either id (untilLeft' step . step)
