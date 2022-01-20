module Control.Monad.Logic.Interface

infixl 1 >>-

||| inverse of `split`, i.e. `split xz >>= reflect = xz`
public export
reflect : Alternative m => Maybe (a, m a) -> m a
reflect Nothing = empty
reflect (Just (a, m)) = pure a <|> m

public export
interface (Monad m, Alternative m) => MonadLogic m where
  ||| basically `uncons`
  split : m a -> m (Maybe (a, m a))
  ||| fair disjunction, basically `(<|>)` but implemented in such a way to allow for infinite lists at the cost of sacrificing associativity
  interleave : m a -> Lazy (m a) -> m a
  ||| fair conjunction, basically `(>>=)` but implemented in such a way to allow for infinite lists at the cost of sacrificing distributivity, and do syntax
  (>>-) : m a -> (a -> m b) -> m b

  interleave xz yz = split xz >>= \case
    Nothing => yz
    Just (x, xs) => pure x <|> interleave yz xs

  xz >>- react = split xz >>= \case
    Nothing => empty
    Just (x, xs) => interleave (react x) (xs >>- react)
