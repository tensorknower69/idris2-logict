module Control.Monad.Logic.Logic

import public Control.Monad.Logic.Interface
import Control.Monad.Identity
import Control.Monad.Trans

-- import Data.Colist
import Data.List.Lazy -- this has more functions than `Data/Colist.idr`

public export
record LogicT (m : Type -> Type) (a : Type) where
  constructor MkLogicT
  runLogicT : forall r. (cons : a -> m r -> m r) -> (nil : m r) -> m r

public export
Logic : (a : Type) -> Type
Logic = LogicT Identity

public export
runLogic : Logic a -> (a -> r -> r) -> r -> r
runLogic xz cons nil = runIdentity $ runLogic xz (map . cons) (Id nil)

||| possibly useless due to cases of infinite branching in underlying monads' unfavorable control flow
public export
observeT : Applicative m => LogicT m a -> m (LazyList a)
observeT xz = runLogicT xz (\x, xs => map (\xs_ => x :: xs_) xs) (pure [])

public export
observe : Logic a -> LazyList a
observe = runIdentity . observeT

public export
Functor (LogicT m) where
  map f xz = MkLogicT $ \cons, nil => runLogicT xz (\x, xs => cons (f x) xs) nil

public export
Applicative (LogicT m) where
  pure x = MkLogicT $ \cons, nil => cons x nil
  fz <*> xz = MkLogicT $ \cons, nil => runLogicT fz (\f, fs => runLogicT xz (\x, xs => cons (f x) xs) fs) nil

public export
Monad (LogicT m) where
  act >>= react = MkLogicT $ \cons, nil => runLogicT act (\r, rs => runLogicT (react r) cons rs) nil

public export
Alternative (LogicT m) where
  empty = MkLogicT $ \cons, nil => nil
  xz <|> yz = MkLogicT $ \cons, nil => runLogicT xz cons (runLogicT yz cons nil)

public export
MonadTrans LogicT where
  lift xz = MkLogicT $ \cons, nil => xz >>= \x => cons x nil

export
HasIO m => HasIO (LogicT m) where
  liftIO = lift . liftIO

public export
Monad m => MonadLogic (LogicT m) where
  split xz = lift $ runLogicT xz (\cons, nil => pure $ Just (cons, lift nil >>= reflect)) (pure Nothing)
