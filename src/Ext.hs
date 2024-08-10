module Ext where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map

filterMaybe :: Maybe a -> (a -> Bool) -> Maybe a
filterMaybe Nothing _ = Nothing
filterMaybe (Just x) f =
    if f x
        then Just x
        else Nothing

localWithContext :: Monad m => (r -> (r, x)) -> (x -> ReaderT r m a) -> ReaderT r m a
localWithContext f k =
    ReaderT $ \r ->
        let (r', x) = f r
         in runReaderT (k x) r'

localStateWithContext :: Monad m => (r -> (r, x)) -> (x -> StateT r m a) -> StateT r m a
localStateWithContext f k =
    StateT $ \r ->
        let (r', x) = f r
         in runStateT (k x) r'

localState :: Monad m => (r -> r) -> StateT r m a -> StateT r m a
localState f k =
    StateT $ \r ->
        let r' = f r
         in runStateT k r'

mapMWithKey :: Monad m => (k -> a -> m b) -> Map.Map k a -> m (Map.Map k b)
mapMWithKey f = unwrapMonad . Map.traverseWithKey (\k a -> WrapMonad (f k a))

type GenIdState = State Int

incrSymCounter :: Monad m => (StateT Int m) Int
incrSymCounter = do
    i <- get
    put $ i + 1
    return i

splitRelation :: Ord a => [(a, (b, c))] -> (Map.Map a b, Map.Map a c)
splitRelation xs = (Map.fromList bs, Map.fromList cs)
  where
    bs = [(a, b) | (a, (b, _)) <- xs]
    cs = [(a, c) | (a, (_, c)) <- xs]
