module Ext where
import Control.Monad.Reader
import Control.Applicative
import qualified Data.Map as Map

filterMaybe :: Maybe a -> (a -> Bool) -> Maybe a
filterMaybe Nothing _ = Nothing
filterMaybe (Just x) f = if f x then Just x else Nothing

localWithContext :: Monad m => (r -> (r, x)) -> (x -> ReaderT r m a) -> ReaderT r m a
localWithContext f k = ReaderT $ \r ->
  let (r', x) = f r
  in runReaderT (k x) r'


mapMWithKey :: Monad m => (k -> a -> m b) -> Map.Map k a -> m (Map.Map k b)
mapMWithKey f = unwrapMonad . Map.traverseWithKey (\k a -> WrapMonad (f k a))
