{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Port
  ( Port,
    encode,
    ($$),
    flow,
    proj1,
    proj2,
    pattern Tup,
    discard,
    (Port.>>),
  )
where

import Cartesian
import Control.Applicative
import Control.Arrow
import Control.Category
import Prelude hiding (fst, id, snd, (.))

newtype Port k r a = Port {unPort :: k r a}

instance Arrow k => Functor (Port k r) where
  fmap f (Port x) = Port (arr f . x)

instance Arrow k => Applicative (Port k r) where
  pure x = Port (arr (const x))
  Port f <*> Port x = Port (arr (uncurry ($)) . (f &&& x))

encode, ($$) :: Category k => k a b -> (Port k r a -> Port k r b)
encode f (Port x) = Port (f . x)
($$) = encode

infix 1 $$

flow, decode :: Category k => (forall r. Port k r a -> Port k r b) -> k a b
flow = decode
decode f = unPort (f (Port id))

pair :: Cartesian k => Port k r a -> Port k r b -> Port k r (a, b)
pair (Port x) (Port y) = Port (x &&&& y)

proj1 :: Cartesian k => Port k r (a, b) -> Port k r a
proj1 = encode fst

proj2 :: Cartesian k => Port k r (a, b) -> Port k r b
proj2 = encode snd

split :: Cartesian k => Port k r (a, b) -> (Port k r a, Port k r b)
split p = (proj1 p, proj2 p)

pattern Tup :: Cartesian k => Port k r a -> Port k r b -> Port k r (a, b)
pattern Tup x y <- (split -> (x, y))
  where
    Tup x y = pair x y

{-# COMPLETE Tup #-}

discard :: Cartesian k => Port k r a -> Port k r ()
discard = encode void

(>>) :: Cartesian k => Port k r a -> Port k r b -> Port k r b
x >> y = proj2 (pair x y)
