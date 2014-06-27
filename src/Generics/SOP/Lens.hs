-- | Generalized lenses
--
-- Intended to be imported qualified
--
-- > import Generics.SOP.Lens as GLens
module Generics.SOP.Lens (
    -- * Generalized lenses
    GLens
  , lens
  , get
  , modify
  , set
    -- * Conversion
  , fromLens
  , fromIso
  , toLens
    -- * Generic computation of lenses for record type
  , glenses
    -- * Labels for the representation types
  , np
  , rep
  , sop
  , head
  , tail
  , i
  ) where

import Prelude hiding (id, (.), curry, uncurry, const, head, tail)
import Control.Arrow
import Control.Category
import Data.Label.Mono (Lens)
import Data.Label.Point (Iso(..))
import qualified Data.Label.Mono as Lens

import Generics.SOP

{-------------------------------------------------------------------------------
  Generalized lens using two categories
-------------------------------------------------------------------------------}

-- | GLens generalizes a monomorphic lens by allowing for different categories
-- for the getter and modifier
data GLens r w a b = GLens (r a b) (w (w b b, a) a)

instance (Category r, ArrowApply w) => Category (GLens r w) where
  id = GLens id app
  (GLens f m) . (GLens g n) = GLens (f . g) (uncurry (curry n . curry m))

lens :: r a b -> w (w b b, a) a -> GLens r w a b
lens = GLens

get :: GLens r w a b -> r a b
get (GLens f _) = f

modify :: GLens r w a b -> w (w b b, a) a
modify (GLens _ g) = g

set :: Arrow w => GLens r w a b -> w (b, a) a
set l = modify l . first (arr const)

{-------------------------------------------------------------------------------
  Conversion
-------------------------------------------------------------------------------}

fromLens :: (Arrow r, ArrowApply w) => Lens (->) a b -> GLens r w a b
fromLens l =
  GLens (arr (Lens.get l))
        (uncurry $ \h -> arr (Lens.set l) . (h . arr (Lens.get l) &&& id))

fromIso :: (Arrow r, ArrowApply w) => Iso (->) a b -> GLens r w a b
fromIso (Iso f g) = GLens (arr f) (uncurry $ \h -> arr g . h . arr f)

toLens :: GLens cat cat a b -> Lens cat a b
toLens (GLens f g) = Lens.lens f g

{-------------------------------------------------------------------------------
  Generic computation of all lenses for a record type
-------------------------------------------------------------------------------}

glenses :: forall r w a xs. (Generic a, Code a ~ '[xs], Arrow r, ArrowApply w) => NP (GLens r w a) xs
glenses = case sing :: Sing (Code a) of
            SCons -> hliftA (\l -> l . sop . rep) np

{-------------------------------------------------------------------------------
  Generalized lenses for representation types
-------------------------------------------------------------------------------}

np :: forall r w xs. (Arrow r, ArrowApply w, SingI xs) => NP (GLens r w (NP I xs)) xs
np = case sing :: Sing xs of
      SNil  -> Nil
      SCons -> i . head :* hliftA (. tail) np

rep :: (Arrow r, ArrowApply w, Generic a) => GLens r w a (Rep a)
rep = fromIso $ Iso from to

sop :: (Arrow r, ArrowApply w) => GLens r w (SOP f '[xs]) (NP f xs)
sop = fromIso $ Iso (\(SOP (Z x)) -> x) (SOP . Z)

head :: (Arrow r, ArrowApply w) => GLens r w (NP f (x ': xs)) (f x)
head = fromLens $ Lens.lens (\(x :* _) -> x) (\(f, x :* xs) -> (f x :* xs))

tail :: (Arrow r, ArrowApply w) => GLens r w (NP f (x ': xs)) (NP f xs)
tail = fromLens $ Lens.lens (\(_ :* xs) -> xs) (\(f, x :* xs) -> (x :* f xs))

i :: (Arrow r, ArrowApply w) => GLens r w (I a) a
i = fromIso $ Iso unI I

{-------------------------------------------------------------------------------
  Auxiliary
-------------------------------------------------------------------------------}

const :: Arrow arr => c -> arr b c
const a = arr (\_ -> a)

curry :: Arrow cat => cat (a, b) c -> (a -> cat b c)
curry m a = m . (const a &&& id)

uncurry :: ArrowApply cat => (a -> cat b c) -> cat (a, b) c
uncurry a = app . arr (first a)
