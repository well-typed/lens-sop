-- | Generalized lenses
--
-- Intended to be imported qualified
--
-- > import Generics.SOP.Lens as GLens
--
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

import Prelude hiding (id, (.), head, tail)

import Control.Category
import Control.Monad
import Data.Functor.Identity
import Data.Kind
import Generics.SOP
import Optics.Core (Optic', Is, A_Getter, A_Setter)

import qualified Optics.Core as Optics

{-------------------------------------------------------------------------------
  Generalized lens using two categories
-------------------------------------------------------------------------------}

-- | GLens generalizes a monomorphic lens by allowing for different monads
-- for the getter and modifier
data GLens (r :: Type -> Type) (w :: Type -> Type) a b =
    GLens (a -> r b) ((b -> w b) -> (a -> w a))

instance Monad r => Category (GLens r w) where
  id = GLens pure id
  (GLens f m) . (GLens g n) = GLens (f <=< g) (n . m)

lens :: (a -> r b) -> ((b -> w b) -> a -> w a) -> GLens r w a b
lens = GLens

get :: GLens r w a b -> a -> r b
get (GLens f _) = f

modify :: GLens r w a b -> (b -> w b) -> a -> w a
modify (GLens _ g) = g

set :: Monad w => GLens r w a b -> b -> a -> w a
set l = modify l . const . pure

{-------------------------------------------------------------------------------
  Conversion
-------------------------------------------------------------------------------}

fromOptics ::
     (Is k A_Getter, Is k A_Setter, Monad r, Monad w)
  => Optic' k is a b -> GLens r w a b
fromOptics l =
    GLens
      (return . Optics.view l)
      (\f a -> (\b -> Optics.set l b a) <$> f (Optics.view l a))

fromLens :: (Monad r, Monad w) => Optics.Lens' a b -> GLens r w a b
fromLens = fromOptics

fromIso :: (Monad r, Monad w) => Optics.Iso' a b -> GLens r w a b
fromIso = fromOptics

toLens :: GLens Identity Identity a b -> Optics.Lens' a b
toLens l = Optics.lens (runIdentity . get l) (\a b -> runIdentity $ set l b a)

{-------------------------------------------------------------------------------
  Generic computation of all lenses for a record type
-------------------------------------------------------------------------------}

glenses :: forall r w a xs.
     (Generic a, Code a ~ '[xs], Monad r, Monad w)
  => NP (GLens r w a) xs
glenses =
    case sList :: SList (Code a) of
      SCons -> hliftA (\l -> l . sop . rep) np

{-------------------------------------------------------------------------------
  Generalized lenses for representation types
-------------------------------------------------------------------------------}

np :: forall r w xs.
     (Monad r, Monad w, SListI xs)
  => NP (GLens r w (NP I xs)) xs
np = case sList :: SList xs of
      SNil  -> Nil
      SCons -> i . head :* hliftA (. tail) np

rep :: (Monad r, Monad w, Generic a) => GLens r w a (Rep a)
rep = fromIso $ Optics.iso from to

sop :: (Monad r, Monad w) => GLens r w (SOP f '[xs]) (NP f xs)
sop = fromIso $ Optics.iso (unZ . unSOP) (SOP . Z)

head :: (Monad r, Monad w) => GLens r w (NP f (x ': xs)) (f x)
head = fromLens $ Optics.lens (\(x :* _) -> x) (\(_ :* xs) x -> x :* xs)

tail :: (Monad r, Monad w) => GLens r w (NP f (x ': xs)) (NP f xs)
tail = fromLens $ Optics.lens (\(_ :* xs) -> xs) (\(x :* _) xs -> (x :* xs))

i :: (Monad r, Monad w) => GLens r w (I a) a
i = fromIso $ Optics.iso unI I
