module Generics.SOP.Lens.Computed (
    -- * Abstract lenses
    AbstractLens(..)
  , abstractId
  , afterGLens
    -- * Getters and setters
  , get
  , set
  , modify
  , getM
  , setM
  , modifyM
    -- * Computing lenses
  , Path
  , CLens
  , lens
    -- * Manually constructing lenses
  , emptyPathOnly
    -- * Configuration
  , LensOptions(..)
  , defaultLensOptions
  ) where

import Prelude hiding (id, (.))

import Control.Category
import Control.Monad
import Data.Functor.Identity
import Data.Maybe (catMaybes)

import Generics.SOP
import Generics.SOP.Lens (GLens)

import qualified Generics.SOP.Lens as GLens

{-------------------------------------------------------------------------------
  Abstract lenses
-------------------------------------------------------------------------------}

-- | An abstract lens qualifies existentially over the target type of the lens
--
-- Sadly, abstract lenses do not form a category, so we provide special
-- identity and composition functions.
data AbstractLens r w c a =
  forall x. c x => AbstractLens (GLens r w a x)

-- | Identity abstract lens
abstractId :: (Monad r, c a) => AbstractLens r w c a
abstractId = AbstractLens id

-- | Compose with a pointwise lens on the right
afterGLens ::
     Monad r
  => AbstractLens r w c   a -- ^ @a -> x@
  -> GLens        r w   b a -- ^ @b -> a@
  -> AbstractLens r w c b   -- ^ @b -> x@
afterGLens (AbstractLens l) l' = AbstractLens (l . l')

{-------------------------------------------------------------------------------
  Getters and setters (mostly just for convenience)
-------------------------------------------------------------------------------}

-- | Getter for computed lenses
--
-- > get l == runIdentity . getM l . Identity
get :: AbstractLens r w c a -> (forall x. c x => (a -> r x) -> b) -> b
get l f = runIdentity $ getM l (Identity . f)

-- | Setter for computed lenses
--
-- > set l == runIdentity . setM l . Identity
set :: Monad w => AbstractLens r w c a -> (forall x. c x => x) -> a -> w a
set l x = runIdentity $ setM l (Identity x)

-- | Modifier for computed lenses
modify :: AbstractLens r w c a -> (forall x. c x => x -> w x) -> a -> w a
modify l f = runIdentity $ modifyM l (Identity f)

-- | Getter with possibility for "compile time" failure
getM :: AbstractLens r w c a
     -> (forall x. c x => (a -> r x) -> m b)
     -> m b
getM (AbstractLens l) k = k (GLens.get l)

-- | Setter with possibility for "compile time" failure
setM ::
     (Monad w, Functor m)
  => AbstractLens r w c a
  -> (forall x. c x => m x)
  -> m (a -> w a)
setM (AbstractLens l) x = fmap (GLens.set l) x

-- | Modifier with possibility for "compile time" failure
modifyM ::
     Functor m
  => AbstractLens r w c a
  -> (forall x. c x => m (x -> w x))
  -> m (a -> w a)
modifyM (AbstractLens l) f = fmap (GLens.modify l) f

{-------------------------------------------------------------------------------
  Paths
-------------------------------------------------------------------------------}

-- | A path is a series of field names. For instance, given
--
-- > data T1 = T1 { a :: Int, b :: Int } deriving Generic
-- > data T2 = T2 { c :: T1,  d :: Int } deriving Generic
--
-- valid paths on T2 are
--
-- > []
-- > ["c"]
-- > ["d"]
-- > ["c", "a"]
-- > ["c", "b"]
type Path = [String]

{-------------------------------------------------------------------------------
  Top-level generic function
-------------------------------------------------------------------------------}

-- | Compute a lens for a given type and path
--
-- The @Either@ is used to indicate "compile time" failure of the computation
-- of the lens (for instance, when this path is invalid for this data type).
--
-- Some lenses may of course be themselves effectful, depending on the category.
-- However, the lenses returned by the generic computation are pure and total
-- (as is evident from the type of glens).
class CLens r w c a where
  lens :: LensOptions -> Path -> Either String (AbstractLens r w c a)

  default lens :: ( HasDatatypeInfo a
                  , Monad r
                  , Monad w
                  , c a
                  , Code a ~ '[xs]
                  , All (CLens r w c) xs
                  )
               => LensOptions -> Path -> Either String (AbstractLens r w c a)
  lens = glens

{-------------------------------------------------------------------------------
  Instances

  We don't provide any instances here, because applications might want to
  implement special kinds of semantics for certain paths for types that we
  normally cannot "look into".
-------------------------------------------------------------------------------}

-- | A lens for abstract types (supports empty paths only)
--
-- Useful for defining CLens instances for types such as Int, Bool,
-- Text, etc.
--
-- > instance CLens c Int where lens = emptyPathOnly
emptyPathOnly ::
     (Monad r, c a)
  => LensOptions -> Path -> Either String (AbstractLens r w c a)
emptyPathOnly _ [] = Right $ abstractId
emptyPathOnly _ _  = Left "Trying to look inside abstract type"

{-------------------------------------------------------------------------------
  Lens options
-------------------------------------------------------------------------------}

data LensOptions = LensOptions {
    -- | Match a selector against a path component
    lensOptionsMatch :: DatatypeName -> FieldName -> String -> Bool
  }

-- | Default match just compares field names
defaultLensOptions :: LensOptions
defaultLensOptions = LensOptions {
    lensOptionsMatch = const (==)
  }

{-------------------------------------------------------------------------------
  The actual generic function
-------------------------------------------------------------------------------}

glens :: forall r w a c xs.
         ( Monad r
         , Monad w
         , HasDatatypeInfo a
         , c a
         , Code a ~ '[xs]
         , All (CLens r w c) xs
         )
      => LensOptions -> Path -> Either String (AbstractLens r w c a)
glens _    []     = Right $ abstractId
glens opts (p:ps) = liftM (`afterGLens` (GLens.sop . GLens.rep))
                         . glens' opts p ps
                         $ datatypeInfo (Proxy :: Proxy a)

glens' :: ( Monad r
          , Monad w
          , All (CLens r w c) xs
          )
       => LensOptions -> String -> Path
       -> DatatypeInfo '[xs]
       -> Either String (AbstractLens r w c (NP I xs))
glens' opts p ps d =
  glens'' opts ps (datatypeName d) p (hd (constructorInfo d))

glens'' :: forall r w c xs.
           ( Monad r
           , Monad w
           , All (CLens r w c) xs
           )
        => LensOptions -> Path
        -> DatatypeName -> String
        -> ConstructorInfo xs
        -> Either String (AbstractLens r w c (NP I xs))
glens'' _ _ _ _ (Constructor _) =
    Left $ "Cannot compute lenses for non-record types"
glens'' _ _ _ _ (Infix _ _ _) =
    Left $ "Cannot compute lenses for non-record types"
glens'' opts ps d p (Record _ fs) =
    case matchingLenses of
      []  -> Left $ "Unknown field " ++ show p ++ " of datatype " ++ show d
      [l] -> l
      _   -> Left $ "Invalid metadata for datatype " ++ show d
  where
    matchingLenses :: [Either String (AbstractLens r w c (NP I xs))]
    matchingLenses = catMaybes . hcollapse $ hcliftA2 pl aux fs GLens.np

    aux :: forall a. CLens r w c a
        => FieldInfo a
        -> GLens r w (NP I xs) a
        -> K (Maybe (Either String (AbstractLens r w c (NP I xs)))) a
    aux (FieldInfo f) l = K $
      if lensOptionsMatch opts d f p
        then Just $ ((`afterGLens` l) `liftM` lens opts ps)
        else Nothing

    pl :: Proxy (CLens r w c)
    pl = Proxy
