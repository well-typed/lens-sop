module Generics.SOP.Lens.Named (
    -- * Monomorphic total lens, abstracted over target
    LensName
  , NamedLens(..)
  , get
  , modify
  , set
    -- * Generic construction
  , gnamedLenses
  ) where

import Generics.SOP
import Generics.SOP.Lens (GLens)
import qualified Generics.SOP.Lens as GLens

{-------------------------------------------------------------------------------
  Wrapper around Data.Label
-------------------------------------------------------------------------------}

type LensName = String

-- | Total abstract lens
data NamedLens a ctxt = forall b. ctxt b => NamedLens {
    unNamedLens :: GLens I I a b
  }

instance Show (NamedLens a ctxt) where
  show _ = "<<NamedLens>"

get :: NamedLens a ctxt -> (forall b. ctxt b => b -> c) -> a -> c
get (NamedLens l) k = k . unI . GLens.get l

modify :: NamedLens a ctxt -> (forall b. ctxt b => b -> b) -> a -> a
modify (NamedLens l) f = unI . GLens.modify l (I . f)

set :: NamedLens a ctxt -> (forall b. ctxt b => b) -> a -> a
set (NamedLens l) b = unI . GLens.set l b

{-------------------------------------------------------------------------------
  Construct named lenses
-------------------------------------------------------------------------------}

-- | Construct named lenses for a record type
--
-- NOTE: This will throw a runtime error for non-record types
gnamedLenses :: forall a ctxt xs.
     (HasDatatypeInfo a, Code a ~ '[xs], All ctxt xs)
  => (DatatypeName -> ConstructorName -> LensName)
  -> [(String, NamedLens a ctxt)]
gnamedLenses mkName = case sList :: SList (Code a) of
    SCons -> zip (fieldNames mkName (datatypeInfo pa))
                 (hcollapse $ hcliftA pc (K . NamedLens) totalLenses)
  where
    totalLenses :: NP (GLens I I a) xs
    totalLenses = GLens.glenses

    pa :: Proxy a
    pa = Proxy

    pc :: Proxy ctxt
    pc = Proxy

fieldNames :: (DatatypeName -> FieldName -> LensName)
           -> DatatypeInfo '[xs] -> [String]
fieldNames mkName d =
  fieldNames' (mkName (datatypeName d)) (hd (constructorInfo d))

fieldNames' :: (FieldName -> LensName) -> ConstructorInfo xs -> [String]
fieldNames' _      (Constructor _)    = error "not a record type"
fieldNames' _      (Infix _ _ _)      = error "not a record type"
fieldNames' mkName (Record      _ fs) = hcollapse $ hliftA aux fs
  where
    aux :: FieldInfo a -> K String a
    aux (FieldInfo n) = K (mkName n)
