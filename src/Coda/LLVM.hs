module Coda.LLVM (fun) where

import Data.Foldable (toList)
import Data.Traversable (mapAccumL)
import LLVM.AST as AST
import LLVM.IRBuilder as IR

-- | A slightly safer version of 'IR.function' using the encoding trick from the @ad@ package
fun
  :: (MonadModuleBuilder m, Traversable f)
  => Name  -- ^ Function name
  -> f (Type, ParameterName)  -- ^ Parameter types and name suggestions
  -> Type  -- ^ Return type
  -> (f Operand -> IRBuilderT m ())  -- ^ Function body builder
  -> m Operand
fun n as r f = IR.function n (toList as) r $ \xs -> f (zipWithT const xs as)

zipWithT :: (Foldable f, Traversable g) => (a -> b -> c) -> f a -> g b -> g c
zipWithT f as = snd . mapAccumL (\(a:as') b -> (as', f a b)) (toList as)
