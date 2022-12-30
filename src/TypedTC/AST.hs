module TypedTC.AST where

import TypedTC.Checker (UTerm (..), UType(..))
import TypedTC.Parser qualified as P
import Data.Text (Text)

type ASTResult a = Either Text a
type LambdaBindings = [P.Identifier]

ast :: P.Expr -> ASTResult UTerm
ast (P.LiteralBool b) = pure $ UBool b
ast (P.LiteralNat n) = pure $ UNat n
ast (P.Succ e) = USucc <$> ast e
ast (P.NatElim a b c) = UNatElim <$> ast a <*> ast b <*> ast c
ast (P.If cond true false) = UIf <$> ast cond <*> ast true <*> ast false
ast (P.App f arg) = UApp <$> ast f <*> ast arg
ast (P.Var (P.Identifier name)) = pure $ UVar name
ast (P.Lambda args body) = do
    body' <- ast body
    pure $ foldr go body' args
  where
    go (P.Identifier argName, argType) = ULambda argName (pType2UType argType)
      
pType2UType :: P.PType -> UType
pType2UType P.PBool = UTBool
pType2UType P.PNat = UTNat
pType2UType (P.PFun a b) = UTLambda (pType2UType a) (pType2UType b)

