{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module TypedTC.Checker where

import Data.Data (Proxy (..))
import Data.HList (
    HList (..),
    HLookupByHNat (..),
    HNat (..),
    hLookupByHNat,
    hSucc,
    (.*.),
 )
import Data.Kind (Type)
import Data.Text (Text)
import Data.Type.Equality (type (:~:) (Refl))
import Numeric.Natural (Natural)

type UTerm :: Type
data UTerm
    = UBool Bool
    | UNat Natural
    | USucc UTerm
    | UNatElim UTerm UTerm UTerm
    | UVar Text
    | ULambda Text UType UTerm
    | UApp UTerm UTerm
    | UIf UTerm UTerm UTerm
    deriving (Eq, Show)

data UType
    = UTBool
    | UTNat
    | UTLambda UType UType
    deriving (Eq, Ord, Show)

data TY a where
    TYBool :: TY Bool
    TYNat :: TY Natural
    TYLambda :: TY a -> TY b -> TY (a -> b)

tyEq :: TY a -> TY b -> Bool
TYBool `tyEq` TYBool = True
TYNat `tyEq` TYNat = True
TYLambda a b `tyEq` TYLambda a' b' = a `tyEq` a' && b `tyEq` b'
_ `tyEq` _ = False

instance Eq (TY a) where
    (==) = tyEq

instance Show (TY a) where
    show :: TY a -> String
    show TYBool = "Bool"
    show TYNat = "Nat"
    show (TYLambda a b) = show a <> " -> " <> show b

type Term :: [Type] -> Type -> Type
data Term env ty where
    TBool :: Bool -> Term env Bool
    TIf :: Term env Bool -> Term env a -> Term env a -> Term env a
    TNat :: Natural -> Term env Natural
    TSucc :: Term env Natural -> Term env Natural
    TNatElim :: Term env a -> Term env (Natural -> a -> a) -> Term env Natural -> Term env a
    TLambda :: TY a -> Term (a : env) b -> Term env (a -> b)
    TVar :: forall (n :: HNat) (env :: [Type]). HLookupByHNat n env => Proxy n -> Term env (HLookupByHNatR n env)
    TApp :: Term env (a -> b) -> Term env a -> Term env b

data Typed ts where
    Typed :: (TY t) -> (Term ts t) -> Typed ts

data SomeType where
    SomeType :: TY t -> SomeType

utype2ty :: UType -> SomeType
utype2ty UTBool = SomeType TYBool
utype2ty UTNat = SomeType TYNat
utype2ty (UTLambda a b) =
    case (utype2ty a, utype2ty b) of
        (SomeType a', SomeType b') -> SomeType (TYLambda a' b')

data TypeContext ts where
    EmptyTC :: TypeContext '[]
    AddType :: TY t -> Text -> TypeContext ts -> TypeContext (t ': ts)

data TCIndex ts where
    TCIndex :: HLookupByHNat n ts => Proxy n -> TY (HLookupByHNatR n ts) -> TCIndex ts

tcLookup :: TypeContext ts -> Text -> Either Text (TCIndex ts)
tcLookup EmptyTC varName = Left $ "Name not found: " <> varName
tcLookup (AddType ty var more) varName
    | var == varName = Right (TCIndex (Proxy @'HZero) ty)
    | otherwise = do
        recur <- tcLookup more varName
        case recur of
            TCIndex n ty' -> Right $ TCIndex (hSucc n) ty'

index2var :: TCIndex ts -> Typed ts
index2var (TCIndex n ty) = Typed ty (TVar n)

withType :: TypeContext ts -> UTerm -> (forall t. (TY t, Term ts t) -> Either Text a) -> Either Text a
withType ctx uterm f = do
    typed <- typeCheck ctx uterm
    case typed of
        Typed ty term -> f (ty, term)

expectType :: Typed ts -> TY t -> Text -> Either Text (Term ts t)
expectType typed ty err =
    case typed of
        Typed ty' term ->
            case sameType ty' ty of
                Just Refl -> pure term
                Nothing -> Left err

typeCheckTo :: TypeContext ts -> UTerm -> TY t -> Text -> Either Text (Term ts t)
typeCheckTo ctx uterm ty err =
    typeCheck ctx uterm >>= \term -> expectType term ty err

typeCheck :: TypeContext ts -> UTerm -> Either Text (Typed ts)
typeCheck ctx (UVar varName) = index2var <$> tcLookup ctx varName
typeCheck ctx (ULambda argName argType body) =
    case utype2ty argType of
        SomeType argType' -> do
            withType (AddType argType' argName ctx) body $ \case
                (bodyTy, bodyTerm) ->
                    pure $ Typed (TYLambda argType' bodyTy) (TLambda argType' bodyTerm)
typeCheck _ (UBool b) = pure $ Typed TYBool (TBool b)
typeCheck _ (UNat n) = pure $ Typed TYNat (TNat n)
typeCheck ctx (UIf cond true false) = do
    condTerm <- typeCheckTo ctx cond TYBool "Invalid If condition type"
    withType ctx true $ \case
        (tt, trueTerm) -> do
            falseTerm <- typeCheckTo ctx false tt "Branches of an if must be of the same type"
            pure $ Typed tt (TIf condTerm trueTerm falseTerm)
typeCheck ctx (USucc n) = do
    nTerm <- typeCheckTo ctx n TYNat "Succ argument must have type Nat"
    pure $ Typed TYNat (TSucc nTerm)
typeCheck ctx (UNatElim z suc n) = do
    z' <- typeCheck ctx z
    case z' of
        Typed resTy zTerm -> do
            suc' <- typeCheck ctx suc
            case suc' of
                Typed (TYLambda TYNat (TYLambda resTy' resTy'')) succTerm ->
                    case sameType resTy' resTy'' of
                        Just Refl -> do
                            case sameType resTy'' resTy of
                                Just Refl -> do
                                    nTerm <- typeCheckTo ctx n TYNat "UNatElim's third argument must be a Nat"
                                    pure $ Typed resTy (TNatElim zTerm succTerm nTerm)
                                Nothing -> Left "UNatElim second argument must return the same type as first argument"
                        Nothing -> Left "UNatElim's second agument must be: a -> a"
                _ -> Left "UnatElim's second argument must be a function"
typeCheck ctx (UApp f arg) = do
    f' <- typeCheck ctx f
    case f' of
        Typed (TYLambda a b) fTerm -> do
            argTerm <- typeCheckTo ctx arg a "Wrong argument type for lambda"
            pure $ Typed b (TApp fTerm argTerm)
        _ -> Left "Application of a non lambda term"

sameType :: TY t1 -> TY t2 -> Maybe (t1 :~: t2)
sameType TYBool TYBool = Just Refl
sameType TYNat TYNat = Just Refl
sameType (TYLambda a b) (TYLambda c d) = do
    Refl <- sameType a c
    Refl <- sameType b d
    pure Refl
sameType _ _ = Nothing

-- shouldntCompile = TLambda TYBool (TIf (TVar (Proxy @('HSucc 'HZero))) (TBool False) (TBool True))
-- shouldCompile   = TLambda TYBool (TIf (TVar (Proxy @'HZero         )) (TBool False) (TBool True))

eval :: HList env -> Term env a -> a
eval _ (TBool b) = b
eval e (TIf cond true false) = if eval e cond then eval e true else eval e false
eval _ (TNat n) = n
eval e (TSucc n) = succ (eval e n)
eval e (TNatElim z suc n) =
    let z' = eval e z
        suc' = eval e suc
        n' = eval e n
     in case n' of
            0 -> z'
            sucm -> suc' sucm (eval e (TNatElim z suc (TNat (sucm - 1))))
eval e (TApp f arg) = eval e f (eval e arg)
eval e (TLambda _ term) = \x -> eval (x .*. e) term
eval e (TVar n) = hLookupByHNat n e

eval' :: Term '[] a -> a
eval' = eval HNil

data UTermFold a = UTermFold
    { fBool :: Bool -> a
    , fNat :: Natural -> a
    , fSucc :: a -> a
    , fVar :: Text -> a
    , fIf :: a -> a -> a -> a
    , fApp :: a -> a -> a
    , fLambda :: Text -> UType -> a -> a
    , fNatElim :: a -> a -> a -> a
    }

foldUTerm :: UTermFold a -> UTerm -> a
foldUTerm f (UBool a) = fBool f a
foldUTerm f (UNat a) = fNat f a
foldUTerm f (USucc a) = fSucc f (foldUTerm f a)
foldUTerm f (UVar a) = fVar f a
foldUTerm f (UIf a b c) = fIf f (foldUTerm f a) (foldUTerm f b) (foldUTerm f c)
foldUTerm f (UApp a b) = fApp f (foldUTerm f a) (foldUTerm f b)
foldUTerm f (ULambda a b c) = fLambda f a b (foldUTerm f c)
foldUTerm f (UNatElim a b c) = fNatElim f (foldUTerm f a) (foldUTerm f b) (foldUTerm f c)
