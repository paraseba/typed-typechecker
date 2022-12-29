{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module TypedTC.Checker where

import Data.Data (Proxy (..))
import Data.HList (HList (..), HLookupByHNat (..), HNat (..), hLookupByHNat, hSucc, (.*.))
import Data.Kind (Type)
import Data.Type.Equality (type (:~:) (Refl))
import Numeric.Natural (Natural)

type UTerm :: Type
data UTerm
    = UBool Bool
    | UNat Natural
    | USucc UTerm
    | UNatElim UTerm UTerm UTerm
    | UVar String
    | ULambda String UType UTerm
    | UApp UTerm UTerm
    | UIf UTerm UTerm UTerm

data UType
    = UTBool
    | UTNat
    | UTLambda UType UType

data TY a where
    TYBool :: TY Bool
    TYNat :: TY Natural
    TYLambda :: TY a -> TY b -> TY (a -> b)

instance Eq (TY a) where
    TYBool == TYBool = True
    TYNat == TYNat = True
    TYLambda a b == TYLambda a' b' = a == a' && b == b'

instance Show (TY a) where
    show = showType

tyEq :: TY a -> TY b -> Bool
TYBool `tyEq` TYBool = True
TYNat `tyEq` TYNat = True
TYLambda a b `tyEq` TYLambda a' b' = a `tyEq` a' && b `tyEq` b'
_ `tyEq` _ = False

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

data Typed k = forall t. Typed (TY t) (k t)

-- fixme ugly []
utype2ty :: UType -> Typed []
utype2ty UTBool = Typed TYBool []
utype2ty UTNat = Typed TYNat []
utype2ty (UTLambda a b) =
    case utype2ty a of
        Typed a' _ ->
            case utype2ty b of
                Typed b' _ -> Typed (TYLambda a' b') []

data TypeContext ts where
    EmptyTC :: TypeContext '[]
    AddType :: TY t -> String -> TypeContext ts -> TypeContext (t ': ts)

tcLookup :: TypeContext ts -> String -> Either String (Typed (Term ts))
tcLookup EmptyTC varName = Left $ "Name not found: " <> varName
tcLookup (AddType ty var more) varName
    | var == varName = Right (Typed ty (TVar (Proxy @'HZero)))
    | otherwise = do
        recur <- tcLookup more varName
        case recur of
            Typed ty' (TVar n) -> Right $ Typed ty' (TVar (hSucc n))
            _ -> Left "Internal error in tcLookup"

typeCheck :: TypeContext ts -> UTerm -> Either String (Typed (Term ts))
typeCheck ctx (UVar varName) = tcLookup ctx varName
typeCheck ctx (ULambda argName argType body) =
    case utype2ty argType of
        Typed argType' _ -> do
            body' <- typeCheck (AddType argType' argName ctx) body
            case body' of
                Typed bodyTy bodyTerm ->
                    pure $ Typed (TYLambda argType' bodyTy) (TLambda argType' bodyTerm)
typeCheck _ (UBool b) = pure $ Typed TYBool (TBool b)
typeCheck _ (UNat n) = pure $ Typed TYNat (TNat n)
typeCheck ctx (UIf cond true false) = do
    cond' <- typeCheck ctx cond
    case cond' of
        Typed TYBool condTerm -> do
            true' <- typeCheck ctx true
            case true' of
                Typed tt trueTerm -> do
                    false' <- typeCheck ctx false
                    case false' of
                        Typed ft falseTerm -> do
                            case sameType tt ft of
                                Nothing -> Left "Branches of an if must be of the same type"
                                Just Refl -> pure $ Typed tt (TIf condTerm trueTerm falseTerm)
        Typed _ _ -> Left "Invalid If condition type"
typeCheck ctx (USucc n) = do
    n' <- typeCheck ctx n
    case n' of
        Typed TYNat nTerm -> do
            pure $ Typed TYNat (TSucc nTerm)
        Typed _ _ -> Left "Invalid argument to Succ"
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
                                    n' <- typeCheck ctx n
                                    case n' of
                                        Typed TYNat nTerm ->
                                            pure $ Typed resTy (TNatElim zTerm succTerm nTerm)
                                        _ -> Left "UNatElim's third argument must be a Nat"
                                Nothing -> Left "UNatElim second argument must return the same type as first argument"
                        Nothing -> Left "UNatElim's second agument must be: a -> a"
                _ -> Left "UnatElim's second argument must be a function"
typeCheck ctx (UApp f arg) = do
    f' <- typeCheck ctx f
    case f' of
        Typed (TYLambda a b) fTerm -> do
            arg' <- typeCheck ctx arg
            case arg' of
                Typed argType argTerm ->
                    case sameType a argType of
                        Nothing -> Left "Wrong argument type for lambda"
                        Just Refl -> pure $ Typed b (TApp fTerm argTerm)
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
eval e (TVar n) = envLookup e n

eval' :: Term '[] a -> a
eval' = eval HNil

evalToNat :: UTerm -> Either String Natural
evalToNat term = do
    typed <- typeCheck EmptyTC term
    case typed of
        Typed ty tterm -> do
            case ty of
                TYNat -> Right $ eval' tterm
                _ -> Left $ "typecheck result /= Nat: " <> show ty

envLookup :: HLookupByHNat n env => HList env -> Proxy n -> HLookupByHNatR n env
envLookup xs n = hLookupByHNat n xs

showType :: TY a -> String
showType TYBool = "Bool"
showType TYNat = "Nat"
showType (TYLambda a b) = showType a <> " -> " <> showType b
