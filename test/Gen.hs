{-# LANGUAGE RecordWildCards #-}

module Gen (uterm, utype, lambdaTermParts) where

import Control.Monad.State.Strict (MonadState, evalStateT, get, gets, modify', put, state)
import Data.Functor (($>))
import Data.Map.Strict qualified as M
import Data.Stream.Infinite qualified as S
import Data.Text qualified as T
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import TypedTC.Checker

data TermGenState = TermGenState
    { tsNamePool :: S.Stream T.Text
    , tsBound :: M.Map UType [(T.Text, UType)]
    }

type TermGen g = (MonadGen g, MonadState TermGenState g, Applicative g)

usableVars :: forall g. TermGen g => UType -> g (Maybe (g UTerm))
usableVars produceType = do
    vars <- gets (M.findWithDefault [] produceType . tsBound)
    case zip [1 ..] (reverse $ useVar <$> vars) of
        [] -> pure Nothing
        appliedVars -> pure $ Just $ Gen.frequency appliedVars
  where
    useVar :: (T.Text, UType) -> g UTerm
    useVar (name, UTLambda ft _) = do
        arg <- uterm ft
        pure (UApp (UVar name) arg)
    useVar (name, _) = pure (UVar name)

recursiveFrequency :: MonadGen m => [(Int, m a)] -> [(Int, m a)] -> m a
recursiveFrequency nonrecur recur =
    Gen.sized $ \n ->
        if n <= 1
            then Gen.frequency nonrecur
            else Gen.frequency $ nonrecur ++ fmap (fmap Gen.small) recur

natTerm :: TermGen g => g UTerm
natTerm = do
    vars <- usableVars UTNat
    let varsOrOther = maybe nonRec (\gen -> (10, gen) : nonRec) vars
    recursiveFrequency varsOrOther recursive
  where
    litNat = UNat . fromInteger <$> Gen.integral (Range.linear 0 10)
    nonRec = [(2, litNat)]
    recursive =
        [ (2, Gen.subterm natTerm USucc)
        , (2, ifTerm natTerm)
        , (2, app UTNat)
        , (1, unatElim UTNat)
        ]

boolTerm :: TermGen g => g UTerm
boolTerm = do
    vars <- usableVars UTBool
    let varsOrOther = maybe nonRec (\gen -> (9, gen) : nonRec) vars
    recursiveFrequency varsOrOther recursive
  where
    nonRec = [(2, litBool)]
    recursive =
        [ (2, ifTerm boolTerm)
        , (3, app UTBool)
        , (1, unatElim UTBool)
        ]
    litBool = UBool <$> Gen.bool

ifTerm :: TermGen g => g UTerm -> g UTerm
ifTerm branchGen = UIf <$> boolTerm <*> branchGen <*> branchGen

initTermGenState :: TermGenState
initTermGenState = TermGenState varNames M.empty
  where
    varNames = S.unfold (\n -> (T.pack $ 'x' : show n, n + 1)) (1 :: Integer)

bindVar :: (MonadState TermGenState g) => UType -> g T.Text
bindVar varType = state popName >>= \name -> modify' (bind name) $> name
  where
    popName s@TermGenState{..} =
        let (varName S.:> moreNames) = tsNamePool
         in (varName, s{tsNamePool = moreNames})
    bind varName s@TermGenState{..} =
        s{tsBound = M.insertWith (<>) (resType varType) [(varName, varType)] tsBound}
    resType (UTLambda _ toType) = toType
    resType other = other

lambdaTermParts' :: TermGen g => UType -> UType -> g (T.Text, UType, UTerm)
lambdaTermParts' fromT toT = do
    old <- get
    varName <- bindVar fromT
    body <- uterm' toT
    put old
    pure (varName, fromT, body)

lambdaTerm :: TermGen g => UType -> UType -> g UTerm
lambdaTerm fromT toT = do
    (n, t, b) <- lambdaTermParts' fromT toT
    pure $ ULambda n t b

utype :: MonadGen g => g UType
utype = Gen.recursive Gen.choice [pure UTBool, pure UTNat] recur
  where
    recur = [UTLambda <$> utype <*> utype]

app :: TermGen g => UType -> g UTerm
app t = do
    fromT <- utype
    f <- lambdaTerm fromT t
    arg <- uterm' fromT
    pure $ UApp f arg

unatElim :: TermGen g => UType -> g UTerm
unatElim t = do
    z <- uterm' t
    suc <- uterm' (UTLambda UTNat (UTLambda t t))
    UNatElim z suc <$> natTerm

uterm' :: TermGen g => UType -> g UTerm
uterm' UTBool = boolTerm
uterm' UTNat = natTerm
uterm' (UTLambda f t) = lambdaTerm f t

uterm :: MonadGen g => UType -> g UTerm
uterm t = evalStateT (uterm' t) initTermGenState

lambdaTermParts :: MonadGen g => UType -> UType -> g (T.Text, UType, UTerm)
lambdaTermParts f t = evalStateT (lambdaTermParts' f t) initTermGenState
