{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.List.NonEmpty (NonEmpty (..))
import Data.Text qualified as T
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog
import Text.Megaparsec
import TypedTC.AST qualified as AST
import TypedTC.Checker
import TypedTC.Parser qualified as P

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
    testGroup
        "Tests"
        [ properties
        , units
        ]

properties :: TestTree
properties =
    testGroup
        "Properties"
        [ testGroup
            "Type checking"
            [ testPropertyNamed "can tc literal Nats" "prop_can_tc_nats" prop_can_tc_nats
            , testPropertyNamed "can tc literal Bools" "prop_can_tc_bools" prop_can_tc_bools
            , testPropertyNamed "can tc Succ" "prop_can_tc_succ" prop_can_tc_succ
            , testPropertyNamed "can tc id Nat" "prop_can_tc_id_nat" prop_can_tc_id_nat
            , testPropertyNamed "can tc if Nat" "prop_can_tc_if_nat" prop_can_tc_if_nat
            ]
        , testGroup
            "Evaluation"
            [ testPropertyNamed "can succ" "prop_can_succ" prop_can_succ
            , testPropertyNamed "can if nat" "prop_can_if_nat" prop_can_if_nat
            , testPropertyNamed "can sum" "prop_can_sum" prop_can_sum
            , testPropertyNamed "can mul" "prop_can_mul" prop_can_mul
            , testPropertyNamed "can fact" "prop_can_fact" prop_can_fact
            ]
        ]

units :: TestTree
units =
    testGroup
        "Unit tests"
        [ testGroup
            "Type checking"
            [ testCase "can tc not" unit_can_tc_not
            , testCase "can tc id Nat" unit_can_tc_id_nat
            , testCase "can tc sum" unit_can_tc_sum
            , testCase "can tc mul" unit_can_tc_mul
            , testCase "can tc fact" unit_can_tc_fact
            , dontTCCase $ ULambda "x" UTNat (UVar "y")
            , dontTCCase $ UIf (UBool True) (UBool False) (UNat 1)
            , dontTCCase $ UIf (UNat 1) (UNat 1) (UNat 1)
            , dontTCCase $ USucc (UBool True)
            , dontTCCase $ UApp (UBool True) (UBool True)
            , dontTCCase $ UNatElim (UBool True) (UBool True) (UNat 5)
            , dontTCCase $ UNatElim (UBool True) (ULambda "n" UTNat (ULambda "x" UTBool (UNat 42))) (UNat 5)
            ]
        , testGroup
            "AST generation"
            [ testCase "ast not" unit_ast_not
            , testCase "ast sum" unit_ast_sum
            ]
        , testGroup
            "Parser"
            [ parserCase "42" (P.LiteralNat 42)
            , parserCase "(42)" (P.LiteralNat 42)
            , parserCase " ( 42 ) " (P.LiteralNat 42)
            , parserCase "True" (P.LiteralBool True)
            , parserCase "  True " (P.LiteralBool True)
            , parserCase "  (True) " (P.LiteralBool True)
            , parserCase "  ( False ) " (P.LiteralBool False)
            , parserCase "Succ 42" (P.Succ (P.LiteralNat 42))
            , parserCase "Succ (42)" (P.Succ (P.LiteralNat 42))
            , parserCase "(Succ 42)" (P.Succ (P.LiteralNat 42))
            , parserCase " ( Succ   42 )  " (P.Succ (P.LiteralNat 42))
            , parserCase "  Succ (if True then 1 else 2)" (P.Succ (P.If (P.LiteralBool True) (P.LiteralNat 1) (P.LiteralNat 2)))
            , parserCase "if True then 1 else 2" (P.If (P.LiteralBool True) (P.LiteralNat 1) (P.LiteralNat 2))
            , parserCase " if   True then (1) else 2  " (P.If (P.LiteralBool True) (P.LiteralNat 1) (P.LiteralNat 2))
            , parserCase "if True then Succ 1 else (Succ 2)" (P.If (P.LiteralBool True) (P.Succ (P.LiteralNat 1)) (P.Succ (P.LiteralNat 2)))
            , parserCase "a" (P.Var "a")
            , parserCase "_a42" (P.Var "_a42")
            , parserCase " a " (P.Var "a")
            , parserCase " (a) " (P.Var "a")
            , parserCase " ( a42 ) " (P.Var "a42")
            , parserCase "a b" (P.App (P.Var "a") (P.Var "b"))
            , parserCase "a b" (P.App (P.Var "a") (P.Var "b"))
            , parserCase "a b c" (P.App (P.App (P.Var "a") (P.Var "b")) (P.Var "c"))
            , parserCase " a ( b ) c " (P.App (P.App (P.Var "a") (P.Var "b")) (P.Var "c"))
            , parserCase " a ( b c) d " (P.App (P.App (P.Var "a") (P.App (P.Var "b") (P.Var "c"))) (P.Var "d"))
            , parserCase "natElim a b c" (P.NatElim (P.Var "a") (P.Var "b") (P.Var "c"))
            , parserCase "natElim (a) b (c)" (P.NatElim (P.Var "a") (P.Var "b") (P.Var "c"))
            , parserCase " natElim ( a ) b   (    c) " (P.NatElim (P.Var "a") (P.Var "b") (P.Var "c"))
            , parserCase "natElim a (b c) d" (P.NatElim (P.Var "a") (P.App (P.Var "b") (P.Var "c")) (P.Var "d"))
            , parserCase "natElim a b c result" (P.App (P.NatElim (P.Var "a") (P.Var "b") (P.Var "c")) (P.Var "result"))
            , parserCase "\\ (x :: Nat) -> x" (P.Lambda (("x", P.PNat) :| []) (P.Var "x"))
            , parserCase "λ (x :: Nat) → x" (P.Lambda (("x", P.PNat) :| []) (P.Var "x"))
            , parserCase "  λ(x :: Nat)   →  (x ) " (P.Lambda (("x", P.PNat) :| []) (P.Var "x"))
            , parserCase "λ (x :: Nat) (y :: Bool) → x y" (P.Lambda (("x", P.PNat) :| [("y", P.PBool)]) (P.App (P.Var "x") (P.Var "y")))
            , parserCase " λ(x :: Nat)(y :: Bool)  → ((x y)) " (P.Lambda (("x", P.PNat) :| [("y", P.PBool)]) (P.App (P.Var "x") (P.Var "y")))
            , parserCase "λ(f :: Nat -> Nat) → f 1" (P.Lambda (("f", P.PFun P.PNat P.PNat) :| []) (P.App (P.Var "f") (P.LiteralNat 1)))
            , parserCase "λ (x :: Nat) → λ (y :: Nat) → y" (P.Lambda (("x", P.PNat) :| []) (P.Lambda (("y", P.PNat) :| []) (P.Var "y")))
            , parserCase "λ (x :: Nat) → λ (y :: Nat) → λ (z :: Nat) → y" (P.Lambda (("x", P.PNat) :| []) (P.Lambda (("y", P.PNat) :| []) (P.Lambda (("z", P.PNat) :| []) (P.Var "y"))))
            , parserCase "(λ (x :: Nat) → x) 42" (P.App (P.Lambda (("x", P.PNat) :| []) (P.Var "x")) (P.LiteralNat 42))
            , unparseableCase "42n"
            , unparseableCase "  TrueXXX "
            , unparseableCase "(True"
            , unparseableCase " if Truethen 1 else 2"
            , unparseableCase " if True then 1else 2"
            , unparseableCase " if True then 1 else2"
            , unparseableCase "λ x → x"
            , unparseableCase "λ x x"
            , unparseableCase "λ x. x"
            , unparseableCase "λ (x) → x"
            , unparseableCase "λ (x Nat) → x"
            , unparseableCase "λ (x :: Nat → x"
            ]
        ]

checkType :: (MonadTest m, HasCallStack) => UTerm -> TY a -> m ()
checkType uterm ty = do
    typed <- evalEither (typeCheck EmptyTC uterm)
    case typed of
        (Typed ty' _) -> do
            diff ty tyEq ty'

assertType :: () => UTerm -> TY a -> Assertion
assertType uterm ty = do
    let res = typeCheck EmptyTC uterm
    case res of
        Right (Typed ty' _) -> do
            assertBool ("Invalid type: " <> show ty <> " /= " <> show ty') $ ty `tyEq` ty'
        Left e -> assertFailure $ "Cannot type check: " <> T.unpack e

anyNatural :: Gen Natural
anyNatural = Gen.integral (Range.linear 0 (2 * fromIntegral (maxBound :: Int)))

prop_can_tc_nats :: Property
prop_can_tc_nats = property $ do
    n <- forAll anyNatural
    checkType (UNat n) TYNat

prop_can_tc_bools :: Property
prop_can_tc_bools = property $ do
    b <- forAll Gen.bool
    checkType (UBool b) TYBool

prop_can_tc_succ :: Property
prop_can_tc_succ = property $ do
    n <- forAll anyNatural
    checkType (USucc $ UNat n) TYNat

prop_can_tc_id_nat :: Property
prop_can_tc_id_nat = property $ do
    n <- forAll anyNatural
    checkType (USucc $ UNat n) TYNat

prop_can_tc_if_nat :: Property
prop_can_tc_if_nat = property $ do
    n <- forAll anyNatural
    m <- forAll anyNatural
    checkType (UIf (UBool True) (UNat n) (UNat m)) TYNat

prop_can_succ :: Property
prop_can_succ = property $ do
    n <- forAll anyNatural
    res <- evalEither $ evalToNat (USucc $ UNat n)
    res === n + 1

prop_can_if_nat :: Property
prop_can_if_nat = property $ do
    n <- forAll anyNatural
    m <- forAll anyNatural
    cond <- forAll Gen.bool
    res <- evalEither $ evalToNat (UIf (UBool cond) (UNat n) (UNat m))
    res === if cond then n else m

prop_can_sum :: Property
prop_can_sum = property $ do
    n <- forAll gen
    m <- forAll gen
    res <- evalEither $ evalToNat (UApp (UApp uSum (UNat n)) (UNat m))
    res === n + m
  where
    gen = Gen.integral (Range.linear 0 50)

prop_can_mul :: Property
prop_can_mul = property $ do
    n <- forAll gen
    m <- forAll gen
    res <- evalEither $ evalToNat (UApp (UApp uMul (UNat n)) (UNat m))
    res === n * m
  where
    gen = Gen.integral (Range.linear 0 50)

prop_can_fact :: Property
prop_can_fact = property $ do
    n <- forAll gen
    res <- evalEither $ evalToNat (UApp uFact (UNat n))
    res === product [1 .. n]
  where
    gen = Gen.integral (Range.linear 0 8)

unit_can_tc_not :: Assertion
unit_can_tc_not = assertType uNot (TYLambda TYBool TYBool)

unit_can_tc_id_nat :: Assertion
unit_can_tc_id_nat = assertType natId (TYLambda TYNat TYNat)

unit_can_tc_sum :: Assertion
unit_can_tc_sum = assertType uSum (TYLambda TYNat (TYLambda TYNat TYNat))

unit_can_tc_mul :: Assertion
unit_can_tc_mul = assertType uMul (TYLambda TYNat (TYLambda TYNat TYNat))

unit_can_tc_fact :: Assertion
unit_can_tc_fact = assertType uFact (TYLambda TYNat TYNat)

unit_ast_not :: Assertion
unit_ast_not = do
    Right (P.StExpr e) <- pure $ P.parseStatement "λ (b :: Bool) → if b then False else True"
    Right uterm <- pure $ AST.ast e
    uNot @?= uterm

unit_ast_sum :: Assertion
unit_ast_sum = do
    Right (P.StExpr e) <- pure $ P.parseStatement "(λ (n :: Nat) → (natElim (λ (n :: Nat) → n) (λ (_ :: Nat) (f :: Nat → Nat) → (λ (n :: Nat) → Succ (f n))) n))"
    Right uterm <- pure $ AST.ast e
    uterm @?= uSum

dontTCCase :: UTerm -> TestTree
dontTCCase uterm = testCase ("Untypeable: " <> show uterm) $ do
    let typed = typeCheck EmptyTC uterm
    case typed of
        Left _ -> pure ()
        Right (Typed ty _) -> assertFailure $ "Unexpected type check. Type: " <> show ty

assertParsedExp :: HasCallStack => P.Expr -> T.Text -> Assertion
assertParsedExp expr s =
    case P.parseStatement s of
        Left e -> assertFailure (errorBundlePretty e)
        Right (P.StExpr expr') -> expr @=? expr'
        Right _ -> assertFailure "Not an expression"

parserCase :: T.Text -> P.Expr -> TestTree
parserCase input expr = testCase (T.unpack input) (assertParsedExp expr input)

unparseableCase :: T.Text -> TestTree
unparseableCase input = testCase (T.unpack ("Unparseable: " <> input)) $
    case P.parseStatement input of
        Left _ -> pure ()
        Right res -> assertFailure ("Unexpeced parseable input. Got: " <> show res)

uNot :: UTerm
uNot = ULambda "b" UTBool (UIf (UVar "b") (UBool False) (UBool True))

natId :: UTerm
natId = ULambda "n" UTNat (UVar "n")

uSum :: UTerm
uSum = ULambda "n" UTNat (UNatElim natId suc (UVar "n"))
  where
    suc = ULambda "_" UTNat (ULambda "f" (UTLambda UTNat UTNat) (ULambda "n" UTNat (USucc (UApp (UVar "f") (UVar "n")))))

uMul :: UTerm
uMul = ULambda "a" UTNat (UNatElim natZero suc (UVar "a"))
  where
    natZero = ULambda "n" UTNat (UNat 0)
    suc = ULambda "_" UTNat (ULambda "f" (UTLambda UTNat UTNat) (ULambda "b" UTNat (UApp (UApp uSum (UVar "b")) (UApp (UVar "f") (UVar "b")))))

uFact :: UTerm
uFact = ULambda "n" UTNat (UNatElim (UNat 1) suc (UVar "n"))
  where
    suc = ULambda "k" UTNat (ULambda "rec" UTNat (UApp (UApp uMul (UVar "rec")) (UVar "k")))
