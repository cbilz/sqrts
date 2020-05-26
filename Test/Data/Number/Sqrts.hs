module Test.Data.Number.Sqrts (sqrts_properties) where

import qualified Data.Map.Strict as M
import Data.Number.CReal (CReal, appRel)
import qualified Data.Number.CReal as CReal
import Data.Ratio
import GHC.Float
import Math.NumberTheory.Primes (factorise)
import Data.Number.Sqrts
import Numeric.IEEE
import Numeric.Natural

import Test.Framework (Test, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck


n = 10000

sqrts_properties :: Test.Framework.Test
sqrts_properties =
  testGroup "Sqrts Properties" [
    testProperty
      "sqrts/back and forth conversion"
      prop_toFrom_Sqrts,

    testProperty
      "sqrts/some conversions to Double"
      prop_SomeToDoubleSqrts,

    testProperty
      "sqrts/some simple algebraic identities"
      prop_SomeEqSqrts,

    testProperty
      "sqrts/convert to Double via CReal"
      prop_CompareConversions,

    testProperty
      "sqrts/compare order with the order on CReal (1/2)"
      prop_OrdBasicSqrts,

    testProperty
      "sqrts/compare order with the order on CReal and Double (2/2)"
      prop_OrdConversionsSqrts,

    testProperty
      "sqrts/fromRational"
      prop_fromRationalSqrts,

    testProperty
      "sqrts/solveQuadEq"
      prop_solvesQuadEqSqrts,

    testProperty
      "sqrts/tryRational"
      prop_tryRationalSqrts,

    testProperty
      "sqrts/reduce"
      prop_reduceSqrts,

    testProperty
      "sqrts/negate"
      prop_negateSqrts,

    testProperty
      "sqrts/recip"
      prop_recipSqrts,

    testProperty
      "sqrts/addition"
      prop_addSqrts,

    testProperty
      "sqrts/multiplication"
      prop_mulSqrts,

    testProperty
      "sqrts/associativity of addition and multiplication"
      prop_assocSqrts,

    testProperty
      "sqrts/commutativity of addition and multiplication"
      prop_commSqrts,

    testProperty
      "sqrts/distributivity"
      prop_distrSqrts,

    testProperty
      "sqrts/add the negative"
      prop_addInvSqrts
  ]


instance Arbitrary Sqrts where
  arbitrary = fmap (fromList . map (\(c,b) -> (fromRational $ abs c, b))) $
    scale (`quot` 4) (arbitrary :: Gen [(Rational, Rational)])


smalln = max 1 (n `div` 10)
n2 = max 1 (floor $ sqrt $ fromIntegral n)
n3 = max 1 (floor $ (fromIntegral n)**(1/3 :: Double))

impl x y = (not x) || y
dblEq :: Double -> Double -> Bool
dblEq x y = x `elem` [predIEEE y, y, succIEEE y]

infix 4 ==:, /=:
(==:) = appRel 60 (==)
(/=:) = appRel 60 (/=)

prop_toFrom_Sqrts :: Sqrts -> Property
prop_toFrom_Sqrts x = withMaxSuccess n $
  (x == fromMap (toMap x)) && (x == fromList (M.toList $ toMap x))

prop_SomeToDoubleSqrts =
  all (uncurry (==))
  [ (toDouble $ (1 + sqrtRat 5)/2  , 1.618033988749895)
  , (toDouble $ 1/2 + sqrtRat(5/4) , 1.618033988749895)
  , (toDouble $ sqrtRat 2          , 1.4142135623730951)
  , (toDouble $ an/ad + bn/bd * sqrtRat(cn/cd), 4.37255209710043)
  ]
  where an = 1224416571661177635055636481814
        ad =  245023016970743266525478794825
        bn = -803110949036128954967964765881
        bd =  959027468541569349522483387030
        cn =  489364355679081900132199584718
        cd =  879673302678325312504786214092

prop_SomeEqSqrts =
  all (uncurry (==))
  [ (4, 1 + 3 * sqrtRat 1)
  , (1 + 3 * sqrtRat 1, 1 + 1/2 * sqrtRat 36) ]

prop_CompareConversions x = withMaxSuccess (10*n) $
  (CReal.toDouble (toCReal x)) `dblEq` (toDouble x)

prop_OrdBasicSqrts :: Rational -> Rational -> Rational -> Property
prop_OrdBasicSqrts a b c = withMaxSuccess n $
  all (uncurry impl)
  [ (sqrts == 0, creal ==: 0)
  , (sqrts < 0, creal < 0)
  , (sqrts > 0, creal > 0) ]
  where sqrts = (fr a) + (fr b) * sqrtRat (fr $ abs c) :: Sqrts
        creal = (fr a) + (fr b) * sqrt (fr $ abs c) :: CReal

prop_OrdConversionsSqrts :: Sqrts -> Sqrts -> Property
prop_OrdConversionsSqrts x y = withMaxSuccess smalln $
  all (uncurry impl)
  [ (x == y, toCReal x ==: toCReal y)
  , (x == y, toDouble x `dblEq` toDouble y)
  , (x < y, toCReal x < toCReal y)
  , (x > y, toCReal x > toCReal y)
  ]

prop_fromRationalSqrts :: Rational -> Property
prop_fromRationalSqrts x = withMaxSuccess n $ property $
  (fr x :: CReal) ==: toCReal (fr x :: Sqrts) &&
  toList (fr x) == if x /= 0 then [(1%1,x)] else []

prop_solvesQuadEqSqrts :: Rational -> Rational -> Rational -> Property
prop_solvesQuadEqSqrts a b c = withMaxSuccess smalln $
  a /= 0 || b /= 0 || c /= 0 ==>
  all (\x -> ((fr a*x^2+fr b*x+fr c :: Sqrts) == 0) && lhs x ==: 0) $
  solveQuadEq a b c
  where lhs x = a'*(toCReal x)^2 + b'*(toCReal x) + c' :: CReal
        [a',b',c'] = map fromRational [a,b,c]

prop_tryRationalSqrts :: Sqrts -> Property
prop_tryRationalSqrts x = withMaxSuccess smalln $ property $
  case tryRational x of Just q -> (fr q :: CReal) ==: toCReal x
                        Nothing -> True

prop_reduceSqrts :: Sqrts -> Property
prop_reduceSqrts x = withMaxSuccess n2 $ property $
  (x' == x) && (toCReal x' ==: toCReal x) && sf
  where
    x' = reduce x
    sf = all (\(_,n) -> n==1) $
      (fst $ unzip $ toList x') >>= split >>= factorise
    split q = filter (/=0) [numerator q, denominator q]


prop_negateSqrts :: Sqrts -> Property
prop_negateSqrts x = withMaxSuccess n2 $ property $
  (negate $ toCReal x) ==: toCReal (negate x)

prop_recipSqrts :: Sqrts -> Property
prop_recipSqrts x = withMaxSuccess n3 $
  (x /= 0 && length (toList x) <= 6) ==>
  (recip $ toCReal x) ==: toCReal (recip x)

prop_addSqrts :: Sqrts -> Sqrts -> Property
prop_addSqrts x y = withMaxSuccess smalln $ property $
  (toCReal x + toCReal y) ==: (toCReal (x + y))

prop_mulSqrts :: Sqrts -> Sqrts -> Property
prop_mulSqrts x y = withMaxSuccess n2 $ property $
  (toCReal x * toCReal y) ==: (toCReal (x * y))

prop_assocSqrts :: Sqrts -> Sqrts -> Sqrts -> Property
prop_assocSqrts x y z = withMaxSuccess n3 $ property $
  (toList $ reduce ((x + y) + z)) == toList (reduce (x + (y + z))) &&
  (toList $ reduce ((x * y) * z)) == toList (reduce (x * (y * z)))

prop_commSqrts :: Sqrts -> Sqrts -> Property
prop_commSqrts x y = withMaxSuccess n2 $ property $
  (toList (x + y)) == toList (y + x) &&
  (toList (x * y)) == toList (y * x)

prop_distrSqrts :: Sqrts -> Sqrts -> Sqrts -> Property
prop_distrSqrts x y z = withMaxSuccess n3 $ property $
  (toList (x * (y + z))) == toList ((x * y) + (x * z))

prop_addInvSqrts :: Sqrts -> Property
prop_addInvSqrts x = withMaxSuccess smalln $ property $
  (toList $ x - x) == []

fr :: (Fractional a) => Rational -> a
fr = fromRational
tr :: (Real a) => a -> Rational
tr = toRational
