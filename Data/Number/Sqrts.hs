{-# LANGUAGE PatternGuards #-}
module Data.Number.Sqrts
  (

    Sqrts (toMap)
  , toDouble
  , toCReal
  , toList
  , fromList
  , fromMap
  , sqrtRat
  , solveQuadEq
  , tryRational
  , reduce

  ) where


import Data.List (partition)
import Data.Maybe (fromJust)
import qualified Data.Map.Strict as M
import Data.Number.CReal (CReal)
import Data.Ratio (Ratio, denominator, numerator, (%))
import Math.NumberTheory.Logarithms (naturalLog2)
import Math.NumberTheory.Powers.Squares (exactSquareRoot, integerSquareRoot)
import Math.NumberTheory.Primes (factorise, factorBack)
import Numeric.Natural (Natural)



{------------
   data Sqrts
   ------------}

-- Representing expressions of the form
--   b1 * sqrt(c1) + b2 * sqrt(c2) + ... + bn * sqrt(cn)
-- for rational numbers bi, nonnegative rational numbers ci and a finite
-- number n.

newtype Sqrts = Sqrts { toMap :: M.Map (Ratio Natural) Rational }

toList = M.toList . toMap
fromList = Sqrts . M.filter (/= 0) .  M.fromListWith (+) .
  filter (\(c,_) -> c /= 0)
fromMap = Sqrts . M.filterWithKey (\c b -> c /= 0 && b /= 0)

sqrtRat q = Sqrts $ if q /= 0 then M.singleton q 1 else M.empty
-- Solves a*x^2+b*x+c=0 for x.
solveQuadEq a b c
  | a == 0 && b == 0 = if c /= 0 then [] else error "Maxop.Sqrts.solveQuadEq"
  | a == 0 && b /= 0 = [ fromRational (-c/b) ]
  | discr >  0 = [ fromList [(1,-b/(2*a)), (fromRational discr,  1/(2*a))]
                 , fromList [(1,-b/(2*a)), (fromRational discr, -1/(2*a))] ]
  | discr == 0 = [ fromRational (-b/(2*a)) ]
  | discr <  0 = []
  where discr = b^2 - 4*a*c

instance Eq Sqrts where
  x == y
    | Just sgn <- trySimpleSign z = sgn == 0
    | otherwise = isZero z
    where z = x-y

instance Ord Sqrts where
  compare x y
    | Just sgn <- trySimpleSign z = compare sgn 0
    | not $ isZero z = compare (numSign z) 0
    | otherwise = EQ
    where z = x-y

-- This returns Just s where s is the signum of x if x is of the form
--   s + b*sqrt(c) + b'*sqrt(c').
-- Otherwise, this returns Nothing. The implementation relies on very basic
-- algebra.
trySimpleSign x
  | [] <- lst0 = Just $ signum s
  | [(c,b)] <- lst0 = Just $ rqiSgn s c b
  | [(c,b),(c',b')] <- lst0 = Just $ rqiSgn
      (rqiSgn s c b * (s^2 + b^2 * toRational c) + sgnSq b' * toRational c')
      c (rqiSgn s c b * 2 * s * b)
  | otherwise = Nothing
  where
    (lst0, lst1) = partition (\(c,b) -> c /= 1) $ toList x
    s = sum $ snd $ unzip lst1
    -- signum of s + b*sqrt(c).
    rqiSgn s c b = signum $ sgnSq b * toRational c + sgnSq s
    sgnSq x = x * abs x

-- We took the idea to these algorithms from:
-- Johannes Blömer: "Computing Sums of Radicals in Polynomial Time" (1993)
isZero = M.null . toMap . reduceGps
tryRational x
  | [] <- redlst = Just 0
  | [(c,b)] <- redlst
  , Just r <- exactSquareRootQ c = Just $ toRational r * b
  | otherwise = Nothing
  where redlst = toList $ reduceGps x

-- One should think of reduceGps as cheap and of makeSquareFree as expensive.
-- In practice, makeSquareFree may not terminate in acceptable time if the
-- input is large.
reduce = makeSquareFree . reduceGps

reduceGps = reduceGpsBy maxLog2
reduceGpsBy f x = fromList groups
  where
    groups = map (\(c,k,b) -> (c,b)) $ foldl ins [] $
      map (\(c,b) -> (c,f c,b)) $ toList x
    ins [] (c,k,b) = [(c,k,b)]
    ins ((c',k',b'):gs) (c,k,b)
      | Just r <- exactSquareRootQ (c/c') =
          if k' <= k then (c', k', (b*toRational r) + b'):gs
                     else (c, k, b + b'/toRational r):gs
      | otherwise = (c',k',b'):ins gs (c,k,b)

exactSquareRootQ q
  | Just rn <- exactSquareRoot $ numerator q
  , Just rd <- exactSquareRoot $ denominator q = Just (rn%rd)
  | otherwise = Nothing

makeSquareFree = fromList . map sepTerm . toList

sepTerm (c, b) = (nsf%dsf, b * toRational (nros%dros))
  where (nsf, nros) = sepPosIntegerSqrt $ numerator c
        (dsf, dros) = sepPosIntegerSqrt $ denominator c

sepPosIntegerSqrt x = (sf, ros)
  where sf = alterExp (`mod` 2)
        ros = alterExp (`div` 2)
        alterExp f = factorBack $ map (\(p, n) -> (p, f n)) factors
        factors = factorise x

-- If this terminates, then the output is the exact signum of the input.
-- This terminates if and only if the input is nonzero.
numSign = signum . snd . sig (\_ s -> s > 1)

scaleStep = 80

normalise n x
  | not $ null x = (exponent, map (factor*) pureSqs, signs)
  | otherwise = (0, [], [])
  where
    (pureSqs, signs) =
      unzip $ map (\(c,b) -> (c * fromRational (b^2), signum' b)) x
    factor = 2^^(2*exponent)
    exponent = n - (maximum $ map qlog2 pureSqs) `quot` 2
    signum' = signum . numerator

sig :: (Int -> Natural -> Bool) -> Sqrts -> (Int, Integer)
sig satisfy x = post . head . dropWhile (not . satisfy') $
  iterate improve init
  where
    (e, sqs, signs) = normalise scaleStep $ toList x
    init = (scaleStep, e, map (integerSquareRoot . floor) sqs)
    improve (k,e,rs) = (2*k, e+k, map (uncurry heron') $
                         zip (map floor $ sc (2*k) sqs) (sc k rs))
    ssum x = sum $ map (uncurry (*)) $ zip (map toInteger x) signs
    satisfy' (_,e,rs)
      = satisfy e (fromInteger $ max 0 (abs (ssum rs) - thresh))
    post (k,e,rs) = (e, ssum rs)
    thresh = 2 * (toInteger $ length signs)
    sc z = map (2^z *)

heron' x est
  | x /= 0 && log2 est > scaleStep + 30 = pick $ iterate improve est
  | otherwise = integerSquareRoot x
  where improve e = (e + x `quot` e) `quot` 2
        pick ~(e1:e2:es)
          | e1 == e2 = e1
          | otherwise = pick (e2:es)

qlog2 q = log2 (numerator q) - log2 (denominator q)
maxLog2 q = max (log2 (numerator q)) (log2 (denominator q))
log2 = naturalLog2 . (max 1)

toDouble :: Sqrts -> Double
toDouble x
  | x == 0 = 0
  | otherwise = if e <= 0 then fromInteger $ s*2^(-e)
                          else fromRational $ s%(2^e)
  where (e,s) = sig (\e s -> s > 2^(dig e)) x
        dig e = max 1 (60 - max 0 (abs e - 1024))

toCReal :: Sqrts -> CReal
toCReal = sum . map (\(c,b) -> (fromRational b) * sqrt (fromRational $ toRational c)) . toList

instance Num Sqrts where
  x + y = reduceGps $ fromMap $ M.unionWith (+) (toMap x) (toMap y)
  x * y = reduceGps $ fromList [ (cx * cy, bx * by)
                               | (cx, bx) <- toList x
                               , (cy, by) <- toList y ]
  abs x = x * signum x
  signum x = case compare x 0 of LT -> -1
                                 EQ ->  0
                                 GT ->  1
  fromInteger = fromRational . fromInteger
  negate x = Sqrts $ M.map negate $ toMap x

instance Fractional Sqrts where
  fromRational q = fromList [(1, q)]
  recip x = prod * fromRational (recip $ fromJust $ tryRational (x * prod))
    where
      signs = tail $ iterate (>>= f) [[]] !! (length lst)
      f xs = [1:xs,-1:xs]
      prod = product $ map (fromList . mulSigns) signs
      mulSigns s = map (\(sgn, (y,x)) -> (y,sgn*x)) $ zip s lst
      lst = toList x

instance Show Sqrts where
  showsPrec p x
    | null lst = showString "0"
    | otherwise =
        showParen (p >= 7) $
        foldr (.) (showSqrt $ last lst) $
          map (\y -> showSqrt y . showString " + ") $
          init lst
    where lst = toList x

showSqrt (c,b) =
  showsPrec 7 b . showString " * sqrt(" . showsPrec 0 c . showString ")"
