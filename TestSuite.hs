module Main where

import Test.Framework (Test, defaultMain)

import Test.Data.Number.Sqrts (sqrts_properties)

main :: IO ()
main = defaultMain tests

tests :: [Test.Framework.Test]
tests = [ sqrts_properties ]
