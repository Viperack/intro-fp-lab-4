{- |
Module      : Simplify
Description : Skeleton for Lab 4: simplifying polynomials.
Copyright   : (c) TDA555/DIT441, Introduction to Functional Programming
License     : BSD
Maintainer  : alexg@chalmers.se
Stability   : experimental

Authors     : <list your names here>
Lab group   : <group number>
-}

module Simplify where

import Poly
import Test.QuickCheck

-- Use the following simple data type for binary operators
data BinOp = AddOp | MulOp deriving Eq

--------------------------------------------------------------------------------
-- * A1
-- Define a data type 'Expr' which represents three kinds of expression:
-- binary operators (use 'BinOp' as a helper type) applied to two expressions,
-- numbers (use Int), and exponentiation x^n.
-- Note that since we consider expressions containing just a single variable,
-- x, your data type should *not* use 'String' or 'Char' anywhere, since this is
-- not needed.

data Expr = Expr -- change this!

--------------------------------------------------------------------------------
-- * A2
-- Define the data type invariant that checks that exponents are never negative
prop_Expr :: Expr -> Bool
prop_Expr = undefined


--------------------------------------------------------------------------------
-- * A3
-- Make 'Expr' an instance of 'Show' (along the lines of the example in the 
-- lecture). You can use Haskell notation for powers: x^2. You should show x^1 
-- as just x. 

-- instance Show Expr where
--   show = undefined

--------------------------------------------------------------------------------
-- * A4
-- Make 'Expr' and instance of 'Arbitrary'.
-- Now you can check the data type invariant that you defined in A2 using
-- QuickCheck.

-- (Optional)
-- Add a definition of function @shrink :: Expr -> [Expr]@ to 'Arbitrary'
-- which gives hints to QuickCheck on possible smaller expressions that it
-- could use to find a smaller counterexample for failing tests.

instance Arbitrary Expr
  where arbitrary = undefined

--------------------------------------------------------------------------------
-- * A5
-- Define the @eval@ function which takes a value for x and an expression and
-- evaluates it.

eval :: Int -> Expr -> Int
eval = undefined

--------------------------------------------------------------------------------
-- * A6
-- Define @exprToPoly@ that converts an expression into a polynomial.
-- Here it is important to think recursively to just solve the bigger problem
-- by solving the smaller problems and combining them in the right way. 

exprToPoly :: Expr -> Poly
exprToPoly = undefined

-- Define (and check) @prop_exprToPoly@, which checks that evaluating the
-- polynomial you get from @exprToPoly@ gives the same answer as evaluating
-- the expression.

prop_exprToPoly = undefined

--------------------------------------------------------------------------------
-- * A7
-- Now define the function going in the other direction.

polyToExpr :: Poly -> Expr
polyToExpr = undefined

-- Write (and check) a quickCheck property for this function similar to
-- question 6. 

prop_polyToExpr = undefined

--------------------------------------------------------------------------------
-- * A8
-- Write a function @simplify@ which simplifies an expression by converting it 
-- to a polynomial and back again.

simplify :: Expr -> Expr
simplify = undefined

--------------------------------------------------------------------------------
-- * A9
-- Write a quickCheck property that checks that a simplified expression does not 
-- contain any "junk", where junk is defined to be multiplication by one or 
-- zero, addition of zero, addition or multiplication of numbers, or x to the
-- power of zero. (You may need to fix A7)

prop_noJunk :: Expr -> Bool
prop_noJunk = undefined

--------------------------------------------------------------------------------
-- * A10
-- Write two IO functions that read respectively write the difficulty, which is
-- modelled as a natural number. Use the 'diffFile' as file path. Note that the
-- difficulty should never be below zero.

type Difficulty = Int

diffFile :: FilePath
diffFile = "difficulty.txt"

readDifficulty :: IO Difficulty
readDifficulty = undefined

writeDifficulty :: Difficulty -> IO ()
writeDifficulty = undefined

--------------------------------------------------------------------------------
-- * A11
-- Define the 'play' function that generates a random expression, a random 
-- value for @x@, show the simplified expression and ask the user to solve it. 
-- If the guess is as expected, give a nice feedback message and increase the 
-- difficulty by one. If the guess was wrong, again give feedback and decrease 
-- the difficulty by one. Then play again.

play :: IO ()
play = undefined

--------------------------------------------------------------------------------