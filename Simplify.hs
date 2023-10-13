{- |
Module      : Simplify
Description : Skeleton for Lab 4: simplifying polynomials.
Copyright   : (c) TDA555/DIT441, Introduction to Functional Programming
License     : BSD
Maintainer  : alexg@chalmers.se
Stability   : experimental

Authors     : Theodor Köhler, Daniel Rising, Ludvig Ingolfson
Lab group   : 31
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

data Expr = Num Int | Op BinOp Expr Expr | Expo Int

--------------------------------------------------------------------------------
-- * A2
-- Define the data type invariant that checks that exponents are never negative
prop_Expr :: Expr -> Bool
prop_Expr (Num _)       = True
prop_Expr (Op _ e1 e2)  = prop_Expr e1 && prop_Expr e2
prop_Expr (Expo n)      = n >= 0

--------------------------------------------------------------------------------
-- * A3
-- Make 'Expr' an instance of 'Show' (along the lines of the example in the 
-- lecture). You can use Haskell notation for powers: x^2. You should show x^1 
-- as just x. 

instance Show Expr where
-- Num
  show (Num n)          = show n
-- Expo
  show (Expo 1)         = "x"
  show (Expo n)         = "x^" ++ show n
-- Op
  show (Op AddOp e1 e2) = show e1 ++ " + " ++ show e2
  show (Op MulOp e1 e2) = showFactor e1 ++ " * " ++ showFactor e2
    where
      showFactor e@(Op AddOp e1 e2) = "(" ++ show e ++ ")"
      showFactor e                  = show e

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
  where arbitrary = sized genExpr

maxExpo, maxNum :: Int
maxExpo = 4
maxNum = 10

genExpr :: Int -> Gen Expr
genExpr n
 | n < 2 = frequency [(1, genExpo), (1, genNum)]
 | otherwise = do
   m <- choose (1, n-1)
   op <- elements [AddOp, MulOp]
   x <- genExpr m
   y <- genExpr (n-m)
   return (Op op x y)
  where
    genNum :: Gen Expr -- Generates number, ex. "-3"
    genNum = do
      n <- choose (0, maxNum)
      return (Num n)
    genExpo :: Gen Expr -- Generates an exponentiation, ex. "x^2"
    genExpo = do
      n <- choose (0, maxExpo)
      return (Expo (abs n))

--------------------------------------------------------------------------------
-- * A5
-- Define the @eval@ function which takes a value for x and an expression and
-- evaluates it.

eval :: Int -> Expr -> Int
eval x (Num n)          = n
eval x (Expo n)         = x^n
eval x (Op AddOp e1 e2) = eval x e1 + eval x e2
eval x (Op MulOp e1 e2) = eval x e1 * eval x e2


--------------------------------------------------------------------------------
-- * A6
-- Define @exprToPoly@ that converts an expression into a polynomial.
-- Here it is important to think recursively to just solve the bigger problem
-- by solving the smaller problems and combining them in the right way. 

exprToPoly :: Expr -> Poly
exprToPoly (Num n)          = fromList [n]
exprToPoly (Expo n)         = fromList $ 1 : replicate n 0
exprToPoly (Op AddOp e1 e2) = exprToPoly e1 + exprToPoly e2
exprToPoly (Op MulOp e1 e2) = exprToPoly e1 * exprToPoly e2


-- Define (and check) @prop_exprToPoly@, which checks that evaluating the
-- polynomial you get from @exprToPoly@ gives the same answer as evaluating
-- the expression.

prop_exprToPoly :: Expr -> Int -> Bool
prop_exprToPoly expr n = eval n expr == evalPoly n (exprToPoly expr)

--------------------------------------------------------------------------------
-- * A7
-- Now define the function going in the other direction.

polyToExpr :: Poly -> Expr
polyToExpr poly = listToExpr $ toList poly
  where
    listToExpr []     = Num 0
    listToExpr [n]    = Num n
    listToExpr (x:xs)
     = addExpr (mulExpr (Num x) (Expo (length xs))) $ listToExpr xs

-- Smart addition, removes identity
addExpr :: Expr -> Expr -> Expr
addExpr (Num 0) y = y
addExpr y (Num 0) = y
addExpr x y       = Op AddOp x y

-- Smart multiplication, removes identity
mulExpr :: Expr -> Expr -> Expr
mulExpr (Num 1) y = y
mulExpr x (Num 1) = x
mulExpr (Num 0) y = Num 0
mulExpr x (Num 0) = Num 0
mulExpr x y = Op MulOp x y

-- Write (and check) a quickCheck property for this function similar to
-- question 6. 

prop_polyToExpr :: Poly -> Int -> Bool
prop_polyToExpr poly n = evalPoly n poly == eval n (polyToExpr poly)

--------------------------------------------------------------------------------
-- * A8
-- Write a function @simplify@ which simplifies an expression by converting it 
-- to a polynomial and back again.

simplify :: Expr -> Expr
simplify = polyToExpr . exprToPoly

--------------------------------------------------------------------------------
-- * A9
-- Write a quickCheck property that checks that a simplified expression does not 
-- contain any "junk", where junk is defined to be multiplication by one or 
-- zero, addition of zero, addition or multiplication of numbers, or x to the
-- power of zero. (You may need to fix A7)
prop_noJunk :: Expr -> Bool
prop_noJunk e = prop_noJunk' (simplify e)
  where
    prop_noJunk' :: Expr -> Bool
    prop_noJunk' (Expo 0)                    = False -- No x to the power of 0
    prop_noJunk' (Op AddOp (Num 0) e2)       = False -- No addition with 0
    prop_noJunk' (Op AddOp e2 (Num 0))       = False -- No addition with 0
    prop_noJunk' (Op MulOp (Num 0) e2)       = False -- No multiplication by 0
    prop_noJunk' (Op MulOp e2 (Num 0))       = False -- No multiplication by 0
    prop_noJunk' (Op MulOp (Num 1) e2)       = False -- No multiplication by 1
    prop_noJunk' (Op MulOp e2 (Num 1))       = False -- No multiplication by 1
    prop_noJunk' (Op AddOp (Num x) (Num y))  = False -- No addition of numbers
    prop_noJunk' (Op MulOp (Num x) (Num y))  = False -- No multiplication of numbers
    prop_noJunk' (Op _ e1 e2)                = prop_noJunk e1 && prop_noJunk e2
    prop_noJunk' _                           = True


--------------------------------------------------------------------------------
-- * A10
-- Write two IO functions that read respectively write the difficulty, which is
-- modelled as a natural number. Use the 'diffFile' as file path. Note that the
-- difficulty should never be below zero.

type Difficulty = Int

diffFile :: FilePath
diffFile = "difficulty.txt"

readDifficulty :: IO Difficulty
readDifficulty = do
  txt <- readFile diffFile
  return (read txt)

writeDifficulty :: Difficulty -> IO ()
writeDifficulty difficulty = do
  if difficulty < 0
    then error "Simplify: Negative difficulty!" -- Should print error message
                                                -- and not change the file
    else writeFile diffFile $ show difficulty

--------------------------------------------------------------------------------
-- * A11
-- Define the 'play' function that generates a random expression, a random 
-- value for @x@, show the simplified expression and ask the user to solve it. 
-- If the guess is as expected, give a nice feedback message and increase the 
-- difficulty by one. If the guess was wrong, again give feedback and decrease 
-- the difficulty by one. Then play again.



play :: IO ()
play = do
  difficulty <- readDifficulty
  x <- generate (choose (1, 4)) -- generate arbitrary
  expr  <- generate (genExpr difficulty)
  -- let answer = eval x expr
  putStr ("Simplify the following expression with x = " ++ show x ++
    "\n\n" ++ show (simplify expr) ++
    "\n\n> ")
  guess <- readLn
  if guess == eval x expr
    then do
      putStrLn "Well Done!\n"
      writeDifficulty (difficulty + 1)
      play
    else do
      putStrLn ("No, it should have been " ++ show (eval x expr) ++ ".")
      writeDifficulty (difficulty - 1)
      play


--------------------------------------------------------------------------------
