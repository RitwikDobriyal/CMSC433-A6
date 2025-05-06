{- | Verification Condition Generation |
   =====================================

Name: Ritwik Dobriyal
Assignment #5
CMSC433, Spring 2025 - Section 0101

In this file, you are going to calculate weakest preconditions for
the non-array part of Mini Dafny, using the Hoare Logic rules we
introduced in the beginning of the semester to propagate "ensures"
clauses backwards from the end of a block of statements, and use
those to calculate the verification conditions that need to hold
for a program to be correct.

We are going to use the "Square.dfy" program that we have been using
throughout the class as our running example:

method Square (x : int) returns (z : int) 
  requires x > 0 
  ensures z == x * x
{
    var y : int := 0;
    z := 0;
    while y < x 
      invariant y <= x && z == y * x
    {
      z := z + x;
      y := y + 1;
    }
}

and it's full annotation in Hoare Logic:

{ x > 0} ->                               (1)
{ 0 <= x && 0 == 0 * x }
    var y : int := 0;
{ y <= x && 0 == y * x }
    z := 0;
{ y <= x && z == y * x }
    while y < x {
{ y <= x && z == y * x && y < x } ->      (2)
{ y + 1 <= x && z + x == (y + 1) * x }
      z := z + x;
{ y + 1 <= x && z == (y + 1) * x }
      y := y + 1;
{ y <= x && z == y * x }
    }
{ y <= x && z == y * x && !(y < x) } ->   (3)
{ z == x * x }

-}

module VCGen where

import Printer
import Syntax

import Test.HUnit

{- | Substitution |
   ================

Recall the Hoare Logic rule for assignment:

   ---------------------
   {Q[a/x] x := a; {Q}

We read this rule as "in order for predicate Q to hold
after executing an assignment, we need Q but with
x substituted for a to hold before".  Which means that
before we calculate weakest preconditions for MiniDafny
statements, we need to define substitution.


We begin by defining a typeclass that characterizes
substitution, given a variable Name and an Expression to
be substituted in.

-}

class Subst a where
  subst :: a -> Name -> Expression -> a

-- | We will write subst e x e' for e [x := e']. To perform this substitution
-- you need to do case analysis on e, propagating the substitution via
-- recursion until you reach the base case of a variable. At that point,
-- you can either perform the substitution or not. Remember, we're ignoring
-- arrays for this project, so we have already left this bit out for you.

instance Subst Expression where
  subst (Var (Proj _ _)) _ _ = error "Ignore arrays for this project"
  subst (Val v) _ _ = Val v -- for values, which don't change when substituting
  subst (Var (Name n)) x e -- for variables...
    | n == x = e -- does variable match? if so, we substitute
    | otherwise = Var (Name n) -- otherwise, we don't do it
  subst (Op1 op e1) x e = Op1 op (subst e1 x e) -- subexpressions? rerun expression
  subst (Op2 e1 op e2) x e = Op2 (subst e1 x e) op (subst e2 x e) -- subexpressions? rerun expression

-- | As an example, consider the loop invariant of Square:
--
--   y <= x && z == y * x
--
--   Or, in our AST representation:

wInv :: Expression
wInv =  Op2 (Op2 (Var (Name "y")) Le (Var (Name "x")))
            Conj
            (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))
            
-- | When propagating the loop invariant backwards inside the loop body,
--   we substitute "y+1" for "y" and obtain:
--
--   y + 1 <= x && z == y * x
--
--   That is:

wYPlus1 :: Expression
wYPlus1 = Op2 (Var (Name "y")) Plus (Val (IntVal 1))

wInvSubstYY1 :: Expression
wInvSubstYY1 = Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x")))
                   Conj
                   (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x"))))

test_substExp :: Test
test_substExp = TestList [ "exp-subst" ~: subst wInv "y" wYPlus1 ~?= wInvSubstYY1 ]

-- | You will also need to implement substitution for predicates, for which
--   you need to invoke substitution for expressions.
--   CAVEAT: But not under binders with the same name!

instance Subst Predicate where
  subst (Forall ys e) x e'
    | x `elem` map fst ys = Forall ys e -- if the variable is in the list of bound variables, we don't substitute
    | otherwise = Forall ys (subst e x e') -- otherwise, we do
  subst (PredOp op1 op op2) x e = PredOp (subst op1 x e) op (subst op2 x e)

test_substPred :: Test
test_substPred = TestList [ "pred-subst" ~: subst (Forall [] wInv) "y" wYPlus1 ~?= Forall [] wInvSubstYY1 ]


{- | Calculating Weakest Preconditions |
   -------------------------------------

Next up, we are going to actually calculate weakest preconditions.
We are also going to organize this in a typeclass, to account for
both statements and blocks of statements.

-}

class WP a where
  wp :: a -> Predicate -> Predicate

{- | The core of automated reasoning using Hoare Logic is the
     calculation of weakest preconditions for statements
     Ignoring asserts and arrays (for this project), we need to
     calculate, using Hoare rules, the weakest precondition
     that needs to hold before the statement is executed in order
     for the postcondition to hold.

   * For empty blocks of statements, we simply leave the postcondition unchanged:

                           --------------------
                            {Q}    { }     {Q}

   * For assignments and declarations we can use the assignment rule
     (ignoring Dafny's requirements that variables assigned to need
     to already be declared, and that variables cannot be redeclared):


                         ----------------------
                         {Q[a/x] x := a; {Q}

     That is, we substitute the expression being assigned to a variable,
     for that variable, in the postcondition predicate.

   * For if statements, let's take a look at the Hoare rule:

                                {P && b } s1 {Q}
                                {P && !b} s2 {Q} 
                        -------------------------------
                        {P} if b { s1 } else { s2 } {Q}

      What is the weakest precondition in this case? We can calculate
      the weakest precondtion for both the "then" and the "else"
      statement blocks. If P1 is the weakest precondition of s1, and P2
      is the weakest precondtion of s2, then the weakest precondition
      for the if statement is

                            b ==> P1 && !b ==> P2

    * For while statements, let's take a look at the Hoare rule:

                                 {P && b} s {P}
                         ---------------------------
                         {P} while b { s } {P && !b}

      While loops are not amenable to automatically computing preconditions,
      so we can simply use the loop invariant as that precondition, as you
      did on paper.

-}

instance WP Statement where
  wp (Assign (Proj _ _) _) p = error "Ignore arrays for this project"
  wp (Assign (Name n) e) p = subst p n e -- this is for assignments
  wp (Decl (x, _) e) p = subst p x e -- this is for declarations
  wp (If e s1 s2) p = -- this predop is for if statements
    PredOp -- it's predops combined with predops through a conjunction, as shown below
      (PredOp (Forall [] e) Implies (wp s1 p))
      Conj
      (PredOp (Forall [] (Op1 Not e)) Implies (wp s2 p))
  wp (While inv _ _) p = inv

-- | You will also need to implement weakest preconditions for blocks
--   of statements, by repeatedly getting the weakest precondition
--   starting from the end.
--   HINT: folds are your friend.
instance WP Block where
  wp (Block ss) p = foldr wp p ss -- using foldr b/c of the hint above

{- | Verification conditions |
   ---------------------------

   The next part of automating verification of programs is to
   use the weakest precondition calculation to compute which
   implications need to hold. For blocks of statements that don't
   contain a while loop, then the only verification condition
   is that the precondition implies the weakest precondition
   of the postcondition through the block---similar to (1) in
   the square example.

   However, each while loop in a program introduces two additional
   verification conditions:

   * The loop invariant plus the guard should imply the weakest
     precondition of the loop invariant through the loop body.
   * The loop invariant plus the negation of the guard should imply
     the weakest precondition of the continuation of the program (or
     the postcondition itself if the while loop is the last statement).

   That is, the following test should pass:
-}

-- | The while loop from Square:
-- while y < x
--   invariant y <= x && z == y * x
-- {
--   z := z + x;
--   y := y + 1;
-- }
wSquareWhile :: Statement
wSquareWhile =
  While (Forall [] (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x")))
                        Conj
                        (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))))
        (Op2 (Var (Name "y")) Lt (Var (Name "x")))
        (Block [ Assign (Name "z") (Op2 (Var (Name "z")) Plus (Var (Name "x")))
               , Assign (Name "y") (Op2 (Var (Name "y")) Plus (Val (IntVal 1)))])

-- | The post condition of Square
-- z == x * x
wWhilePost :: Expression
wWhilePost = Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))

-- | The two verification conditions it gives rise to --- (2) and (3) above.
-- y <= x && z == y * x && y < x ==> (y + 1 <= x && z + x == (y + 1) * x)
-- y <= x && z == y * x && ! (y < x) ==> z == x * x

vcsWhile :: [Predicate]
vcsWhile =
  [PredOp (PredOp (Forall [] (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x")))))) Conj (Forall [] (Op2 (Var (Name "y")) Lt (Var (Name "x"))))) Implies (Forall [] (Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x"))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Var (Name "x"))) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x"))))))
  ,PredOp (PredOp (Forall [] (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x")))))) Conj (Forall [] (Op1 Not (Op2 (Var (Name "y")) Lt (Var (Name "x")))))) Implies (Forall [] (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))))]

test_vcStmt :: Test
test_vcStmt =
  TestList [ "vc - while" ~: vcStmt (Forall [] wWhilePost) wSquareWhile ~?= vcsWhile ]

-- | To implement this, first, calculate the latter two for a single statement:
vcStmt :: Predicate -> Statement -> [Predicate]
vcStmt p (While inv e b) = -- combining predicate with expression from while
  [ 
  PredOp (PredOp inv Conj (Forall [] e)) Implies (wp b inv), -- first predop
  PredOp (PredOp inv Conj (Forall [] (Op1 Not e))) Implies p -- second predop in list
  ]
vcStmt _ _ = []

-- | Then, calculate the while loop verification conditions for blocks.
-- i COOKED i thought i burnt down the kitchen but LETS GOOOOOOO
vcBlock :: Predicate -> Block -> [Predicate]
vcBlock p (Block ss) = 
  snd $ foldr helper (p, []) ss
  where
    helper s (curr, cond) = -- helper function to generate VCs and update
      let newVC = vcStmt curr s -- get VC from current statement
      in
      (wp s curr, newVC ++ cond) -- update results w/new postcondition and VCs

{- | Lifting to Methods |
   ----------------------

Then, to put everything together, we need to use the specification of the methods
as the precondition and postcondition of the method body.

First, we provide you with code that joins requires and ensures specifications
of a method together into a single predicate.
-}
requires :: [Specification] -> Predicate
requires [] = Forall [] (Val (BoolVal True))
requires (Requires p : ps) = PredOp p Conj (requires ps)
requires (_ : ps) = requires ps

ensures :: [Specification] -> Predicate
ensures [] = Forall [] (Val (BoolVal True))
ensures (Ensures p : ps) = PredOp p Conj (ensures ps)
ensures (_ : ps) = ensures ps

{- | Finally, given a method, use the requires and ensures functions
     defined above to calculate the verification conditions for the
     whole method:
     - The method precondition implies the weakest precondtion of the
       method postcondition through the method body.
     - Followed by the verification conditions that while loops in the
       method block give rise to.
-}
vc :: Method -> [Predicate] 
vc (Method _ _ _ specs (Block ss)) =
  let e = ensures specs
      r = requires specs
  in
  PredOp r Implies (wp (Block ss) e) : vcBlock e (Block ss)
  -- implies weakest pre of method body to post with vcBlock, Block, and wp


-- | As a complete end-to-end test, the verification conditions for the whole of
--   the Square method is the list of the following three expressions (in order):
-- x > 0 && true ==> (0 <= x && 0 == 0 * x)
-- y <= x && z == y * x && y < x ==> (y + 1 <= x && z + x == (y + 1) * x)
-- y <= x && z == y * x && ! (y < x) ==> (z == x * x && true)

wSquare :: Method
wSquare = Method "Square" [("x",TInt)] [("z",TInt)] [Requires (Forall [] (Op2 (Var (Name "x")) Gt (Val (IntVal 0)))),Ensures (Forall [] (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))))] (Block [Decl ("y",TInt) (Val (IntVal 0)),Assign (Name "z") (Val (IntVal 0)),While (Forall [] (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x")))))) (Op2 (Var (Name "y")) Lt (Var (Name "x"))) (Block [Assign (Name "z") (Op2 (Var (Name "z")) Plus (Var (Name "x"))),Assign (Name "y") (Op2 (Var (Name "y")) Plus (Val (IntVal 1)))])])

vcSquare :: [Predicate]
vcSquare = [ PredOp (PredOp (Forall [] (Op2 (Var (Name "x")) Gt (Val (IntVal 0)))) Conj (Forall [] (Val (BoolVal True)))) Implies (Forall [] (Op2 (Op2 (Val (IntVal 0)) Le (Var (Name "x"))) Conj (Op2 (Val (IntVal 0)) Eq (Op2 (Val (IntVal 0)) Times (Var (Name "x"))))))
           , PredOp (PredOp (Forall [] (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x")))))) Conj (Forall [] (Op2 (Var (Name "y")) Lt (Var (Name "x"))))) Implies (Forall [] (Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x"))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Var (Name "x"))) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x"))))))
           , PredOp (PredOp (Forall [] (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x")))))) Conj (Forall [] (Op1 Not (Op2 (Var (Name "y")) Lt (Var (Name "x")))))) Implies (PredOp (Forall [] (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x"))))) Conj (Forall [] (Val (BoolVal True))))]

test_vc_method :: Test
test_vc_method = TestList [ "vc square" ~: vc wSquare ~?= vcSquare ]
