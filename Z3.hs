{- | Z3 integration |
   ==================

    Name: Ritwik Dobriyal
    Z3 Implementation (Final Project)
    CMSC433, Spring 2025 - Section 0101

   The final step in implementing a verifier like Dafny is to
   check whether the verification conditions generated using
   weakest preconditions actually hold. To do that, we will
   use the Z3 theorem prover.

   We will do this by creating a so called
   "SMTLib" file with the extnension .smt2 for _every_ verification
   condition.

   For an example, consider the first verification condition of our
   "Square.dfy" program: 

     x > 0 && true ==> (0 <= x && 0 == 0 * x)

   This gives rise to the following .smt2 file (available as
   "Square.dfy1.smt2") on the course website.

; Declare Constant x
(declare-const x Int)
; assert the negation of the verification condition:
(assert (not (=> (and (> x 0) true) (and (<= 0 x) (= 0 (* 0 x))))))
; ask z3 to check it
(check-sat)

    Read below for additional details on the SMT2 format.

    Your task is to create such a file given a Predicate p. We provide
    you with a simple IO handler that relies on a function

      toSMT :: Predicate -> String

    Your final project is to implement this function.  To implement
    this function, we have imported the pretty printing library we
    used in a previous homework. It is highly recommended that you
    mimic the organization of your pretty printers to facilitate
    debugging your code.  That said, you are welcome to use any part
    of the standard library that doesn't require editing the cabal
    file of the project. 

========================
Declaration of Constants 
========================

    The first part of the file is a series of constant declarations with
    the following syntax:

(declare-const <variable-name> <type>)

    Variable names are just strings, and for the purposes of this final
    project, you can assume that all variables that appear in a predicate
    are integers. To lift that assumption we would need to implement a type
    checker for Dafny, which we haven't done.

    Before you begin constructing the .smt2 file, you should calculate
    the variables that appear in a given predicate p, and create a
    declaration such as the one in the example for each one. We have
    imported the Data.Set library for you --- it is recommended that
    you use it, but again, you are welcome to design and implement
    this final project in any way you see fit.
   

==========
Assertions
==========

    The second part of the file is the negation of the verification condition
    where every operation is in prefix form. For example, given the predicate:

      (x > 0 && true) ==> (0 <= x && 0 == 0 * x)

    we will assert it's negation: 

      (assert (not (=> (and (> x 0) true) (and (<= 0 x) (= 0 (* 0 x))))))

    Each operation appears in parentheses before its arguments:
    For example:

           x > 0              translates to              (> x 0)
           0 * x              translates to              (* 0 x)
       false && true          translates to              (and false true)
           0 == x             translates to              (= 0 x)

    While this format makes for syntax that is hard for humans to
    read, you should find that it's much more suitable for being
    automatically generated recursively from the AST of an expression.

=========
Check SAT
=========
   
    The final part of your file should be a single call to check the
    satisfiability of the assertion you created above:

(check-sat)

    Z3 (and similar solvers) are capable of finding satisfying assignments
    for a plethora of formulas involving integer arithmetic, or returning
    "unsat" if such an assignment doesn't exist. That's why we check for
    the satisfiability of the negation of the verification condition: if
    z3 says that the negation cannot be satisfied, then we are guaranteed
    that it is a tautology that holds in all contexts.

-}


{-
  MY NOTES FOR THE IMPLEMENTATION:

  - based off of the z3 lecture, at a high level:
    1) i need to calculate the set of variables or constants i have; without this,
        z3 tweaks out 
    2) translate the predicate to a string -> refer to the pretty printer file
        (Printer.hs); if i use a type class (like PP in Printer.hs), and then
          translate everything (like uops like in Printer.hs), it will be way easier
          than manually doing all this
    3) try to use the Data.Set api from standard library; i can use anything;
        what i should do is add all variables/constants i see into a set,
        recursively use stuff like empty and insert and so on, and then iterate
        using a map or fold function (over the set)
  - it should not be that long; code shouldn't be like >80 lines of code so 
      i should be able to do this in a few hours, the implementation should
      not be that hard i just need to figure out how to be clever; i need to
      make sure that i basically "negate" the verification condition and 
      assert the negation as well

-}
module Z3 where

import Syntax
import Data.List(intersperse)
import Text.PrettyPrint ( (<+>), Doc )
import qualified Text.PrettyPrint as PP

import System.Process(readProcessWithExitCode)
import Data.Set(Set)
import qualified Data.Set as Set

-- this is the type class i need here; i go from a generic to a doc, just like Printer.hs
class ToZ3 a where
 toZ3Doc :: a -> Doc

-- now i need to get variables and constants recursively... 
getVars :: Predicate -> Set Name
getVars (Forall [] e) = getVarsExp e  -- just need to deal with empty 
getVars (PredOp p1 _ p2) = Set.union (getVars p1) (getVars p2) -- combine the two
getVars _ = Set.empty -- need to make sure i have the case where there's an empty set
-- making sure i deal with expressions instead of just predicates
getVarsExp :: Expression -> Set Name
getVarsExp (Val _) = Set.empty
getVarsExp (Var (Name n)) = Set.singleton n
getVarsExp (Op1 _ e) = getVarsExp e
getVarsExp (Op2 e1 _ e2) = Set.union (getVarsExp e1) (getVarsExp e2)
getVarsExp _ = Set.empty  -- again empty set, i don't care about arrays

-- now convert the expressions to z3
instance ToZ3 Expression where
 toZ3Doc (Val (IntVal i)) = PP.integer (toInteger i)
 toZ3Doc (Val (BoolVal b)) = PP.text (if b then "true" else "false")
 toZ3Doc (Var (Name n)) = PP.text n
 toZ3Doc (Op1 op e) = PP.parens $ toZ3Doc op <+> toZ3Doc e
 toZ3Doc (Op2 e1 op e2) = PP.parens $ toZ3Doc op <+> toZ3Doc e1 <+> toZ3Doc e2
 toZ3Doc _ = error "array not supported"

-- also convert predicates to z3
instance ToZ3 Predicate where
 toZ3Doc (Forall [] e) = toZ3Doc e
 toZ3Doc (PredOp p1 op p2) = PP.parens $ toZ3Doc op <+> toZ3Doc p1 <+> toZ3Doc p2
 toZ3Doc _ = error "only empty quantifier supported"

-- this is binary operations; idk if i did this right tho
instance ToZ3 Bop where
 toZ3Doc Plus = PP.char '+'
 toZ3Doc Minus = PP.char '-'
 toZ3Doc Times = PP.char '*'
 toZ3Doc Divide = PP.text "div"
 toZ3Doc Modulo = PP.text "mod"
 toZ3Doc Iff = PP.text "<=>"
 toZ3Doc Neq = PP.text "/="
 toZ3Doc Eq = PP.char '='
 toZ3Doc Lt = PP.char '<'
 toZ3Doc Le = PP.text "<="
 toZ3Doc Gt = PP.char '>'
 toZ3Doc Ge = PP.text ">="
 toZ3Doc Conj = PP.text "and"
 toZ3Doc Disj = PP.text "or"
 toZ3Doc Implies = PP.text "=>"

-- need to include unary operations as well
instance ToZ3 Uop where
 toZ3Doc Neg = PP.char '-'
 toZ3Doc Not = PP.text "not"
 toZ3Doc Len = PP.text ".Length"
 --toZ3Doc _ = error "array not supported"

-- this is the main function for project
toSMT :: Predicate -> String
toSMT p = PP.render $ PP.vcat [
 -- declare constants and variables; without this z3 messes up
 PP.vcat [PP.parens $ PP.text "declare-const" <+> PP.text v <+> PP.text "Int" 
         | v <- Set.toList (getVars p)],
 -- assert the negation here; if i don't negate then again z3 messes up
 PP.parens $ PP.text "assert" <+> PP.parens (PP.text "not" <+> toZ3Doc p),
 -- need to check sat, like in the lecture video
 PP.text "(check-sat)"
 ]

-- | The name of the z3 executable. Change this to whatever it is in your system:
--   In unix based systems, this is just "z3".
--   In Windows, it will be the name of the executable that was installed alongside Dafny.
z3 :: String
z3 = "z3"

-- | This function uses "toSMT" in order to write a file, and invoke z3 on it, checking its
--   output. You're welcome to modify this function as you see fit, the only thing we will
--   automatically test is your "toSMT" function.
convertAndCheck :: Predicate -> String -> IO Bool
convertAndCheck p fn = do
  writeFile fn (toSMT p)
  (_exitCode, stdout, _stderr) <- readProcessWithExitCode z3 [fn] ""
  case stdout of
    's':'a':'t':_ -> return False
    'u':'n':'s':'a':'t':_ -> return True
    _ -> error $ "Z3 output was neither sat or unsat: " ++ stdout