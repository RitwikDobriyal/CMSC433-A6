{- | A Parser for MiniDafny
     ======================

Name: Ritwik Dobriyal
Assignment #3
CMSC433, Spring 2025 - Section 0101
NOTE: The testing I've done for this project was done with stack ghci; 
I did not include test cases in the project file itself. 

For this problem, you will implement a parser for the Lu programming language.

-}

module Parser where

{- |

Make sure that you read the [`Syntax`](Syntax.html) module that describes
the syntax of MiniDafny before continuing.

This problem also uses definitions from the Parsers module from the lecture
notes, gathered together in the module [`Parser.hs`](Parser.hs). Operations
such as `chainl1` and `filter` are imported as `P.chainl1` and `P.filter`.
You should also familiarize yourself with this module before continuing.

The goal of this part of the exercise is to give you practice with the
operations in the `Control.Applicative` library. As a result the `Parser`
type is *not* given a monad instance, so you will not be able use `do`
notation with it. Furthermore, you may not edit the `Parser` module, and you
do not have access to the constructor for the `Parser` type, so you will not
be able to define your own monad instance either. 

-}

import Control.Applicative
import qualified Data.Char as Char
import Syntax
import Printer
import ParserLib (Parser)
import qualified ParserLib as P
import Test.HUnit  (runTestTT,Test(..),Assertion, (~?=), (~:), assert, Counts)

{- | Testing your Parser
      ------------------

Your primary method of testing your parser should be using the following properties, though you will also
want to define your own unit tests as you go.

In particular, the following "round tripping" properties should be satisfied
 by your implementation. These properties state that given an arbitrary
 Value/Expression/Statement, if we pretty print it 

-}

prop_roundtrip_val :: Value -> Bool
prop_roundtrip_val v = P.parse valueP (pretty v) == Right v

prop_roundtrip_exp :: Expression -> Bool
prop_roundtrip_exp e = P.parse expP (pretty e) == Right e

prop_roundtrip_stat :: Statement -> Bool
prop_roundtrip_stat s = P.parse statementP (pretty s) == Right s

{- | More Parser combinators
     -----------------------

As a warm-up, let's define a few helper functions that we can use later.

In general, so that our parsers are flexible about spaces that appear in
source programs, all of the parsers will need to skip over any trailing white
space.

First, define a parser combinator which takes a parser, runs it,
then skips over any whitespace characters occurring afterwards. HINT: you'll
need the `space` parser from the [Parser](Parser.hs) library.

-}

wsP :: Parser a -> Parser a
wsP p = p <* many P.space

test_wsP :: Test
test_wsP = TestList [
  P.parse (wsP P.alpha) "a" ~?= Right 'a',
  P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc"
  ]

{- |
Use this to define a parser that accepts *only* a particular string `s`
and consumes any white space that follows. The last test case ensures
that trailing whitespace is being treated appropriately.
-}

stringP :: String -> Parser ()
stringP s = wsP (P.string s) *> pure () -- can't use hlint b/c it will import

test_stringP :: Test
test_stringP = TestList [
  P.parse (stringP "a") "a" ~?= Right (),
  P.parse (stringP "a") "b" ~?= Left "No parses",
  P.parse (many (stringP "a")) "a  a" ~?= Right [(),()]
  ]

-- | Define a parser that will accept a particular string `s`, returning a
-- | given value `x`, and also and consume any white space that follows.

constP :: String -> a -> Parser a
constP s x = wsP (P.string s) *> pure x

test_constP :: Test
test_constP = TestList [
  P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
  P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa"
  ]

-- | We will also use `stringP` for some useful operations that parse between
-- | delimiters, consuming additional whitespace.

parens :: Parser a -> Parser a
parens x = P.between (stringP "(") x (stringP ")")

braces :: Parser a -> Parser a
braces x = P.between (stringP "{") x (stringP "}")

-- >>> P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]"
-- Right [1,1,1]
brackets :: Parser a -> Parser a
brackets x = P.between (stringP "[") x (stringP "]")



{- | Parsing Constants
     -----------------

Now let's write parsers for the `Value` type, except for table constants
(which we won't parse).

-}

valueP :: Parser Value
valueP = intValP <|> boolValP

-- | To do so, fill in the implementation of the four parsers above. As above, these
--   four parsers should consume any following whitespace. You can make sure that happens
--   by testing 'many' uses of the parser in a row.

-- >>> P.parse (many intValP) "1 2\n 3"
-- Right [IntVal 1,IntVal 2,IntVal 3]
intValP :: Parser Value
intValP = IntVal <$> wsP P.int

-- >>> P.parse (many boolValP) "true false\n true"
-- Right [BoolVal True,BoolVal False,BoolVal True]
boolValP :: Parser Value
boolValP = BoolVal <$> (constP "true" True <|> constP "false" False)

-- | At this point you should be able to run tests using the `prop_roundtrip_val` property. 

{- | Parsing Types
     -------------

We provide you with the parser for types, which for miniDafny can only be "int", "bool", or "array<int>".

-}

typeP :: Parser Type
typeP = constP "int" TInt <|> constP "bool" TBool <|> constP "array<int>" TArrayInt

{- | Parsing Expressions
     -------------------

Next, let's parse some Mini Dafny expressions.

We've already stratified the grammar for you, so that we'll get the
appropriate precedence and associativity for the binary and unary
operators. Make sure to read the end of the parsers lecture to understand how
this code works.

However, this code *won't* work until you complete all the parts of this section.
-}

expP :: Parser Expression
expP    = conjP where
  conjP   = compP `P.chainl1` opAtLevel (level Conj)
  compP   = catP `P.chainl1` opAtLevel (level Gt)
  catP    = sumP `P.chainl1` opAtLevel (level Eq)
  sumP    = prodP `P.chainl1` opAtLevel (level Plus)
  prodP   = uopexpP `P.chainl1` opAtLevel (level Times)
  uopexpP = baseP
      <|> Op1 <$> uopP <*> uopexpP
  baseP = lenP
       <|> Var <$> varP
       <|> parens expP
       <|> Val <$> valueP
      -- .Length here

-- | Parse an operator at a specified precedence level
opAtLevel :: Int -> Parser (Expression -> Expression -> Expression)
opAtLevel l = flip Op2 <$> P.filter (\x -> level x == l) bopP

-- | A variable is a prefix followed by array indexing or ".Length" or just a name.
-- | We've also done this one for you.

-- >>>  P.parse (many varP) "x y z"
-- Right [Name "x", Name "y", Name "z"]
-- >>> P.parse varP "y[1]"
-- Right (Proj "y" (Val (IntVal 1)))
varP :: Parser Var
varP = (Proj <$> nameP <*> brackets expP) <|> (Name <$> nameP)

lenP :: Parser Expression
lenP = (Op1 Len . Var . Name) <$> (nameP <* stringP ".Length")

{- | 
Define an expression parser for names. Names can be any sequence of upper and
lowercase letters, digits and underscores, not beginning with a digit and not
being a reserved word. Your parser should also consume any trailing
whitespace characters.
-}

reserved :: [String]
reserved = [ "assert", "break","else","Length"
 ,"false","for","function","invariant","if","in"
 ,"return","true","method","int", "bool"
 ,"while", "requires","ensures", "forall"]

-- >>> P.parse (many nameP) "x sfds _ int"
-- Right ["x","sfds", "_"]
-- NOTE: need to factor in reserved keywords and filter them out
nameP :: Parser Name
nameP = wsP $ P.filter
     (`notElem` reserved)
     ((:) -- using cons operator to factor in head and rest of list
      <$> P.satisfy (\c -> Char.isAlpha c || c == '_')
      <*> many (P.satisfy (\c -> Char.isAlphaNum c || c == '_')))

-- Now write parsers for the unary and binary operators. Make sure you
--  check out the Syntax module for the list of all possible
--  operators. The tests are not exhaustive.

-- >>> P.parse (many uopP) "- - !"
-- Right [Neg,Neg,Not]
uopP :: Parser Uop
uopP = wsP $ P.choice [
     constP "-" Neg,
     constP "!" Not,
     constP ".Length" Len
     ]

-- >>> P.parse (many bopP) "+ >= &&"
-- Right [Plus,Ge,Conj]
-- NOTE: going from longer characters to shorter characters to avoid 
-- partial matches
bopP :: Parser Bop
bopP = wsP $ P.choice [
     constP "<==>" Iff,
     constP "==>" Implies,
     constP "&&" Conj,
     constP "||" Disj,
     constP "==" Eq,
     constP "!=" Neq,
     constP ">=" Ge,
     constP "<=" Le,
     constP "+" Plus,
     constP "-" Minus,
     constP "*" Times,
     constP "/" Divide,
     constP "%" Modulo,
     constP ">" Gt,
     constP "<" Lt
     ]

-- | At this point you should be able to test the  `prop_roundtrip_exp` property.

{- | Parsing Statements
     ------------------

First, define a parser for bindings... 

-}

bindingP :: Parser Binding
bindingP = wsP $ (,) <$> nameP <*> (stringP ":" *> typeP)

-- | ...and predicates...
-- as stated by prof in discord, try to evaluate as forall and if that fails 
-- evaluate as predop
predicateP :: Parser Predicate
predicateP = forallP <|> predOpP
  where
    -- handle forall case 
    forallP = Forall
      <$> (stringP "forall" *> 
          wsP (P.sepBy bindingP (stringP ",") <* stringP "::"))
      <*> expP
    -- then i need to handle predicate operations; using chainl1
    predOpP = iffP
      where
        iffP = impliesP `P.chainl1` predOpPrecedence (level Iff)
        impliesP = conjP `P.chainl1` predOpPrecedence (level Implies)
        conjP = disjP `P.chainl1` predOpPrecedence (level Conj)
        disjP = compP `P.chainl1` predOpPrecedence (level Disj)
        compP = baseP `P.chainl1` predOpPrecedence (level Eq)
         <|> baseP `P.chainl1` predOpPrecedence (level Ge)
         <|> baseP `P.chainl1` predOpPrecedence (level Le)
         <|> baseP `P.chainl1` predOpPrecedence (level Gt)
         <|> baseP `P.chainl1` predOpPrecedence (level Lt)
        baseP = parens predOpP
         <|> forallP 
         <|> (Forall [] <$> expP)
    -- need to factor in precedence for operators too; using flip and filter
    predOpPrecedence l = wsP $ flip PredOp
      <$> P.filter (\x -> level x == l) bopP

-- | Finally, define a parser for statements:
-- NOTE: need to factor in decl, assign, if, and while cases + whitespace
-- NOTE: syntax for while case is different than syntax in program (invariant is 
-- flipped to expression)
statementP :: Parser Statement
statementP = wsP $ P.choice [
     Decl <$> (stringP "var" *> wsP bindingP) <*> 
          (stringP ":=" *> expP <* stringP ";"),
     Assign <$> varP <*> (stringP ":=" *> expP <* stringP ";"),
     If <$> (wsP (stringP "if") *> expP)
          <*> blockP
          <*> ((wsP (stringP "else") *> blockP) <|> pure (Block [])),
    --While <$> (wsP (stringP "while") *> wsP invariantP)
     --     <*> wsP expP
     --     <*> blockP
     flip While <$> (wsP (stringP "while") *> wsP expP)  
          <*> ((wsP (stringP "invariant") *> wsP predicateP) <|> 
               pure (Forall [] (Val (BoolVal True)))) 
          <*> blockP  
  ]


invariantP :: Parser Predicate
invariantP = (stringP "invariant" *> predicateP) <|> 
     pure (Forall [] (Val (BoolVal True)))

-- | ... and one for blocks.

blockP :: Parser Block
blockP = wsP $ Block <$> braces (many statementP <|> pure [])

{- | Parsing Methods
     ---------------

   Implement parsing for methods. You will probably want to modularize it
   by implementing parsing for specifications and many bindings.

-}


methodP :: Parser Method
methodP = Method
  <$> (wsP (stringP "method") *> wsP nameP)
  <*> wsP (parens (P.sepBy bindingP (stringP ",") <|> pure [])) 
  <*> (wsP (stringP "returns") *> wsP (parens (P.sepBy bindingP (stringP ",") 
     <|> pure [])) <|> pure []) 
  <*> many ((Requires <$> (wsP (stringP "requires") *> predicateP)) 
     <|> (Ensures <$> (wsP (stringP "ensures") *> predicateP)))
  <*> wsP blockP


{- | Parsing Expressions and Files
     -----------------------------

Finally, we'll export these convenience functions for calling
the parser.

-}

parseDafnyExp :: String -> Either P.ParseError Expression
parseDafnyExp = P.parse expP

parseDafnyStat :: String -> Either P.ParseError Statement
parseDafnyStat = P.parse statementP

parseDafnyFile :: String -> IO (Either P.ParseError Method)
parseDafnyFile = P.parseFromFile (const <$> methodP <*> P.eof)

{- File-based tests
   ----------------
-}

--tParseFiles :: Test
--tParseFiles = "parse files" ~: TestList [
--                 "min"  ~: p "dafny/Min.dfy"  wMin,
--                 "minVal"  ~: p "dafny/findMinVal.dfy"  wMinVal,
--                 "minIndex"  ~: p "dafny/findMinIndex.dfy"  wMinIndex,                 
--                 "minMax"   ~: p "dafny/minMax.dfy"   wMinMax,
--                 "arraySpec" ~: p "dafny/arraySpec.dfy" wArraySpec
--               ] where
--   p fn ast = do
--     result <- parseDafnyFile fn
--     case result of
--       (Left _) -> assert False
--       (Right ast') -> assert (ast == ast')

{- | Unit Tests
      ---------

These unit tests summarize the tests given above.
-}

test_comb = "parsing combinators" ~: TestList [
 P.parse (wsP P.alpha) "a" ~?= Right 'a',
 P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc",
 P.parse (stringP "a") "a" ~?= Right (),
 P.parse (stringP "a") "b" ~?= Left "No parses",
 P.parse (many (stringP "a")) "a  a" ~?= Right [(),()],
 P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
 P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa",
 P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]" ~?= Right [1,1,1]
 ]

test_value = "parsing values" ~: TestList [
 P.parse (many intValP) "1 2\n 3" ~?= Right [IntVal 1,IntVal 2,IntVal 3],
 P.parse (many boolValP) "true false\n true" ~?= Right [BoolVal True,BoolVal False,BoolVal True]
 ]

test_exp = "parsing expressions" ~: TestList [
 P.parse (many varP) "x y z" ~?= Right [Name "x", Name "y", Name "z"],
 P.parse (many nameP) "x sfds _" ~?= Right ["x","sfds", "_"],
 P.parse (many uopP) "- -" ~?=  Right [Neg,Neg],
 P.parse (many bopP) "+ >= .." ~?= Right [Plus,Ge]
 ]

test_stat = "parsing statements" ~: TestList [
 P.parse statementP "x := 3;" ~?= Right (Assign (Name "x") (Val (IntVal 3))),
 P.parse statementP "if x { y := true; }" ~?=
    Right (If (Var (Name "x")) (Block [Assign (Name "y") (Val $ BoolVal True)]) (Block [])),
 P.parse statementP "while 0 { }" ~?=
    Right (While (Forall [] (Val (BoolVal True))) (Val (IntVal 0)) (Block []))
   ]

-- | Testing summary
--------------------

test_all :: IO Counts
test_all = runTestTT $ TestList [ test_comb, test_value, test_exp, test_stat] -- tParseFiles ]

