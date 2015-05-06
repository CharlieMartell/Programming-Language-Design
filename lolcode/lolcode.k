require "modules/pattern-matching.k"
require "modules/unification.k"

/*!
\title{LOLCODE }
\author{Charlie Martell}
\organization{CS 422, University of Illinois at Urbana-Champaign} */

/*@ \section{Abstract}
LOLCODE is an esoteric programming language inspired by lolspeak, 
the language expressed in examples of the lolcat Internet meme.
The language was created in 2007 by Adam Lindsay, researcher at the 
Computing Department of Lancaster University.

The language is not clearly defined in terms of operator priorities 
and correct syntax, but several functioning interpreters and compilers 
already exist. One interpretation of the language has been proven 
Turing-complete.

LOLCODE's keywords are drawn from the heavily compressed (shortened) 
patois of the lolcat Internet meme. Here follows a Hello world program 
and a simple program to output a file to a monitor. Similar code was printed 
in the Houston Chronicle.

HAI
CAN HAS STDIO?
VISIBLE "HAI WORLD!"
KTHXBYE*/


module LOLCODE-SYNTAX
imports BUILTIN-SYNTAX-HOOKS

/*@ \section{Syntax}
This section defines the syntax of LOLCODE.*/
 syntax ProgramStart  ::= "HAI" CodeBlock "KTHXBAI"

 syntax CodeBlock     ::=  Statement 
                        |  Statement CodeBlock
  
 syntax Statement     ::= Statement Statement 
                        | Declaration ";"
                        //| Loop 
                        // | Comment ";)"
                        | PrintBlock  ";"
                        // | IfBlock ";)"
                        | InputBlock ";"
                        // | FuncDecl ";)"
                        // | Assignment ";)"
                        // | Exp ";)"
  
 // syntax Loop          ::= "IM IN YR" Label "WILE" Exp CodeBlock
 //                        | "IM OUTTA YR" Label
  
 syntax Declaration   ::= "I HAS A" Label
                        // | "I HAS A" Label "ITZ" Value


 syntax Label         ::= Token{[a-z][\_a-zA-Z0-9]*}       [notInRules, autoReject, token, regex("[a-z][\\_a-zA-Z0-9]*")]

 syntax Value         ::= Int
                        | Bool
                        | String 

 // syntax Comment       ::= "BTW" String
 //                        | "OBTW" String "TLDR"
  
  syntax PrintBlock    ::= "VISIBLE" Exps "MKAY?"
  
 // syntax IfBlock       ::= "O RLY?" "YA RLY" CodeBlock "OIC"
 //                        | "O RLY?" "YA RLY" CodeBlock ElseIfBlock

 // syntax ElseIfBlock   ::= "MEBBE" Exp CodeBlock ElseIfBlock
 //                        | "NO WAI" CodeBlock
 //                        | "MEBBE" Exp CodeBlock

 syntax InputBlock    ::= "GIMMEH" String 

// //No Param, One Param, Two Param
//  syntax FuncDecl      ::= "HOW DUZ I" Label CodeBlock "IF U SAY SO"
//                         | "HOW DUZ I" Label "YR" Label CodeBlock "IF U SAY SO"
//                         | "HOW DUZ I" Label "YR" Label "AN YR" Label CodeBlock "IF U SAY SO"

 syntax Assignment    ::= Label "R" Exp                         [strict]

 syntax Exps          ::= List{Exp,","}          [strict]  // automatically hybrid now

 syntax Exp           ::= Value
                        // | "BOTH SAEM" Exp "AN" Exp    [strict]
                        // | "BOTH OF" Exp "AN" Exp      [strict]
                        // | "EITHER OF" Exp "AN" Exp    [strict]
                        // | "BIGGR OF" Exp "AN" Exp     [strict]
                        // | "SMALLR OF" Exp "AN" Exp    [strict]
                        // | "SUM OF" Exp "AN" Exp       [strict]
                        // | "DIFF OF" Exp "AN" Exp      [strict]
                        // | "PRODUKT OF" Exp "AN" Exp   [strict]
                        // | "QUOSHUNT OF" Exp "AN" Exp  [strict]
                        // | "MOD OF" Exp "AN" Exp       [strict]
                        // | "MAEK" Exp "A" Type                [strict]
                        // | "NOT" Exp                          [strict]
//                         | Token{[a-z][\_a-zA-Z0-9]*}       [notInRules, autoReject, token]
//                         | WIN | FAIL | NOOB | (0-9)* | (0-9)*.(0-9)* | "string"
//                         | any character string
//                         | tbd


// rule <k> "I HAS A" X:Id "ITZ" E:Exp; => "I HAS A" X; X "R" E; ...</k> [macro]

endmodule


module LOLCODE
  imports LOLCODE-SYNTAX

  /*@ \section{Basic Semantic Infrastructure}
  Before one starts adding semantic rules to a \K definition, one needs to
  define the basic semantic infrastructure consisting of definitions for
  {\em values} and {\em configuration}.  As discussed in the definitions
  in the \K tutorial, the values are needed to know when to stop applying
  the heating rules and when to start applying the cooling rules corresponding
  to strictness or context declarations.  The configuration serves as a backbone
  for the process of configuration abstraction which allows users to only
  mention the relevant cells in each semantic rule, the rest of the configuration
  context being inferred automatically.  Although in some cases the configuration
  could be automatically inferred from the rules, we believe that it is very
  useful for language designers/semanticists to actually think of and design
  their configuration explicitly, so the current implementation of \K requires
  one to define it. */
  
  /*@ \subsection{Values}
  We here define the values of the language that the various fragments of
  programs evaluate to.  First, integers and Booleans are values.  As discussed,
  arrays evaluate to special array reference values holding (1) a location from
  where the array's elements are contiguously allocated in the store, and
  (2) the size of the array.  Functions evaluate to function values as
  $\lambda$-abstractions (we do not need to evaluate functions to closures
  because each function is executed in the fixed global environment and
  function definitions cannot be nested).  Like in IMP and other
  languages, we finally tell the tool that values are \K results. */

  syntax Val ::= Int | Bool | String | loc(Int)
  // syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  // syntax KResult ::= Val

  configuration <T color="red">
                  <k color="green"> ($PGM:ProgramStart) </k>
                  //<genv color="pink"> .Map </genv>
                  //<store color="white"> .Map </store>
                  <br/>
                  <env color="violet"> .Map </env>
                  <store color="white"> .Map </store>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>

  rule <k> HAI CB:CodeBlock KTHXBAI => CB ...</k>

  syntax KItem ::= "undefined"  [latex(\bot)]

  

  rule <k> I HAS A X:Label; => . ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> undefined ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

  // rule <k> X:Id R E:Exp => E ...<k>

//---------------------PRINT LINE----------------------------
  rule <k> VISIBILE E:Exps => . ...</k> <out>... .List => ListItem(E) </out>
    [print]
  // rule VISIBILE .Vals; => .  [structural]
//-----------------------------------------------------------

//------------------LVALUE AND LOOKUP-----------------------
  syntax Exp ::= lvalue(K)

  rule <k> lvalue(X:Id => loc(L)) ...</k> <env>... X |-> L:Int ...</env>
    [structural]

  // context lvalue(_:>Exp[HOLE:>Exps])
  // context lvalue(HOLE:>Exp[_:>Exps])

  rule lvalue(lookup(L:Int) => loc(L))  [structural]

   syntax KItem ::= lookup(Int)
  rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]
//-----------------------------------------------------------

endmodule
