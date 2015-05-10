requires "modules/unification.k"
/*!
\setlength{\parindent}{1em}
\title{OmgRofl}
\author{Charlie Martell}
\organization{CS 422, University of Illinois at Urbana-Champaign} */

/*@ \section{Abstract}
Omgrofl is an esoteric programming language created in 2006 by Juraj Borza. 
It is equipped with a stack/queue, has support for byte-sized variables and 
keywords resembling Internet slang. The name comes from combining the slang 
"words" omg and rofl. Rofl is actually one of Omgrofl's commands.
*/
module OMGROFL-SYNTAX
/*@ \section{Syntax}
This module defines the syntax of OmgRofl\@.
The Semantic Constructs are as follows 
wtf condition – is a conditional statement (like if in C).
rtfm – begins a loop.
4 variable iz initial-value 2 end-value - begins a "for" loop.
stfw x – reads a value into x. A byte character is read from standard input, 
and its value is stored into x, like in brainfuck.
rofl x – prints out the value of x as a byte character. Also like in brainfuck.
n00b x – pushes x onto the stack / enqueues x.
l33t x – pops a value from the stack and stores it into x. 
If the stack/queue is empty, 0 is stored into x.
haxor x - dequeues a value. If the stack/queue is empty, 0 is stored into x.
stfu – exits application immediately. It is unnecessary at the end of the program, 
use it only when you want to terminate the execution of the program in another place 
(like exit in C.)
brb – serves as end in Pascal, } in C. See wtf or rtfm.
variable iz x – is assignment – like = in C.
lmao x – increments x by one.
lulz x – decrements value of x by one.
*/

 syntax Stmt ::= Exp
               | "lmao" Exp
               | "lulz" Exp             
               | "stfw" Id                [read]
               | "wtf" Exp Stmts "brb" [strict(1)]
               | "4" Exp "iz" Exp "2lmfao" Exp Stmts "brb" [strict(3)]
               | Loop
               | "tldr"
               | "n00b" Exp [strict]             
               | "l33t" Id                
               | "haxor" Id  
               | "stfu" 
               | Exp "to" "/dev/null"
               | "rofl" Exp               [print]                      
 
 syntax Loop ::= "rtfm" Stmts "brb"

 syntax Assignment ::= Exp "iz" Exp   [strict(2)]

 syntax Exp ::= Int 
              | Id 
              | Bool
              | Conditional
              | Assignment

 syntax Conditional ::= Exp "iz" "liek" Exp           [strict(1)]
                      | Exp "nope" "iz" "liek" Exp    [strict(1)]
                      | Exp "iz" "uber" Exp           [strict(1)]
                      | Exp "nope" "iz" "uber" Exp    [strict(1)]
                      | Bool  


 syntax Stmts ::= Stmt
                > Stmts  Stmts              [left]

 //Need to rework regex to only take lo*l
 syntax Lol ::= Token{[a-z][a-zA-Z0-9\_]*}        [variable, onlyLabel, autoReject, token]

 syntax KItem ::= "newline" 

 rule E:Exp to /dev/null => E iz 0 [macro]

endmodule

module OMGROFL
  imports OMGROFL-SYNTAX
  imports UNIFICATION
/*@ \section{Semantics}
This module defines the semantics of OmgRofl\@.
Before you start adding semantic rules to a \K definition, you need to
define the basic semantic infrastructure consisting of definitions for
{\em results} and the {\em configuration}.  */

  syntax Val ::= Int | Bool
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

/*@ The configuration variable $\${\it PGM}$ tells the \K tool where to
place the program.  More precisely, the command
``\texttt{krun program}'' parses the program and places the resulting
\K abstract syntax tree in the \textsf{k} cell before invoking the
semantic rules described in the sequel.  The ``$\kdot$'' in the
\textsf{state} cell, written \texttt{.Map} in ASCII in the
\texttt{imp.k} file, is \K's way to say ``nothing''.  Technically, it
is a constant which is the unit, or identity, of all maps in \K
(similar dot units exist for other \K structures, such as lists, sets,
multi-sets, etc.).  */
configuration <T color="magenta">
                <k color="green"> $PGM:Stmts </k>
                <state color="red"> .Map </state>
                <in stream="stdin" color="cyan"> .List </in>
                <out stream="stdout" color="blue"> .List </out>
                <stack color="purple"> .List </stack>
              </T>


//------------Semantics for defining new variables and adds them to state------
 syntax KItem ::= "addId(" Id ")"

 rule <k> addId(X:Id) => . ...</k>
  <state>... (.Map => X|->0) ...</state>

 syntax KItem ::= "addIdValue""(" Id "," Exp ")" [strict(2)]

 rule <k> addIdValue(X:Id, I:Int) => . ...</k>
 <state>... X |-> (_ => I) ...</state>

 rule <k> (X:Id iz I:Id) => addId(X) ~> addIdValue(X, I) ...</k>
      <state> Rho </state>  when notBool(X in keys(Rho))

 rule <k> (X:Id iz I:Int) => addId(X) ~> addIdValue(X, I) ...</k>
      <state> Rho </state>  when notBool(X in keys(Rho))
 rule <k> (X:Id iz I:Int) => addIdValue(X, I) ...</k>
      <state> Rho </state>  when X in keys(Rho)
//-----------------------------------------------------------------------------

//------------------------------For Loop---------------------------------------
  syntax KItem ::= "while" "(" Exp "nope" "iz" "liek" Exp ")" "{" Stmts "}"
  rule <k> 4 E1:Exp iz E2:Exp 2lmfao I:Int S:Stmts brb =>
          E1 iz E2 ~> while(E1 nope iz liek I){S} ...</k>

  rule <k> while(V1:Exp nope iz liek V2:Exp) {S} 
          => S ~> newline ~> while(V1 nope iz liek V2) {S} ...</k>
      <state> V1 |-> X </state>
      when (X =/=K V2)

    rule <k> while(V1:Exp nope iz liek V2:Exp) {S} => . ...</k>
      <state> V1 |-> X </state>
      when (X ==K V2)
//-----------------------------------------------------------------------------

//-------------------------------Loop------------------------------------------
 rule <k> rtfm Ss:Stmts brb => Ss ~> rtfm Ss brb ...</k>
 rule <k> tldr ~> X:Loop => . ...</k>
 rule <k> tldr ~> X ~> Z => tldr ~> Z ...</k>
//-----------------------------------------------------------------------------

//---------------------------------Increment-----------------------------------
  rule <k> lmao L:Id => . ...</k>
       <state>... L |-> (I => I +Int 1) ...</state>  [increment]
//-----------------------------------------------------------------------------

//---------------------------------Decrement-----------------------------------
  rule <k> lulz L:Id => . ...</k>
       <state>... L |-> (I => I -Int 1) ...</state>  [increment]
//-----------------------------------------------------------------------------

//---------------------------------End-----------------------------------------
 rule <k> stfu ~> _ => stfu ...</k>
 rule <k> stfu => . </k>
//-----------------------------------------------------------------------------

//--------------------------------Lookup---------------------------------------
  rule <k> X:Id => V ...</k>
       <state>... X |-> V:Val ...</state> [lookup]
//-----------------------------------------------------------------------------

//----------------------------Stack/Queue Operations---------------------------
  rule <k> n00b E:Int => . ...</k>
       <stack> .List => ListItem(E) ...</stack>

  rule <k> l33t X:Id => addId(X) ~> addIdValue(X, E:Int) ...</k>
       <stack> ListItem(E) => .List ...</stack>
       <state> Rho </state>
       when notBool(X in keys(Rho))

  rule <k> l33t X:Id => addIdValue(X, E:Int) ...</k>
       <stack> ListItem(E) => .List ...</stack>
       <state> Rho </state>
       when X in keys(Rho)

  rule <k> haxor X:Id => addId(X) ~> addIdValue(X, E) ...</k>
       <stack>... ListItem(E) => .List </stack>
       <state> Rho </state>
       when notBool(X in keys(Rho))

  rule <k> haxor X:Id => addIdValue(X, E) ...</k>
       <stack>... ListItem(E) => .List </stack>
       <state> Rho </state>
       when X in keys(Rho)
//-----------------------------------------------------------------------------

//----------------------------Conditionals-------------------------------------
 rule wtf true S:Stmts brb => S
 rule wtf false S:Stmts brb => .
 rule V1:Val iz liek V2:Val => V1 ==K V2
 rule V1:Val nope iz liek V2:Val => V1 =/=K V2
 rule V1:Int iz uber V2:Int => V1 >Int V2
 rule V1:Int nope iz uber V2:Int => V1 <=Int V2
//-----------------------------------------------------------------------------

//----------------------------------IO-----------------------------------------
 rule <k> rofl X:Id => . ...</k>
      <state>... X |-> I:Int ...</state>
      <out>... .List => ListItem(chrChar(I:Int)) </out>
 rule <k> rofl X:Int => . ...</k>
      <out>... .List => ListItem(chrChar(X:Int)) </out>

 rule <k> stfw X:Id => addId(X) ~> addIdValue(X, In) ...</k>
      <in> ListItem(In:Int) => .List ...</in> 
//-----------------------------------------------------------------------------

//-------------Dirty trick for handing no newline delimiter--------------------
  rule ( X ) S:Stmt => X ~> newline ~> S
  rule <k> newline ~> X => X ...</k>
//-----------------------------------------------------------------------------
endmodule