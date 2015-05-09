requires "modules/unification.k"
// /*!
// \title{OmgRofl}
// \author{Charlie Martell}
// \organization{CS 422, University of Illinois at Urbana-Champaign} */

// /*@ \section{Abstract}
// Omgrofl is an esoteric programming language created in 2006 by Juraj Borza. 
// It is equipped with a stack/queue, has support for byte-sized variables and 
// keywords resembling Internet slang. The name comes from combining the slang 
// "words" omg and rofl. Rofl is actually one of Omgrofl's commands.

// Hello World Program vv
// lol iz 72
// rofl lol
// lol iz 101
// rofl lol
// lol iz 108
// rofl lol
// rofl lol
// lool iz 111
// rofl lool
// loool iz 44
// rofl loool
// loool iz 32
// rofl loool
// loool iz 87
// rofl loool
// rofl lool
// lool iz 114
// rofl lool
// rofl lol
// lol iz 100
// rofl lol
// lol iz 33
// rofl lol
// stfu
// */
module OMGROFL-SYNTAX
  imports UNIFICATION 
  //imports BUILTIN-SYNTAX-HOOKS

 syntax Val ::= Int 

 syntax Stmt ::= Assignment
               // | "stfu                    [token]
               | Out 

 syntax Out ::= "rofl" Id               [print]

 syntax Assignment ::= Id "iz" Val

 syntax Stmts ::= Stmt
                > Stmts  Stmts              [left]

 //Need to rework regex to only take lo*l
 syntax Lol ::= Token{[a-z][a-zA-Z0-9\_]*}        [variable, onlyLabel, autoReject, token]

 syntax KItem ::= "newline" 

 syntax Sep ::= Sep "~> newline ~>" Stmt
              | Stmt      

 // rule S1:Sep S2:Stmt => S1 ~> newline ~> S2 [macro]
 rule ( X ) S:Stmt => X ~> newline ~> S

endmodule

module OMGROFL
  imports OMGROFL-SYNTAX

configuration <T color="magenta">
                <k color="green"> $PGM:Stmts </k>
                <state color="red"> .Map </state>
                <in stream="stdin" color="cyan"> .List </in>
                <out stream="stdout" color="blue"> .List </out>
              </T>

 /*@ \subsubsection{Assignment}
  The assigned variable is updated in the state.  The variable is expected
  to be declared, otherwise the semantics will get stuck.  At the same time,
 //  the assignment is dissolved. */

//------------Semantics for defining new variables and adds them to state------
 syntax KItem ::= "addId(" Id ")"

 rule <k> addId(X:Id) => . ...</k>
 <state>... (.Map => X|->0) ...</state>

 syntax KItem ::= "addIdValue(" Id "," Int ")"

 rule <k> addIdValue(X:Id, I:Int) => . ...</k>
 <state>... X |-> (_ => I) ...</state>

 rule <k> (X:Id iz I:Int):Assignment => addId(X) ~> addIdValue(X, I) ...</k>
      <state> Rho </state>  when notBool(X in keys(Rho))
 rule <k> (X:Id iz I:Int):Assignment => addIdValue(X, I) ...</k>
      <state> Rho </state>  when X in keys(Rho)  
//-----------------------------------------------------------------------------

//--------------------Printing to stdout---------------------------------------

 rule <k> rofl X:Id => . ...</k>
 <state>... X |-> I:Int ...</state>
 <out>... .List => ListItem(chrChar(I:Int)) </out>

  //  rule <k> print(V:Val, Es => Es)! ...</k> <out>... .List => ListItem(V) </out>
  //   [print]
  // rule print(.Vals)! => .  [structural]
//-----------------------------------------------------------------------------

//-------------Dirty trick for handing no newline delimiter--------------------
  rule <k> newline ~> X => X ...</k>
//-----------------------------------------------------------------------------

