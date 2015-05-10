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



 syntax Stmt ::= Exp
               | "rofl" Exp               [print]
               | "sftw" Id                [read]
               | "wtf" Exp Stmts "brb" [strict(1)]
               | "4" Exp "iz" Exp "2lmfao" Exp Stmts "ayylmao" [strict(3)]
               | "rtfm" Stmts "brb"

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
                      | "lmao" Exp 
                      | Bool  


 syntax Stmts ::= Stmt
                > Stmts  Stmts              [left]

 //Need to rework regex to only take lo*l
 syntax Lol ::= Token{[a-z][a-zA-Z0-9\_]*}        [variable, onlyLabel, autoReject, token]

 syntax KItem ::= "debug" | "newline" 


endmodule

module OMGROFL
  imports OMGROFL-SYNTAX

  syntax Val ::= Int | Bool
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

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
  rule <k> 4 E1:Exp iz E2:Exp 2lmfao I:Int S:Stmts ayylmao =>
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
 //TODO
//-----------------------------------------------------------------------------

//---------------------------------Increment-----------------------------------
  rule <k> lmao L:Id => . ...</k>
       <state>... L |-> (I => I +Int 1) ...</state>  [increment]
//-----------------------------------------------------------------------------

//--------------------------------Lookup---------------------------------------
  rule <k> X:Id => V ...</k>
       <state>... X |-> V:Val ...</state> [lookup]
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

 rule <k> sftw X:Id => addId(X) ~> addIdValue(X, In) ...</k>
      <in> ListItem(In:Int) => .List ...</in> 
//-----------------------------------------------------------------------------

//-------------Dirty trick for handing no newline delimiter--------------------
  rule ( X ) S:Stmt => X ~> newline ~> S
  rule <k> newline ~> X => X ...</k>
//-----------------------------------------------------------------------------
endmodule