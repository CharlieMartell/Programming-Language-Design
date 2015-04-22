
/*!
\title{OmgRofl}
\author{Charlie Martell}
\organization{CS 422, University of Illinois at Urbana-Champaign} */

/*@ \section{Abstract}
Omgrofl is an esoteric programming language created in 2006 by Juraj Borza. 
It is equipped with a stack/queue, has support for byte-sized variables and 
keywords resembling Internet slang. The name comes from combining the slang 
"words" omg and rofl. Rofl is actually one of Omgrofl's commands.

Hello World Program vv
lol iz 72
rofl lol
lol iz 101
rofl lol
lol iz 108
rofl lol
rofl lol
lool iz 111
rofl lool
loool iz 44
rofl loool
loool iz 32
rofl loool
loool iz 87
rofl loool
rofl lool
lool iz 114
rofl lool
rofl lol
lol iz 100
rofl lol
lol iz 33
rofl lol
stfu
*/
module OMGROFL-SYNTAX
  //imports BUILTIN-SYNTAX-HOOKS

  syntax Stmt ::= Id "iz" Int "!"                 
               | "rofl" Id "!"

  syntax Stmts ::= Stmt 
                 | Stmts Stmts 


endmodule

module OMGROFL
  imports OMGROFL-SYNTAX

configuration <T>
              <k> $PGM:Stmts </k>
                <state color="red"> .Map </state>
                <in stream="stdin"> .List </in>
                <out stream="stdout"> .List </out>
              </T>

 /*@ \subsubsection{Assignment}
  The assigned variable is updated in the state.  The variable is expected
  to be declared, otherwise the semantics will get stuck.  At the same time,
 //  the assignment is dissolved. */
 // rule <k> X:Id iz I:Int ! => . ...</k>
 // <state> Rho:Map (.Map => X |-> 0) </state>
 //    when notBool (X in keys(Rho))

 rule <k> X:Id iz I:Int! => . ...</k>
 <state>... X |-> (_ => I) ...</state>

 rule <k> rofl X:Id! => . ...</k>
 <state>... X |-> I ...</state>
 // <out> .List => ListItem(chrChar(I)) </out>

 // rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
 //    when notBool (X in keys(Rho))
 //  rule int .Ids; S => S  [structural]

 // rule <k> stfu ! => . ...</k>

endmodule
