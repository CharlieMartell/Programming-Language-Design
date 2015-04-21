module SIMPLE-LOLCODE-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

  syntax Id ::= "main" [token]

  syntax Decl ::= IHASA Exps ";"
                | "function" Id "(" Ids ")" Block

  syntax IHASA ::= "I HAS A"

  syntax Exp ::= Int | Bool | String | Id
               | "(" Exp ")"             [bracket]
               | "++" Exp
               > Exp "[" Exps "]"        [strict]
               > Exp "(" Exps ")"        [strict]
               | "-" Exp                 [strict]
               | "sizeOf" "(" Exp ")"    [strict]
               | "read" "(" ")"
               > left:
                 Exp "*" Exp             [strict, left]
               | Exp "/" Exp             [strict, left]
               | Exp "%" Exp             [strict, left]
               > left:
                 Exp "+" Exp             [strict, left]
               | Exp "-" Exp             [strict, left]
               > non-assoc:
                 Exp "<" Exp             [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               | Exp "!=" Exp            [strict, non-assoc]
               > "!" Exp                 [strict]
               > left:
                 Exp "&&" Exp            [strict(1), left]
               | Exp "||" Exp            [strict(1), left]
               > "spawn" Block
               > Exp "=" Exp             [strict(2), right]

  syntax Ids  ::= List{Id,","}
  syntax Exps ::= List{Exp,","}          [strict]  

  syntax Block ::= "{" "}"
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
                | "for" "(" Stmts Exp ";" Exp ")" Block
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [strict]
                | "try" Block "catch" "(" Id ")" Block
                | "throw" Exp ";"                       [strict]
                | "join" Exp ";"                        [strict]
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Stmt
                 | Stmts Stmts                          [right]

  syntax Start ::= "HAI" Stmts "KTHXBAI"

  rule if (E) S => if (E) S else {}                                 [macro]
  rule for(Start Cond; Step) {S} => {Start while (Cond) {S Step;}}  [macro]
  rule for(Start Cond; Step) {} => {Start while (Cond) {Step;}}     [macro]
  rule IHA:IHASA E1:Exp, E2:Exp, Es:Exps; => IHA:IHASA E1; IHA:IHASA E2, Es;          [macro]
  rule HAI S:Stmts KTHXBAI => S                                     [macro]
  rule IHA:IHASA X:Id = E; => IHA:IHASA X; X = E;                               [macro]
  //rule IHA:IHASA X:Id = E; => IHA:IHASA X; X = E;                               [macro]

endmodule

module SIMPLE-LOLCODE
  imports SIMPLE-LOLCODE-SYNTAX

  syntax Val ::= Int | Bool | String
               | array(Int,Int)
               | lambda(Ids,Stmt)
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:Stmts ~> execute) </k>
                      <br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                      </control>
                      <br/>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                      <id color="pink"> 0 </id>
                    </thread>
                  </threads>
                  <br/>
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan"> .Set </busy>
                  <terminated color="red"> .Set </terminated>
                  <br/>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>

  syntax KItem ::= "undefined"  [latex(\bot)]

  rule <k> IHA:IHASA X:Id; => . ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> undefined ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

  context IHA:IHASA _:Id[HOLE];

  rule <k> IHA:IHASA X:Id[N:Int]; => . ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> array(L +Int 1, N)
                          (L +Int 1) ... (L +Int N) |-> undefined ...</store>
       <nextLoc> L => L +Int 1 +Int N </nextLoc>
    when N >=Int 0

  syntax Id ::= "$1" | "$2"
  rule IHA:IHASA X:Id[N1:Int, N2:Int, Vs:Vals];
    => IHA:IHASA X[N1];
       {
         for(IHA:IHASA $1 = 0; $1 <= N1 - 1; ++$1) {
           IHA:IHASA $2[N2, Vs];
           X[$1] = $2;
         }
       }
    [structural]

  rule <k> function F(Xs) S => . ...</k>
       <env> Env => Env[F <- L] </env>
       <store>... .Map => L |-> lambda(Xs, S) ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

  syntax KItem ::= "execute"
  rule <k> execute => main(.Exps); </k>
       <env> Env </env>
       <genv> .Map => Env </genv>  [structural]

  rule <k> X:Id => V ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]

  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store>  [increment]

  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
  rule I1 - I2 => I1 -Int I2
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 when I2 =/=K 0
  rule I1 % I2 => I1 %Int I2 when I2 =/=K 0
  rule - I => 0 -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2

  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2

  rule ! T => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E

  rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs]
    [structural, anywhere]

  rule array(L,_)[N:Int] => lookup(L +Int N)
    [structural, anywhere]

  rule sizeOf(array(_,N)) => N

  syntax KItem ::=  (Map,K,ControlCellFragment)

  rule <k> lambda(Xs,S)(Vs:Vals) ~> K => mkDecls(Xs,Vs) S return; </k>
       <control>
         <fstack> .List => ListItem((Env,K,C)) ...</fstack>
         C
       </control>
       <env> Env => GEnv </env>
       <genv> GEnv </genv>

  rule <k> return(V:Val); ~> _ => V ~> K </k>
       <control>
         <fstack> ListItem((Env,K,C)) => .List ...</fstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

  syntax Val ::= "nothing"
  rule return; => return nothing;   [macro]

  rule <k> read() => I ...</k> <in> ListItem(I:Int) => .List ...</in>  [read]

  context (HOLE => lvalue(HOLE)) = _

  rule <k> loc(L) = V:Val => V ...</k> <store>... L |-> (_ => V) ...</store>
    [assignment]

  rule {} => .  [structural]
  rule <k> { S } => S ~> env(Env) ...</k>  <env> Env </env>  [structural]

  rule S1:Stmts S2:Stmts => S1 ~> S2  [structural]

  rule _:Val; => .

  rule if ( true) S else _ => S
  rule if (false) _ else S => S

  rule while (E) S => if (E) {S while(E)S}  [structural]

  rule <k> print(V:Val, Es => Es); ...</k> <out>... .List => ListItem(V) </out>
    [print]
  rule print(.Vals); => .  [structural]

  syntax KItem ::= (Id,Stmts,K,Map,ControlCellFragment)

  syntax KItem ::= "popx"

  rule <k> (try S1 catch(X) {S2} => S1 ~> popx) ~> K </k>
       <control>
         <xstack> .List => ListItem((X, S2, K, Env, C)) ...</xstack>
         C
       </control>
       <env> Env </env>

  rule <k> popx => . ...</k>
       <xstack> ListItem(_) => .List ...</xstack>

  // rule <k> throw V:Val; ~> _ => { ?IHA:IHASA X = V; S2 } ~> K </k>
  //      <control>
  //        <xstack> ListItem((X, S2, K, Env, C)) => .List ...</xstack>
  //        (_ => C)
  //      </control>
  //      <env> _ => Env </env>

  // rule <thread>...
  //        <k> spawn S => !T:Int ...</k>
  //        <env> Env </env>
  //      ...</thread>
  //      (. => <thread>...
  //              <k> S </k>
  //              <env> Env </env>
  //              <id> !T </id>
  //            ...</thread>)

  // rule (<thread>... <k>.</k> <holds>H</holds> <id>T</id> ...</thread> => .)
  //      <busy> Busy => Busy -Set keys(H) </busy>
  //      <terminated>... .Set => SetItem(T) ...</terminated>

  // rule <k> join T:Int; => . ...</k>
  //      <terminated>... SetItem(T) ...</terminated>

  // rule <k> acquire V:Val; => . ...</k>
  //      <holds>... .Map => V |-> 0 ...</holds>
  //      <busy> Busy (.Set => SetItem(V)) </busy>
  //   when (notBool(V in Busy))  [acquire]

  // rule <k> acquire V; => . ...</k>
  //      <holds>... V:Val |-> (N => N +Int 1) ...</holds>

  // rule <k> release V:Val; => . ...</k>
  //      <holds>... V |-> (N => N -Int 1) ...</holds>
  //   when N >Int 0

  // rule <k> release V; => . ...</k> <holds>... V:Val |-> 0 => .Map ...</holds>
  //      <busy>... SetItem(V) => .Set ...</busy>

  // rule <k> rendezvous V:Val; => . ...</k>
  //      <k> rendezvous V; => . ...</k>  [rendezvous]

  syntax Stmts ::= mkDecls(Ids,Vals)  [function]
  rule mkDecls((X:Id, Xs:Ids), (V:Val, Vs:Vals)) => ?IHA:IHASA X=V; mkDecls(Xs,Vs)
  rule mkDecls(.Ids,.Vals) => {}

  syntax KItem ::= lookup(Int)
  rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]

  syntax KItem ::= env(Map)
  rule <k> env(Env) => . ...</k> <env> _ => Env </env>  [structural]

  rule (env(_) => .) ~> env(_)  [structural]

  syntax Exp ::= lvalue(K)
  syntax Val ::= loc(Int)

  rule <k> lvalue(X:Id => loc(L)) ...</k> <env>... X |-> L:Int ...</env>
    [structural]

  context lvalue(_:>Exp[HOLE:>Exps])
  context lvalue(HOLE:>Exp[_:>Exps])

  rule lvalue(lookup(L:Int) => loc(L))  [structural]

  syntax Map ::= Int "..." Int "|->" K
    [function, latex({#1}\ldots{#2}\mapsto{#3})]
  rule N...M |-> _ => .Map  when N >Int M
  rule N...M |-> K => N |-> K (N +Int 1)...M |-> K  when N <=Int M

endmodule
