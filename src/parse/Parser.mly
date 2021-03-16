%{
exception Unexpected_knights of string
open RunConfig
%}

%token <int> INT
%token <string> GLOBAL
%token <string> REGISTER
%token <string> STRING
%token <string> QUOTED_STRING

%token DO WHILE IF ELSE
%token LPAREN RPAREN
%token LBRACE RBRACE
%token LSPAREN RSPAREN
%token SEMICOLON
%token PARALLEL
%token ASSIGN
%token SKIP
%token PRINT
%token DOT LD ST

%token FADD CAS

%token FENCE
%token NONATOMIC RELAXED ACQUIRE RELEASE SC
%token WHITEPICKET

%token EXCLUSIVE NOT_EXCLUSIVE
%token STRONG NORMAL

%token LOCK UNLOCK

%token TIMES DIVIDE PLUS MINUS
%token EQUAL GT GTE LT LTE NOT AND OR

%token NAME VALUES COMMENT
%token CONF_SEP
%token COMMA

%token ALLOW FORBID

%token EOF

%right SEMICOLON
%left OR
%left AND
%nonassoc NOT

%left PLUS
%left MINUS
%left TIMES
%left DIVIDE

%start <RunConfig.t option * AST.ast * AST.outcome list option> top

%%

top: c=option(config) a=ast option(SEMICOLON) o=option(outcomes) EOF { (c, a, o) }

name: n=STRING { n }
    | n=GLOBAL { n }
    | n=QUOTED_STRING { n }

config: NAME EQUAL n=name
	VALUES EQUAL vs=delimited(LBRACE, separated_list(COMMA, INT), RBRACE)
	c=option(comment)
	CONF_SEP { { name=n; values=vs; comment=c } }

comment: COMMENT s=QUOTED_STRING { s }


block: LBRACE a=ast option(SEMICOLON) RBRACE     { a }

ord: NONATOMIC   { AST.NonAtomic }
  | RELAXED     { AST.Relaxed }
  | ACQUIRE     { AST.Acquire }
  | RELEASE     { AST.Release }
  | SC          { AST.SC }
  | WHITEPICKET { raise (Unexpected_knights "NI! NI! NI!") }

expr: v=INT                   { AST.Number v }
  | r=REGISTER                { AST.Register r }
  | e1=expr TIMES e2=expr     { AST.Multiplication (e1, e2) }
  | e1=expr DIVIDE e2=expr    { AST.Division (e1, e2) }
  | e1=expr PLUS e2=expr      { AST.Addition (e1, e2) }
  | e1=expr MINUS e2=expr     { AST.Subtraction (e1, e2) }
  | LPAREN e=expr RPAREN      { e }

%inline e_op:
  | EQUAL     { fun (l,r) -> AST.Equality (l,r) }
  | NOT EQUAL { fun (l,r) -> AST.Negation (AST.Equality (l, r)) }
  | GT        { fun (l,r) -> AST.Gt (l,r) }
  | LT        { fun (l,r) -> AST.Lt (l,r) }
  | GTE       { fun (l,r) -> AST.Gte (l,r) }
  | LTE       { fun (l,r) -> AST.Lte (l,r) }


%inline b_op:
  | AND   { fun (l,r) -> AST.Conjunction (l,r) }
	| OR    { fun (l,r) -> AST.Disjunction (l,r) }

bexpr: e1=expr o=e_op e2=expr            { o (e1,e2) }
  | b1=bexpr o=b_op b2=bexpr          { o (b1, b2) }
  | NOT b=bexpr                       { AST.Negation b }
  | LPAREN b=bexpr RPAREN             { b }

exclusivity:
  | EXCLUSIVE     { AST.Exclusive }
  | NOT_EXCLUSIVE { AST.NotExclusive }

rmw_strength:
  | NORMAL { AST.Normal }
  | STRONG { AST.Strong }

%inline load:
  | x=GLOBAL                            { fun r -> AST.(Load (r, x, Relaxed, NotExclusive)) }
  | x=GLOBAL DOT LD LPAREN a=ord RPAREN { fun r -> AST.(Load (r, x, a, NotExclusive)) }
  | x=GLOBAL DOT LD LPAREN a=ord COMMA e=exclusivity RPAREN { fun r -> AST.Load (r, x, a, e) }

%inline assign:
  | e=expr                              
    { fun r -> AST.Assign (r, e) }
  | FADD LPAREN g=GLOBAL COMMA o_r=ord COMMA o_w=ord COMMA e=expr RPAREN
    { fun r -> AST.Fadd(r, g, AST.Normal, o_r, o_w, e) }
  | FADD LPAREN g=GLOBAL COMMA rs=rmw_strength COMMA o_r=ord COMMA o_w=ord COMMA e=expr RPAREN
    { fun r -> AST.Fadd(r, g, rs, o_r, o_w, e) }
  | CAS LPAREN g=GLOBAL COMMA o_r=ord COMMA o_w=ord COMMA e1=expr COMMA e2=expr RPAREN
    { fun r -> AST.Cas(r, g, o_r, o_w, e1, e2) }

store:
  | g=GLOBAL ASSIGN e=expr                                                { AST.(Store (g, e, Relaxed, Normal)) }
  | g=GLOBAL DOT ST LPAREN e=expr COMMA a=ord RPAREN                      { AST.(Store (g, e, a, Normal)) }
  | g=GLOBAL DOT ST LPAREN e=expr COMMA a=ord COMMA s=rmw_strength RPAREN { AST.Store(g, e, a, s) }

ast:
  | SKIP                              { AST.Skip }
  | s=store                           { s }
  | r=REGISTER ASSIGN ld=load         { ld r }
  | r=REGISTER ASSIGN a=assign        { a r }
  | a1=ast SEMICOLON a2=ast           { AST.Sequence (a1, a2) }
  | b1=block PARALLEL b2=block        { AST.Parallel (b1, b2) }
  | IF b=bexpr bt=block ELSE bf=block { AST.Conditional (b, bt, bf) }
  | IF b=bexpr bt=block               { AST.Conditional (b, bt, AST.Skip) }
  | WHILE b=bexpr blk=block           { AST.While (b, blk) }
  | DO blk=block WHILE b=bexpr        { AST.Sequence (blk, AST.While(b, blk)) }
  | FENCE LPAREN o=ord RPAREN         { AST.Fence o }
  | PRINT LPAREN e=expr RPAREN        { AST.Print e }
  | LOCK                              { AST.Lock }
  | UNLOCK                            { AST.Unlock }


expect:
  | n=name EQUAL ALLOW { AST.Allow n }
  | n=name EQUAL FORBID { AST.Forbid n }

expect_list:
  | LSPAREN es=separated_list(COMMA, expect) RSPAREN { es }

outcome:
  | ALLOW e1=bexpr exp=expect_list c=option(QUOTED_STRING) { AST.Allowed (e1, exp, c) }
  | FORBID e1=bexpr exp=expect_list c=option(QUOTED_STRING) { AST.Forbidden (e1, exp, c) }

outcomes: CONF_SEP v=separated_list(SEMICOLON, outcome) { v }
