%{
  open Ftree
%}
%token REQUIRES ENSURES LOCAL SHARED
%token SEMICOLON WHILE FOR IF ELSE
%token INT
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COMMA ASSIGN OR AND EQ NEQ LT GT LE GE PLUS MINUS MULT DIV MOD POW EXCLAM
%token IMPL TRUE FALSE FORALL EXISTS DOT SUM ACTIVE AT BACKSLASH LAMBDA
%token <string> ID
%token <int> INTV
%token EOF
%token SECTIONSEP
%token COLON THREADS

// %token SYNC SKIP TID NT
%token <Ftree.const * Ftree.xyz> CONST

%left DOT
%left SEMICOLON
%right IMPL
%left OR
%left AND
%left EQ NEQ LT GT LE GE
%left PLUS MINUS
%left MULT DIV MOD
%right POW
%left UMINUS
%left EXCLAM
%left AT

%start expr
%type <Ftree.parsetree> expr

%%

expr:
  TRUE                  { pt_true }
| FALSE                 { pt_false }
| expr IMPL expr  { pt_impl [$1] $3 }
| expr OR expr    { pt_or [$1; $3] }
| expr AND expr   { pt_and [$1; $3] }
| EXCLAM expr        { pt_not $2 }
| FORALL ID trigger SEMICOLON expr { pt_forall $2 $3 $5 }
| FORALL ID trigger COLON THREADS SEMICOLON expr
                        { pt_forall_threads $2 $3 $7 }
| EXISTS ID trigger SEMICOLON expr { pt_exists $2 $3 $5 }
| EXISTS ID trigger COLON THREADS SEMICOLON expr
                        { pt_exists_threads $2 $3 $7 }
| expr EQ expr          { pt_eq $1 $3 }
| expr NEQ expr         { pt_neq $1 $3 }
| expr LT expr          { pt_lt $1 $3 }
| expr GT expr          { pt_gt $1 $3 }
| expr LE expr          { pt_le $1 $3 }
| expr GE expr          { pt_ge $1 $3 }
| expr PLUS expr	{ pt_plus $1 $3 }
| expr MINUS expr	{ pt_minus $1 $3 }
| expr MULT expr	{ pt_mult $1 $3 }
| expr DIV expr         { pt_div $1 $3 }
| expr MOD expr         { pt_mod $1 $3 }
| expr POW expr         { pt_pow $1 $3 }
| MINUS expr %prec UMINUS	{ pt_uminus $2 }
/* | ID LPAREN arg_expr_list RPAREN        { pt_call ($1, $3) } */
| INTV                  { pt_int $1 }
| SUM LPAREN expr COMMA expr COMMA lambda RPAREN {
        let (v, e) = $7 in pt_sum v e $3 $5
  }
| ACTIVE LPAREN expr RPAREN     { pt_act $3 }
|  expr AT expr          { pt_at $1 $3 }
| LPAREN expr RPAREN	{ $2 }
| ID index_list         { pt_acc $1 $2 }
| CONST                    { pt_const (fst $1) (snd $1) }

lambda:
| LAMBDA INT ID SEMICOLON expr { ($3, $5) }

trigger:
| /* empty */   { [] }
| LBRACKET expr RBRACKET        { [$2] }
| LBRACKET expr COMMA expr RBRACKET        { [$2; $4] }

index_list:
  /* empty */	{ [] }
| LBRACKET expr RBRACKET index_list	{ $2 :: $4 }

/* arg_expr_list: */
  /* empty    { [] } */
/* | expr	{ [$1] } */
/* | expr COMMA arg_expr_list	{ $1 :: $3 } */

/* formula: */
/*   TRUE                  { pt_true } */
/* | FALSE                 { pt_false } */
/* | formula IMPL formula  { pt_impl [$1; $3] } */
/* | formula OR formula    { pt_or [$1; $3] } */
/* | formula AND formula   { pt_and [$1; $3] } */
/* | EXCLAM formula        { pt_not $2 } */
/* | FORALL ID SEMICOLON formula { pt_forall $2 $4 } */
/* | FORALL ID COLON THREADS SEMICOLON formula */
/*                         { pt_forall_threads $2 $6 } */
/* | EXISTS ID SEMICOLON formula { pt_exists $2 $4 } */
/* | LPAREN formula RPAREN { $2 } */
/* | term EQ term          { pt_eq $1 $3 } */
/* | term NEQ term         { pt_neq $1 $3 } */
/* | term LT term          { pt_lt $1 $3 } */
/* | term GT term          { pt_gt $1 $3 } */
/* | term LE term          { pt_le $1 $3 } */
/* | term GE term          { pt_ge $1 $3 } */
/* | term                    { pt_term $1 } */

/* term: */
/* /\*  NT                    { TNT } *\/ */
/* | term PLUS term	{ pt_plus $1 $3 } */
/* | term MINUS term	{ pt_minus $1 $3 } */
/* | term MULT term	{ pt_mult $1 $3 } */
/* | term DIV term         { pt_div $1 $3 } */
/* | term MOD term         { pt_mod $1 $3 } */
/* | term POW term         { pt_pow $1 $3 } */
/* | MINUS term %prec UMINUS	{ pt_uminus $2 } */
/* /\* | ID LPAREN arg_term_list RPAREN        { pt_call ($1, $3) } *\/ */
/* | INTV                  { pt_int (string_of_int $1) } */
/* | SUM LPAREN ID COMMA term COMMA term COMMA term RPAREN { */
/*         pt_sum id $5 $7 $9 */
/*   } */
/* | AT LPAREN term COMMA term RPAREN          { pt_at $5 $3 } */
/* | LPAREN term RPAREN	{ $2 } */
/* | ID index_list         { pt_acc $1 $2 } */

/* index_list: */
/*   /\* empty *\/	{ [] } */
/* | LBRACKET term RBRACKET index_list	{ $2 :: $4 } */

/* /\* arg_term_list: *\/ */
/*   /\* empty    { [] } *\/ */
/* /\* | term	{ [$1] } *\/ */
/* /\* | term COMMA arg_term_list	{ $1 :: $3 } *\/ */

