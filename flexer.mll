{
  open Fparser
  let reserved_words = [
    ("True", TRUE);
    ("False", FALSE);
    ("sum", SUM);
    ("active", ACTIVE);
    ("int", INT);
    ("integer", INT);
    ("thread", THREADS);
    ("forall", FORALL);
    ("exists", EXISTS);
    ("lambda", LAMBDA);
  ]
  let special_constants = [
    ("threadIdx", Ftree.TID);
    ("blockIdx", Ftree.BID);
    ("blockDim", Ftree.BDIM);
    ("gridDim", Ftree.GDIM);
  ]
}

  rule main = parse
  [' ' '\009' '\012' '\n']+
| "//"[^'\n']*'\n' {main lexbuf}
| ['0'-'9']+ {INTV (int_of_string (Lexing.lexeme lexbuf))}
| ";" {SEMICOLON}
| "(" {LPAREN}
| ")" {RPAREN}
| "[" {LBRACKET}
| "]" {RBRACKET}
| "{" {LBRACE}
| "}" {RBRACE}
| "," {COMMA}
| "->" {IMPL}
| "||" {OR}
| "&&" {AND}
| "!"  {EXCLAM}
| "==" {EQ}
| "=" {ASSIGN}
| "!=" {NEQ}
| "<=" {LE}
| ">=" {GE}
| "<" {LT}
| ">" {GT}
| "+" {PLUS}
| "-" {MINUS}
| "*" {MULT}
| "^" {POW}
| "/" {DIV}
| "%" {MOD}
| "." {DOT}
| "%%" {SECTIONSEP}
| "@" {AT}
| ":" {COLON}
(* | "__syncthreads()"	{SYNC} *)
| ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* {
    let id = Lexing.lexeme lexbuf in
      try List.assoc id reserved_words
      with Not_found ->
        try let t = List.assoc id special_constants in
            CONST (t, accessor lexbuf)
        with Not_found -> ID id
  }
| eof {EOF}

and accessor = parse
  ".x" {Ftree.X}
| ".y" {Ftree.Y}
| ".z" {Ftree.Z}
