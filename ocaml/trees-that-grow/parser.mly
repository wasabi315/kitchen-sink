%{
open Syntax
%}

%token LAM DOT LET EQ IN LPAREN RPAREN EOF
%token <string> ID

%start <parsed> main

%%

let main :=
  t = term; EOF; { t }

let atom :=
  | LPAREN; t = term; RPAREN; { t }
  | located(
      v = ID; { EVar ((), v) }
    )

let spine :=
  | a = atom; { a }
  | located(
      s = spine; a = atom; { EApp ((), s, a) }
    )

let lam :=
  located(
    LAM; b = ID; DOT; t = term; { ELam ((), b, t) }
  )

let _let :=
  located(
    LET; x = ID; EQ; t = term; IN; u = term; { ELet ((), x, t, u) }
  )

let term :=
  | lam
  | _let
  | spine

let located(X) ==
  x = X; { x, Asai.Range.of_lex_range $loc }
