%{
open Syntax
%}

%token LAM DOT LET EQ IN SUC NATREC LPAREN RPAREN EOF
%token <int> NAT
%token <string> ID

%start <parsed> main

%%

let main :=
  t = term; EOF; { t }

let atom :=
  | LPAREN; t = term; RPAREN; { t }
  | located(
      | SUC; { ESuc () }
      | NATREC; { ENatrec () }
      | n = NAT; { ENat ((), n) }
      | v = ID; { EVar ((), v) }
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
  bind = located(
    LET; x = ID; EQ; t = term; { x, t }
  );
  IN;
  u = term;
  { let (x, t), loc = bind
    in ELet ((), x, t, u), loc
  }

let term :=
  | lam
  | _let
  | spine

let located(X) ==
  x = X; { x, Asai.Range.of_lex_range $loc }
