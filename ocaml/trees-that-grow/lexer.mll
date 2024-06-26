{
open Parser

exception Error
}

let space = [' ' '\r' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']*

rule read = parse
  | space { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }
  | '\\' { LAM }
  | '.' { DOT }
  | '=' { EQ }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | "let" { LET }
  | "in" { IN }
  | id
    { let s = Lexing.lexeme lexbuf in
      ID s
    }
  | eof { EOF }
  | _ { raise Error }
