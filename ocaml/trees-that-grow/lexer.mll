{
open Parser

exception Error
}

let space = [' ' '\r' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']*
let nat = ['1'-'9']['0'-'9']* | '0'

rule read = parse
  | space { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }
  | '\\' { LAM }
  | '.' { DOT }
  | '=' { EQ }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | "in" { IN }
  | "let" { LET }
  | "suc" { SUC }
  | "natrec" { NATREC }
  | nat
    { let s = Lexing.lexeme lexbuf in
      NAT (int_of_string s)
    }
  | id
    { let s = Lexing.lexeme lexbuf in
      ID s
    }
  | eof { EOF }
  | _ { raise Error }
