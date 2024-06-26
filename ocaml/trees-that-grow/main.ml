open! Core
open Format
open Syntax
open Rename
open Infer

let ( let@@ ) x f = x ~f

let parse_file fname =
  let@@ chan = In_channel.with_file fname in
  let lexbuf = Lexing.from_channel chan in
  Lexing.set_filename lexbuf fname;
  try Parser.main Lexer.read lexbuf with
  | Lexer.Error ->
    Reporter.fatal ~loc:(Asai.Range.of_lexbuf lexbuf) Parse_err "unexpected token"
  | Parser.Error ->
    Reporter.fatal ~loc:(Asai.Range.of_lexbuf lexbuf) Parse_err "failed to parse the code"
;;

let () =
  let@@ () = Reporter.run in
  let fname = (Sys.get_argv ()).(1) in
  printf
    "--------------------------------------------------------------------------------@.";
  let term = parse_file fname in
  printf "@[<v>%a@]@." pp_parsed term;
  printf
    "--------------------------------------------------------------------------------@.";
  let term = rename term in
  printf "@[<v>%a@]@." pp_renamed term;
  printf
    "--------------------------------------------------------------------------------@.";
  let ((_, (_, ty)) as term) = infer term in
  printf "@[<v>%a : %a@]@." pp_typed term pp_ty ty
;;
