module C_printer : sig
  open Format

  val output : formatter -> (unit -> unit) -> unit
  val func : ('a, formatter, unit, (unit -> unit) -> unit) format4 -> 'a
  val stmt : ('a, formatter, unit) format -> 'a
  val return : ('a, formatter, unit) format -> 'a
  val if' : ('a, formatter, unit, (unit -> unit) -> unit) format4 -> 'a
  val else' : (unit -> unit) -> unit
end = struct
  open Format

  let proto_ctx, func_ctx = 0, 1
  let printer_bufs = Array.init 2 (fun _ -> Queue.create ())

  let output ppf f =
    Array.iter Queue.clear printer_bufs;
    f ();
    fprintf ppf "@[<v>";
    Array.iter (Queue.iter (( |> ) ppf)) printer_bufs;
    fprintf ppf "@]@."
  ;;

  let print_to ctx = kdprintf (fun p -> Queue.add p printer_bufs.(ctx))

  let make_block ctx =
    kdprintf (fun p f ->
      print_to ctx "@,@[<v 2>%t{" p;
      f ();
      print_to ctx "@]@,}")
  ;;

  let func fmt =
    kdprintf
      (fun p f ->
        print_to proto_ctx "@,%t;" p;
        make_block func_ctx "%t " p f)
      fmt
  ;;

  let stmt fmt = kdprintf (print_to func_ctx "@,%t;") fmt
  let if' fmt = kdprintf (make_block func_ctx "if (%t) ") fmt
  let else' f = make_block func_ctx "else " f
  let return fmt = kdprintf (stmt "return %t") fmt
end

let _test =
  let open C_printer in
  output Format.str_formatter (fun () ->
    func "int main(void)" (fun () ->
      stmt {|printf("%%d\n", even(10))|};
      return "0");
    func "int even(int n)" (fun () ->
      if' "n == 0" (fun () -> return "1");
      else' (fun () -> return "odd(n - 1)"));
    func "int odd(int n)" (fun () ->
      if' "n == 0" (fun () -> return "0");
      else' (fun () -> return "even(n - 1)")));
  let expected =
    {|
int main(void);
int even(int n);
int odd(int n);
int main(void) {
  printf("%d\n", even(10));
  return 0;
}
int even(int n) {
  if (n == 0) {
    return 1;
  }
  else {
    return odd(n - 1);
  }
}
int odd(int n) {
  if (n == 0) {
    return 0;
  }
  else {
    return even(n - 1);
  }
}
|}
  in
  let actual = Format.flush_str_formatter () in
  assert (String.equal expected actual)
;;

(* Example *)

module Tiny_c = struct
  type program = { funcs : func list }

  and func =
    { name : string
    ; param : string
    ; body : stmt list
    }

  and stmt =
    | Return of expr
    | IfZero of expr * stmt list * stmt list

  and expr =
    | Int of int
    | Var of string
    | Add of expr * expr
    | Call of string * expr

  let even_odd =
    { funcs =
        [ { name = "even"
          ; param = "n"
          ; body =
              [ IfZero
                  ( Var "n"
                  , [ Return (Int 1) ]
                  , [ Return (Call ("odd", Add (Var "n", Int (-1)))) ] )
              ]
          }
        ; { name = "odd"
          ; param = "n"
          ; body =
              [ IfZero
                  ( Var "n"
                  , [ Return (Int 0) ]
                  , [ Return (Call ("even", Add (Var "n", Int (-1)))) ] )
              ]
          }
        ]
    }
  ;;
end

module Codegen_printf = struct
  open Tiny_c
  open Printf

  let rec pp_expr oc = function
    | Int n -> fprintf oc "%d" n
    | Var v -> fprintf oc "%s" v
    | Add (e1, e2) -> fprintf oc "%a + %a" pp_expr e1 pp_expr e2
    | Call (f, e) -> fprintf oc "%s(%a)" f pp_expr e
  ;;

  let spaces_of indent = String.make indent ' '

  let rec pp_stmt indent oc stmt =
    fprintf oc "\n%s" (spaces_of indent);
    match stmt with
    | Return e -> fprintf oc "return %a;" pp_expr e
    | IfZero (e, s1, s2) ->
      fprintf oc "if (%a == 0) {" pp_expr e;
      List.iter (pp_stmt (indent + 2) oc) s1;
      fprintf oc "\n%s}" (spaces_of indent);
      fprintf oc "\n%selse {" (spaces_of indent);
      List.iter (pp_stmt (indent + 2) oc) s2;
      fprintf oc "\n%s}" (spaces_of indent)
  ;;

  let pp_proto oc { name; param; _ } = fprintf oc "\nint %s(int %s);" name param

  let pp_func oc { name; param; body } =
    fprintf oc "\nint %s(int %s) {" name param;
    List.iter (pp_stmt 2 oc) body;
    fprintf oc "\n}"
  ;;

  let gen oc { funcs } =
    List.iter (pp_proto oc) funcs;
    List.iter (pp_func oc) funcs;
    printf "\n"
  ;;
end

module Codegen_format = struct
  open Tiny_c
  open Format

  let rec pp_expr ppf = function
    | Int n -> fprintf ppf "%d" n
    | Var v -> fprintf ppf "%s" v
    | Add (e1, e2) -> fprintf ppf "%a + %a" pp_expr e1 pp_expr e2
    | Call (f, e) -> fprintf ppf "%s(%a)" f pp_expr e
  ;;

  let rec pp_stmt ppf = function
    | Return e -> fprintf ppf "@,return %a;" pp_expr e
    | IfZero (e, s1, s2) ->
      fprintf ppf "@,@[<v 2>if (%a == 0) {" pp_expr e;
      List.iter (pp_stmt ppf) s1;
      fprintf ppf "@]@,}@,@[<v 2>else {";
      List.iter (pp_stmt ppf) s2;
      fprintf ppf "@]@,}"
  ;;

  let pp_proto ppf { name; param; _ } = fprintf ppf "@,int %s(int %s);" name param

  let pp_func ppf { name; param; body } =
    fprintf ppf "@,@[<v 2>int %s(int %s) {" name param;
    List.iter (pp_stmt ppf) body;
    fprintf ppf "@]@,}"
  ;;

  let gen ppf { funcs } =
    fprintf ppf "@[<v>";
    List.iter (pp_proto ppf) funcs;
    List.iter (pp_func ppf) funcs;
    fprintf ppf "@]@."
  ;;
end

module Codegen_c_printer = struct
  open Tiny_c
  open C_printer

  let pp_expr = Codegen_format.pp_expr

  let rec gen_stmt = function
    | Return e -> return "%a" pp_expr e
    | IfZero (e, s1, s2) ->
      if' "%a == 0" pp_expr e (fun () -> List.iter gen_stmt s1);
      else' (fun () -> List.iter gen_stmt s2)
  ;;

  let gen_func { name; param; body } =
    func "int %s(int %s)" name param (fun () -> List.iter gen_stmt body)
  ;;

  let gen ppf { funcs } = output ppf (fun () -> List.iter gen_func funcs)
end

let () = Codegen_printf.gen stdout Tiny_c.even_odd
let () = Codegen_format.gen Format.std_formatter Tiny_c.even_odd
let () = Codegen_c_printer.gen Format.std_formatter Tiny_c.even_odd
