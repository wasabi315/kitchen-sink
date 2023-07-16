open Format

module C_printer : sig
  val output : formatter -> (unit -> unit) -> unit
  val fn : ('a, formatter, unit, (unit -> unit) -> unit) format4 -> 'a
  val ( ! ) : ('a, formatter, unit) format -> 'a
  val ifel : ('a, formatter, unit, (unit -> unit) -> (unit -> unit) -> unit) format4 -> 'a
end = struct
  let proto_ctx, func_ctx = 0, 1
  let q = Array.init 2 (fun _ -> Queue.create ())

  let output ppf f =
    Array.iter Queue.clear q;
    f ();
    fprintf ppf "@[<v>#include <stdio.h>";
    Array.iter (Queue.iter (( |> ) ppf)) q;
    fprintf ppf "@]@."
  ;;

  let print_to ctx = kdprintf (fun p -> Queue.add p q.(ctx))

  let fn fmt =
    kdprintf
      (fun p f ->
        print_to proto_ctx "@,%t;" p;
        print_to func_ctx "@,@[<v 4>%t {" p;
        f ();
        print_to func_ctx "@]@,}")
      fmt
  ;;

  let ( ! ) fmt = kdprintf (print_to func_ctx "@,%t;") fmt

  let ifel fmt =
    kdprintf
      (fun p t e ->
        print_to func_ctx "@,@[<v 4>if (%t) {" p;
        t ();
        print_to func_ctx "@]@,@[<v 4>} else {";
        e ();
        print_to func_ctx "@]@,}")
      fmt
  ;;
end

module Toy_lang = struct
  type program =
    { main : string
    ; main_arg : int
    ; fns : (string * string * expr) list
    }

  and expr =
    | Int of int
    | Var of string
    | Add of expr * expr
    | Sub of expr * expr
    | IsZero of expr
    | Call of string * expr
    | If of expr * expr * expr
end

module Codegen = struct
  let gen_var =
    let count = ref 0 in
    fun () ->
      count := !count + 1;
      sprintf "v%d" !count
  ;;

  open C_printer

  let gen_body =
    let rec gen_expr = function
      | Toy_lang.Int n -> dprintf "%d" n
      | Var v -> dprintf "%s" v
      | Add (l, r) -> dprintf "(%t + %t)" (gen_expr l) (gen_expr r)
      | Sub (l, r) -> dprintf "(%t - %t)" (gen_expr l) (gen_expr r)
      | IsZero e -> dprintf "(%t == 0)" (gen_expr e)
      | Call (f, e) -> dprintf "%s(%t)" f (gen_expr e)
      | If (c, t, e) ->
        let v = gen_var () in
        !"int %s" v;
        (ifel "%t" (gen_expr c))
          (fun () -> !"%s = %t" v (gen_expr t))
          (fun () -> !"%s = %t" v (gen_expr e));
        dprintf "%s" v
    in
    fun expr -> !"return %t" (gen_expr expr)
  ;;

  let gen_fn (fn_name, param_name, body) =
    fn "int %s(int %s)" fn_name param_name (fun () -> gen_body body)
  ;;

  let gen_program prog =
    fn "int main(void)" (fun () ->
      !"printf(\"%%d\\n\", %s(%d))" prog.Toy_lang.main prog.main_arg;
      !"return 0");
    List.iter gen_fn prog.fns
  ;;

  let f ppf prog = output ppf (fun () -> gen_program prog)
end

let () =
  let program =
    { Toy_lang.main = "even"
    ; main_arg = 100
    ; fns =
        [ "even", "n", If (IsZero (Var "n"), Int 1, Call ("odd", Sub (Var "n", Int 1)))
        ; "odd", "n", If (IsZero (Var "n"), Int 0, Call ("even", Sub (Var "n", Int 1)))
        ]
    }
  in
  Codegen.f std_formatter program
;;
