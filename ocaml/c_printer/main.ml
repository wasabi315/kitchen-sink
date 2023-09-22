open Format

module C_printer : sig
  val output : formatter -> (unit -> unit) -> unit
  val func : ('a, formatter, unit, (unit -> unit) -> unit) format4 -> 'a
  val stmt : ('a, formatter, unit) format -> 'a
  val return : ('a, formatter, unit) format -> 'a
  val if' : ('a, formatter, unit, (unit -> unit) -> unit) format4 -> 'a
  val else' : (unit -> unit) -> unit
end = struct
  let proto_ctx, func_ctx = 0, 1
  let printer_qs = Array.init 2 (fun _ -> Queue.create ())

  let output ppf f =
    Array.iter Queue.clear printer_qs;
    f ();
    fprintf ppf "@[<v>";
    Array.iter (Queue.iter (( |> ) ppf)) printer_qs;
    fprintf ppf "@]@."
  ;;

  let print_to ctx = kdprintf (fun p -> Queue.add p printer_qs.(ctx))

  let make_block ctx =
    kdprintf (fun p f ->
      print_to ctx "@,@[<v 4>%t{" p;
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

let _test1 =
  let open C_printer in
  output str_formatter (fun () ->
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
  let actual = flush_str_formatter () in
  assert (String.equal expected actual)
;;

module Toy_lang = struct
  type program = { funcs : func list }

  and func =
    { name : string
    ; param : string
    ; body : expr
    }

  and expr =
    | Int of int
    | Var of string
    | Add of expr * expr
    | Call of string * expr
    | IfZero of expr * expr * expr
end

module Codegen : sig
  val gen : formatter -> Toy_lang.program -> unit
end = struct
  open C_printer

  let tmp_count = ref 0

  let create_tmp () =
    incr tmp_count;
    asprintf "tmp%d" !tmp_count
  ;;

  let dpf = dprintf

  let rec gen_expr = function
    | Toy_lang.Int n -> dpf "%d" n
    | Var v -> dpf "%s" v
    | Add (l, r) -> dpf "(%t + %t)" (gen_expr l) (gen_expr r)
    | Call (f, e) -> dpf "%s(%t)" f (gen_expr e)
    | IfZero (c, t, e) ->
      let tmp = create_tmp () in
      stmt "int %s" tmp;
      if' "%t == 0" (gen_expr c) (fun () -> stmt "%s = %t" tmp (gen_expr t));
      else' (fun () -> stmt "%s = %t" tmp (gen_expr e));
      dpf "%s" tmp
  ;;

  let gen_func { Toy_lang.name; param; body } =
    func "int %s(int %s)" name param (fun () -> return "%t" (gen_expr body))
  ;;

  let gen_program prog = List.iter gen_func prog.Toy_lang.funcs

  let gen ppf prog =
    tmp_count := 0;
    output ppf (fun () -> gen_program prog)
  ;;
end

let _test2 =
  let program =
    { Toy_lang.funcs =
        [ { name = "even"
          ; param = "n"
          ; body = IfZero (Var "n", Int 1, Call ("odd", Add (Var "n", Int (-1))))
          }
        ; { name = "odd"
          ; param = "n"
          ; body = IfZero (Var "n", Int 0, Call ("even", Add (Var "n", Int (-1))))
          }
        ]
    }
  in
  let expected =
    {|
int even(int n);
int odd(int n);
int even(int n) {
    int tmp1;
    if (n == 0) {
        tmp1 = 1;
    }
    else {
        tmp1 = odd((n + -1));
    }
    return tmp1;
}
int odd(int n) {
    int tmp2;
    if (n == 0) {
        tmp2 = 0;
    }
    else {
        tmp2 = even((n + -1));
    }
    return tmp2;
}
|}
  in
  Codegen.gen str_formatter program;
  let actual = flush_str_formatter () in
  assert (String.equal expected actual)
;;

let () = printf "OK!@."
