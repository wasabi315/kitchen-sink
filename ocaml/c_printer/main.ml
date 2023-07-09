open Format

module C_printer : sig
  val output : formatter -> (unit -> unit) -> unit
  val func : ('a, formatter, unit, (unit -> unit) -> unit) format4 -> 'a
  val __ : ('a, formatter, unit) format -> 'a
  val if' : ('a, formatter, unit, (unit -> unit) -> unit) format4 -> 'a
end = struct
  let proto_ctx, func_ctx = 0, 1
  let q = Array.init 2 (fun _ -> Queue.create ())

  let output ppf f =
    Array.iter Queue.clear q;
    f ();
    fprintf ppf "@[<v>";
    Array.iter (Queue.iter (( |> ) ppf)) q;
    fprintf ppf "@]@."
  ;;

  let add_to ctx fmt = kdprintf (fun p -> Queue.add p q.(ctx)) fmt

  let func fmt =
    kdprintf
      (fun p f ->
        add_to proto_ctx "@,%t;" p;
        add_to func_ctx "@,@[<v 4>%t {" p;
        f ();
        add_to func_ctx "@]@,}")
      fmt
  ;;

  let __ fmt = kdprintf (add_to func_ctx "@,%t;") fmt

  let if' fmt =
    kdprintf
      (fun p f ->
        add_to func_ctx "@,@[<v 4>if (%t)" p;
        f ();
        add_to func_ctx "@]@,}")
      fmt
  ;;
end

let () =
  let open C_printer in
  let program n =
    func "int main(void)" (fun () ->
      __ "printf(\"%%d\\n\", even(%d))" n;
      __ "return 0");
    func "int even(int n)" (fun () ->
      if' "n == 0" (fun () -> __ "return 1");
      __ "return odd(n - 1)");
    func "int odd(int n)" (fun () ->
      if' "n == 0" (fun () -> __ "return 0");
      __ "return even(n - 1)")
  in
  output std_formatter (fun () -> program 100)
;;
