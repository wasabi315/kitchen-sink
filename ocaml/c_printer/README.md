# A thin wrapper around `Format` for C code generation

```ocaml
module C_printer : sig
  val output : formatter -> (unit -> unit) -> unit
  val func : ('a, formatter, unit, (unit -> unit) -> unit) format4 -> 'a
  val stmt : ('a, formatter, unit) format -> 'a
  val return : ('a, formatter, unit) format -> 'a
  val if' : ('a, formatter, unit, (unit -> unit) -> unit) format4 -> 'a
  val else' : (unit -> unit) -> unit
end

let _test1 =
  let open C_printer in
  output std_formatter (fun () ->
    func "int main(void)" (fun () ->
      stmt {|printf("%%d\n", even(10))|};
      return "0");
    func "int even(int n)" (fun () ->
      if' "n == 0" (fun () -> return "1");
      else' (fun () -> return "odd(n - 1)"));
    func "int odd(int n)" (fun () ->
      if' "n == 0" (fun () -> return "0");
      else' (fun () -> return "even(n - 1)")));
;;
```
