open! Core
open Format

module type Lambda = sig
  type 'a t

  val ( % ) : ('a -> 'b) t -> 'a t -> 'b t
  val lam : ('a t -> 'b t) -> ('a -> 'b) t
end

module Eval : Lambda with type 'a t = 'a = struct
  type 'a t = 'a

  let ( % ) f x = f x
  let lam f = f
end

let pp_paren show_paren = dprintf @@ if show_paren then "(%t)" else "%t"

module Pretty : sig
  type 'a t

  val pp : formatter -> 'a t -> unit

  include Lambda with type 'a t := 'a t
end = struct
  type 'a t = prec -> formatter -> unit
  and prec = int

  let pp ppf t = t 0 ppf

  let pp_subscript =
    let subs =
      [| "\u{2080}"
       ; "\u{2081}"
       ; "\u{2082}"
       ; "\u{2083}"
       ; "\u{2084}"
       ; "\u{2085}"
       ; "\u{2086}"
       ; "\u{2087}"
       ; "\u{2088}"
       ; "\u{2089}"
      |]
    in
    let rec loop ppf acc n =
      if n >= 10
      then loop ppf ((n mod 10) :: acc) (n / 10)
      else (
        pp_print_string ppf subs.(n);
        List.iter acc ~f:(fun d -> pp_print_string ppf subs.(d)))
    in
    fun ppf n -> loop ppf [] n
  ;;

  let fresh =
    let count = ref 0 in
    fun () ->
      let pp_var = Fn.const @@ dprintf "x%a" pp_subscript !count in
      count := !count + 1;
      pp_var
  ;;

  let ( % ) f x =
    let pp_f = f 10 in
    let pp_x = x 11 in
    fun prec -> pp_paren (prec > 10) @@ dprintf "%t%t" pp_f pp_x
  ;;

  let lam f =
    let var = fresh () in
    let pp_var = var 0 in
    let pp_body = f var 0 in
    fun prec -> pp_paren (prec > 0) @@ dprintf "\u{03BB}%t.%t" pp_var pp_body
  ;;
end

module DeBruijnPretty : sig
  type 'a t

  val pp : formatter -> 'a t -> unit

  include Lambda with type 'a t := 'a t
end = struct
  type 'a t = level -> prec -> formatter -> unit
  and level = int
  and prec = int

  let pp ppf t = t 0 0 ppf

  let ( % ) f x level =
    let pp_f = f level 10 in
    let pp_x = x level 11 in
    fun prec -> pp_paren (prec > 10) @@ dprintf "%t%t" pp_f pp_x
  ;;

  let lam f level =
    let var level' = Fn.const @@ dprintf "%d" (level' - level) in
    let pp_body = f var (level + 1) 0 in
    fun prec -> pp_paren (prec > 0) @@ dprintf "\u{03BB}%t" pp_body
  ;;
end

module SKI = struct
  module type S = sig
    type 'a t

    val ( % ) : ('a -> 'b) t -> 'a t -> 'b t
    val s : unit -> (('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c) t
    val k : unit -> ('a -> 'b -> 'a) t
    val i : unit -> ('a -> 'a) t
  end

  module Make (L : Lambda) : S with type 'a t = 'a L.t = struct
    include L

    let s () = lam @@ fun x -> lam @@ fun y -> lam @@ fun z -> x % z % (y % z)
    let k () = lam @@ fun x -> lam @@ fun _ -> x
    let i () = lam @@ fun x -> x
  end
end

module SKIEval = SKI.Make (Eval)
module SKIPretty = SKI.Make (Pretty)
module SKIDeBruijnPretty = SKI.Make (DeBruijnPretty)

let () =
  printf "%d\n" @@ SKIEval.(s () % k () % i ()) 1;
  printf "%a\n" Pretty.pp SKIPretty.(s () % k () % i ());
  printf "%a\n" DeBruijnPretty.pp SKIDeBruijnPretty.(s () % k () % i ())
;;
