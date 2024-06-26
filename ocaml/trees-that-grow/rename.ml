open! Core
open Syntax
open Format

type x_renamed =
  < xname : int
  ; xbind : unit
  ; xnat : unit
  ; xsuc : unit
  ; xnatrec : unit
  ; xvar : string
  ; xapp : unit
  ; xlam : string
  ; xlet : string
  ; xmeta : Asai.Range.t >

type renamed = x_renamed term

let pp_renamed =
  let rec pp prec : renamed -> formatter -> unit = function
    | ENat (_, n), _ -> dprintf "%d" n
    | ESuc _, _ -> dprintf "suc"
    | ENatrec _, _ -> dprintf "natrec"
    | EVar (_, v), _ -> dprintf "#%d" v
    | EApp (_, t, u), _ -> pp_paren (prec > 10) (dprintf "%t %t" (pp 10 t) (pp 11 u))
    | ELam (_, _, t), _ -> pp_paren (prec > 0) (dprintf "λ %t" (pp 0 t))
    | ELet (_, _, t, u), _ ->
      pp_paren (prec > 0) (dprintf "let %t in@, %t" (pp 0 t) (pp 0 u))
  in
  Fn.flip (pp 0)
;;

let rename =
  let rec rn env : parsed -> renamed = function
    | ((ENat _ | ESuc _ | ENatrec _), _) as e -> e
    | EVar ((), x), loc ->
      let i = List.findi env ~f:(fun _ y -> String.(x = y)) in
      (match i with
       | None -> Reporter.fatalf ~loc Unbound_var {|unbound variable "%s"|} x
       | Some (i, _) -> EVar (x, i), loc)
    | EApp ((), e1, e2), loc -> EApp ((), rn env e1, rn env e2), loc
    | ELam ((), x, e), loc -> ELam (x, (), rn (x :: env) e), loc
    | ELet ((), x, e1, e2), loc ->
      let e1 = Reporter.tracef {|when checking "%s"|} x @@ fun () -> rn env e1 in
      ELet (x, (), e1, rn (x :: env) e2), loc
  in
  rn []
;;
