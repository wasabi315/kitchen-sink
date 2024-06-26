open! Core
open Format

type 'x term = 'x term' * 'xmeta
  constraint
    'x =
    < xname : 'xname
    ; xbind : 'xbind
    ; xvar : 'xvar
    ; xapp : 'xapp
    ; xlam : 'xlam
    ; xlet : 'xlet
    ; xmeta : 'xmeta
    ; .. >

and 'x term' =
  | EVar of 'xvar * 'xname
  | EApp of 'xapp * 'x term * 'x term
  | ELam of 'xlam * 'xbind * 'x term
  | ELet of 'xlet * 'xbind * 'x term * 'x term
  constraint
    'x =
    < xname : 'xname
    ; xbind : 'xbind
    ; xvar : 'xvar
    ; xapp : 'xapp
    ; xlam : 'xlam
    ; xlet : 'xlet
    ; xmeta : 'xmeta
    ; .. >

type x_parsed =
  < xname : string
  ; xbind : string
  ; xvar : unit
  ; xapp : unit
  ; xlam : unit
  ; xlet : unit
  ; xmeta : Asai.Range.t >

type parsed = x_parsed term

let pp_paren b p ppf =
  if b then fprintf ppf "(";
  fprintf ppf "%t" p;
  if b then fprintf ppf ")"
;;

let pp_parsed =
  let rec pp prec : parsed -> formatter -> unit = function
    | EVar (_, v), _ -> dprintf "%s" v
    | EApp (_, t, u), _ -> pp_paren (prec > 10) (dprintf "%t %t" (pp 10 t) (pp 11 u))
    | ELam (_, x, t), _ -> pp_paren (prec > 0) (dprintf "λ%s. %t" x (pp 0 t))
    | ELet (_, x, t, u), _ ->
      pp_paren (prec > 0) (dprintf "let %s = %t in@, %t" x (pp 0 t) (pp 0 u))
  in
  Fn.flip (pp 0)
;;
