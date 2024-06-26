open! Core
open Syntax
open Format
open Rename
module Id = Int
module Level = Int

type ty_ =
  | TNat'
  | TVar' of tvar ref
  | TArr' of ty_ * ty_

and tvar =
  | Unbound of Id.t * Level.t
  | Link of ty_
  | Generic of Id.t

type scheme_ = Id.Set.t * ty_

let gen_id =
  let r = ref 0 in
  fun () ->
    let id = !r in
    incr r;
    id
;;

type x_typed_ =
  < xname : int
  ; xbind : unit
  ; xnat : unit
  ; xsuc : unit
  ; xnatrec : unit
  ; xvar : string
  ; xapp : unit
  ; xlam : string * ty_ (* type of the argument *)
  ; xlet : string * scheme_ (* type of the bound variable *)
  ; xmeta : Asai.Range.t * ty_ >

type typed_ = x_typed_ term

let pp_ty_ =
  let rec pp prec = function
    | TNat' -> dprintf "Nat"
    | TVar' { contents = Unbound (id, _) } -> dprintf "_%d" id
    | TVar' { contents = Link ty } -> pp prec ty
    | TVar' { contents = Generic id } -> dprintf "'%d" id
    | TArr' (ty1, ty2) ->
      pp_paren (prec > 10) (dprintf "%t -> %t" (pp 11 ty1) (pp 10 ty2))
  in
  Fn.flip (pp 0)
;;

let pp_scheme_ ppf (ids, ty) =
  fprintf
    ppf
    "∀ %a. %a"
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") (fun ppf -> fprintf ppf "_%d"))
    (Set.to_list ids)
    pp_ty_
    ty
;;

let pp_typed_ =
  let rec pp : typed_ -> formatter -> unit = function
    | ENat (_, n), _ -> dprintf "%d" n
    | ESuc _, _ -> dprintf "suc"
    | ENatrec _, _ -> dprintf "natrec"
    | EVar (_, i), (_, ty) -> dprintf "(#%d : %a)" i pp_ty_ ty
    | EApp (_, t, u), (_, ty) -> dprintf "(%t %t : %a)" (pp t) (pp u) pp_ty_ ty
    | ELam ((_, argty), (), t), (_, ty) ->
      dprintf "((λ _: %a. %t) : %a)" pp_ty_ argty (pp t) pp_ty_ ty
    | ELet ((_, varty), (), t, u), (_, ty) ->
      dprintf "((let _: %a = %t in@, %t) : %a)" pp_scheme_ varty (pp t) (pp u) pp_ty_ ty
  in
  Fn.flip pp
;;

let new_var level = TVar' (ref (Unbound (gen_id (), level)))

let rec occurs id = function
  | TNat' -> false
  | TVar' { contents = Unbound (id', _) } -> id = id'
  | TVar' { contents = Link ty } -> occurs id ty
  | TVar' { contents = Generic _ } -> false
  | TArr' (ty1, ty2) -> occurs id ty1 || occurs id ty2
;;

let rec adjust_level level = function
  | TNat' -> ()
  | TVar' ({ contents = Unbound (id, level') } as tv) ->
    if level' > level then tv := Unbound (id, level)
  | TVar' { contents = Link ty } -> adjust_level level ty
  | TVar' { contents = Generic _ } -> ()
  | TArr' (ty1, ty2) ->
    adjust_level level ty1;
    adjust_level level ty2
;;

let rec unify ty1 ty2 =
  match ty1, ty2 with
  | _, _ when phys_equal ty1 ty2 -> ()
  | TArr' (ty11, ty12), TArr' (ty21, ty22) ->
    unify ty11 ty21;
    unify ty12 ty22
  | TVar' { contents = Link ty1 }, ty2 | ty1, TVar' { contents = Link ty2 } ->
    unify ty1 ty2
  | TVar' ({ contents = Unbound (id, level) } as tv), ty
  | ty, TVar' ({ contents = Unbound (id, level) } as tv) ->
    if occurs id ty then Reporter.fatalf Type_err "Recursive type detected";
    adjust_level level ty;
    tv := Link ty
  | _ -> Reporter.fatalf Type_err "Could not match %a and %a" pp_ty_ ty1 pp_ty_ ty2
;;

let rec generalise level = function
  | TVar' ({ contents = Unbound (id, level') } as tv) when level' > level ->
    tv := Generic id;
    Id.Set.singleton id, TVar' tv
  | TVar' { contents = Link ty } -> generalise level ty
  | TArr' (ty1, ty2) ->
    let tvs1, ty1 = generalise level ty1 in
    let tvs2, ty2 = generalise level ty2 in
    Set.union tvs1 tvs2, TArr' (ty1, ty2)
  | t -> Id.Set.empty, t
;;

let instantiate level ty =
  let id_var_map = Hashtbl.create (module Id) in
  let rec f = function
    | TNat' -> TNat'
    | TVar' { contents = Link ty } -> f ty
    | TVar' { contents = Generic id } ->
      Hashtbl.find_or_add id_var_map id ~default:(fun () -> new_var level)
    | TVar' { contents = Unbound _ } as ty -> ty
    | TArr' (ty1, ty2) -> TArr' (f ty1, f ty2)
  in
  f ty
;;

let rec match_fun_ty = function
  | TArr' (paramty, retty) -> paramty, retty
  | TVar' { contents = Link ty } -> match_fun_ty ty
  | TVar' ({ contents = Unbound (_, level) } as tv) ->
    let paramty = new_var level in
    let retty = new_var level in
    tv := Link (TArr' (paramty, retty));
    paramty, retty
  | t -> Reporter.fatalf Type_err "Expected a function type, but got %a" pp_ty_ t
;;

let rec infer_ env level : renamed -> typed_ = function
  | (ENat _ as e), loc -> e, (loc, TNat')
  | (ESuc _ as e), loc -> e, (loc, TArr' (TNat', TNat'))
  | (ENatrec _ as e), loc ->
    let tv = new_var level in
    let ty = TArr' (tv, TArr' (TArr' (TNat', TArr' (tv, tv)), TArr' (TNat', tv))) in
    e, (loc, ty)
  | EVar (x, i), loc ->
    let ty = instantiate level (List.nth_exn env i) in
    EVar (x, i), (loc, ty)
  | EApp ((), t, u), loc ->
    let ((_, (_, funty)) as t) = infer_ env level t in
    let paramty, retty = match_fun_ty funty in
    let ((_, (_, argty)) as u) = infer_ env level u in
    unify paramty argty;
    EApp ((), t, u), (loc, retty)
  | ELam (x, (), t), loc ->
    let argty = new_var level in
    let ((_, (_, retty)) as t) = infer_ (argty :: env) level t in
    let ty = TArr' (argty, retty) in
    ELam ((x, argty), (), t), (loc, ty)
  | ELet (x, (), t, u), loc ->
    let ((_, (_, varty)) as t) =
      Reporter.tracef ~loc "When typechecking %s" x @@ fun () -> infer_ env (level + 1) t
    in
    let ((_, varty) as scheme) = generalise level varty in
    let ((_, (_, bodyty)) as u) = infer_ (varty :: env) level u in
    ELet ((x, scheme), (), t, u), (loc, bodyty)
;;

type ty =
  | TNat
  | TVar of char
  | TArr of ty * ty

type scheme = Char.Set.t * ty

type x_typed =
  < xname : int
  ; xbind : unit
  ; xnat : unit
  ; xsuc : unit
  ; xnatrec : unit
  ; xvar : string
  ; xapp : unit
  ; xlam : string * ty (* type of the argument *)
  ; xlet : string * scheme (* type of the bound variable *)
  ; xmeta : Asai.Range.t * ty >

type typed = x_typed term

let pp_ty =
  let rec pp prec = function
    | TNat -> dprintf "Nat"
    | TVar id -> dprintf "%c" id
    | TArr (ty1, ty2) -> pp_paren (prec > 10) (dprintf "%t -> %t" (pp 11 ty1) (pp 10 ty2))
  in
  Fn.flip (pp 0)
;;

let pp_scheme ppf (ids, ty) =
  fprintf
    ppf
    "∀ %a. %a"
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") pp_print_char)
    (Set.to_list ids)
    pp_ty
    ty
;;

let pp_typed ppf t =
  let rec pp prec = function
    | ENat (_, n), _ -> dprintf "%d" n
    | ESuc _, _ -> dprintf "suc"
    | ENatrec _, _ -> dprintf "natrec"
    | EVar (_, i), _ -> dprintf "#%d" i
    | EApp (_, t, u), _ -> pp_paren (prec > 10) (dprintf "%t %t" (pp 10 t) (pp 11 u))
    | ELam ((_, argty), (), t), _ ->
      pp_paren (prec > 0) (dprintf "λ _: %a. %t" pp_ty argty (pp 0 t))
    | ELet ((_, varty), (), t, u), _ ->
      pp_paren
        (prec > 0)
        (dprintf "let _: %a = %t in@, %t" pp_scheme varty (pp 0 t) (pp 0 u))
  in
  pp 0 t ppf
;;

let fresh_qvar =
  let r = ref 'a' in
  fun () ->
    let tvar = !r in
    r := Char.of_int_exn (Char.to_int !r + 1);
    tvar
;;

let typed_of_typed_ =
  let tbl = Hashtbl.create (module Id) in
  let rec ty_of_ty_ : ty_ -> ty = function
    | TNat' -> TNat
    | TVar' { contents = Unbound (_, _) } ->
      Reporter.fatalf Impossible "Unbound type variable"
    | TVar' { contents = Link ty } -> ty_of_ty_ ty
    | TVar' { contents = Generic id } ->
      TVar (Hashtbl.find_or_add tbl ~default:fresh_qvar id)
    | TArr' (ty1, ty2) -> TArr (ty_of_ty_ ty1, ty_of_ty_ ty2)
  in
  let scheme_of_scheme_ ((ids, ty) : scheme_) : scheme =
    ( Set.map (module Char) ids ~f:(Hashtbl.find_or_add tbl ~default:fresh_qvar)
    , ty_of_ty_ ty )
  in
  let rec f : typed_ -> typed = function
    | (ENat _ as e), (loc, ty) -> e, (loc, ty_of_ty_ ty)
    | (ESuc _ as e), (loc, ty) -> e, (loc, ty_of_ty_ ty)
    | (ENatrec _ as e), (loc, ty) -> e, (loc, ty_of_ty_ ty)
    | EVar (x, i), (loc, ty) -> EVar (x, i), (loc, ty_of_ty_ ty)
    | EApp ((), t, u), (loc, ty) ->
      let t = f t in
      let u = f u in
      let ty = ty_of_ty_ ty in
      EApp ((), t, u), (loc, ty)
    | ELam ((x, argty), (), t), (loc, ty) ->
      let argty = ty_of_ty_ argty in
      let t = f t in
      let ty = ty_of_ty_ ty in
      ELam ((x, argty), (), t), (loc, ty)
    | ELet ((x, scheme), (), t, u), (loc, ty) ->
      let scheme = scheme_of_scheme_ scheme in
      let t = f t in
      let u = f u in
      let ty = ty_of_ty_ ty in
      ELet ((x, scheme), (), t, u), (loc, ty)
  in
  f
;;

let infer t =
  let ((_, (_, ty)) as t) = infer_ [] 1 t in
  (* generalize toplevel term implicitly *)
  let _ = generalise 0 ty in
  typed_of_typed_ t
;;
