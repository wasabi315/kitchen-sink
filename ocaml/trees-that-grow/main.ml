open! Core
open Format

module Tuple = struct
  include Tuple

  module Make_sexpable (T1 : Sexpable) (T2 : Sexpable) = struct
    include Tuple.Make (T1) (T2)
    include Tuple.Sexpable (T1) (T2)
  end

  module Make3_sexpable (T1 : Sexpable) (T2 : Sexpable) (T3 : Sexpable) = struct
    type t = T1.t * T2.t * T3.t

    open Sexp

    let sexp_of_t (t1, t2, t3) =
      List [ T1.sexp_of_t t1; T2.sexp_of_t t2; T3.sexp_of_t t3 ]
    ;;

    let t_of_sexp = function
      | List [ t1; t2; t3 ] -> T1.t_of_sexp t1, T2.t_of_sexp t2, T3.t_of_sexp t3
      | _ -> of_sexp_error "Tuple.Make3_sexpable.t" (Atom "expected 3-element list")
    ;;
  end
end

(* Syntax *)

module type X = sig
  module Name : Sexpable.S
  module XVar : Sexpable.S
  module XApp : Sexpable.S
  module Decl : Sexpable.S
  module XLam : Sexpable.S
  module LetDecl : Sexpable.S
  module XLet : Sexpable.S
end

module Term (X : X) = struct
  open X

  type t =
    | Var of XVar.t * Name.t
    | App of XApp.t * t * t
    | Lam of XLam.t * Decl.t * t
    | Let of XLet.t * LetDecl.t * t * t
  [@@deriving sexp]
end

module Parsed = struct
  include Term (struct
      module Name = String
      module XVar = Unit
      module XApp = Unit
      module Decl = String
      module XLam = Unit
      module LetDecl = String
      module XLet = Unit
    end)

  let lam var t = Lam ((), var, t)
  let ( % ) t1 t2 = App ((), t1, t2)
  let var v = Var ((), v)
  let let' var t1 t2 = Let ((), var, t1, t2)
end

module Renamed = Term (struct
    module Name = Int (* debruijn index *)
    module XVar = String (* original name *)
    module XApp = Unit
    module Decl = Unit
    module XLam = String (* original name *)
    module LetDecl = Unit
    module XLet = String (* original name *)
  end)

module Type' = struct
  type t =
    | TVar of tvar ref
    | Arr of t * t

  and tvar =
    | Unbound of int * level
    | Bound of int
    | Link of t

  and level = int [@@deriving sexp]
end

module Typed' = Term (struct
    module Name = Int
    module XVar = Tuple.Make_sexpable (String) (Type')
    module XApp = Type'
    module Decl = Unit
    module XLam = Tuple.Make_sexpable (String) (Type')
    module LetDecl = Unit
    module XLet = Tuple.Make3_sexpable (String) (Type') (Type')
  end)

module Type = struct
  type t =
    | TVar of char
    | Arr of t * t
  [@@deriving sexp]
end

module Typed = Term (struct
    module Name = Int
    module XVar = Tuple.Make_sexpable (String) (Type)
    module XApp = Type
    module Decl = Unit
    module XLam = Tuple.Make_sexpable (String) (Type)
    module LetDecl = Unit
    module XLet = Tuple.Make3_sexpable (String) (Type) (Type)
  end)

(* Renaming *)

let rename =
  let rec aux env : Parsed.t -> Renamed.t = function
    | Var ((), var) ->
      (match List.findi env ~f:(fun _ -> String.equal var) with
       | Some (index, _) -> Var (var, index)
       | None -> failwithf "unbound variable %s" var ())
    | App ((), t1, t2) ->
      let t1 = aux env t1 in
      let t2 = aux env t2 in
      App ((), t1, t2)
    | Lam ((), var, t) ->
      let env = var :: env in
      let t = aux env t in
      Lam (var, (), t)
    | Let ((), var, t1, t2) ->
      let t1 = aux env t1 in
      let env = var :: env in
      let t2 = aux env t2 in
      Let (var, (), t1, t2)
  in
  aux []
;;

(* Type inference *)

let rec occur_check lvl tvar = function
  | Type'.TVar { contents = Link t } -> occur_check lvl tvar t
  | TVar { contents = Bound _ } -> assert false
  | TVar ({ contents = Unbound (tvar', lvl') } as r) ->
    if tvar = tvar' then failwith "occur_check" else r := Unbound (tvar', min lvl lvl')
  | Arr (t1, t2) ->
    occur_check lvl tvar t1;
    occur_check lvl tvar t2
;;

let rec unify (t1 : Type'.t) (t2 : Type'.t) =
  match t1, t2 with
  | t1, t2 when phys_equal t1 t2 -> ()
  | TVar { contents = Link t1 }, t2 | t1, TVar { contents = Link t2 } -> unify t1 t2
  | TVar ({ contents = Unbound (id, lvl) } as tvar), t
  | t, TVar ({ contents = Unbound (id, lvl) } as tvar) ->
    occur_check lvl id t;
    tvar := Link t
  | Arr (t1l, t1r), Arr (t2l, t2r) ->
    unify t1l t2l;
    unify t1r t2r
  | TVar { contents = Bound _ }, _ | _, TVar { contents = Bound _ } -> assert false
;;

let fresh_tvar =
  let counter = ref 0 in
  fun lvl ->
    let tvar = Type'.TVar (ref (Type'.Unbound (!counter, lvl))) in
    incr counter;
    tvar
;;

let rec generalize lvl : Type'.t -> unit = function
  | TVar ({ contents = Unbound (id, lvl') } as tvar) when lvl' > lvl -> tvar := Bound id
  | TVar { contents = Link t } -> generalize lvl t
  | Arr (t1, t2) ->
    generalize lvl t1;
    generalize lvl t2
  | _ -> ()
;;

let instantiate lvl : Type'.t -> Type'.t =
  let rec aux subst : Type'.t -> Type'.t = function
    | TVar { contents = Link t } -> aux subst t
    | TVar { contents = Bound id } ->
      Hashtbl.find_or_add subst id ~default:(fun () -> fresh_tvar lvl)
    | Arr (t1, t2) -> Arr (aux subst t1, aux subst t2)
    | ty -> ty
  in
  aux (Hashtbl.create (module Int))
;;

let fresh_qvar =
  let counter = ref 'a' in
  fun () ->
    let tvar = Type.TVar !counter in
    counter := Char.of_int_exn (Char.to_int !counter + 1);
    tvar
;;

let rec typed_of_typed' : Typed'.t -> Typed.t =
  let tvar_map = Hashtbl.create (module Int) in
  let rec type_of_type' : Type'.t -> Type.t = function
    | TVar { contents = Unbound (v, _) } | TVar { contents = Bound v } ->
      Hashtbl.find_or_add tvar_map v ~default:fresh_qvar
    | TVar { contents = Link t } -> type_of_type' t
    | Arr (t1, t2) -> Arr (type_of_type' t1, type_of_type' t2)
  in
  function
  | Var ((name, ty), index) -> Var ((name, type_of_type' ty), index)
  | App (ty, t1, t2) ->
    let ty = type_of_type' ty in
    let t1 = typed_of_typed' t1 in
    let t2 = typed_of_typed' t2 in
    App (ty, t1, t2)
  | Lam ((name, arg_ty), (), t) ->
    let arg_ty = type_of_type' arg_ty in
    let t = typed_of_typed' t in
    Lam ((name, arg_ty), (), t)
  | Let ((name, t1_ty, t2_ty), (), t1, t2) ->
    let t1_ty = type_of_type' t1_ty in
    let t2_ty = type_of_type' t2_ty in
    let t1 = typed_of_typed' t1 in
    let t2 = typed_of_typed' t2 in
    Let ((name, t1_ty, t2_ty), (), t1, t2)
;;

let infer =
  let rec aux lvl (env : Type'.t list) : Renamed.t -> Typed'.t * Type'.t = function
    | Var (name, index) ->
      let t = instantiate lvl (List.nth_exn env index) in
      Var ((name, t), index), t
    | App ((), t1, t2) ->
      let t1, t1_ty = aux lvl env t1 in
      let t2, t2_ty = aux lvl env t2 in
      let res_ty = fresh_tvar lvl in
      unify t1_ty (Arr (t2_ty, res_ty));
      App (res_ty, t1, t2), res_ty
    | Lam (name, (), t) ->
      let arg_ty = fresh_tvar lvl in
      let t, t_ty = aux lvl (arg_ty :: env) t in
      Lam ((name, arg_ty), (), t), Arr (arg_ty, t_ty)
    | Let (name, (), t1, t2) ->
      let t1, t1_ty = aux (lvl + 1) env t1 in
      generalize lvl t1_ty;
      let t2, t2_ty = aux lvl (t1_ty :: env) t2 in
      Let ((name, t1_ty, t2_ty), (), t1, t2), t2_ty
  in
  fun t ->
    let t, ty = aux 0 [] t in
    generalize 0 ty;
    typed_of_typed' t
;;

(* main *)

let ex =
  let open Parsed in
  let' "k" (lam "x" (lam "y" (var "x")))
  @@ let' "s" (lam "f" (lam "g" (lam "x" (var "f" % var "x" % (var "g" % var "x")))))
  @@ let' "i" (var "s" % var "k" % var "k")
  @@ (var "s" % var "k" % var "i")
;;

let () =
  print_endline
    "--------------------------------------------------------------------------------";
  Sexp.output_hum stdout (Parsed.sexp_of_t ex);
  print_newline ();
  print_endline
    "--------------------------------------------------------------------------------";
  let ex = rename ex in
  Sexp.output_hum stdout (Renamed.sexp_of_t ex);
  print_newline ();
  print_endline
    "--------------------------------------------------------------------------------";
  let ex = infer ex in
  Sexp.output_hum stdout (Typed.sexp_of_t ex)
;;
