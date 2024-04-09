open! Core
open Format

module Tuple = struct
  include Tuple

  module Make_sexpable (T1 : Sexpable) (T2 : Sexpable) = struct
    include Tuple.Make (T1) (T2)
    include Tuple.Sexpable (T1) (T2)
  end
end

(* Syntax *)

module type X = sig
  module Name : Sexpable.S
  module XVar : Sexpable.S
  module XApp : Sexpable.S
  module Decl : Sexpable.S
  module XLam : Sexpable.S
end

module Term (X : X) = struct
  open X

  type t =
    | Var of XVar.t * Name.t
    | App of XApp.t * t * t
    | Lam of XLam.t * Decl.t * t
  [@@deriving sexp]
end

module Parsed = struct
  include Term (struct
      module Name = String
      module XVar = Unit
      module XApp = Unit
      module Decl = String
      module XLam = Unit
    end)

  let lam var t = Lam ((), var, t)
  let ( @ ) t1 t2 = App ((), t1, t2)
  let var v = Var ((), v)
end

module Renamed = Term (struct
    module Name = Int (* debruijn index *)
    module XVar = String (* original name *)
    module XApp = Unit
    module Decl = Unit
    module XLam = String (* original name *)
  end)

module Type' = struct
  type t =
    | TVar of tvar ref
    | Arr of t * t

  and tvar =
    | Unbound of int
    | Link of t
  [@@deriving sexp]
end

module Typed' = Term (struct
    module Name = Int
    module XVar = Tuple.Make_sexpable (String) (Type')
    module XApp = Type'
    module Decl = Unit
    module XLam = Tuple.Make_sexpable (String) (Type')
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
  in
  aux []
;;

(* Type inference *)

let rec occur_check tvar = function
  | Type'.TVar tvar' -> if phys_equal tvar tvar' then failwith "occur_check"
  | Arr (t1, t2) ->
    occur_check tvar t1;
    occur_check tvar t2
;;

let rec unify (t1 : Type'.t) (t2 : Type'.t) =
  match t1, t2 with
  | t1, t2 when phys_equal t1 t2 -> ()
  | TVar { contents = Link t1 }, t2 | t1, TVar { contents = Link t2 } -> unify t1 t2
  | TVar ({ contents = Unbound _ } as tvar), t
  | t, TVar ({ contents = Unbound _ } as tvar) ->
    occur_check tvar t;
    tvar := Link t
  | Arr (t1l, t1r), Arr (t2l, t2r) ->
    unify t1l t2l;
    unify t1r t2r
;;

let fresh_tvar =
  let counter = ref 0 in
  fun () ->
    let tvar = Type'.TVar (ref (Type'.Unbound !counter)) in
    incr counter;
    tvar
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
    | TVar { contents = Unbound v } -> Hashtbl.find_or_add tvar_map v ~default:fresh_qvar
    | TVar { contents = Link t } -> type_of_type' t
    | Arr (t1, t2) -> Arr (type_of_type' t1, type_of_type' t2)
  in
  function
  | Var ((name, ty), index) -> Var ((name, type_of_type' ty), index)
  | App (ty, t1, t2) -> App (type_of_type' ty, typed_of_typed' t1, typed_of_typed' t2)
  | Lam ((name, arg_ty), (), t) ->
    Lam ((name, type_of_type' arg_ty), (), typed_of_typed' t)
;;

let infer =
  let rec aux (env : Type'.t list) : Renamed.t -> Typed'.t * Type'.t = function
    | Var (name, index) ->
      let t = List.nth_exn env index in
      Var ((name, t), index), t
    | App ((), t1, t2) ->
      let t1, t1_ty = aux env t1 in
      let t2, t2_ty = aux env t2 in
      let res_ty = fresh_tvar () in
      unify t1_ty (Arr (t2_ty, res_ty));
      App (res_ty, t1, t2), res_ty
    | Lam (name, (), t) ->
      let arg_ty = fresh_tvar () in
      let t, t_ty = aux (arg_ty :: env) t in
      Lam ((name, arg_ty), (), t), Arr (arg_ty, t_ty)
  in
  fun t -> typed_of_typed' (fst (aux [] t))
;;

(* main *)

let () =
  let open Parsed in
  let ex = lam "f" (lam "g" (lam "x" ((var "f" @ var "x") @ var "g" @ var "x"))) in
  Sexp.output_hum stdout (Parsed.sexp_of_t ex);
  print_newline ();
  let ex' = rename ex in
  Sexp.output_hum stdout (Renamed.sexp_of_t ex');
  print_newline ();
  let ex'' = infer ex' in
  Sexp.output_hum stdout (Typed.sexp_of_t ex'')
;;
