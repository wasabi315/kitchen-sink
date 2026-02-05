open! Core
open Format

type name = string
type index = int
type level = int
type iso_var = int

type iso_side =
  | Forward
  | Backward

type term =
  | Var of index
  | Link of iso_var * iso_side
  | U
  | Pi of name * term * term
  | Lam of name * term
  | App of term * term
  | Sigma of name * term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | Weaken of term
[@@deriving variants]

let ( @-> ) t u = Pi ("_", t, Weaken u)
let ( @* ) t u = Sigma ("_", t, Weaken u)

type value =
  | VRigid of level * spine
  | VLink of iso_var * iso_side * spine
  | VU
  | VPi of name * value * (value -> value)
  | VLam of name * (value -> value)
  | VSigma of name * value * (value -> value)
  | VPair of value * value

and spine =
  | SNil
  | SApp of spine * value
  | SFst of spine
  | SSnd of spine
  | SCurry of iso_var * spine
  | SAssoc of iso_var * spine

type iso =
  | Link of iso_var
  | Refl
  | Sym of iso
  | Trans of iso * iso
  | Assoc
  | Comm
  | Curry
  | Pi_cong_l of iso
  | Pi_cong_r of iso
  | Sigma_cong_l of iso
  | Sigma_cong_r of iso

let iso_context : iso option Stdlib.Dynarray.t = Stdlib.Dynarray.create ()
let lookup_iso = Stdlib.Dynarray.get iso_context

let new_iso_var () =
  let i = Stdlib.Dynarray.length iso_context in
  Stdlib.Dynarray.add_last iso_context None;
  i
;;

let set_iso iv i = Stdlib.Dynarray.set iso_context iv (Some i)
let clear_iso () = Stdlib.Dynarray.clear iso_context

let rec eval env = function
  | Var x -> List.nth_exn env x
  | Link (i, s) -> vunknown i s
  | U -> VU
  | Pi (x, a, b) ->
    let a = eval env a in
    let b v = eval (v :: env) b in
    VPi (x, a, b)
  | Lam (x, t) ->
    let t v = eval (v :: env) t in
    VLam (x, t)
  | App (t, u) ->
    let t = eval env t in
    let u = eval env u in
    t % u
  | Sigma (x, a, b) ->
    let a = eval env a in
    let b v = eval (v :: env) b in
    VSigma (x, a, b)
  | Pair (t, u) ->
    let t = eval env t in
    let u = eval env u in
    VPair (t, u)
  | Fst t ->
    let t = eval env t in
    vfst t
  | Snd t ->
    let t = eval env t in
    vsnd t
  | Weaken t ->
    (match env with
     | [] -> failwith "out of range"
     | _ :: env -> eval env t)

and ( % ) t u =
  match t with
  | VLam (_, t) -> t u
  | VRigid (x, sp) -> VRigid (x, SApp (sp, u))
  | VLink (i, s, sp) -> VLink (i, s, SApp (sp, u))
  | _ -> failwith "not a function"

and ( %% ) t = function
  | SNil -> t
  | SApp (sp, u) -> t %% sp % u
  | SFst sp -> vfst (t %% sp)
  | SSnd sp -> vsnd (t %% sp)
  | SCurry (iv, sp) -> curry iv (t %% sp)
  | SAssoc (iv, sp) -> assoc iv (t %% sp)

and vfst = function
  | VPair (t, _) -> t
  | VRigid (x, sp) -> VRigid (x, SFst sp)
  | VLink (i, s, sp) -> VLink (i, s, SFst sp)
  | _ -> failwith "not a pair"

and vsnd = function
  | VPair (_, t) -> t
  | VRigid (x, sp) -> VRigid (x, SSnd sp)
  | VLink (i, s, sp) -> VLink (i, s, SSnd sp)
  | _ -> failwith "not a pair"

and vunknown i s =
  match lookup_iso i, s with
  | None, _ -> VLink (i, s, SNil)
  | Some i, Forward -> transport_fun i
  | Some i, Backward -> transport_inv_fun i

and transport i v =
  match i with
  | Link i ->
    (match lookup_iso i with
     | Some i -> transport i v
     | None -> VLink (i, Forward, SApp (SNil, v)))
  | Refl -> v
  | Sym i -> transport_inv i v
  | Trans (i, j) -> transport j (transport i v)
  | Assoc ->
    let v1 = vfst (vfst v) in
    let v2 = vsnd (vfst v) in
    let v3 = vsnd v in
    VPair (v1, VPair (v2, v3))
  | Comm ->
    let v1 = vfst v in
    let v2 = vsnd v in
    VPair (v2, v1)
  | Curry -> VLam ("x", fun x -> VLam ("y", fun y -> v % VPair (x, y)))
  | Pi_cong_l i -> VLam ("x", fun x -> v % transport_inv i x)
  | Pi_cong_r i -> VLam ("x", fun x -> transport i (v % x))
  | Sigma_cong_l i ->
    let v1 = transport i (vfst v) in
    let v2 = vsnd v in
    VPair (v1, v2)
  | Sigma_cong_r i ->
    let v1 = vfst v in
    let v2 = transport i (vsnd v) in
    VPair (v1, v2)

and transport_inv i v =
  match i with
  | Link i ->
    (match lookup_iso i with
     | Some i -> transport_inv i v
     | None -> VLink (i, Backward, SApp (SNil, v)))
  | Refl -> v
  | Sym i -> transport i v
  | Trans (i, j) -> transport_inv i (transport_inv j v)
  | Assoc ->
    let v1 = vfst v in
    let v2 = vfst (vsnd v) in
    let v3 = vsnd (vsnd v) in
    VPair (VPair (v1, v2), v3)
  | Comm ->
    let v1 = vfst v in
    let v2 = vsnd v in
    VPair (v2, v1)
  | Curry -> VLam ("p", fun p -> v % vfst p % vsnd p)
  | Pi_cong_l i -> VLam ("x", fun x -> v % transport i x)
  | Pi_cong_r i -> VLam ("x", fun x -> transport_inv i (v % x))
  | Sigma_cong_l i ->
    let v1 = transport_inv i (vfst v) in
    let v2 = vsnd v in
    VPair (v1, v2)
  | Sigma_cong_r i ->
    let v1 = vfst v in
    let v2 = transport_inv i (vsnd v) in
    VPair (v1, v2)

and transport_fun i = VLam ("x", transport i)
and transport_inv_fun i = VLam ("x", transport_inv i)

and force = function
  | VLink (i, s, sp) as t ->
    (match lookup_iso i, s with
     | Some i, Forward -> force (transport_fun i %% sp)
     | Some i, Backward -> force (transport_inv_fun i %% sp)
     | None, _ -> t)
  | t -> t

and curry iv t =
  match force t with
  | VPi (x, VSigma (y, a, b), c) ->
    let t = VPi (y, a, fun u -> VPi (x, b u, fun v -> c (VPair (u, v)))) in
    let iv' = new_iso_var () in
    let t = curry iv' t in
    set_iso iv @@ Trans (Curry, Link iv');
    t
  | VPi (x, a, b) ->
    let iv' = new_iso_var () in
    let b v = curry iv' (b v) in
    set_iso iv @@ Pi_cong_r (Link iv');
    VPi (x, a, b)
  | VLink (iv', s, sp) ->
    let iv'' = new_iso_var () in
    set_iso iv (Link iv'');
    VLink (iv', s, SCurry (iv'', sp))
  | t ->
    set_iso iv Refl;
    t

and assoc iv t =
  match force t with
  | VSigma (x, VSigma (y, a, b), c) ->
    let t = VSigma (y, a, fun u -> VSigma (x, b u, fun v -> c (VPair (u, v)))) in
    let iv' = new_iso_var () in
    let t = assoc iv' t in
    set_iso iv @@ Trans (Assoc, Link iv');
    t
  | VSigma (x, a, b) ->
    let iv' = new_iso_var () in
    let b v = assoc iv' (b v) in
    set_iso iv @@ Sigma_cong_r (Link iv');
    VSigma (x, a, b)
  | VLink (iv', s, sp) ->
    let iv'' = new_iso_var () in
    set_iso iv (Link iv'');
    VLink (iv', s, SAssoc (iv'', sp))
  | t ->
    set_iso iv Refl;
    t
;;

let rec quote l t =
  match force t with
  | VRigid (x, sp) -> quote_spine l (Var (l - x - 1)) sp
  | VLink (i, s, sp) -> quote_spine l (Link (i, s)) sp
  | VU -> U
  | VPi (x, a, b) ->
    let a = quote l a in
    let b = quote (l + 1) (b (VRigid (l, SNil))) in
    Pi (x, a, b)
  | VLam (x, t) ->
    let t = quote (l + 1) (t (VRigid (l, SNil))) in
    Lam (x, t)
  | VSigma (x, a, b) ->
    let a = quote l a in
    let b = quote (l + 1) (b (VRigid (l, SNil))) in
    Sigma (x, a, b)
  | VPair (t, u) ->
    let t = quote l t in
    let u = quote l u in
    Pair (t, u)

and quote_spine l hd = function
  | SNil -> hd
  | SApp (sp, t) -> App (quote_spine l hd sp, quote l t)
  | SFst t -> Fst (quote_spine l hd t)
  | SSnd t -> Snd (quote_spine l hd t)
  | SCurry _ -> failwith "pending curry"
  | SAssoc _ -> failwith "pending assoc"
;;

let rec normalise iv = function
  | VPi (x, a, b) ->
    let iva = new_iso_var () in
    let ivb = new_iso_var () in
    let iv' = new_iso_var () in
    set_iso iv @@ Trans (Pi_cong_l (Link iva), Trans (Pi_cong_r (Link ivb), Link iv'));
    let a = normalise iva a in
    let b v = normalise ivb (b (transport_inv (Link iva) v)) in
    let t = curry iv' (VPi (x, a, b)) in
    t
  | VSigma (x, a, b) ->
    let iva = new_iso_var () in
    let ivb = new_iso_var () in
    let iv' = new_iso_var () in
    set_iso iv
    @@ Trans (Sigma_cong_l (Link iva), Trans (Sigma_cong_r (Link ivb), Link iv'));
    let a = normalise iva a in
    let b v = normalise ivb (b (transport_inv (Link iva) v)) in
    let t = assoc iv' (VSigma (x, a, b)) in
    t
  | v ->
    set_iso iv Refl;
    v
;;

let sym = function
  | Refl -> Refl
  | Sym i -> i
  | i -> Sym i
;;

let trans i j =
  match i, j with
  | Refl, j -> j
  | i, Refl -> i
  | _ -> Trans (i, j)
;;

let pi_cong_l = function
  | Refl -> Refl
  | i -> Pi_cong_l i
;;

let pi_cong_r = function
  | Refl -> Refl
  | i -> Pi_cong_r i
;;

let sigma_cong_l = function
  | Refl -> Refl
  | i -> Sigma_cong_l i
;;

let sigma_cong_r = function
  | Refl -> Refl
  | i -> Sigma_cong_r i
;;

let rec zonk_iso = function
  | Link x as i ->
    (match lookup_iso x with
     | Some j ->
       let j = zonk_iso j in
       set_iso x j;
       j
     | None -> i)
  | Sym i -> sym (zonk_iso i)
  | Trans (i, j) -> trans (zonk_iso i) (zonk_iso j)
  | Pi_cong_l i -> pi_cong_l (zonk_iso i)
  | Pi_cong_r i -> pi_cong_r (zonk_iso i)
  | Sigma_cong_l i -> sigma_cong_l (zonk_iso i)
  | Sigma_cong_r i -> sigma_cong_r (zonk_iso i)
  | i -> i
;;

let normalise0 t =
  let t = eval [] t in
  let iv = new_iso_var () in
  let t = normalise iv t in
  let t = quote 0 t in
  t, zonk_iso (Option.value_exn (lookup_iso iv))
;;

let par p q d = if p > q then dprintf "(%t)" d else d
let proj_p = 5
let app_p = 4
let sigma_p = 3
let pi_p = 2
let abs_p = 1
let pair_p = 0

let subscript_digits = [| "₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉" |]

let int_to_subscript n =
  String.concat_map (Int.to_string n) ~f:(fun c ->
    subscript_digits.(Char.get_digit_exn c))
;;

let freshen ns =
  let rec go i n =
    let candidate = if i = 0 then n else n ^ int_to_subscript i in
    match List.find ns ~f:(String.equal candidate) with
    | Some _ -> go (i + 1) n
    | None -> candidate
  in
  go 0
;;

let format_term =
  let rec go ns p = function
    | Var x -> dprintf "%s" (List.nth_exn ns x)
    | Link (i, _) -> dprintf "?%d" i
    | U -> dprintf "U"
    | Pi ("_", a, b) ->
      par p pi_p @@ dprintf "%t → %t" (go ns sigma_p a) (go ("_" :: ns) pi_p b)
    | Pi (n, a, b) ->
      let n = freshen ns n in
      par p pi_p @@ dprintf "%t%t" (pi_bind n ns a) (go_pi (n :: ns) b)
    | Lam (n, t) ->
      let n = freshen ns n in
      par p abs_p @@ dprintf "λ %s%t" n (go_abs (n :: ns) t)
    | App (t, u) -> par p app_p @@ dprintf "%t %t" (go ns app_p t) (go ns proj_p u)
    | Sigma ("_", a, b) ->
      par p sigma_p @@ dprintf "%t × %t" (go ns app_p a) (go ("_" :: ns) sigma_p b)
    | Sigma (n, a, b) ->
      let n = freshen ns n in
      par p sigma_p @@ dprintf "%t × %t" (pi_bind n ns a) (go (n :: ns) sigma_p b)
    | Fst t -> par p proj_p @@ dprintf "%t.1" (go ns proj_p t)
    | Snd t -> par p proj_p @@ dprintf "%t.2" (go ns proj_p t)
    | Pair (t, u) -> par p pair_p @@ dprintf "%t , %t" (go ns abs_p t) (go ns pair_p u)
    | Weaken t ->
      (match ns with
       | [] -> failwith "out of range"
       | _ :: ns -> go ns p t)
  and pi_bind n ns a = dprintf "(%s : %t)" n (go ns pair_p a)
  and go_pi ns = function
    | Pi ("_", a, b) -> dprintf " → %t → %t" (go ns sigma_p a) (go ("_" :: ns) pi_p b)
    | Pi (n, a, b) ->
      let n = freshen ns n in
      dprintf " %t%t" (pi_bind n ns a) (go_pi (n :: ns) b)
    | b -> dprintf " → %t" (go ns pi_p b)
  and go_abs ns = function
    | Lam (n, t) ->
      let n = freshen ns n in
      dprintf " %s%t" n (go_abs (n :: ns) t)
    | t -> dprintf ". %t" (go ns abs_p t)
  in
  go
;;

let rec format_iso p = function
  | Refl -> dprintf "refl"
  | Link i -> dprintf "?%d" i
  | Sym i -> par p 11 @@ dprintf "%t⁻¹" (format_iso 12 i)
  | Trans (i, j) -> par p 9 @@ dprintf "%t · %t" (format_iso 10 i) (format_iso 10 j)
  | Assoc -> dprintf "Assoc"
  | Comm -> dprintf "Comm"
  | Curry -> dprintf "Curry"
  | Pi_cong_l i -> par p 10 @@ dprintf "ΠL %t" (format_iso 11 i)
  | Pi_cong_r i -> par p 10 @@ dprintf "ΠR %t" (format_iso 11 i)
  | Sigma_cong_l i -> par p 10 @@ dprintf "ΣL %t" (format_iso 11 i)
  | Sigma_cong_r i -> par p 10 @@ dprintf "ΣR %t" (format_iso 11 i)
;;

let ex1 =
  pi "F" (((U @* U) @-> U) @-> U) @@ pi "G" ((U @* U) @-> U) @@ app (var 1) (var 0)
;;

let ex2 =
  pi "F" ((U @* U) @-> U) @@ pi "A" U @@ pi "B" U @@ app (var 2) (pair (var 1) (var 0))
;;

let ex3 =
  pi "A" U
  @@ pi "B" (var 0 @-> U)
  @@ pi "P" (sigma "x" (var 1) (app (var 1) (var 0)) @-> U)
  @@ pi "p" (sigma "x" (var 2) (app (var 2) (var 0)))
  @@ pi "q" (sigma "y" (var 3) (app (var 3) (var 0)))
  @@ app (var 2) (var 1)
  @* app (var 2) (var 0)
;;

let () =
  List.iter [ ex1; ex2; ex3 ] ~f:(fun t ->
    printf "----------------\n\n";
    printf "%t\n\n" (format_term [] 0 t);
    let t', i = normalise0 t in
    printf "  ↓ %t\n\n" (format_iso 0 i);
    printf "%t\n\n" (format_term [] 0 t');
    let i = transport_fun i in
    printf "conversion function:\n";
    printf "  %t\n\n" (format_term [] 0 @@ quote 0 i);
    clear_iso ())
;;
