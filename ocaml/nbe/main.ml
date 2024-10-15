type name = string

type term =
  | Var of name
  | App of term * term
  | Abs of name * term
  | Let of name * term * term
  | Zero
  | Suc of term
  | Rec of term * term * term

type value =
  | VAbs of name * (value Lazy.t -> value)
  | VVar of name * spine
  | VZero
  | VSuc of value Lazy.t

and spine =
  | SNil
  | SApp of spine * value Lazy.t
  | SRec of value Lazy.t * value Lazy.t * spine

module Env = Map.Make (String)

type env = value Lazy.t Env.t

let ( % ) (v : value) (u : value Lazy.t) : value =
  match v with
  | VAbs (_, f) -> f u
  | VVar (hd, sp) -> VVar (hd, SApp (sp, u))
  | _ -> failwith "applying non-function"
;;

let rec vrec (z : value Lazy.t) (s : value Lazy.t) (n : value) : value =
  match n with
  | VZero -> Lazy.force z
  | VSuc n -> Lazy.force s % n % Lazy.map (vrec z s) n
  | VVar (hd, sp) -> VVar (hd, SRec (z, s, sp))
  | _ -> failwith "rec on non-number"
;;

let rec eval (env : env) : term -> value = function
  | Var x -> Lazy.force (Env.find x env)
  | App (t, u) -> eval env t % lazy (eval env u)
  | Abs (x, t) -> VAbs (x, fun u -> eval (Env.add x u env) t)
  | Let (x, t, u) -> eval (Env.add x (lazy (eval env t)) env) u
  | Zero -> VZero
  | Suc n -> VSuc (lazy (eval env n))
  | Rec (z, s, n) -> vrec (lazy (eval env z)) (lazy (eval env s)) (eval env n)
;;

let rec freshen (env : env) (x : name) : name =
  if Env.mem x env then freshen env (x ^ "'") else x
;;

let rec quote (env : env) : value -> term = function
  | VAbs (x, f) ->
    let x = freshen env x in
    let v = Lazy.from_val (VVar (x, SNil)) in
    quote (Env.add x v env) (f v)
  | VVar (x, sp) -> quoteSpine env (Var x) sp
  | VZero -> Zero
  | VSuc n -> Suc (quote env (Lazy.force n))

and quoteSpine (env : env) (hd : term) : spine -> term = function
  | SNil -> hd
  | SApp (sp, u) -> App (quoteSpine env hd sp, quote env (Lazy.force u))
  | SRec (z, s, sp) ->
    Rec (quote env (Lazy.force z), quote env (Lazy.force s), quoteSpine env hd sp)
;;

let normalize (t : term) : term = quote Env.empty (eval Env.empty t)

let term_of_nat : int -> term =
  let rec go acc = function
    | 0 -> acc
    | n -> go (Suc acc) (n - 1)
  in
  go Zero
;;

let nat_of_term : term -> int =
  let rec go acc = function
    | Zero -> acc
    | Suc n -> go (acc + 1) n
    | _ -> failwith "not a number"
  in
  go 0
;;

let plus : term =
  Abs ("m", Abs ("n", Rec (Var "n", Abs ("_", Abs ("x", Suc (Var "x"))), Var "m")))
;;

let ( + ) (m : term) (n : term) : term = App (App (plus, m), n)
let mult : term = Abs ("m", Abs ("n", Rec (Zero, Abs ("_", App (plus, Var "n")), Var "m")))
let ( * ) (m : term) (n : term) : term = App (App (mult, m), n)
let id = Abs ("x", Var "x")
let const = Abs ("x", Abs ("_", Var "x"))

let omega =
  let f = Abs ("x", App (Var "x", Var "x")) in
  App (f, f)
;;

let () =
  let open Format in
  (* normalizes *)
  ignore @@ normalize (App (App (const, id), omega));
  printf "%d\n"
  @@ nat_of_term
  @@ normalize
  @@ ((term_of_nat 8 * term_of_nat 5) + term_of_nat 2)
;;
