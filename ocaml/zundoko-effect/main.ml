open Format

module ZunDoko : sig
  val zun : unit -> unit
  val doko : unit -> unit
  val run : (unit -> 'a) -> 'a
end = struct
  open Effect
  open Effect.Shallow

  type 'a Effect.t += Zun : unit Effect.t
  type 'a Effect.t += Doko : unit Effect.t
  type 'a Effect.t += Kiyoshi : unit Effect.t

  let zun () = perform Zun
  let doko () = perform Doko
  let kiyoshi () = perform Kiyoshi
  let default_handler = { retc = (fun x -> x); exnc = raise; effc = (fun _ -> None) }
  let zun_then next k = continue_with k (zun ()) next
  let doko_then next k = continue_with k (doko ()) next

  let doko_kiyoshi_then next k =
    continue_with
      k
      (doko ();
       kiyoshi ())
      next
  ;;

  let rec zun0 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun_then zun1)
          | Doko -> Some (doko_then zun0)
          | _ -> None)
    }

  and zun1 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun_then zun2)
          | Doko -> Some (doko_then zun0)
          | _ -> None)
    }

  and zun2 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun_then zun3)
          | Doko -> Some (doko_then zun0)
          | _ -> None)
    }

  and zun3 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun_then zun4)
          | Doko -> Some (doko_then zun0)
          | _ -> None)
    }

  and zun4 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun_then zun4)
          | Doko -> Some (doko_kiyoshi_then zun0)
          | _ -> None)
    }
  ;;

  let rec printer =
    let printf_continue str k = continue_with k (printf str) printer in
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (printf_continue "\u{30BA}\u{30F3}\n")
          | Doko -> Some (printf_continue "\u{30C9}\u{30B3}\n")
          | Kiyoshi -> Some (printf_continue "\u{30AD}\u{30E8}\u{30B7}\u{FF01}\n")
          | _ -> None)
    }
  ;;

  let run f = continue_with (fiber @@ continue_with (fiber f) ()) zun0 printer
end

open ZunDoko

let () =
  run (fun () ->
    zun ();
    doko ();
    doko ();
    doko ();
    zun ();
    doko ();
    zun ();
    zun ();
    zun ();
    zun ();
    zun ();
    doko ();
    zun ();
    doko ())
;;
