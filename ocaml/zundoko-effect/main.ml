open Format

module ZunDoko : sig
  val zun : unit -> unit
  val doko : unit -> unit
  val run : (unit -> 'a) -> 'a
end = struct
  open Effect
  open Effect.Shallow

  type 'a t += Zun : unit t | Doko : unit t | Kiyoshi : unit t

  let zun () = perform Zun
  let doko () = perform Doko
  let kiyoshi () = perform Kiyoshi
  let default_handler = { retc = (fun x -> x); exnc = raise; effc = (fun _ -> None) }
  let ( / ) act next k = continue_with k (act ()) next

  let ( & ) act1 act2 () =
    act1 ();
    act2 ()
  ;;

  let rec s0 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun / s1)
          | Doko -> Some (doko / s0)
          | _ -> None)
    }

  and s1 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun / s2)
          | Doko -> Some (doko / s0)
          | _ -> None)
    }

  and s2 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun / s3)
          | Doko -> Some (doko / s0)
          | _ -> None)
    }

  and s3 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun / s4)
          | Doko -> Some (doko / s0)
          | _ -> None)
    }

  and s4 =
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (zun / s4)
          | Doko -> Some ((doko & kiyoshi) / s0)
          | _ -> None)
    }
  ;;

  let rec printer =
    let printf_continue str k = continue_with k (printf str) printer in
    { default_handler with
      effc =
        (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
          match eff with
          | Zun -> Some (printf_continue "\u{30BA}\u{30F3}\u{266A}\n")
          | Doko -> Some (printf_continue "\u{30C9}\u{30B3}\u{266A}\n")
          | Kiyoshi ->
            Some (printf_continue "\u{30AD}\u{00B7}\u{30E8}\u{00B7}\u{30B7}\u{FF01}\n")
          | _ -> None)
    }
  ;;

  let run f = continue_with (fiber @@ continue_with (fiber f) ()) s0 printer
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
