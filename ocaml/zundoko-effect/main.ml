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

  let with_kiyoshi =
    let rec state numZun =
      { default_handler with
        effc =
          (fun (type a) (eff : a t) : ((a, _) continuation -> _) option ->
            match eff, numZun with
            | Zun, 4 -> Some (zun / state 4)
            | Zun, _ -> Some (zun / state (numZun + 1))
            | Doko, 4 -> Some ((doko & kiyoshi) / state 0)
            | Doko, _ -> Some (doko / state 0)
            | _ -> None)
      }
    in
    fun f -> continue_with (fiber f) () (state 0)
  ;;

  let pretty =
    let rec handler =
      let printf_continue str k = continue_with k (printf str) handler in
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
    in
    fun f -> continue_with (fiber f) () handler
  ;;

  let run f = pretty @@ fun () -> with_kiyoshi f
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
