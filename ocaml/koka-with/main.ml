open Printf

let ( let@@ ) = ( @@ )

let twice f =
  f ();
  f ()
;;

let iter l = Fun.flip List.iter l

let () =
  (* equivalent to:
      Fun.protect ~finally:(fun () -> printf "Bye!") @@ fun () ->
        twice @@ fun () ->
          iter [ false; true ] @@ fun n ->
            iter [ false; true ] @@ fun m ->
              printf "(%b, %b)\n" n m
  *)
  let@@ () = Fun.protect ~finally:(fun () -> printf "Bye!") in
  let@@ () = twice in
  let@@ n = iter [ false; true ] in
  let@@ m = iter [ false; true ] in
  printf "(%b, %b)\n" n m
;;
