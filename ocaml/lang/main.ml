module Lang = struct
  type 'a t =
    { accept : bool
    ; deriv : 'a -> 'a t
    }

  let member w l = (List.fold_left (fun l c -> l.deriv c) l w).accept
  let rec empty = { accept = false; deriv = (fun _ -> empty) }
  let epsilon = { accept = true; deriv = (fun _ -> empty) }
  let single x = { accept = false; deriv = (fun y -> if x = y then epsilon else empty) }

  let rec ( + ) l1 l2 =
    { accept = l1.accept || l2.accept; deriv = (fun x -> l1.deriv x + l2.deriv x) }
  ;;

  let rec ( * ) l1 l2 =
    { accept = l1.accept && l2.accept
    ; deriv =
        (fun x -> if l1.accept then (l1.deriv x * l2) + l2.deriv x else l1.deriv x * l2)
    }
  ;;

  let ( ~* ) l =
    let rec kl = { accept = true; deriv = (fun x -> l.deriv x * kl) } in
    kl
  ;;
end

module Number = struct
  open Lang

  let zero = single '0'

  let nonzero =
    single '1'
    + single '2'
    + single '3'
    + single '4'
    + single '5'
    + single '6'
    + single '7'
    + single '8'
    + single '9'
  ;;

  let digit = zero + nonzero
  let number = zero + (nonzero * ~*digit)
  let signed_number = (epsilon + single '+' + single '-') * number
  let member s = member (List.init (String.length s) (String.get s))
  let is_number s = member s number
  let is_signed_number s = member s signed_number
end

open Printf

let () =
  let open Number in
  printf "is_number \"\" = %b\n" (is_number "");
  printf "is_number \"0\" = %b\n" (is_number "0");
  printf "is_number \"1\" = %b\n" (is_number "1");
  printf "is_number \"01\" = %b\n" (is_number "01");
  printf "is_number \"10\" = %b\n" (is_number "10");
  printf "is_number \"100\" = %b\n" (is_number "100");
  printf "is_signed_number \"100\" = %b\n" (is_signed_number "100");
  printf "is_signed_number \"-100\" = %b\n" (is_signed_number "-100");
  printf "is_signed_number \"+100\" = %b\n" (is_signed_number "+100");
  printf "is_signed_number \"+-100\" = %b\n" (is_signed_number "+-100")
;;
