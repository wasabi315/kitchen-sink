open! Core

module Message = struct
  type t =
    | Parse_err
    | Unbound_var
    | Type_err
    | Impossible

  let default_severity = function
    | Parse_err -> Asai.Diagnostic.Error
    | Unbound_var -> Error
    | Type_err -> Error
    | Impossible -> Bug
  ;;

  let short_code = function
    | Parse_err -> "E0001"
    | Unbound_var -> "E0002"
    | Type_err -> "E0003"
    | Impossible -> "E9999"
  ;;
end

include Asai.Reporter.Make (Message)
module Term = Asai.Tty.Make (Message)

let run ~f =
  run
    ~emit:Term.display
    ~fatal:(fun d ->
      Term.display d;
      exit 1)
    f
;;
