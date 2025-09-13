import Free.Basic

-- example

inductive Teletype : Type where
  | putString : String → Teletype
  | getString : Teletype

def Teletype.ReturnType (t : Teletype) : Type :=
  match t with
  | .putString _ => Unit
  | .getString => String

def Teletype.Container : Container where
  Shape := Teletype
  Position := Teletype.ReturnType

def Teletype.runIO : Free Teletype.Container α → IO α :=
  Free.foldr pure (fun s => match s with
    | ⟨ .putString s, k ⟩ => IO.print s >>= k
    | ⟨ .getString, k ⟩ => IO.getStdin >>= fun stdin => stdin.getLine >>= k)

def Teletype.put (s : String) : Free Teletype.Container Unit :=
  Free.send Teletype.Container (Teletype.putString s)

def Teletype.get : Free Teletype.Container String :=
  Free.send Teletype.Container Teletype.getString

def exampleTeletypeProgram : Free Teletype.Container Unit := do
  let s ← Teletype.get
  Teletype.put s

def main : IO Unit := Teletype.runIO exampleTeletypeProgram
