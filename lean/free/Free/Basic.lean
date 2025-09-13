-- A port of Agda's Data.Container modules

-- Definition of a container

structure Container : Type (max s p + 1) where
  mk ::
  Shape    : Type s
  Position : Shape → Type p

def Container.extension (C : Container) (α : Type u) : Type _ :=
  Σ s : C.Shape, (C.Position s → α)

notation "⟦ " term " ⟧" => Container.extension term

instance : Functor ⟦ C ⟧ where
  map f C := ⟨ C.1, fun x => f (C.2 x) ⟩

-- Container combinators

namespace Container

  def id : Container where
    Shape := Unit
    Position := fun _ => Unit

  def const (A : Type u) : Container where
    Shape := A
    Position := fun _ => Empty

  def sum (C₁ C₂ : Container) : Container where
    Shape := C₁.Shape ⊕ C₂.Shape
    Position s := match s with
      | .inl s => C₁.Position s
      | .inr s => C₂.Position s

  def product (C₁ C₂ : Container) : Container where
    Shape := C₁.Shape × C₂.Shape
    Position s := C₁.Position s.1 ⊕ C₂.Position s.2

  def compose (C₁ C₂ : Container) : Container where
    Shape := ⟦ C₁ ⟧ C₂.Shape
    Position s := Σ p, C₂.Position (s.2 p)

end Container

-- Free monad

inductive Free (C : Container) (α : Type u) : Type _ where
  | pure : α → Free C α
  -- inline Container.extension so Lean can see that positivity is maintained
  | impure : (s : C.Shape) → (k : C.Position s → Free C α) → Free C α

namespace Free

  def send (C : Container) (s : C.Shape) : Free C (C.Position s) := .impure s .pure

  def foldr (algP : α → β) (algI : ⟦ C ⟧ β → β) (m : Free C α) : β :=
    match m with
    | .pure a => algP a
    | .impure s k => algI ⟨ s, fun x => foldr algP algI (k x) ⟩

  def map (f : α → β) (m : Free C α) : Free C β :=
    match m with
    | .pure a => .pure (f a)
    | .impure s k => .impure s (fun x => map f (k x))

  def seq (mf : Free C (α → β)) (m : Unit → Free C α) : Free C β :=
    match mf with
    | .pure f => map f (m ())
    | .impure s k => .impure s (fun x => seq (k x) m)

  def bind (m : Free C α) (f : α → Free C β) : Free C β :=
    match m with
    | .pure a => f a
    | .impure s k => .impure s (fun x => bind (k x) f)

end Free

instance : Functor (Free C) where
  map := Free.map

instance : Applicative (Free C) where
  pure := Free.pure
  seq := Free.seq

instance : Monad (Free C) where
  bind := Free.bind
