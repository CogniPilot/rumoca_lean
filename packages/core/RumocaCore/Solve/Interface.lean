import Parser.Token
import RumocaCore.Tensor

/-! The declared interface of a prepared model: one resolved declaration per
source component, in source order. Each declaration keeps its name, its
causality from the `input`/`output` prefix (none is `local`), its role in the
prepared problem, its declared extents as a tensor shape, its start value and
the names its value (for a state, its derivative) structurally reads. Rank and
extents stay native: an array declaration is one declaration with its declared
dimensions, never one declaration per element, and scalars are rank 0.

Each admitted profile produces this list from its resolved AST. Backends read
it to export variables and never resolve source names themselves. `declaredIn`
reads the same information back from a token stream, so each profile's
soundness theorem ties the list to the parsed source text. -/
namespace Rumoca.Solve
open _root_.Parser

/-- The causality prefix of a source declaration. -/
inductive Causality where
  | input
  | output
  | «local»
  deriving Repr, DecidableEq

/-- The role a declared component plays in the prepared problem: an input, a
continuous state (whose derivative the problem computes) or a computed
algebraic value. -/
inductive Role where
  | input
  | state
  | algebraic
  deriving Repr, DecidableEq

/-- How the initial value of a declared component is determined: fixed by its
start value, or computed by the prepared problem. -/
inductive Initial where
  | exact
  | calculated
  deriving Repr, DecidableEq

/-- One resolved source declaration. `start` is the uniform per-element start
value of the declaration, when it has one. -/
structure Declaration where
  name : String
  causality : Causality
  role : Role
  shape : Tensor.Shape
  start : Option Nat
  dependencies : List String
  deriving Repr, DecidableEq

/-- An input has no initial attribute; a state starts from its start value; a
computed algebraic value is calculated. -/
def Declaration.initial (d : Declaration) : Option Initial :=
  match d.role with
  | .input => none
  | .state => some .exact
  | .algebraic => some .calculated

/-- The resolved declarations of one parsed source, in source order. -/
structure Interface where
  declarations : List Declaration
  deriving Repr, DecidableEq

/-- The name of the independent time variable. `time` is a reserved Modelica
word, so no source declaration carries it. -/
def timeName : String := "time"

/-- Every name a declaration's value (for a state, its derivative) reads is a
declared name of the same interface. -/
def Interface.Closed (i : Interface) : Prop :=
  ∀ d ∈ i.declarations, ∀ name ∈ d.dependencies, name ∈ i.declarations.map Declaration.name

/-! ### Declarations read back from source tokens -/

/-- The source subscript of declared extents: none for a scalar, otherwise
`[d₁, …, dₖ]`. -/
def subscriptTokens : List Nat → List Token
  | [] => []
  | d :: ds => .literal "[" :: .literal (toString d) ::
      (ds.flatMap fun n => [.literal ",", .literal (toString n)]) ++ [.literal "]"]

/-- The tokens up to and including the closing bracket of a subscript. -/
def closeSubscript : List Token → List Token
  | [] => []
  | .literal "]" :: _ => [.literal "]"]
  | t :: rest => t :: closeSubscript rest

/-- The subscript at the head of a token stream, or none. -/
def subscriptAt : List Token → List Token
  | .literal "[" :: rest => .literal "[" :: closeSubscript rest
  | _ => []

/-- The causality stated by the token preceding a `Real` type specifier. -/
def causalityBefore : Option Token → Causality
  | some (.literal "input") => .input
  | some (.literal "output") => .output
  | _ => .local

/-- Every `Real` component declaration of a token stream, in source order: its
name, the causality of its prefix and its subscript tokens. -/
def declaredAfter (previous : Option Token) : List Token → List (String × Causality × List Token)
  | [] => []
  | .literal "Real" :: .ident name :: rest =>
      (name, causalityBefore previous, subscriptAt rest) :: declaredAfter (some (.ident name)) rest
  | t :: rest => declaredAfter (some t) rest

def declaredIn (tokens : List Token) : List (String × Causality × List Token) :=
  declaredAfter none tokens

/-- How a declaration is written in source: name, causality and subscript. -/
def Declaration.signature (d : Declaration) : String × Causality × List Token :=
  (d.name, d.causality, subscriptTokens d.shape.dimensions)

/-- Every declaration read back from a token stream names an identifier token of
that stream. -/
theorem declaredAfter_ident (previous : Option Token) (tokens : List Token) :
    ∀ entry ∈ declaredAfter previous tokens, .ident entry.1 ∈ tokens := by
  fun_induction declaredAfter previous tokens with
  | case1 => intro entry member; cases member
  | case2 previous name rest ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih entry member))
  | case3 previous t rest _ ih =>
    intro entry member
    exact List.mem_cons_of_mem _ (ih entry member)

theorem declaredIn_ident (tokens : List Token) (i : Interface)
    (sound : declaredIn tokens = i.declarations.map Declaration.signature) :
    ∀ d ∈ i.declarations, .ident d.name ∈ tokens := by
  intro d member
  have entry : Declaration.signature d ∈ declaredIn tokens := by
    rw [sound]; exact List.mem_map_of_mem member
  exact declaredAfter_ident none tokens _ entry

end Rumoca.Solve
