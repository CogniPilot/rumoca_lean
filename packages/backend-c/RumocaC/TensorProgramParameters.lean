import RumocaC.TensorProgramSyntax
import RumocaC.TensorCalls

/-! Typed parameter values and scope binding for prepared tensor functions.
The proofs quantify over arbitrary valid signatures and header dictionaries. -/

namespace Rumoca.CTensor.Lowering.Arguments
open CTree CMemory
open Syntax

def type : ParamKind → CType
  | .input | .output => .pointer
  | .count => .size

/-- The admitted C parameter values, independently of the conversion function. -/
inductive Admissible : ParamKind → Value → Prop where
  | input (address : Option Address) : Admissible .input (.pointer address)
  | output (address : Option Address) : Admissible .output (.pointer address)
  | count (value : Nat) (bounded : value < 2 ^ 64) : Admissible .count (.integer value)

abbrev Values := String → Value

def Valid (params : List Syntax.Parameter) (args : Values) : Prop :=
  ∀ p ∈ params, Admissible p.kind (args p.name)

def locals : List Syntax.Parameter → Values → CBody.Locals
  | [] => fun _ _ => none
  | p :: ps => fun args => CBody.bind (locals ps args) p.name (args p.name)

def types : List Syntax.Parameter → CLoops.Types
  | [] => fun _ => none
  | p :: ps => CLoops.bindType (types ps) p.name (type p.kind)

def values (params : List Syntax.Parameter) (args : Values) : List Value :=
  params.map fun p => args p.name

theorem locals_absent (params : List Syntax.Parameter) (args : Values) (name : String)
    (absent : name ∉ params.map Syntax.Parameter.name) : locals params args name = none := by
  induction params with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    simp only [locals, CBody.bind, if_neg absent.1, ih absent.2]

theorem locals_present (params : List Syntax.Parameter) (args : Values) (name : String)
    (present : name ∈ params.map Syntax.Parameter.name) : locals params args name = some (args name) := by
  induction params with
  | nil => simp at present
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons] at present
    by_cases eq : name = p.name
    · simp [locals, CBody.bind, eq]
    · simp only [locals, CBody.bind, if_neg eq, ih (present.resolve_left eq)]

theorem types_absent (params : List Syntax.Parameter) (name : String)
    (absent : name ∉ params.map Syntax.Parameter.name) : types params name = none := by
  induction params with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    simp only [types, CLoops.bindType, if_neg absent.1, ih absent.2]

variable [interface : CInterface]

theorem header_type (kind : ParamKind) (header : CTensor.HeaderTypes interface) :
    interface.types kind.type = some (type kind) := by
  cases kind with
  | input => exact header.input
  | output => exact header.output
  | count => exact header.size

theorem cast_admissible (kind : ParamKind) (value : Value) (header : CTensor.HeaderTypes interface)
    (valid : Admissible kind value) : CBody.cast kind.type value = some value := by
  apply CLoops.Calls.cast_of_type _ (type kind) _ _ (header_type kind header)
  cases valid with
  | input | output => rfl
  | count count bounded => exact CLoops.convert_size_nat count bounded

theorem bind_parameters (params : List Syntax.Parameter) (args : Values)
    (header : CTensor.HeaderTypes interface) (distinct : (params.map Syntax.Parameter.name).Nodup)
    (valid : Valid params args) :
    CCalls.parameters (params.map Syntax.Parameter.tree) (values params args) = some (locals params args) := by
  induction params with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    exact CLoops.Calls.bind_parameter p.tree (ps.map Syntax.Parameter.tree) (args p.name) (args p.name)
      (values ps args) (locals ps args) rfl
      (ih distinct.2 (fun q hq => valid q (List.mem_cons_of_mem p hq)))
      (locals_absent ps args p.name distinct.1)
      (cast_admissible p.kind (args p.name) header (valid p (List.mem_cons_self)))

theorem bind_types (params : List Syntax.Parameter) (header : CTensor.HeaderTypes interface)
    (distinct : (params.map Syntax.Parameter.name).Nodup) :
    CLoops.Calls.parameterTypes (params.map Syntax.Parameter.tree) = some (types params) := by
  induction params with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    simp only [List.map_cons, CLoops.Calls.parameterTypes, Syntax.Parameter.tree,
      Bool.false_eq_true, ↓reduceIte, ih distinct.2, types_absent ps p.name distinct.1,
      Option.isSome_none, header_type p.kind header, bind, Option.bind_some, pure, types]

end Rumoca.CTensor.Lowering.Arguments
