import RumocaFMI3.StaticStorage
import RumocaFMI3.TensorInstanceStorage
import RumocaFMI3.Runtime
import RumocaFMI3.PrinterTypes
import RumocaFMI3.AdapterPreprocessing
import RumocaCore.Tensor.Matrix
import Mathlib.Tactic.FinCases

/-! Permanent FMI adapter storage for a prepared tensor model instance.

The scalar adapter declares a scalar instance record (`StaticStorage`), whose
single `double x` model member matches the scalar Solve state. A prepared
`Solve.TensorFMI3Model shape` instead stores contiguous tensor regions: the
independent time base, the input tensor `u`, the state tensor `x`, the state
derivative `dx`, and, when the prepared problem exposes a dense observation, the
Jacobian matrix `J`. Each tensor region is a `double` array whose element count
is the symbolic shape volume (`N` for the state-sized tensors, `N*N` flattened
for the square matrix `J`), rendered through the shared decimal renderer. The
record is completed by the FMI lifecycle, host and slot bookkeeping fields the
tensor bodies read.

This is the record layout the tensor bodies address through `TensorInstance`:
the member names and array element counts agree with `TensorInstance.field` and
the tensor region counts (`layout_names`, `layout_state_extent`,
`layout_output_extent`). The permanent pool array, its always-lock-free flag
array and the capacity constant are shared verbatim with the scalar storage;
only the record body differs. There is no dynamic allocation and no tensor
coordinate is enumerated: the extents stay symbolic in the shape.

The production tensor renderer consumes these declarations. These layout and
tokenization facts alone do not certify actual artifact bytes or native layout,
and do not admit a new CLI or grammar case. -/
namespace Rumoca.FMI3.TensorStorage
open Rumoca.Tensor

/-! ### Record members -/

/-- A permanent instance-record member: either a scalar field or a contiguous
`double` region with a symbolic element count. -/
inductive Member where
  | scalar (type name : String)
  | region (name : String) (extent : Nat)
  deriving DecidableEq, Repr

/-- The declared member name, independent of whether it carries an array
extent. -/
def Member.baseName : Member → String
  | .scalar _ name => name
  | .region name _ => name

/-- The rendered C declarator text of one member, without indentation or line
terminator: `type name;` for a scalar and `double name[count];` for a region. -/
def Member.render : Member → String
  | .scalar type name => type ++ " " ++ name ++ ";"
  | .region name extent => "double " ++ name ++ "[" ++ toString extent ++ "];"

/-- The FMI-visible tensor regions of the instance record, in declaration order,
matching `TensorInstance.fieldNames`. The time base is the scalar (rank-0)
member; `x`, `u` and `dx` have the state element count; the Jacobian `J` is
present exactly when the prepared problem exposes a dense observation, flattened
to the `N*N` matrix element count. -/
def regionMembers (shape : Shape) (hasOutput : Bool) : List Member :=
  [.scalar "double" TensorInstance.timeName,
   .region TensorInstance.stateName shape.volume,
   .region TensorInstance.inputName shape.volume,
   .region TensorInstance.derivativeName shape.volume] ++
  (if hasOutput then
      [.region TensorInstance.outputName (matrixShape shape.volume shape.volume).volume]
    else [])

/-- The FMI lifecycle, host and slot bookkeeping fields the tensor bodies read:
the kind and mode, the stop-time interval, the event-time bookkeeping cells the
Model Exchange completed-step body maintains (`timeMin`, `eventTime`,
`lastCompleted`), the logging flag, the captured environment and logger, and the
reserved slot index. These mirror the scalar instance record's non-model fields. -/
def bookkeepingMembers : List Member :=
  [.scalar "double" "stop", .scalar "double" "timeMin", .scalar "double" "eventTime",
   .scalar "double" "lastCompleted", .scalar "int" "kind", .scalar "int" "mode",
   .scalar "fmi3Boolean" "stopDefined", .scalar "fmi3Boolean" "logging",
   .scalar "fmi3InstanceEnvironment" "environment",
   .scalar "fmi3LogMessageCallback" "logger", .scalar "size_t" "slot"]

/-- All members of the tensor instance record, tensor regions first. -/
def members (shape : Shape) (hasOutput : Bool) : List Member :=
  regionMembers shape hasOutput ++ bookkeepingMembers

/-- The record's declared name; the tensor bodies bind `Instance *m`, so the
tensor record keeps the shared `Instance` typedef name and the pool array reuses
it verbatim. -/
def recordName : String := "Instance"

/-- The rendered tensor instance record: a `typedef struct` in the same layout
as the shared record renderer, each member indented and line-terminated. -/
def recordRender (shape : Shape) (hasOutput : Bool) : String :=
  "typedef struct {\n" ++
    String.join ((members shape hasOutput).map fun m => "  " ++ m.render ++ "\n") ++
    "} " ++ recordName ++ ";\n"

/-- The complete tensor storage section: the tensor instance record, and the
shared permanent pool array, always-lock-free flag array and capacity constant.
The scalar numerical `Model` record is not declared here: the tensor bodies
address the tensor instance record and call the prepared tensor kernel entry
`rumoca_rhs` directly, so the scalar record and its scalar helpers carry no
meaning for the tensor adapter. -/
def storageRender (shape : Shape) (hasOutput : Bool) : String :=
  recordRender shape hasOutput ++
    (StaticStorage.instances StaticStorage.deploymentCapacity).render ++
    (StaticStorage.flags StaticStorage.deploymentCapacity).render ++
    (StaticStorage.count StaticStorage.deploymentCapacity).render

/-- The exported prototype of the prepared tensor derivative kernel entry
`rumoca_rhs`, in the shape the tensor plan gives it: three contiguous `double`
regions (the state `x`, input `u` and derivative `dx`) and the element count. The
member names agree with `TensorInstance` and the region roles with the plan's
`input`/`output` parameter kinds (`const double *` for the read regions,
`double *` for the written derivative). This is the signature the C IVP product
renders for the plan's derivative function. -/
def kernelSignature : CTree.Signature :=
  ⟨"void", "rumoca_rhs",
    [⟨"const double *", TensorInstance.stateName, false⟩,
     ⟨"const double *", TensorInstance.inputName, false⟩,
     ⟨"double *", TensorInstance.derivativeName, false⟩,
     ⟨"size_t", "count", false⟩]⟩

/-- The forward declaration of the prepared tensor kernel entry `rumoca_rhs`. The
tensor bodies call this entry directly with the instance's `x`, `u` and `dx`
region pointers and the element count; the preamble declaration makes those calls
match the definition in the included private kernel `model.c`. It replaces the
scalar `model_rhs`/`model_advance` wrapper helpers, which called the scalar
kernel over the scalar `Model` record and are dead for the tensor adapter. -/
def kernelPrototype : String := kernelSignature.render ++ ";\n"

/-- The exported prototype of the prepared scratch-free square-Jacobian diagonal
kernel entry `rumoca_square_jacobian_diag`, in the shape the certified tensor
kernel product gives it (`Rumoca.CTensor.SquareDiagonal.function`): the read
coefficient region (`const double *`), the written dense-matrix region
(`double *`), the state element count and the flattened matrix cell count. The
tensor derivative getter calls this entry with the instance's input region `u`,
output region `J`, the element count and the matrix cell count; the definition is
supplied by the same included private kernel `model.c` that defines `rumoca_rhs`. -/
def jacobianSignature : CTree.Signature :=
  ⟨"void", "rumoca_square_jacobian_diag",
    [⟨"const double *", "coeff", false⟩,
     ⟨"double *", "out", false⟩,
     ⟨"size_t", "count", false⟩,
     ⟨"size_t", "cells", false⟩]⟩

/-- The forward declaration of the prepared square-Jacobian diagonal kernel entry
`rumoca_square_jacobian_diag`. It is declared next to `rumoca_rhs` and always
emitted: the certified entry is defined once in the included private kernel
`model.c`, and the tensor derivative getter calls it only when the prepared
problem exposes a dense observation. -/
def jacobianPrototype : String := jacobianSignature.render ++ ";\n"

/-- The tensor adapter declaration preamble: the shared header inclusion block,
the tensor storage section and the forward declarations of the two prepared
tensor kernel entries (`rumoca_rhs` and `rumoca_square_jacobian_diag`). This
replaces `Runtime.declarations` (which declares the scalar instance record) in
the tensor renderer. Both entry prototypes are always declared; the certified
kernel product defines both in the included private `model.c`, and the getter
calls the second only when the record carries the dense output. -/
def declarations (shape : Shape) (hasOutput : Bool) : String :=
  Runtime.declarationPrefix ++ storageRender shape hasOutput ++ kernelPrototype ++
    jacobianPrototype ++ "\n"

/-! ### Record members generic in the input and output regions

The record member set is parameterized by the profile presence flags `hasInput`
and `hasOutput`: the tensor profile carries both regions, the constant-rate
profile (`G01`) carries neither. The current tensor definitions are the
`hasInput := true` instance of the generic renderers, recovered by `rfl`. -/

/-- The tensor region members, generic in the input and output regions. The time
base is always the scalar member; the state `x` and derivative `dx` are always
present; the input `u` is present when `hasInput`; the Jacobian `J` is present
when `hasOutput`. -/
def regionMembersG (shape : Shape) (hasInput hasOutput : Bool) : List Member :=
  [.scalar "double" TensorInstance.timeName,
   .region TensorInstance.stateName shape.volume] ++
  (if hasInput then [.region TensorInstance.inputName shape.volume] else []) ++
  [.region TensorInstance.derivativeName shape.volume] ++
  (if hasOutput then
      [.region TensorInstance.outputName (matrixShape shape.volume shape.volume).volume]
    else [])

/-- All members of the profile-generic instance record, tensor regions first. -/
def membersG (shape : Shape) (hasInput hasOutput : Bool) : List Member :=
  regionMembersG shape hasInput hasOutput ++ bookkeepingMembers

/-- The profile-generic instance record render. -/
def recordRenderG (shape : Shape) (hasInput hasOutput : Bool) : String :=
  "typedef struct {\n" ++
    String.join ((membersG shape hasInput hasOutput).map fun m => "  " ++ m.render ++ "\n") ++
    "} " ++ recordName ++ ";\n"

/-- The profile-generic storage section. -/
def storageRenderG (shape : Shape) (hasInput hasOutput : Bool) : String :=
  recordRenderG shape hasInput hasOutput ++
    (StaticStorage.instances StaticStorage.deploymentCapacity).render ++
    (StaticStorage.flags StaticStorage.deploymentCapacity).render ++
    (StaticStorage.count StaticStorage.deploymentCapacity).render

/-- The profile-generic declaration preamble. -/
def declarationsG (shape : Shape) (hasInput hasOutput : Bool) : String :=
  Runtime.declarationPrefix ++ storageRenderG shape hasInput hasOutput ++ kernelPrototype ++
    jacobianPrototype ++ "\n"

/-- The tensor profile is the input-present instance of the generic region members. -/
theorem regionMembers_eq (shape : Shape) (hasOutput : Bool) :
    regionMembers shape hasOutput = regionMembersG shape true hasOutput := rfl

/-- The tensor profile is the input-present instance of the generic members. -/
theorem members_eq (shape : Shape) (hasOutput : Bool) :
    members shape hasOutput = membersG shape true hasOutput := rfl

/-- The tensor profile is the input-present instance of the generic record render. -/
theorem recordRender_eq (shape : Shape) (hasOutput : Bool) :
    recordRender shape hasOutput = recordRenderG shape true hasOutput := rfl

/-- The tensor profile is the input-present instance of the generic storage render. -/
theorem storageRender_eq (shape : Shape) (hasOutput : Bool) :
    storageRender shape hasOutput = storageRenderG shape true hasOutput := rfl

/-- The tensor profile is the input-present instance of the generic declarations. -/
theorem declarations_eq (shape : Shape) (hasOutput : Bool) :
    declarations shape hasOutput = declarationsG shape true hasOutput := rfl

/-! ### Record layout agrees with the addressed tensor regions -/

/-- The tensor region members carry exactly the member names `TensorInstance`
addresses, in the same order: the time base, the state, input and derivative
tensors and, when present, the Jacobian output. -/
theorem layout_names (shape : Shape) :
    (regionMembers shape true).map Member.baseName = TensorInstance.fieldNames := by
  simp [regionMembers, Member.baseName, TensorInstance.fieldNames, TensorInstance.timeName,
    TensorInstance.stateName, TensorInstance.inputName, TensorInstance.derivativeName,
    TensorInstance.outputName]

/-- Without a dense observation the region members are the four state-sized
members, matching `TensorInstance.fieldNames` without the `J` output. -/
theorem layout_names_core (shape : Shape) :
    (regionMembers shape false).map Member.baseName =
      [TensorInstance.timeName, TensorInstance.stateName, TensorInstance.inputName,
       TensorInstance.derivativeName] := by
  simp [regionMembers, Member.baseName]

/-- The state, input and derivative regions declare the state element count, the
count `TensorInstance.core` uses to `place` each region. -/
theorem layout_state_extent (shape : Shape) (hasOutput : Bool) :
    Member.region TensorInstance.stateName shape.volume ∈ regionMembers shape hasOutput ∧
    Member.region TensorInstance.inputName shape.volume ∈ regionMembers shape hasOutput ∧
    Member.region TensorInstance.derivativeName shape.volume ∈ regionMembers shape hasOutput := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [regionMembers]

/-- The Jacobian region declares the flattened `N*N` matrix element count, the
count `TensorInstance.store` uses to `place` the dense output, and this equals
the volume of the square matrix shape over the state element count. -/
theorem layout_output_extent (shape : Shape) :
    Member.region TensorInstance.outputName ((matrixShape shape.volume shape.volume).volume)
        ∈ regionMembers shape true ∧
    (matrixShape shape.volume shape.volume).volume = shape.volume * shape.volume := by
  refine ⟨by simp [regionMembers], ?_⟩
  simp [matrixShape, Shape.volume]

/-! ### Constant-rate profile layout

The no-input, no-output profile declares the time base, the state vector and its
derivative, matching `TensorInstance.fieldNames` without the `u` input and the
`J` output. -/

/-- The constant-rate region members carry the time base, the state and the
derivative, in the field order `TensorInstance` addresses. -/
theorem layout_names_constant (shape : Shape) :
    (regionMembersG shape false false).map Member.baseName =
      [TensorInstance.timeName, TensorInstance.stateName, TensorInstance.derivativeName] := by
  simp [regionMembersG, Member.baseName]

/-- The constant-rate state and derivative regions declare the state element count,
the count `TensorInstance.coreNoInput` uses to `place` each region. -/
theorem layout_state_extent_constant (shape : Shape) :
    Member.region TensorInstance.stateName shape.volume ∈ regionMembersG shape false false ∧
    Member.region TensorInstance.derivativeName shape.volume ∈ regionMembersG shape false false := by
  refine ⟨?_, ?_⟩ <;> simp [regionMembersG]

/-! ### Tokenization under the shared C scanner

The tensor storage section scans, under the shared maximal-munch scanner
(`CTokens.Prefix`), into the same token vocabulary the scalar declarations use,
extended with the array-declarator tokens `[ number ]` for each contiguous
region. The shared model record, permanent pool array, always-lock-free flag
array and capacity constant reuse the shared record/array/constant renderers and
their proofs verbatim; only the tensor instance record body is tokenized here. -/
section Tokenization
open CObject CTree.Syntax CTokens

/-- One scalar member line `  type name;\n` scans into its three tokens. -/
private theorem scalar_line (type name : String)
    (typeParts : CIdentifierToken.WordParts type)
    (nameParts : CIdentifierToken.WordParts name) (rest : List Char) :
    CTokens.Prefix (("  " ++ (Member.scalar type name).render ++ "\n").toList ++ rest)
      [Token.word type, .word name, .punctuator ";"] rest := by
  have wType := CTokens.word_prefix typeParts (marker := ' ')
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (name.toList ++ ';' :: '\n' :: rest)
  have wName := CTokens.word_prefix nameParts (marker := ';')
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ('\n' :: rest)
  have semi := CTokens.separator_prefix (spelling := ";") (by simp) ('\n' :: rest)
  have tail := wName.append (semi.append (CTokens.Prefix.space (c := '\n') (by decide +kernel) .done))
  have body := wType.append (CTokens.Prefix.space (c := ' ') (by decide +kernel) tail)
  simpa only [Member.render, String.toList_append, List.append_assoc, List.cons_append,
    List.nil_append] using
    CTokens.Prefix.space (c := ' ') (by decide +kernel)
      (CTokens.Prefix.space (c := ' ') (by decide +kernel) body)

/-- One region member line `  double name[extent];\n` scans into the
array-declarator tokens, with the symbolic extent as one decimal number token. -/
private theorem region_line (name : String) (extent : Nat)
    (nameParts : CIdentifierToken.WordParts name) (rest : List Char) :
    CTokens.Prefix (("  " ++ (Member.region name extent).render ++ "\n").toList ++ rest)
      [Token.word "double", .word name, .punctuator "[", .number (toString extent),
       .punctuator "]", .punctuator ";"] rest := by
  have wDouble := CTokens.word_prefix
    (show CIdentifierToken.WordParts "double" from ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩)
    (marker := ' ') (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (name.toList ++ '[' :: ((toString extent).toList ++ ']' :: ';' :: '\n' :: rest))
  have wName := CTokens.word_prefix nameParts (marker := '[')
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ((toString extent).toList ++ ']' :: ';' :: '\n' :: rest)
  have openB := CTokens.separator_prefix (spelling := "[") (by simp)
    ((toString extent).toList ++ ']' :: ';' :: '\n' :: rest)
  have num := CTokens.natural_prefix extent (marker := ']') (by decide +kernel) (';' :: '\n' :: rest)
  have closeB := CTokens.separator_prefix (spelling := "]") (by simp) (';' :: '\n' :: rest)
  have semi := CTokens.separator_prefix (spelling := ";") (by simp) ('\n' :: rest)
  have tail := wName.append (openB.append (num.append (closeB.append
    (semi.append (CTokens.Prefix.space (c := '\n') (by decide +kernel) .done)))))
  have body := wDouble.append (CTokens.Prefix.space (c := ' ') (by decide +kernel) tail)
  simpa only [Member.render, String.toList_append, List.append_assoc, List.cons_append,
    List.nil_append] using
    CTokens.Prefix.space (c := ' ') (by decide +kernel)
      (CTokens.Prefix.space (c := ' ') (by decide +kernel) body)

/-- Word-parts for the concrete member type and name tokens used below. -/
private theorem parts_double : CIdentifierToken.WordParts "double" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_int : CIdentifierToken.WordParts "int" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_time : CIdentifierToken.WordParts "time" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_x : CIdentifierToken.WordParts TensorInstance.stateName := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_u : CIdentifierToken.WordParts TensorInstance.inputName := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_dx : CIdentifierToken.WordParts TensorInstance.derivativeName := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_J : CIdentifierToken.WordParts TensorInstance.outputName := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_stop : CIdentifierToken.WordParts "stop" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_timeMin : CIdentifierToken.WordParts "timeMin" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_eventTime : CIdentifierToken.WordParts "eventTime" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_lastCompleted : CIdentifierToken.WordParts "lastCompleted" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_kind : CIdentifierToken.WordParts "kind" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_mode : CIdentifierToken.WordParts "mode" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_stopDefined : CIdentifierToken.WordParts "stopDefined" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_logging : CIdentifierToken.WordParts "logging" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_environment : CIdentifierToken.WordParts "environment" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_logger : CIdentifierToken.WordParts "logger" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_slot : CIdentifierToken.WordParts "slot" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_boolean : CIdentifierToken.WordParts "fmi3Boolean" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_env : CIdentifierToken.WordParts "fmi3InstanceEnvironment" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_cb : CIdentifierToken.WordParts "fmi3LogMessageCallback" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_size : CIdentifierToken.WordParts "size_t" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_typedef : CIdentifierToken.WordParts "typedef" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_struct : CIdentifierToken.WordParts "struct" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
private theorem parts_Instance : CIdentifierToken.WordParts "Instance" := ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩

/-- The word-parts obligation for one member: its type and name (scalar) or its
name (region). -/
def MemberWF : Member → Prop
  | .scalar type name => CIdentifierToken.WordParts type ∧ CIdentifierToken.WordParts name
  | .region name _ => CIdentifierToken.WordParts name

/-- The token vocabulary one member scans into. -/
def memberTokens : Member → List Token
  | .scalar type name => [.word type, .word name, .punctuator ";"]
  | .region name extent =>
      [.word "double", .word name, .punctuator "[", .number (toString extent),
       .punctuator "]", .punctuator ";"]

/-- One member line scans into its member tokens, of either kind. -/
private theorem member_line (m : Member) (wf : MemberWF m) (rest : List Char) :
    CTokens.Prefix (("  " ++ m.render ++ "\n").toList ++ rest) (memberTokens m) rest := by
  cases m with
  | scalar type name => exact scalar_line type name wf.1 wf.2 rest
  | region name extent => exact region_line name extent wf rest

/-- A block of member lines scans into the concatenated member tokens. -/
private theorem block_prefix (ms : List Member) (wf : ∀ m ∈ ms, MemberWF m) :
    ∃ tokens, ∀ rest, CTokens.Prefix
      ((String.join (ms.map fun m => "  " ++ m.render ++ "\n")).toList ++ rest) tokens rest := by
  induction ms with
  | nil => exact ⟨[], fun _ => by simpa using CTokens.Prefix.done⟩
  | cons m ms ih =>
    obtain ⟨tailTokens, tailPrefix⟩ := ih (fun m mem => wf m (by simp [mem]))
    refine ⟨memberTokens m ++ tailTokens, fun rest => ?_⟩
    have head := member_line m (wf m (by simp))
      ((String.join (ms.map fun m => "  " ++ m.render ++ "\n")).toList ++ rest)
    have composed := head.append (tailPrefix rest)
    simpa only [List.map_cons, CString.join_toList, List.flatMap_cons, List.flatMap_nil,
      String.toList_append, List.append_assoc] using composed

/-- The fixed bookkeeping members have valid word-parts. These fields are the
same for every profile, so the obligation is discharged once, and the membership
quantifier is reduced to a fixed conjunction of member obligations rather than
enumerated by case analysis inside each profile's member proof. -/
private theorem bookkeeping_wf : ∀ m ∈ bookkeepingMembers, MemberWF m := by
  simp only [bookkeepingMembers, MemberWF, List.forall_mem_cons]
  exact ⟨⟨parts_double, parts_stop⟩, ⟨parts_double, parts_timeMin⟩,
    ⟨parts_double, parts_eventTime⟩, ⟨parts_double, parts_lastCompleted⟩,
    ⟨parts_int, parts_kind⟩, ⟨parts_int, parts_mode⟩,
    ⟨parts_boolean, parts_stopDefined⟩, ⟨parts_boolean, parts_logging⟩,
    ⟨parts_env, parts_environment⟩, ⟨parts_cb, parts_logger⟩,
    ⟨parts_size, parts_slot⟩, by simp⟩

set_option maxHeartbeats 1000000 in
/-- The profile-generic tensor region members have valid word-parts. The region
list is at most five short members, so the case analysis stays over the small
region list and is independent of the fixed bookkeeping fields. -/
private theorem regionMembersG_wf (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    ∀ m ∈ regionMembersG shape hasInput hasOutput, MemberWF m := by
  intro m mem
  cases hasInput <;> cases hasOutput <;>
    (simp only [regionMembersG, reduceIte, List.append_assoc, List.cons_append,
      List.nil_append] at mem
     fin_cases mem <;>
       first
         | exact ⟨parts_double, parts_time⟩ | exact parts_x | exact parts_u
         | exact parts_dx | exact parts_J)

/-- Every member of the profile-generic instance record has valid word-parts,
composed from the small region obligation and the fixed bookkeeping obligation. -/
private theorem membersG_wf (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    ∀ m ∈ membersG shape hasInput hasOutput, MemberWF m := by
  intro m mem
  rw [membersG, List.mem_append] at mem
  rcases mem with hreg | hbook
  · exact regionMembersG_wf shape hasInput hasOutput m hreg
  · exact bookkeeping_wf m hbook

/-- Every member of the tensor instance record has valid word-parts. The tensor
profile is the input-present instance of the profile-generic record, so the
obligation is exactly the profile-generic one. -/
private theorem members_wf (shape : Tensor.Shape) (hasOutput : Bool) :
    ∀ m ∈ members shape hasOutput, MemberWF m :=
  membersG_wf shape true hasOutput

/-- A leading keyword word token followed by one separating space. -/
private theorem kw (name : String) (parts : CIdentifierToken.WordParts name) (rest : List Char) :
    CTokens.Prefix ((name ++ " ").toList ++ rest) [Token.word name] rest := by
  have word := CTokens.word_prefix parts (marker := ' ')
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rest
  simpa only [String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    word.append (CTokens.Prefix.space (c := ' ') (by decide +kernel) .done)

/-- The rendered tensor instance record scans into a concrete token sequence
under the shared scanner: the `typedef struct` header, the member tokens
(including the array-declarator tokens for each region), and the closing
`} Instance;`. -/
theorem record_printed (shape : Tensor.Shape) (hasOutput : Bool) :
    ∃ tokens, ∀ rest, CTokens.Prefix ((recordRender shape hasOutput).toList ++ rest) tokens rest := by
  obtain ⟨bodyTokens, bodyPrefix⟩ := block_prefix (members shape hasOutput) (members_wf shape hasOutput)
  refine ⟨[Token.word "typedef", .word "struct", .punctuator "{"] ++ bodyTokens ++
    [.punctuator "}", .word "Instance", .punctuator ";"], fun rest => ?_⟩
  have semicolon := (CTokens.separator_prefix (spelling := ";") (by simp) ('\n' :: rest)).append
    (CTokens.Prefix.space (c := '\n') (by decide +kernel) .done)
  have word := CTokens.word_prefix parts_Instance (marker := ';')
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ('\n' :: rest)
  have close := CTokens.separator_prefix (spelling := "}") (by simp)
    (' ' :: ("Instance".toList ++ ';' :: '\n' :: rest))
  have tail := close.append (CTokens.Prefix.space (c := ' ') (by decide +kernel) (word.append semicolon))
  have body := CTokens.Prefix.space (c := '\n') (by decide +kernel)
    ((bodyPrefix _).append tail)
  have opening := CTokens.separator_prefix (spelling := "{") (by simp)
    ('\n' :: ((String.join ((members shape hasOutput).map fun m => "  " ++ m.render ++ "\n")).toList ++
      '}' :: ' ' :: ("Instance".toList ++ ';' :: '\n' :: rest)))
  simpa only [recordRender, recordName, String.toList_append, List.append_assoc, List.cons_append,
    List.nil_append] using
    (kw "typedef" parts_typedef _).append ((kw "struct" parts_struct _).append (opening.append body))

/-- The complete tensor storage section scans into a concrete token sequence:
the tensor instance record and the shared permanent pool array, flag array and
capacity constant. The shared declarations reuse their existing
render/tokenization proofs; the tensor instance record uses `record_printed`. -/
theorem storage_printed (shape : Tensor.Shape) (hasOutput : Bool) :
    ∃ tokens, ∀ rest, CTokens.Prefix ((storageRender shape hasOutput).toList ++ rest) tokens rest := by
  obtain ⟨recordTokens, recordLex⟩ := record_printed shape hasOutput
  obtain ⟨arrayTokens, arrayPhrase, arrayLex⟩ :=
    CObject.array_renders (StaticStorage.instances_printable (capacity := StaticStorage.deploymentCapacity) (by decide +kernel))
  obtain ⟨flagTokens, flagPhrase, flagLex⟩ :=
    CObject.array_renders (StaticStorage.flags_printable (capacity := StaticStorage.deploymentCapacity) (by decide +kernel))
  obtain ⟨countTokens, countPhrase, countLex⟩ :=
    CObject.constant_renders (StaticStorage.count_printable StaticStorage.deploymentCapacity)
  refine ⟨recordTokens ++ arrayTokens ++ flagTokens ++ countTokens, fun rest => ?_⟩
  have composed := (recordLex _).append ((arrayLex _).append ((flagLex _).append (countLex rest)))
  simpa only [storageRender, String.toList_append, List.append_assoc] using composed

/-- The tensor declaration preamble is the shared header inclusion block
(reused verbatim from the scalar preamble) followed by the tensor storage
section. This exposes the header-inclusion prefix as model-independent and
identical to the scalar declarations' header block. -/
theorem declarations_header (shape : Tensor.Shape) (hasOutput : Bool) :
    (declarations shape hasOutput).toList =
      Runtime.declarationPrefix.toList ++
        (storageRender shape hasOutput ++ kernelPrototype ++ jacobianPrototype ++ "\n").toList := by
  simp [declarations, String.toList_append]

/-! ### Profile-generic tokenization

The same maximal-munch tokenization holds for the record generic in the input
and output regions, so the constant-rate profile (`false false`) tokenizes into
its member vocabulary as well. The word-parts obligation `membersG_wf` is shared
with the tensor profile above. -/

/-- The profile-generic record scans into a concrete token sequence under the
shared scanner. -/
theorem recordG_printed (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    ∃ tokens, ∀ rest, CTokens.Prefix ((recordRenderG shape hasInput hasOutput).toList ++ rest) tokens rest := by
  obtain ⟨bodyTokens, bodyPrefix⟩ :=
    block_prefix (membersG shape hasInput hasOutput) (membersG_wf shape hasInput hasOutput)
  refine ⟨[Token.word "typedef", .word "struct", .punctuator "{"] ++ bodyTokens ++
    [.punctuator "}", .word "Instance", .punctuator ";"], fun rest => ?_⟩
  have semicolon := (CTokens.separator_prefix (spelling := ";") (by simp) ('\n' :: rest)).append
    (CTokens.Prefix.space (c := '\n') (by decide +kernel) .done)
  have word := CTokens.word_prefix parts_Instance (marker := ';')
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ('\n' :: rest)
  have close := CTokens.separator_prefix (spelling := "}") (by simp)
    (' ' :: ("Instance".toList ++ ';' :: '\n' :: rest))
  have tail := close.append (CTokens.Prefix.space (c := ' ') (by decide +kernel) (word.append semicolon))
  have body := CTokens.Prefix.space (c := '\n') (by decide +kernel)
    ((bodyPrefix _).append tail)
  have opening := CTokens.separator_prefix (spelling := "{") (by simp)
    ('\n' :: ((String.join ((membersG shape hasInput hasOutput).map fun m => "  " ++ m.render ++ "\n")).toList ++
      '}' :: ' ' :: ("Instance".toList ++ ';' :: '\n' :: rest)))
  simpa only [recordRenderG, recordName, String.toList_append, List.append_assoc, List.cons_append,
    List.nil_append] using
    (kw "typedef" parts_typedef _).append ((kw "struct" parts_struct _).append (opening.append body))

/-- The profile-generic storage section scans into a concrete token sequence. -/
theorem storageG_printed (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    ∃ tokens, ∀ rest, CTokens.Prefix ((storageRenderG shape hasInput hasOutput).toList ++ rest) tokens rest := by
  obtain ⟨recordTokens, recordLex⟩ := recordG_printed shape hasInput hasOutput
  obtain ⟨arrayTokens, arrayPhrase, arrayLex⟩ :=
    CObject.array_renders (StaticStorage.instances_printable (capacity := StaticStorage.deploymentCapacity) (by decide +kernel))
  obtain ⟨flagTokens, flagPhrase, flagLex⟩ :=
    CObject.array_renders (StaticStorage.flags_printable (capacity := StaticStorage.deploymentCapacity) (by decide +kernel))
  obtain ⟨countTokens, countPhrase, countLex⟩ :=
    CObject.constant_renders (StaticStorage.count_printable StaticStorage.deploymentCapacity)
  refine ⟨recordTokens ++ arrayTokens ++ flagTokens ++ countTokens, fun rest => ?_⟩
  have composed := (recordLex _).append ((arrayLex _).append ((flagLex _).append (countLex rest)))
  simpa only [storageRenderG, String.toList_append, List.append_assoc] using composed

/-- The profile-generic declaration preamble exposes the shared header-inclusion
prefix, identical to the scalar declarations' header block. -/
theorem declarationsG_header (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    (declarationsG shape hasInput hasOutput).toList =
      Runtime.declarationPrefix.toList ++
        (storageRenderG shape hasInput hasOutput ++ kernelPrototype ++ jacobianPrototype ++ "\n").toList := by
  simp [declarationsG, String.toList_append]

end Tokenization

end Rumoca.FMI3.TensorStorage
