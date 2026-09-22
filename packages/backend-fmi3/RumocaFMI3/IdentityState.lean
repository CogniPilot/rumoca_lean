import RumocaFMI3.IdentityCode
import RumocaC.CallSignature
import RumocaC.CallCasts
import RumocaC.NullComparison

/-! Fresh scope and statement execution of the private identity validator.
Parameters are ordinary opaque pointers; all string access is through the
explicit library calls proved separately. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory

structure Arguments where
  name : Option Address
  token : Option Address
  expected : Option Address
  whitespace : Option Address

def Arguments.values (args : Arguments) : List Value :=
  [.pointer args.name, .pointer args.token, .pointer args.expected, .pointer args.whitespace]

def parameterLocals (args : Arguments) : CBody.Locals :=
  CBody.bind (CBody.bind (CBody.bind (CBody.bind (fun _ => none)
    "whitespace" (.pointer args.whitespace)) "expected" (.pointer args.expected))
      "token" (.pointer args.token)) "name" (.pointer args.name)

def parameterTypes : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (CLoops.bindType (CLoops.bindType (fun _ => none)
    "whitespace" .pointer) "expected" .pointer) "token" .pointer) "name" .pointer

def locals (args : Arguments) (length prefixLength : Nat) (difference : Int) : CBody.Locals :=
  CBody.bind (CBody.bind (CBody.bind (parameterLocals args)
    "length" (.integer length)) "prefix" (.integer prefixLength)) "difference" (.integer difference)

def types : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (CLoops.bindType parameterTypes "length" .size) "prefix" .size) "difference" .int32

def checks : List Stmt := [nullCheck "name", nullCheck "token", nullCheck "expected", nullCheck "whitespace"]
def body : List Stmt := [measure, measurePrefix, blank, compareToken, comparisonReturn]

variable [interface : CInterface]

theorem parameters_bound (args : Arguments) (pointer : interface.types "const char *" = some .pointer) :
    CCalls.parameters function.signature.parameters args.values = some (parameterLocals args) := by
  have converted : CCalls.Signature.Arguments function.signature.parameters args.values args.values :=
    .cons pointer rfl (.cons pointer rfl (.cons pointer rfl (.cons pointer rfl .nil)))
  have bound := CCalls.Signature.parameters_bound converted (by decide)
  simpa only [function, Arguments.values, CCalls.Signature.locals_cons, CCalls.Signature.locals,
    List.map_nil, List.zip_nil_left, List.lookup_nil, parameterLocals] using bound

theorem parameter_types (pointer : interface.types "const char *" = some .pointer) :
    CLoops.Calls.parameterTypes function.signature.parameters = some parameterTypes := by
  simp [CLoops.Calls.parameterTypes, function, CCalls.parameterType, pointer, parameterTypes, CLoops.bindType]

theorem initialization (args : Arguments) (heap : Heap)
    (size : interface.types "size_t" = some .size) (integer : interface.types "int" = some .int32) :
    CLoops.run 3 (.running function.body (parameterLocals args) parameterTypes heap) =
      some (.running (checks ++ body) (locals args 0 0 0) types heap) := by
  let env1 := CBody.bind (parameterLocals args) "length" (.integer 0)
  let env2 := CBody.bind env1 "prefix" (.integer 0)
  let types1 := CLoops.bindType parameterTypes "length" .size
  let types2 := CLoops.bindType types1 "prefix" .size
  have first := CLoops.declare_local (parameterLocals args) parameterTypes heap "size_t" "length" (.nat 0)
    (.declare "size_t" "prefix" (.nat 0) :: .declare "int" "difference" (.nat 0) :: checks ++ body)
    .size (.integer 0) (.integer 0) size (by simp [parameterLocals, CBody.bind]) rfl
    (CLoops.convert_size_nat 0 (by decide))
  have second := CLoops.declare_local env1 types1 heap "size_t" "prefix" (.nat 0)
    (.declare "int" "difference" (.nat 0) :: checks ++ body)
    .size (.integer 0) (.integer 0) size (by simp [env1, parameterLocals, CBody.bind]) rfl
    (CLoops.convert_size_nat 0 (by decide))
  have third := CLoops.declare_local env2 types2 heap "int" "difference" (.nat 0) (checks ++ body)
    .int32 (.integer 0) (.integer 0) integer (by simp [env2, env1, parameterLocals, CBody.bind]) rfl (by decide)
  change CLoops.run 3 (.running
    (.declare "size_t" "length" (.nat 0) :: .declare "size_t" "prefix" (.nat 0) ::
      .declare "int" "difference" (.nat 0) :: checks ++ body) (parameterLocals args) parameterTypes heap) = _
  dsimp only [env1, types1] at second
  dsimp only [env2, types2, env1, types1] at third
  simp only [List.cons_append] at first second third ⊢
  simp only [CLoops.run, first, second, third, bind, Option.bind_some]
  rfl

theorem null_step (env : CBody.Locals) (types : CLoops.Types) (heap : Heap) (name : String)
    (pointer : Option Address) (rest : List Stmt)
    (found : env name = some (.pointer pointer)) (voidPointer : interface.types "void *" = some .pointer) :
    CLoops.next (.running (nullCheck name :: rest) env types heap) =
      some (.running ((if pointer.isNone then [falseReturn] else []) ++ rest) env types heap) := by
  cases pointer <;>
    simp [nullCheck, falseReturn, CLoops.next, CLoops.nextWith, CLoops.noDeclarations,
      CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith,
      CBody.resolve, found, CNull.literal_eval voidPointer, CBody.comparison,
      CBody.boolean, Value.truth]

theorem checks_pass (name token expected whitespace : Address) (heap : Heap)
    (voidPointer : interface.types "void *" = some .pointer) :
    CLoops.run 4 (.running (checks ++ body)
      (locals ⟨some name, some token, some expected, some whitespace⟩ 0 0 0) types heap) =
    some (.running body (locals ⟨some name, some token, some expected, some whitespace⟩ 0 0 0) types heap) := by
  let env := locals ⟨some name, some token, some expected, some whitespace⟩ 0 0 0
  have first := null_step env types heap "name" (some name)
    ([nullCheck "token", nullCheck "expected", nullCheck "whitespace"] ++ body)
    (by simp [env, locals, parameterLocals, CBody.bind]) voidPointer
  have second := null_step env types heap "token" (some token)
    ([nullCheck "expected", nullCheck "whitespace"] ++ body)
    (by simp [env, locals, parameterLocals, CBody.bind]) voidPointer
  have third := null_step env types heap "expected" (some expected) ([nullCheck "whitespace"] ++ body)
    (by simp [env, locals, parameterLocals, CBody.bind]) voidPointer
  have fourth := null_step env types heap "whitespace" (some whitespace) body
    (by simp [env, locals, parameterLocals, CBody.bind]) voidPointer
  change CLoops.run 4 (.running (checks ++ body) env types heap) = _
  simp only [checks, List.cons_append, List.nil_append] at first second third fourth ⊢
  simp only [CLoops.run, first, second, third, fourth, Option.isNone_some, Bool.false_eq_true,
    if_false, List.nil_append, bind, Option.bind_some]
  rfl

end Rumoca.FMI3.Identity
