import RumocaC.CallParameters
import RumocaC.TypedCallProofs

/-! Sufficient conditions for actual fresh-scope call entry. Argument
conversion is a per-parameter relation; the resulting environment is an
independent standard-library lookup of the named output values. These proofs
do not require a successful call or a caller-supplied local/type environment. -/
noncomputable section
namespace Rumoca.CCalls.Signature
open CTree CMemory
variable [interface : CInterface]

def Ready (signature : CTree.Signature) : Prop :=
  (signature.parameters.map Parameter.name).Nodup ∧
    signature.parameters.all (fun p => (interface.types (parameterType p)).isSome) = true ∧
    (signature.result == "void" || (interface.types signature.result).isSome) = true

instance (signature : CTree.Signature) : Decidable (Ready signature) := by
  unfold Ready
  infer_instance

inductive Arguments : List Parameter → List Value → List Value → Prop where
  | nil : Arguments [] [] []
  | cons : interface.types (parameterType p) = some type →
      convert type input = some output → Arguments ps inputs outputs →
      Arguments (p :: ps) (input :: inputs) (output :: outputs)

theorem Arguments.length (arguments : Arguments ps inputs outputs) : ps.length = outputs.length := by
  induction arguments <;> simp_all

def locals (ps : List Parameter) (values : List Value) : CBody.Locals :=
  fun name => ((ps.map Parameter.name).zip values).lookup name

omit interface in
theorem locals_cons (p : Parameter) (ps : List Parameter) (v : Value) (vs : List Value) :
    locals (p :: ps) (v :: vs) = CBody.bind (locals ps vs) p.name v := by
  funext name
  by_cases same : name = p.name
  · subst name
    simp [locals, CBody.bind]
  · have different : (name == p.name) = false := beq_eq_false_iff_ne.mpr same
    simp [locals, CBody.bind, List.lookup_cons, same, different]

omit interface in
theorem locals_missing (sameLength : ps.length = values.length)
    (absent : name ∉ ps.map Parameter.name) : locals ps values name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have keys : ((ps.map Parameter.name).zip values).map Prod.fst = ps.map Parameter.name :=
    List.map_fst_zip (by simpa using sameLength.le)
  have present : pair.1 ∈ ps.map Parameter.name := by
    rw [← keys]
    exact List.mem_map.mpr ⟨pair, member, rfl⟩
  have different : name ≠ pair.1 := fun same => absent (same ▸ present)
  simpa using different

theorem parameters_bound (arguments : Arguments ps inputs outputs)
    (unique : (ps.map Parameter.name).Nodup) :
    parameters ps inputs = some (locals ps outputs) := by
  induction arguments with
  | nil => rfl
  | @cons p type input output ps inputs outputs resolved converted tail ih =>
    have names : p.name ∉ ps.map Parameter.name ∧ (ps.map Parameter.name).Nodup := by
      simpa using unique
    have bound := ih names.2
    have fresh := locals_missing tail.length names.1
    rw [locals_cons]
    simp [parameters, bound, fresh, CBody.cast, resolved, converted]

theorem call_entry (ready : Ready fn.signature) (arguments : Arguments fn.signature.parameters inputs outputs)
    (program : Program) (heap : Heap) (stack : Typed.Continuation)
    (defined : program.definitions fn.signature.name = some (.tree fn)) :
    ∃ types,
      Typed.next program (.calling fn.signature.name inputs heap stack) =
        some (.body (.running fn.body (locals fn.signature.parameters outputs) types heap)
          fn.signature.result stack) ∧
      Parameters.Coherent (locals fn.signature.parameters outputs) types := by
  have bound := parameters_bound arguments ready.1
  obtain ⟨types, typeBindings, coherent⟩ := Parameters.parameters_typed _ _ _ bound
  exact ⟨types, Typed.tree_entry program fn.signature.name inputs heap stack fn _ types
    defined bound typeBindings, coherent⟩

/-- A proof witness for each value type; this is not a C initializer policy. -/
def witnessValue : CType → Value
  | .float64 => .float64 0
  | .pointer => .pointer none
  | _ => .integer 0

omit interface in
theorem witness_valid (type : CType) : convert type (witnessValue type) = some (witnessValue type) := by
  cases type <;> simp [witnessValue, convert, Value.truth, CUnsigned.value]
  rename_i signed
  cases signed <;> decide +kernel

theorem arguments_exist (known : ps.all (fun p => (interface.types (parameterType p)).isSome) = true) :
    ∃ values, Arguments ps values values := by
  induction ps with
  | nil => exact ⟨[], .nil⟩
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true] at known
    obtain ⟨type, resolved⟩ := Option.isSome_iff_exists.mp known.1
    obtain ⟨values, tail⟩ := ih known.2
    exact ⟨witnessValue type :: values, .cons resolved (witness_valid type) tail⟩

end Rumoca.CCalls.Signature
