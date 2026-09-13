import RumocaFMI3.RuntimePreprocessing
import RumocaFMI3.IdentifierProofs

/-! Character-rewrite stability of the actual complete FMI adapter renderer.
This does not interpret its preprocessing directives or included headers. -/
namespace Rumoca.FMI3.AdapterPreprocessing
open CTree Preprocessing

theorem name_plain (parts : NameParts name) : Plain name.toList := by
  obtain ⟨first, rest, chars, head, tail⟩ := parts
  intro c member
  rw [chars] at member
  have good : _root_.Parser.identRest c = true := by
    rcases List.mem_cons.mp member with rfl | member
    · simp [_root_.Parser.identRest, head]
    · exact List.all_eq_true.mp tail c member
  constructor <;> intro same <;> subst c <;>
    simp [_root_.Parser.identRest, _root_.Parser.identStart, _root_.Parser.asciiLetter] at good

theorem helpers_inputs (fn : CTree.Function) (member : fn ∈ Runtime.helpers) :
    FunctionInputs fn := by
  simp only [Runtime.helpers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [FunctionInputs, SignatureInputs, ParameterInputs, StmtInputs, ExprInputs,
      Runtime.setMode, Runtime.put, Runtime.mode, Runtime.n, Runtime.v, Runtime.field,
      Runtime.log, Runtime.branch, Runtime.both, Runtime.ret, Runtime.call, Plain,
      Identity.function, Identity.nullCheck, Identity.falseReturn, Identity.measure, Identity.measurePrefix,
      Identity.blank, Identity.compareToken, Identity.comparisonReturn, CTree.Expr.nullPointer,
      CAtomicScan.function, CAtomicScan.scan, CAtomicScan.attempt, CAtomicScan.selected, CAtomicScan.advance]

set_option maxRecDepth 4096 in
theorem declarations_stable : Stable Runtime.declarations.toList := by
  apply plain_stable
  unfold Plain
  decide +kernel

theorem prefix_stable (name : String) (valid : Plain name.toList) :
    Stable (functionPrefix name).toList := by
  have checked := plain_stable valid
  simp only [functionPrefix, modelIdentifier]
  c_preprocessing_parts

theorem render_stable (model : Solve.FMI3Model source) (signatures : List Signature)
    (name : Plain model.name.toList)
    (valid : ∀ signature ∈ signatures, SignatureInputs signature) :
    Stable (Runtime.render model signatures).toList := by
  have checkedPrefix := prefix_stable model.name name
  have declarations := declarations_stable
  have helpers := Stable.join (Runtime.helpers.map CTree.Function.render) (by
    intro text member
    obtain ⟨fn, occurs, rfl⟩ := List.mem_map.mp member
    exact function_stable fn (helpers_inputs fn occurs))
  have functions := Stable.join
    (signatures.map (fun signature => (Runtime.function model signature).render)) (by
      intro text member
      obtain ⟨signature, occurs, rfl⟩ := List.mem_map.mp member
      exact function_stable _ (RuntimePreprocessing.function_inputs model signature
        (valid signature occurs)))
  simp only [Runtime.render, String.toList_append]
  exact (((checkedPrefix.append (plain_stable (by simp [Plain]))).append declarations).append
    helpers).append functions

theorem render_preprocessed (model : Solve.FMI3Model source) (signatures : List Signature)
    (name : Plain model.name.toList)
    (valid : ∀ signature ∈ signatures, SignatureInputs signature)
    (steps : Relation.ReflTransGen CString.Rewrite (Runtime.render model signatures).toList out) :
    out = (Runtime.render model signatures).toList :=
  (render_stable model signatures name valid).preprocessed steps

end Rumoca.FMI3.AdapterPreprocessing
