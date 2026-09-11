import Rumoca.ParseFiles

/-! Exact refinement of the former eager terminal presentation. The reference
is proof-only. Parser, resolver, structured diagnostics and failure status are
preserved for every input, including file-read failures. -/
namespace Rumoca.CLI
open Lean

noncomputable def analyzeReference (item : String × Except String String) :
    Json × Option String :=
  let (name, read) := item
  let failure (diagnostic : Json) (message : String) :=
    (Json.mkObj [("path", toJson name), ("ok", toJson false),
      ("diagnostics", toJson #[diagnostic])], some message)
  match read with
  | .error e => failure (Json.mkObj [("phase", "io"), ("message", toJson e)]) s!"{name}: {e}"
  | .ok source =>
    let error (e : Parser.Source.Diagnostic source) :=
      failure (Diagnostics.toJson e) (Diagnostics.render name e)
    let result := Parallel.parseOne ⟨name, source⟩
    match result.parsed with
    | .error e => error e
    | .ok p => match p.resolve with
      | .error e => error e
      | .ok _ => (Json.mkObj [("path", toJson name), ("ok", toJson true),
          ("model", toJson p.parsed.ast.name), ("diagnostics", toJson (#[] : Array Json))], none)

theorem analyze_eq_reference (terminal : Bool) (item : String × Except String String) :
    analyze terminal item =
      ((analyzeReference item).1,
        (analyzeReference item).2.map (fun message => if terminal then message else "")) := by
  rcases item with ⟨name, read⟩
  cases read with
  | error e => rfl
  | ok source =>
      cases parsed : (Parallel.parseOne ⟨name, source⟩).parsed with
      | error e => simp [analyze, analyzeReference, parsed]
      | ok p =>
          cases resolved : p.resolve <;> simp [analyze, analyzeReference, parsed, resolved]

theorem analyze_json (terminal : Bool) (item : String × Except String String) :
    (analyze terminal item).1 = (analyzeReference item).1 := by
  rw [analyze_eq_reference]

theorem analyze_failure (terminal : Bool) (item : String × Except String String) :
    (analyze terminal item).2.isSome = (analyzeReference item).2.isSome := by
  rw [analyze_eq_reference]
  simp

theorem analyze_terminal (item : String × Except String String) :
    analyze true item = analyzeReference item := by
  rw [analyze_eq_reference]
  simp

/-- The CLI's ordered JSON array and aggregate error flag are independent of
terminal formatting and scheduling for every file-read snapshot batch. -/
theorem analyze_batch (jobs : Nat) (terminal : Bool)
    (items : List (String × Except String String)) :
    (Parser.Parallel.map jobs (analyze terminal) items).map Prod.fst =
      (items.map analyzeReference).map Prod.fst ∧
    (Parser.Parallel.map jobs (analyze terminal) items).any (fun r => r.2.isSome) =
      (items.map analyzeReference).any (fun r => r.2.isSome) := by
  simp [Parser.Parallel.map_eq, List.map_map, List.any_map,
    Function.comp_def, analyze_json, analyze_failure]

end Rumoca.CLI
