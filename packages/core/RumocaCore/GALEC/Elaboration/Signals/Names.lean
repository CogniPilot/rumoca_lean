import GALECParser.AST
import RumocaCore.GALEC.Signals

/-! Signal names of interfaces, error-signal statements and checks. The
admitted subset has no error-signal declaration syntax, so a name is admitted
only as the canonical spelling of a predefined signal (eFMI §3.2.5 §1.1-§1.3);
any other name, including a would-be user-defined signal, is rejected. -/
namespace Rumoca.GALEC.Elaboration.SignalNames
open _root_.Parser

def readName : AST.Name → Option Signal
  | .ident spelling => Signal.read spelling
  | _ => none

theorem readName_iff (name : AST.Name) (signal : Signal) :
    readName name = some signal ↔ name = .ident signal.name := by
  cases name with
  | ident spelling =>
    simp only [readName, Signal.read_iff, Token.ident.injEq]
    exact eq_comm
  | literal _ => simp [readName]
  | number _ => simp [readName]

def signals : List AST.Name → Option (List Signal)
  | [] => some []
  | name :: rest => (readName name).bind fun signal => (signals rest).map (signal :: ·)

theorem signals_iff (names : List AST.Name) (list : List Signal) :
    signals names = some list ↔ names = list.map fun signal => .ident signal.name := by
  induction names generalizing list with
  | nil =>
    cases list <;> simp [signals]
  | cons name rest ih =>
    simp only [signals, Option.bind_eq_some_iff, Option.map_eq_some_iff, readName_iff, ih]
    constructor
    · rintro ⟨signal, rfl, tail, rfl, rfl⟩
      rfl
    · intro same
      cases list with
      | nil => cases same
      | cons signal tail =>
        simp only [List.map_cons, List.cons.injEq] at same
        exact ⟨signal, same.1, tail, same.2, rfl⟩

/-- The set named by a list of signal names, if every name is predefined. -/
def read (names : List AST.Name) : Option SignalSet :=
  (signals names).map SignalSet.ofList

/-- Independent meaning: the names are the canonical spellings of signals
whose set is `set`. Order and repetition carry no meaning. -/
def Denotes (names : List AST.Name) (set : SignalSet) : Prop :=
  ∃ list : List Signal, names = list.map (fun signal => .ident signal.name) ∧
    set = SignalSet.ofList list

theorem read_iff (names : List AST.Name) (set : SignalSet) :
    read names = some set ↔ Denotes names set := by
  simp only [read, Option.map_eq_some_iff, signals_iff, Denotes]
  exact ⟨fun ⟨list, named, same⟩ => ⟨list, named, same.symm⟩,
    fun ⟨list, named, same⟩ => ⟨list, named, same.symm⟩⟩

theorem denotes_unique {names : List AST.Name} {first second : SignalSet}
    (denoted : Denotes names first) (again : Denotes names second) : first = second :=
  Option.some.inj (((read_iff _ _).mpr denoted).symm.trans ((read_iff _ _).mpr again))

theorem signals_rejected (member : name ∈ names) (unknown : readName name = none) :
    signals names = none := by
  induction names with
  | nil => cases member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | later
    · simp [signals, unknown]
    · cases found : readName first with
      | none => simp [signals, found]
      | some signal => simp [signals, found, ih later]

/-- Any name that is not the spelling of a predefined signal is rejected,
wherever it occurs in the list. -/
theorem read_rejected (member : name ∈ names) (unknown : readName name = none) :
    read names = none := by
  simp [read, signals_rejected member unknown]

theorem undeclared_rejected (spelling : String) (unknown : Signal.read spelling = none)
    (before after : List AST.Name) :
    read (before ++ .ident spelling :: after) = none :=
  read_rejected (name := .ident spelling) (by simp) unknown

end Rumoca.GALEC.Elaboration.SignalNames
