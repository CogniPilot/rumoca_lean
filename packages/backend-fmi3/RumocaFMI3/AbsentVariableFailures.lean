import RumocaFMI3.AbsentVariableRuntime

noncomputable section
namespace Rumoca.FMI3.AbsentVariables
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface

def failureMessage : String := "No variables of this type exist"

def SuppressedContract [CInterface] (ty : VariableType) (write : Bool)
    (program : Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (references sizes values : Option Address) (n m : UInt64)
    (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) → (n.toNat ≠ 0 ∨ m.toNat ≠ 0) →
    ∀ observed, (machine program).Behaves
      (.calling (signature ty write).name
        (arguments ty.hasSizes (some p) references sizes values n m) heap .done) observed ↔
      observed = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

def LoggedContract [CInterface] (ty : VariableType) (write : Bool)
    (program : Program Invocation) (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (references sizes values environment : Option Address)
    (n m : UInt64) (kind : Kind) (mode : Mode)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    (n.toNat ≠ 0 ∨ m.toNat ≠ 0) →
    (∀ observed, (machine program).Behaves
      (.calling (signature ty write).name
        (arguments ty.hasSizes (some p) references sizes values n m) heap .done) observed ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        observed = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ observed = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message failureMessage)

theorem suppressed_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source)
    (ty : VariableType) (write : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E) (message : Address) (heap : Heap),
      program.internal.definitions (signature ty write).name =
        some (.tree (Runtime.function model (signature ty write))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals failureMessage = some message → SuppressedContract ty write program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program message heap defined helper messageBound p references sizes values n m
    kind mode logger logging hk hm hl hg suppressed nonempty observed
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact StaticErrors.failure_suppressed_behaviors ((ErrorContext.static objects literals).withRounding header)
    program (Runtime.function model (signature ty write))
    (arguments ty.hasSizes (some p) references sizes values n m) heap heap p message failureMessage
    _ logger logging (body_agrees header objects literals model ty write)
    (nonempty_prefix (static := ⟨literals⟩) model ty write heap p references sizes values n m kind mode
      hk modeLoaded True.intro nonempty)
    defined helper messageBound hm hl hg suppressed observed

theorem logged_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source)
    (ty : VariableType) (write : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program Invocation) (category message : Address) (heap : Heap) (signed : Bool),
      program.internal.definitions (signature ty write).name =
        some (.tree (Runtime.function model (signature ty write))) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "logStatus" = some category → literals failureMessage = some message →
      Stored signed heap category "logStatus" → Stored signed heap message failureMessage →
      LoggedContract ty write program category message heap signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program category message heap signed defined helper categoryBound messageBound categoryStored messageStored
    p logger references sizes values environment n m kind mode name effect address external hk hm hl hg he nonempty
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have all := StaticErrors.failure_all_behaviors ((ErrorContext.static objects literals).withRounding header)
    program (Runtime.function model (signature ty write))
    (arguments ty.hasSizes (some p) references sizes values n m) heap heap p message category logger
    failureMessage name environment _ (External.observed (Logging.signature name) effect)
    (body_agrees header objects literals model ty write)
    (nonempty_prefix (static := ⟨literals⟩) model ty write heap p references sizes values n m kind mode
      hk modeLoaded True.intro nonempty)
    defined helper messageBound address external rfl categoryBound hm hl hg he
  constructor
  · intro observed
    exact (all observed).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) observed)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

end Rumoca.FMI3.AbsentVariables
end
