import RumocaCore.Modelica.Selection

/-! Shared static checks for selecting admitted models from the general
syntax tree. Each check either returns the information it reads or rejects the
tree at the index of the token that violates it. A check's success lemma states
the exact subtree it accepted, so a selection's printed tokens follow by
computation. Token indices are the printed widths of the preceding nodes. -/
namespace Rumoca.Modelica.Select
open _root_.Parser AST

/-- MLS 3.7 §4.9 predefined type names. They cannot be redeclared, so a
declared or referenced name may not be one of them. -/
def predefined (name : String) : Bool := ["Real", "Integer", "Boolean", "String"].contains name

/-- An identifier token that names a declared or referenced entity. -/
def name (pos : Nat) (what : String) : Token → Except Rejection String
  | .ident s => if predefined s then .error ⟨pos, s!"{what} may not be the predefined type name {s}"⟩
      else .ok s
  | .number s => .error ⟨pos, s!"{what} must be an identifier, not the number {s}"⟩
  | token => .error ⟨pos, s!"{what} must be an identifier, not {token.text}"⟩

theorem name_ok {pos : Nat} {what s : String} {t : Token} (h : name pos what t = .ok s) :
    t = .ident s := by
  cases t with
  | ident x =>
    simp only [name] at h
    split at h
    · contradiction
    · cases h; rfl
  | number _ | literal _ | string _ | comment _ => cases h

/-- A bare unindexed, undotted reference whose token is the given one. -/
def bare (token : Token) : Expr := .reference ⟨false, [⟨token, none⟩]⟩

/-- An unindexed, undotted reference to a named entity. -/
def reference (pos : Nat) (what : String) : Expr → Except Rejection String
  | .reference ⟨false, [⟨token, none⟩]⟩ => name pos what token
  | _ => .error ⟨pos, s!"{what} must be a plain name"⟩

theorem reference_ok {pos : Nat} {what s : String} {e : Expr} (h : reference pos what e = .ok s) :
    e = bare (.ident s) := by
  unfold reference at h
  split at h
  · rw [name_ok h]; rfl
  · cases h

/-- A bare number whose spelling satisfies `admitted`. -/
def numeral (pos : Nat) (what : String) (admitted : String → Bool) : Expr → Except Rejection String
  | .reference ⟨false, [⟨.number spelling, none⟩]⟩ =>
    if admitted spelling then .ok spelling else .error ⟨pos, s!"{what} may not be {spelling}"⟩
  | .string value => .error ⟨pos, s!"{what} must be a Real number, not the String {value.text}"⟩
  | _ => .error ⟨pos, s!"{what} must be a number"⟩

theorem numeral_ok {pos : Nat} {what : String} {admitted : String → Bool} {e : Expr} {s : String}
    (h : numeral pos what admitted e = .ok s) : e = bare (.number s) ∧ admitted s = true := by
  unfold numeral at h
  split at h
  · split at h
    · rename_i admits
      cases h
      exact ⟨rfl, admits⟩
    · cases h
  · cases h
  · cases h

/-- The number spelled exactly `spelling`. -/
def exactly (pos : Nat) (what spelling : String) (e : Expr) : Except Rejection Unit :=
  (numeral pos what (· == spelling) e).map fun _ => ()

theorem exactly_ok {pos : Nat} {what spelling : String} {e : Expr} {u : Unit}
    (h : exactly pos what spelling e = .ok u) : e = bare (.number spelling) := by
  unfold exactly at h
  cases found : numeral pos what (· == spelling) e with
  | error _ => rw [found] at h; cases h
  | ok s =>
    obtain ⟨shape, same⟩ := numeral_ok found
    rw [shape, show s = spelling by simpa using same]

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- An absent optional part. -/
def absent {α : Type} (pos : Nat) (message : String) : Option α → Except Rejection Unit
  | none => .ok ()
  | some _ => .error ⟨pos, message⟩

theorem absent_ok {α : Type} {pos : Nat} {message : String} {o : Option α} {u : Unit}
    (h : absent pos message o = .ok u) : o = none := by
  cases o with
  | none => rfl
  | some _ => cases h

/-- An empty description string; description strings are not admitted yet. -/
def descriptionString (pos : Nat) : List Token → Except Rejection Unit
  | [] => .ok ()
  | _ :: _ => .error ⟨pos, "description strings are not admitted yet"⟩

theorem descriptionString_ok {pos : Nat} {strings : List Token} {u : Unit}
    (h : descriptionString pos strings = .ok u) : strings = [] := by
  cases strings with
  | nil => rfl
  | cons _ _ => cases h

/-- An empty description: no description string and no annotation clause, which
are not admitted yet. -/
def description (pos : Nat) (d : Description) : Except Rejection Unit := do
  descriptionString pos d.strings
  absent pos "annotations are not admitted yet" d.annotation

theorem description_ok {pos : Nat} {d : Description} {u : Unit}
    (h : description pos d = .ok u) : d = ⟨[], none⟩ := by
  obtain ⟨strings, annotation⟩ := d
  unfold description at h
  cases found : descriptionString pos strings with
  | error _ => rw [found] at h; cases h
  | ok _ =>
    rw [found] at h
    have unannotated : annotation = none := absent_ok h
    rw [descriptionString_ok found, unannotated]

/-- The only class of a stored definition: `model NAME ... end NAME;` without a
description string or class annotation. -/
def model (d : StoredDefinition) : Except Rejection (String × Composition × String) :=
  match d.classes with
  | [] => .error ⟨0, "expected one class definition"⟩
  | [⟨prefixes, .long first strings body last⟩] =>
    if prefixes = .literal "model" then do
      let modelName ← name 1 "the model name" first
      descriptionString 2 strings
      absent (2 + (Print.composition { body with annotation := none }).length)
        "annotations are not admitted yet" body.annotation
      let endName ← name (3 + (Print.composition body).length) "the end name" last
      return (modelName, body, endName)
    else .error ⟨0, "expected a model"⟩
  | first :: _ :: _ =>
    .error ⟨(Print.classDefinition first).length + 1, "only one class definition is admitted"⟩

theorem model_ok {d : StoredDefinition} {modelName endName : String} {body : Composition}
    (h : model d = .ok (modelName, body, endName)) :
    d = ⟨[⟨.literal "model",
      .long (.ident modelName) [] ⟨body.elements, body.sections, none⟩ (.ident endName)⟩]⟩ := by
  obtain ⟨classes⟩ := d
  rcases classes with _ | ⟨⟨prefixes, ⟨first, strings, body', last⟩⟩, _ | ⟨_, _⟩⟩
  · cases h
  · simp only [model] at h
    split at h
    · rename_i isModel
      subst isModel
      obtain ⟨n, found, h⟩ := bind_ok h
      obtain ⟨_, described, h⟩ := bind_ok h
      obtain ⟨_, unannotated, h⟩ := bind_ok h
      obtain ⟨e, ended, h⟩ := bind_ok h
      cases h
      obtain ⟨elements, sections, annotation⟩ := body
      have none' : annotation = none := absent_ok unannotated
      rw [name_ok found, name_ok ended, descriptionString_ok described, none']
    · cases h
  · cases h

/-- `Real NAME [subscripts]` declared with the given prefix, one name per
clause, without a condition attribute or description; returns the name, the
declared subscripts and the modification. -/
def declaration (pos : Nat) (what : String) (typePrefix : Option Token) :
    Element → Except Rejection (String × Option (List Expr) × Option Modification)
  | .component ⟨written, typeName, subscripts, declarations⟩ =>
    if written ≠ typePrefix then .error ⟨pos, s!"{what} has the wrong input/output prefix"⟩
    else
      let pos := pos + (Print.typePrefix written).length
      if typeName ≠ [.ident "Real"] then .error ⟨pos, s!"{what} must have type Real"⟩
      else if subscripts.isSome then .error ⟨pos + 1, s!"{what} has subscripts on its type"⟩
      else match declarations with
        | [⟨⟨token, indices, modification⟩, condition, described⟩] => do
          let declared ← name (pos + 1) what token
          let after := pos + 1 + (Print.declaration ⟨token, indices, modification⟩).length
          absent after "condition attributes are not admitted yet" condition
          description after described
          return (declared, indices, modification)
        | _ => .error ⟨pos + 1, s!"{what} must declare exactly one name"⟩

theorem declaration_ok {pos : Nat} {what : String} {typePrefix : Option Token} {e : Element}
    {declared : String} {indices : Option (List Expr)} {modification : Option Modification}
    (h : declaration pos what typePrefix e = .ok (declared, indices, modification)) :
    e = .component ⟨typePrefix, [.ident "Real"], none,
      [⟨⟨.ident declared, indices, modification⟩, none, ⟨[], none⟩⟩]⟩ := by
  obtain ⟨⟨written, typeName, subscripts, declarations⟩⟩ := e
  simp only [declaration] at h
  split at h
  · cases h
  · rename_i samePrefix
    simp only [Decidable.not_not] at samePrefix
    subst samePrefix
    split at h
    · cases h
    · rename_i sameType
      simp only [Decidable.not_not] at sameType
      subst sameType
      split at h
      · cases h
      · rename_i unsubscripted
        simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
          at unsubscripted
        subst unsubscripted
        split at h
        · rename_i token indices' modification' condition described
          obtain ⟨n, found, h⟩ := bind_ok h
          obtain ⟨_, unconditioned, h⟩ := bind_ok h
          obtain ⟨_, undescribed, h⟩ := bind_ok h
          cases h
          rw [name_ok found, absent_ok unconditioned, description_ok undescribed]
        · cases h

/-- `der(NAME)`. -/
def derivative (pos : Nat) : Expr → Except Rejection String
  | .call .der [argument] => reference (pos + 2) "the differentiated name" argument
  | _ => .error ⟨pos, "the left side must be der applied to one declared name"⟩

theorem derivative_ok {pos : Nat} {e : Expr} {s : String} (h : derivative pos e = .ok s) :
    e = .call .der [bare (.ident s)] := by
  unfold derivative at h
  split at h
  · rw [reference_ok h]
  · cases h

/-- An equation without a description. -/
def plain (e : Equation) : SomeEquation := ⟨e, ⟨[], none⟩⟩

/-- The equations of a section, none with a description. -/
def plainEquations (pos : Nat) : List SomeEquation → Except Rejection (List Equation)
  | [] => .ok []
  | ⟨e, described⟩ :: rest => do
    description (pos + (Print.equation e).length) described
    let others ← plainEquations (pos + (Print.equation e).length + 1) rest
    return e :: others

theorem plainEquations_ok {pos : Nat} {qs : List SomeEquation} {es : List Equation}
    (h : plainEquations pos qs = .ok es) : qs = es.map plain := by
  induction qs generalizing pos es with
  | nil => cases h; rfl
  | cons q rest ih =>
    obtain ⟨e, described⟩ := q
    obtain ⟨_, undescribed, h⟩ := bind_ok h
    obtain ⟨others, following, h⟩ := bind_ok h
    cases h
    rw [description_ok undescribed, ih following]
    rfl

/-- Equations without descriptions are read back unchanged. -/
theorem plainEquations_plain (pos : Nat) (es : List Equation) :
    plainEquations pos (es.map plain) = .ok es := by
  induction es generalizing pos with
  | nil => rfl
  | cons e rest ih =>
    simp [plainEquations, plain, description, descriptionString, absent, ih, bind, Except.bind,
      pure, Except.pure]

/-- The equations of the single equation section. -/
def equations (pos : Nat) (body : Composition) : Except Rejection (List Equation) :=
  match body.sections with
  | [⟨equations⟩] => plainEquations (pos + 1) equations
  | [] => .error ⟨pos, "expected one equation section"⟩
  | first :: _ :: _ =>
    .error ⟨pos + (Print.equationSection first).length, "only one equation section is admitted"⟩

theorem equations_ok {pos : Nat} {body : Composition} {es : List Equation}
    (h : equations pos body = .ok es) : body.sections = [⟨es.map plain⟩] := by
  unfold equations at h
  split at h
  · rename_i same
    rw [same, plainEquations_ok h]
  · cases h
  · cases h

/-- The width of printed elements with their separators. -/
def elementsWidth (elements : List Element) : Nat :=
  (elements.flatMap fun e => Print.element e ++ [.literal ";"]).length

/-- Exactly one item. -/
def one {α : Type} (pos : Nat) (message : String) : List α → Except Rejection α
  | [item] => .ok item
  | _ => .error ⟨pos, message⟩

theorem one_ok {α : Type} {pos : Nat} {message : String} {items : List α} {item : α}
    (h : one pos message items = .ok item) : items = [item] := by
  unfold one at h
  split at h
  · cases h; rfl
  · cases h

/-- A scalar, unmodified `Real NAME` declaration without a prefix. -/
def state (pos : Nat) (what : String) (e : Element) : Except Rejection String := do
  let declared ← declaration pos what none e
  match declared.2.1, declared.2.2 with
  | none, none => .ok declared.1
  | some _, _ => .error ⟨pos + 2, s!"{what} must be scalar"⟩
  | none, some _ => .error ⟨pos + 2, s!"{what} may not have a modification"⟩

theorem state_ok {pos : Nat} {what s : String} {e : Element} (h : state pos what e = .ok s) :
    e = .component ⟨none, [.ident "Real"], none, [⟨⟨.ident s, none, none⟩, none, ⟨[], none⟩⟩]⟩ := by
  obtain ⟨⟨declared, indices, modification⟩, found, h⟩ := bind_ok h
  rw [declaration_ok found]
  cases indices <;> cases modification <;> simp at h
  cases h
  rfl

end Rumoca.Modelica.Select
