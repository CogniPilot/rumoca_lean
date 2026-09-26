import RumocaCore.Modelica.Select

/-! Annotations (MLS 3.7 chapter 18) are parsed in full as class modifications.
An annotation that only documents or presents a model is discarded; one whose
meaning changes translation or simulation is rejected (`screen`), so discarding
annotations never changes the meaning of a model silently. `erase` removes every
annotation clause from a syntax tree. An annotation clause occurs in a
description and at the end of a class composition; class modifications and
description strings contain none. -/
namespace Rumoca.Modelica.Annotation
open _root_.Parser AST

/-- MLS 3.7 chapter 18 annotations whose meaning affects translation or
simulation: parameter evaluation (`Evaluate`), inlining (`Inline`, `LateInline`,
`InlineAfterIndexReduction`), event generation (`GenerateEvents`), function
derivatives and inverses (`derivative`, `inverse`, `smoothOrder`) and the
simulation experiment (`experiment`). -/
def meaningChanging : List String :=
  ["Evaluate", "Inline", "LateInline", "InlineAfterIndexReduction", "GenerateEvents",
    "derivative", "inverse", "smoothOrder", "experiment"]

/-! ### Screening meaning-changing annotations -/

/-- The arguments of an annotation clause starting at token `pos`: the first
argument whose name is meaning-changing is rejected at its name token. -/
def arguments (pos : Nat) : List Argument → Except Rejection Unit
  | [] => .ok ()
  | a :: rest =>
    match a.modification.name with
    | [.ident s] =>
      if meaningChanging.contains s then
        .error ⟨pos + (if a.each then 1 else 0),
          s!"the annotation {s} changes the meaning of the model and is not supported"⟩
      else arguments (pos + (Print.argument a).length + 1) rest
    | _ => arguments (pos + (Print.argument a).length + 1) rest

/-- An optional annotation clause whose `annotation` keyword is token `pos`. -/
def clause (pos : Nat) : Option (List Argument) → Except Rejection Unit
  | none => .ok ()
  | some a => arguments (pos + 2) a

def description (pos : Nat) (d : Description) : Except Rejection Unit :=
  clause (pos + (Print.descriptionString d.strings).length) d.annotation

def declarations (pos : Nat) : List ComponentDeclaration → Except Rejection Unit
  | [] => .ok ()
  | c :: rest => do
    description (pos + (Print.declaration c.declaration).length +
      (Print.condition c.condition).length) c.description
    declarations (pos + (Print.componentDeclaration c).length + 1) rest

def element (pos : Nat) : Element → Except Rejection Unit
  | .component c => declarations (pos + (Print.typePrefix c.typePrefix).length +
      (Print.name c.typeName).length + (Print.subscripts c.subscripts).length) c.declarations

def elements (pos : Nat) : List Element → Except Rejection Unit
  | [] => .ok ()
  | e :: rest => do
    element pos e
    elements (pos + (Print.element e).length + 1) rest

def equations (pos : Nat) : List SomeEquation → Except Rejection Unit
  | [] => .ok ()
  | q :: rest => do
    description (pos + (Print.equation q.equation).length) q.description
    equations (pos + (Print.someEquation q).length + 1) rest

def sections (pos : Nat) : List EquationSection → Except Rejection Unit
  | [] => .ok ()
  | s :: rest => do
    equations (pos + 1) s.equations
    sections (pos + (Print.equationSection s).length) rest

def composition (pos : Nat) (c : Composition) : Except Rejection Unit := do
  elements pos c.elements
  sections (pos + Select.elementsWidth c.elements) c.sections
  clause (pos + Select.elementsWidth c.elements + (c.sections.flatMap Print.equationSection).length)
    c.annotation

def classes (pos : Nat) : List ClassDefinition → Except Rejection Unit
  | [] => .ok ()
  | c :: rest => do
    match c.specifier with
    | .long _ strings body _ =>
      composition (pos + 2 + (Print.descriptionString strings).length) body
    classes (pos + (Print.classDefinition c).length + 1) rest

/-- Reject the first meaning-changing annotation of a stored definition at its
name token. -/
def screen (d : StoredDefinition) : Except Rejection Unit := classes 0 d.classes

/-! ### Erasing annotations -/

def Description.erase (d : Description) : Description := ⟨d.strings, none⟩

def ComponentDeclaration.erase (c : ComponentDeclaration) : ComponentDeclaration :=
  ⟨c.declaration, c.condition, Description.erase c.description⟩

def Element.erase : Element → Element
  | .component c => .component { c with declarations := c.declarations.map ComponentDeclaration.erase }

def SomeEquation.erase (q : SomeEquation) : SomeEquation := ⟨q.equation, Description.erase q.description⟩

def EquationSection.erase (s : EquationSection) : EquationSection := ⟨s.equations.map SomeEquation.erase⟩

def Composition.erase (c : Composition) : Composition :=
  ⟨c.elements.map Element.erase, c.sections.map EquationSection.erase, none⟩

def ClassDefinition.erase : ClassDefinition → ClassDefinition
  | ⟨prefixes, .long name strings body endName⟩ => ⟨prefixes, .long name strings (Composition.erase body) endName⟩

/-- The stored definition with every annotation clause removed. -/
def erase (d : StoredDefinition) : StoredDefinition := ⟨d.classes.map ClassDefinition.erase⟩

/-! ### Trees without an `annotation` keyword -/

/-- Neither screening nor erasing affects a tree whose printed tokens contain
no `annotation` keyword. -/
def Unannotated (tokens : List Token) : Prop := .literal "annotation" ∉ tokens

private theorem description_none {d : Description}
    (free : Unannotated (Print.description d)) : d.annotation = none := by
  obtain ⟨strings, annotation⟩ := d
  cases annotation with
  | none => rfl
  | some a => exact absurd (by simp [Print.description, Print.annotation, Print.annotationClause]) free

private theorem declarations_none {cs : List ComponentDeclaration}
    (free : Unannotated (Print.declarations cs)) : ∀ c ∈ cs, c.description.annotation = none := by
  intro c member
  apply description_none
  intro inside
  apply free
  cases cs with
  | nil => cases member
  | cons first rest =>
    simp only [Print.declarations, List.mem_append, List.mem_flatMap, List.mem_cons]
    rcases List.mem_cons.mp member with rfl | member
    · exact .inl (by simp [Print.componentDeclaration, inside])
    · exact .inr ⟨c, member, .inr (by simp [Print.componentDeclaration, inside])⟩

private theorem element_none {e : Element} (free : Unannotated (Print.element e)) :
    ∀ c ∈ (match e with | .component c => c.declarations), c.description.annotation = none := by
  obtain ⟨c⟩ := e
  exact declarations_none fun inside => free (by simp [Print.element, Print.componentClause, inside])

private theorem equations_none {qs : List SomeEquation}
    (free : Unannotated (qs.flatMap fun q => Print.someEquation q ++ [.literal ";"])) :
    ∀ q ∈ qs, q.description.annotation = none := by
  intro q member
  apply description_none
  intro inside
  exact free (List.mem_flatMap.mpr ⟨q, member, by simp [Print.someEquation, inside]⟩)

private theorem map_self {α : Type} {f : α → α} : ∀ {l : List α}, (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.map_cons, h x (List.mem_cons_self ..), map_self fun y m => h y (List.mem_cons_of_mem _ m)]

/-- A tree without an `annotation` keyword has no annotation clause. -/
theorem erase_unannotated {d : StoredDefinition}
    (free : Unannotated (Print.storedDefinition d)) : erase d = d := by
  obtain ⟨classes⟩ := d
  simp only [erase, StoredDefinition.mk.injEq]
  apply map_self
  intro c member
  obtain ⟨prefixes, name, strings, ⟨elements, sections, annotation⟩, endName⟩ := c
  have inside : Unannotated (Print.composition ⟨elements, sections, annotation⟩) := fun h =>
    free (List.mem_flatMap.mpr ⟨_, member, by simp [Print.classDefinition, Print.classSpecifier, h]⟩)
  have noClass : annotation = none := by
    cases annotation with
    | none => rfl
    | some a => exact absurd (by simp [Print.composition, Print.classAnnotation, Print.annotationClause]) inside
  subst noClass
  simp only [ClassDefinition.erase, Composition.erase, ClassDefinition.mk.injEq,
    ClassSpecifier.long.injEq, Composition.mk.injEq, true_and, and_true]
  constructor
  · apply map_self
    intro e found
    obtain ⟨c⟩ := e
    have none' := element_none (e := .component c) fun h =>
      inside (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨_, found, List.mem_append_left _ h⟩)))
    simp only [Element.erase, Element.component.injEq]
    obtain ⟨p, n, s, ds⟩ := c
    simp only [ComponentClause.mk.injEq, true_and]
    apply map_self
    intro cd found'
    obtain ⟨declaration, condition, ⟨strings', annotation'⟩⟩ := cd
    have := none' _ found'
    simp only at this
    subst this
    rfl
  · apply map_self
    intro s found
    obtain ⟨qs⟩ := s
    have none' := equations_none (qs := qs) fun h =>
      inside (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, found, List.mem_cons_of_mem _ h⟩)))
    simp only [EquationSection.erase, EquationSection.mk.injEq]
    apply map_self
    intro q found'
    obtain ⟨equation, ⟨strings', annotation'⟩⟩ := q
    have := none' _ found'
    simp only at this
    subst this
    rfl

/-! ### Screening an erased tree -/

private theorem declarations_erase (pos : Nat) (cs : List ComponentDeclaration) :
    declarations pos (cs.map ComponentDeclaration.erase) = .ok () := by
  induction cs generalizing pos with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, declarations, ComponentDeclaration.erase, description,
      Description.erase, clause, ih, bind, Except.bind]

private theorem elements_erase (pos : Nat) (es : List Element) :
    elements pos (es.map Element.erase) = .ok () := by
  induction es generalizing pos with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨c⟩ := e
    simp only [List.map_cons, elements, Element.erase, element, declarations_erase, ih, bind,
      Except.bind]

private theorem equations_erase (pos : Nat) (qs : List SomeEquation) :
    equations pos (qs.map SomeEquation.erase) = .ok () := by
  induction qs generalizing pos with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.map_cons, equations, SomeEquation.erase, description, Description.erase,
      clause, ih, bind, Except.bind]

private theorem sections_erase (pos : Nat) (ss : List EquationSection) :
    sections pos (ss.map EquationSection.erase) = .ok () := by
  induction ss generalizing pos with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, sections, EquationSection.erase, equations_erase, ih, bind,
      Except.bind]

private theorem classes_erase (pos : Nat) (cs : List ClassDefinition) :
    classes pos (cs.map ClassDefinition.erase) = .ok () := by
  induction cs generalizing pos with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨prefixes, name, strings, body, endName⟩ := c
    simp only [List.map_cons, classes, ClassDefinition.erase, composition, Composition.erase,
      elements_erase, sections_erase, clause, ih, bind, Except.bind]

/-- An erased tree has no annotation to reject. -/
theorem screen_erase (d : StoredDefinition) : screen (erase d) = .ok () := classes_erase 0 d.classes

/-- Screening accepts a tree without an `annotation` keyword. -/
theorem screen_unannotated {d : StoredDefinition} (free : Unannotated (Print.storedDefinition d)) :
    screen d = .ok () := by
  rw [← erase_unannotated free]
  exact screen_erase d

end Rumoca.Modelica.Annotation
