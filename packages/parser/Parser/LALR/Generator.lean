import Parser.LALR.Item
import Parser.LALR.First
import Parser.LALR.Fuel

/-! Candidate LALR(1) construction in Lean: nullable/FIRST fixed point,
canonical LR(1) closure and goto, then union of lookaheads for identical LR(0)
kernels. Conflicts are errors, with no implicit precedence or shift preference.
This is preprocessing, not the trusted language contract. The runtime remains
separate, and production use awaits the complete table validator. -/
namespace Parser.LALR

structure Limits where
  states : Nat := 4096
  items : Nat := 65536
  deriving Repr

private def itemLE (a b : Item) : Bool :=
  a.production < b.production || (a.production == b.production &&
    (a.dot < b.dot || (a.dot == b.dot && a.lookahead ≤ b.lookahead)))

private def normalize (items : ItemSet) : ItemSet :=
  (items.mergeSort itemLE).eraseDups

def firstPass (g : Grammar) (facts : Array First) : Array First :=
  g.productions.foldl (fun acc p =>
    let f := firstSequence facts p.output
    let old := acc[p.input]?.getD {}
    acc.setIfInBounds p.input ⟨old.nullable || f.nullable, mergeTerminals old.terminals f.terminals⟩) facts

private def firstLoop (g : Grammar) : Nat → Array First → Except String (Array First)
  | 0, _ => .error "nullable/FIRST fixed point exhausted its bound"
  | fuel + 1, facts =>
    let next := firstPass g facts
    if next == facts then .ok facts else firstLoop g fuel next

def firstSets (g : Grammar) : Except String (Array First) :=
  firstLoop g (g.nonterminals * (g.terminals + 1) + 1) (Array.replicate g.nonterminals {})

def closurePass (g : Grammar) (facts : Array First) (items : ItemSet) : ItemSet := Id.run do
  let mut result := items
  for item in items do
    if let some (.nonterminal n) := nextSymbol g item then
      let some p := g.productions[item.production]? | continue
      let lookaheads := LALR.lookaheads facts (p.output.drop (item.dot + 1)) item.lookahead
      for index in [:g.productions.size] do
        if (g.productions[index]?.map (·.input)) == some n then
          for lookahead in lookaheads do
            result := ⟨index, 0, lookahead⟩ :: result
  return normalize result

private def closureLoop (g : Grammar) (facts : Array First) (limit : Nat) :
    Nat → ItemSet → Except String ItemSet
  | 0, _ => .error "LR(1) closure exhausted its bound"
  | fuel + 1, items =>
    let next := closurePass g facts items
    if next.length > limit then .error "LR(1) item limit exceeded"
    else if next == items then .ok items
    else closureLoop g facts limit fuel next

def closure (g : Grammar) (facts : Array First) (limit : Nat) (items : ItemSet) :
    Except String ItemSet :=
  closureLoop g facts limit (limit + 1) (normalize items)

def gotoItems (g : Grammar) (facts : Array First) (limit : Nat)
    (items : ItemSet) (symbol : Atom) : Except String ItemSet :=
  closure g facts limit (items.filterMap fun item =>
    if nextSymbol g item = some symbol then some { item with dot := item.dot + 1 } else none)

structure Collection where
  states : Array ItemSet
  edges : Array Edge
  deriving Repr, DecidableEq

private def collect (g : Grammar) (facts : Array First) (limits : Limits) :
    Nat → Nat → Collection → Except String Collection
  | 0, _, _ => .error "canonical LR(1) state limit exceeded"
  | fuel + 1, cursor, collection => do
    if cursor ≥ collection.states.size then return collection
    let items := collection.states[cursor]!
    let symbols := (items.filterMap (nextSymbol g)).eraseDups
    let mut result := collection
    for symbol in symbols do
      let target ← gotoItems g facts limits.items items symbol
      if !target.isEmpty then
        let index ← match result.states.findIdx? (· == target) with
          | some index => pure index
          | none => do
            if result.states.size ≥ limits.states then throw "canonical LR(1) state limit exceeded"
            pure result.states.size
        if index == result.states.size then result := { result with states := result.states.push target }
        result := { result with edges := result.edges.push ⟨cursor, symbol, index⟩ }
    collect g facts limits fuel (cursor + 1) result

def canonical (g : Grammar) (limits : Limits := {}) : Except String Collection := do
  if !g.wellFormed then throw "ill-formed context-free grammar"
  if limits.states == 0 then throw "canonical LR(1) state limit exceeded"
  let augmented := augment g
  let facts ← firstSets augmented
  let start ← closure augmented facts limits.items [⟨g.productions.size, 0, g.terminals⟩]
  collect augmented facts limits (limits.states + 1) 0 ⟨#[start], #[]⟩

/-- Kernels, not all closure items: FIRST can be empty for an unproductive
nonterminal, so erasing lookaheads from full closures is not the merge key. -/
def kernel (augmentedRule : Nat) (items : ItemSet) : List (Nat × Nat) :=
  ((items.filter fun i => i.dot > 0 || i.production == augmentedRule).map
    fun i => (i.production, i.dot)).eraseDups |>.mergeSort (fun a b =>
      a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))

def merge (augmentedRule : Nat) (collection : Collection) : Except String Collection := do
  let mut states : Array ItemSet := #[]
  let mut kernels : Array (List (Nat × Nat)) := #[]
  let mut mapping : Array Nat := #[]
  for items in collection.states do
    let key := kernel augmentedRule items
    match kernels.findIdx? (· == key) with
    | none =>
      mapping := mapping.push states.size
      kernels := kernels.push key
      states := states.push items
    | some index =>
      mapping := mapping.push index
      states := states.setIfInBounds index (normalize (states[index]! ++ items))
  let mut edges : Array Edge := #[]
  for edge in collection.edges do
    let some source := mapping[edge.source]? | throw "invalid canonical edge source"
    let some target := mapping[edge.target]? | throw "invalid canonical edge target"
    match edges.find? (fun e => e.source == source && decide (e.symbol = edge.symbol)) with
    | none => edges := edges.push ⟨source, edge.symbol, target⟩
    | some previous =>
      if previous.target != target then throw "inconsistent transition after LR(0) kernel merging"
  return ⟨states, edges⟩

private def putAction (tables : Tables) (state lookahead : Nat) (action : Action) :
    Except String Tables := do
  let some row := tables.actions[state]? | throw "action state out of range"
  let some entry := row[lookahead]? | throw "lookahead out of range"
  if let some previous := entry then
    if previous != action then
      throw s!"LALR conflict in state {state}, lookahead {lookahead}: {repr previous} versus {repr action}"
  return { tables with
    actions := tables.actions.setIfInBounds state (row.setIfInBounds lookahead (some action)) }

def buildTables (g : Grammar) (collection : Collection) : Except String Tables := do
  let mut tables : Tables := ⟨
    Array.replicate collection.states.size (Array.replicate (g.terminals + 1) none),
    Array.replicate collection.states.size (Array.replicate g.nonterminals none)⟩
  for edge in collection.edges do
    if edge.target ≥ collection.states.size then throw "transition target out of range"
    match edge.symbol with
    | .terminal t =>
      if t ≥ g.terminals then throw "cannot shift EOF or an unknown token"
      tables ← putAction tables edge.source t (.shift edge.target)
    | .nonterminal n =>
      let some row := tables.gotos[edge.source]? | throw "goto source out of range"
      let some entry := row[n]? | throw "goto nonterminal out of range"
      if let some previous := entry then
        if previous != edge.target then throw "conflicting goto transitions"
      tables := { tables with
        gotos := tables.gotos.setIfInBounds edge.source (row.setIfInBounds n (some edge.target)) }
  let augmented := augment g
  for state in [:collection.states.size] do
    for item in collection.states[state]! do
      let some p := augmented.productions[item.production]? | throw "invalid item production"
      if item.dot > p.output.length then throw "invalid item dot"
      if item.dot == p.output.length then
        if item.production == g.productions.size then
          if item.lookahead != g.terminals then throw "augmented acceptance without EOF"
          tables ← putAction tables state item.lookahead .accept
        else tables ← putAction tables state item.lookahead (.reduce item.production)
  return tables

structure Candidate where
  canonicalStates : Nat
  collection : Collection
  tables : Tables
  deriving Repr

def generate (g : Grammar) (limits : Limits := {}) : Except String Candidate := do
  let lr ← canonical g limits
  let lalr ← merge g.productions.size lr
  return ⟨lr.states.size, lalr, ← buildTables g lalr⟩

/-- Propose nonterminal credits for a linear valid-word fuel budget. The
bounded monotone search can fail; acceptance still requires `Fuel.validate`
and its independent kernel certificate. No language-specific cases occur. -/
def generateBudget (g : Grammar) (attempts : Nat := 20) : Except String Fuel.Budget := do
  if !g.wellFormed then throw "ill-formed grammar for fuel budget"
  let mut perToken := 1
  for _ in [:attempts] do
    let mut budget : Fuel.Budget := ⟨perToken, Array.replicate g.nonterminals 0⟩
    for _ in [:g.nonterminals + 1] do
      for p in g.productions do
        let required := (1 - (p.output.map budget.weight).sum).toNat
        let old := budget.nonterminals[p.input]?.getD 0
        budget := { budget with nonterminals :=
          budget.nonterminals.setIfInBounds p.input (max old required) }
      if Fuel.validate g budget then return budget
    perToken := perToken * 2
  throw "linear parsing budget search exhausted its bound"

end Parser.LALR
