/-! Lexical feature inventory of emitted C text.

The inventory scans the characters of a C source file once, left to right, and
records outside comments, string literals and character constants: how often each
watched word occurs (every C keyword that introduces a statement, selection or
declaration kind, and every identifier of the `<stdlib.h>` allocation and
`<stdarg.h>` variadic interfaces), how often each punctuator occurs (longest
match over the C punctuator list), and the text of every preprocessing
directive line. It is a checker, not a C front end: it assigns no meaning to the
tokens it counts.

Two decidable predicates over an inventory state what the generated C must not
contain. `allocationFree` holds when no allocation identifier occurs and no
directive names `stdlib.h` (MISRA C:2025 Directive 4.12 and Rule 21.3).
`featureFree` holds when no jump, `switch`, `for` or `do` statement, union,
enumeration, type-generic selection, non-returning specifier, variadic argument
access, shift, bitwise, remainder, conditional, increment, decrement or compound
assignment operator, and no ellipsis occurs. The artifact checkers compute the
inventory of the actual bytes of every emitted C file and check both predicates in
the kernel (`certify`). -/
namespace Rumoca.CFeatures

/-- The counted words and punctuators with their occurrence counts, in order of
first occurrence, and the directive lines in file order. -/
structure Inventory where
  words : List (String × Nat)
  punctuators : List (String × Nat)
  directives : List String
  deriving DecidableEq, Repr, Inhabited

def bump (key : String) : List (String × Nat) → List (String × Nat)
  | [] => [(key, 1)]
  | (k, n) :: rest => if k = key then (k, n + 1) :: rest else (k, n) :: bump key rest

/-- Identifiers of the `<stdlib.h>` memory-management interface. -/
def allocationWords : List String := ["malloc", "calloc", "realloc", "free", "aligned_alloc"]

/-- Words whose occurrence marks a feature the generated C does not use. -/
def forbiddenWords : List String :=
  ["goto", "switch", "case", "default", "for", "do", "break", "continue", "union", "enum",
   "_Generic", "_Noreturn", "register", "va_start", "va_arg", "va_end", "va_copy", "va_list"] ++
    allocationWords

/-- The counted words: the forbidden words and the statement, declaration and
qualifier keywords the generated C uses. -/
def watched : List String :=
  forbiddenWords ++ ["if", "else", "while", "return", "struct", "typedef", "extern", "static",
    "volatile", "const", "sizeof", "_Atomic", "_Thread_local", "restrict", "inline"]

/-- Every C punctuator (C11 6.4.6) except the digraphs, which the generated C
does not spell. -/
def punctuatorList : List String :=
  ["...", "<<=", ">>=", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||",
   "*=", "/=", "%=", "+=", "-=", "&=", "^=", "|=", "##",
   "[", "]", "(", ")", "{", "}", ".", "&", "*", "+", "-", "~", "!", "/", "%", "<", ">", "^", "|",
   "?", ":", ";", "=", ",", "#"]

/-- Punctuators of the shift, bitwise, remainder, conditional, increment,
decrement and compound-assignment operators, the ellipsis and token pasting. -/
def forbiddenPunctuators : List String :=
  ["<<", ">>", "<<=", ">>=", "|", "^", "~", "|=", "&=", "^=", "%", "%=", "?", ":", "++", "--",
   "*=", "/=", "+=", "-=", "...", "##"]

inductive Mode where
  | code | word | number | punct | string | stringEscape | character | characterEscape
  | lineComment | blockComment | blockStar | directive
  deriving DecidableEq, Repr, Inhabited

/-- The scanner state after a prefix of the text: the lexical mode, the reversed
characters of the pending word, punctuator or directive, whether only
whitespace precedes on the current line, and the inventory so far. -/
structure State where
  mode : Mode
  buffer : List Char
  lineStart : Bool
  inventory : Inventory
  deriving DecidableEq, Repr, Inhabited

def identStart (c : Char) : Bool := c.isAlpha || c = '_'
def identRest (c : Char) : Bool := c.isAlphanum || c = '_'

def punctuatorPrefix (p : List Char) : Bool := punctuatorList.any fun s => p.isPrefixOf s.toList

def emitWord (s : State) : Inventory :=
  let w := String.ofList s.buffer.reverse
  if watched.contains w then { s.inventory with words := bump w s.inventory.words } else s.inventory

def emitPunctuator (s : State) : Inventory :=
  { s.inventory with punctuators := bump (String.ofList s.buffer.reverse) s.inventory.punctuators }

def emitDirective (s : State) : Inventory :=
  { s.inventory with directives := s.inventory.directives ++ [String.ofList s.buffer.reverse] }

/-- Begin the lexical item that starts with `c` in code context. -/
def start (inventory : Inventory) (lineStart : Bool) (c : Char) : State :=
  if c = '\n' then ⟨.code, [], true, inventory⟩
  else if c = ' ' || c = '\t' || c = '\r' then ⟨.code, [], lineStart, inventory⟩
  else if c = '#' && lineStart then ⟨.directive, [], false, inventory⟩
  else if identStart c then ⟨.word, [c], false, inventory⟩
  else if c.isDigit then ⟨.number, [], false, inventory⟩
  else if c = '"' then ⟨.string, [], false, inventory⟩
  else if c = '\'' then ⟨.character, [], false, inventory⟩
  else ⟨.punct, [c], false, inventory⟩

/-- Consume one character. -/
def step (s : State) (c : Char) : State :=
  match s.mode with
  | .code => start s.inventory s.lineStart c
  | .word => if identRest c then { s with buffer := c :: s.buffer } else start (emitWord s) false c
  | .number => if identRest c || c = '.' then s else start s.inventory false c
  | .punct =>
    if s.buffer = ['/'] && c = '*' then ⟨.blockComment, [], false, s.inventory⟩
    else if s.buffer = ['/'] && c = '/' then ⟨.lineComment, [], false, s.inventory⟩
    else if punctuatorPrefix (s.buffer.reverse ++ [c]) then { s with buffer := c :: s.buffer }
    else start (emitPunctuator s) false c
  | .string =>
    if c = '\\' then { s with mode := .stringEscape }
    else if c = '"' then { s with mode := .code } else s
  | .stringEscape => { s with mode := .string }
  | .character =>
    if c = '\\' then { s with mode := .characterEscape }
    else if c = '\'' then { s with mode := .code } else s
  | .characterEscape => { s with mode := .character }
  | .lineComment => if c = '\n' then ⟨.code, [], true, s.inventory⟩ else s
  | .blockComment => if c = '*' then { s with mode := .blockStar } else s
  | .blockStar =>
    if c = '/' then { s with mode := .code }
    else if c = '*' then s else { s with mode := .blockComment }
  | .directive =>
    if c = '\n' then ⟨.code, [], true, emitDirective s⟩ else { s with buffer := c :: s.buffer }

/-- Close a pending item at the end of the text. -/
def finish (s : State) : Inventory :=
  match s.mode with
  | .word => emitWord s
  | .punct => emitPunctuator s
  | .directive => emitDirective s
  | _ => s.inventory

def initial : State := ⟨.code, [], true, ⟨[], [], []⟩⟩

/-- The inventory of a complete C source file. -/
def inventory (text : List Char) : Inventory := finish (text.foldl step initial)

def containsText (text part : List Char) : Bool :=
  match text with
  | [] => part.isEmpty
  | c :: rest => part.isPrefixOf (c :: rest) || containsText rest part

/-- No allocation identifier and no `<stdlib.h>` directive. -/
def allocationFree (inventory : Inventory) : Bool :=
  inventory.words.all (fun entry => !allocationWords.contains entry.1) &&
    inventory.directives.all (fun directive => !containsText directive.toList "stdlib.h".toList)

/-- No forbidden word and no forbidden punctuator. -/
def featureFree (inventory : Inventory) : Bool :=
  inventory.words.all (fun entry => !forbiddenWords.contains entry.1) &&
    inventory.punctuators.all (fun entry => !forbiddenPunctuators.contains entry.1)

/-- Scanning a text in consecutive blocks composes: the state after a block is
the state the rest of the text starts from. -/
theorem foldl_block (block rest : List Char) (s t : State) (h : block.foldl step s = t) :
    (block ++ rest).foldl step s = rest.foldl step t := by
  rw [List.foldl_append, h]

/-- An allocation-free inventory contains no allocation word. -/
theorem allocationFree_words {inventory : Inventory} (free : allocationFree inventory = true)
    (word : String) (allocation : word ∈ allocationWords) (count : Nat) :
    (word, count) ∉ inventory.words := by
  intro member
  simp only [allocationFree, Bool.and_eq_true, List.all_eq_true] at free
  have := free.1 _ member
  simp [allocation] at this

/-- A feature-free inventory contains no forbidden punctuator. -/
theorem featureFree_punctuators {inventory : Inventory} (free : featureFree inventory = true)
    (punctuator : String) (forbidden : punctuator ∈ forbiddenPunctuators) (count : Nat) :
    (punctuator, count) ∉ inventory.punctuators := by
  intro member
  simp only [featureFree, Bool.and_eq_true, List.all_eq_true] at free
  have := free.2 _ member
  simp [forbidden] at this

/-- A feature-free inventory contains no forbidden word. -/
theorem featureFree_words {inventory : Inventory} (free : featureFree inventory = true)
    (word : String) (forbidden : word ∈ forbiddenWords) (count : Nat) :
    (word, count) ∉ inventory.words := by
  intro member
  simp only [featureFree, Bool.and_eq_true, List.all_eq_true] at free
  have := free.1 _ member
  simp [forbidden] at this

end Rumoca.CFeatures
