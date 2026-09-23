import Parser.LALR.EBNFActions
import Parser.LALR.ActionCertificate

/-! Universal recursive and nullable action instantiations. These are proofs for
arbitrary depths, not a finite collection of successful parser examples. -/
namespace Parser.LALR.Frontend.StructuralActions.RecursiveFixture

inductive Token where
  | ident (spelling : String)
  | leftParen
  | rightParen

def classify : Token → Parser.Symbol
  | .ident _ => .ident
  | .leftParen => .literal "("
  | .rightParen => .literal ")"

/-- Distinct rule result types exercise genuinely typed cross-rule delegation. -/
def Result : String → Type
  | "expr" => Nat
  | "atom" => Token
  | _ => Unit

def exprAction : Action Token Result Nat :=
  .alt (.map (fun _ => 0) (.ref "atom"))
    (.map (fun value => value.2.1 + 1)
      (.seq (.terminal (.literal "(")) (.seq (.ref "expr") (.terminal (.literal ")")))))

def rules : Rules Token Result
  | "expr" => some exprAction
  | "atom" => some (.terminal .ident)
  | _ => none

/-- Source grammar is authored independently of the action erasure. -/
def source : EBNF.Grammar :=
  [("expr", .alt (.ref "atom")
    (.seq (.terminal (.literal "(")) (.seq (.ref "expr") (.terminal (.literal ")"))))),
   ("atom", .terminal .ident)]

theorem covered : Covers source rules := by
  intro name e member
  simp only [source, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨exprAction, rfl, rfl, by simp [exprAction, Action.WellFormed]⟩
  · exact ⟨.terminal .ident, rfl, rfl, by simp [Action.WellFormed]⟩

theorem licensed : Licensed source rules := by
  intro name a found
  unfold rules at found
  split at found
  · cases Option.some.inj found
    simp [source, exprAction, Action.expr, Action.WellFormed]
  · cases Option.some.inj found
    simp [source, Action.expr, Action.WellFormed]
  · contradiction

def tree : Nat → String → Structure.Value Token
  | 0, spelling => .named "expr" (.altLeft
      (.seq (.terminal (.literal "(")) (.seq (.ref "expr") (.terminal (.literal ")"))))
      (.named "atom" (.terminal .ident (.ident spelling))))
  | n + 1, spelling => .named "expr" (.altRight (.ref "atom")
      (.seq (.terminal (.literal "(") .leftParen)
        (.seq (tree n spelling) (.terminal (.literal ")") .rightParen))))

theorem meaning (n : Nat) (spelling : String) :
    Denotes rules classify (.ref "expr") (tree n spelling) n := by
  induction n with
  | zero =>
    action_certificate
  | succ n ih =>
    exact .ref rfl (.altRight (.map (f := fun value : Token × Nat × Token => value.2.1 + 1)
      (.seq (.terminal (payload := Token.leftParen) rfl)
        (.seq ih (.terminal (payload := Token.rightParen) rfl)))))

theorem arbitrary_depth (n : Nat) (spelling : String) :
    run rules classify (.ref "expr") (tree n spelling) = some n :=
  denotes_run (meaning n spelling)

theorem source_valid (n : Nat) (spelling : String) :
    Structure.Valid source classify (tree n spelling) :=
  denotes_valid licensed (meaning n spelling) trivial

def nullableTree : Nat → Structure.Value Token
  | 0 => .manyEmpty (.terminal (.literal ""))
  | n + 1 => .manyCons .empty (nullableTree n)

theorem nullable_meaning (n : Nat) :
    Denotes rules classify (.many .empty) (nullableTree n) (List.replicate n ()) := by
  induction n with
  | zero => exact .manyEmpty
  | succ n ih => exact .manyCons .empty ih

theorem nullable_depth (n : Nat) :
    run rules classify (.many .empty) (nullableTree n) = some (List.replicate n ()) :=
  denotes_run (nullable_meaning n)

end Parser.LALR.Frontend.StructuralActions.RecursiveFixture
