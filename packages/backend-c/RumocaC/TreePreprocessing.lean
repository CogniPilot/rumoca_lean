import RumocaC.StringLiteral
import Init.Data.Nat.ToString

/-! Reusable preservation of printed characters through C11 trigraph
replacement and line splicing (N1570 5.1.1.2 and 5.2.1.1). These properties do
not establish source encoding, tokenization, typing, macro expansion, header
meanings or execution. -/
namespace Rumoca.CTree.Preprocessing

/-- Reject a physical newline immediately following a backslash. -/
def unspliced : Bool → List Char → Bool
  | _, [] => true
  | previous, c :: cs => !(previous && c == '\n') && unspliced (c == '\\') cs

def endSlash (text : List Char) (previous : Bool) : Bool :=
  text.foldl (fun _ c => c == '\\') previous

theorem unspliced_append (left right : List Char) (previous : Bool) :
    unspliced previous (left ++ right) =
      (unspliced previous left && unspliced (endSlash left previous) right) := by
  induction left generalizing previous with
  | nil => simp [unspliced, endSlash]
  | cons c cs ih => simp [unspliced, endSlash, ih, Bool.and_assoc]

/-- A fragment without character rewrites, ending at a boundary that cannot
start a trigraph or line splice with the next fragment. Empty fragments qualify. -/
structure Stable (text : List Char) : Prop where
  questions : CString.safeFrom false text = true
  endQuestion : CString.endMark text false = false
  splices : unspliced false text = true
  endBackslash : endSlash text false = false

theorem Stable.append (left : Stable a) (right : Stable b) : Stable (a ++ b) := by
  rcases left with ⟨lq, leq, ls, les⟩
  rcases right with ⟨rq, req, rs, res⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [CString.safe_append, lq, leq, rq]
  · simp only [CString.endMark] at leq req ⊢
    simp [List.foldl_append, leq, req]
  · simp [unspliced_append, ls, les, rs]
  · simp only [endSlash] at les res ⊢
    simp [List.foldl_append, les, res]

/-- Raw printer fragments contain no question marks or backslashes. Quoted
string payloads use the existing certified UTF-8 byte escaping instead. -/
def Plain (text : List Char) : Prop := ∀ c ∈ text, c ≠ '?' ∧ c ≠ '\\'

instance (text : List Char) : Decidable (Plain text) :=
  inferInstanceAs (Decidable (∀ c ∈ text, c ≠ '?' ∧ c ≠ '\\'))

theorem plain_stable (plain : Plain text) : Stable text := by
  induction text with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons c cs ih =>
      have first := plain c (by simp)
      have nq : (c == '?') = false := beq_eq_false_iff_ne.mpr first.1
      have ns : (c == '\\') = false := beq_eq_false_iff_ne.mpr first.2
      obtain ⟨sq, eq, ss, es⟩ := ih (fun d hd => plain d (by simp [hd]))
      exact ⟨by simp [CString.safeFrom, nq, sq],
        by simpa [CString.endMark, nq] using eq,
        by simp [unspliced, ns, ss],
        by simpa [endSlash, ns] using es⟩

theorem ascii_unspliced (ascii : CString.printableASCII text = true) (previous : Bool) :
    unspliced previous text = true := by
  induction text generalizing previous with
  | nil => rfl
  | cons c cs ih =>
      simp only [CString.printableASCII, List.all_cons, Bool.and_eq_true] at ascii
      have notNewline : c ≠ '\n' := by
        intro same
        subst c
        simp at ascii
      simp [unspliced, notNewline, ih ascii.2]

theorem quote_stable (s : String) : Stable (quote s).toList := by
  refine ⟨CString.quote_safe s, ?_, ascii_unspliced (CString.quote_ascii s) false, ?_⟩
  · simp [quote, String.toList_append, CString.endMark, List.foldl_append]
  · simp [quote, String.toList_append, endSlash, List.foldl_append]

theorem Stable.no_rewrite (stable : Stable text) : ¬ CString.Rewrite text out := by
  intro step
  cases step with
  | trigraph before after c replacement found =>
      have safe := stable.questions
      simp [CString.safe_append, CString.safeFrom] at safe
  | splice before after =>
      have safe := stable.splices
      simp [unspliced_append, unspliced] at safe

theorem Stable.preprocessed (stable : Stable text)
    (steps : Relation.ReflTransGen CString.Rewrite text out) : out = text := by
  induction steps with
  | refl => rfl
  | tail path step ih =>
      rw [ih] at step
      exact False.elim (stable.no_rewrite step)

theorem Stable.join (strings : List String) (valid : ∀ s ∈ strings, Stable s.toList) :
    Stable (String.join strings).toList := by
  rw [CString.join_toList]
  induction strings with
  | nil => exact plain_stable (by simp [Plain])
  | cons s ss ih =>
      exact (valid s (by simp)).append (ih (fun t ht => valid t (by simp [ht])))

theorem Stable.intercalate (separator : String) (sep : Stable separator.toList)
    (strings : List String) (valid : ∀ s ∈ strings, Stable s.toList) :
    Stable (String.intercalate separator strings).toList := by
  have go (strings : List String) : ∀ acc : String, Stable acc.toList →
      (∀ s ∈ strings, Stable s.toList) →
      Stable (String.intercalate separator (acc :: strings)).toList := by
    induction strings with
    | nil => intro acc h _; exact h
    | cons s ss ih =>
        intro acc ha all
        apply ih (acc ++ separator ++ s)
        · simpa only [String.toList_append] using (ha.append sep).append (all s (by simp))
        · exact fun t ht => all t (by simp [ht])
  cases strings with
  | nil => change Stable ([] : List Char); exact plain_stable (by simp [Plain])
  | cons s ss => exact go ss s (valid s (by simp)) (fun t ht => valid t (by simp [ht]))

theorem natural_stable (n : Nat) : Stable (toString n).toList := by
  apply plain_stable
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  intro c member
  have digit := Nat.isDigit_of_mem_toDigits (by decide +kernel) (by decide +kernel) member
  constructor <;> intro same <;> subst c <;> simp at digit

theorem binOp_stable (op : BinOp) : Stable op.render.toList := by
  cases op <;> exact plain_stable (by simp [BinOp.render, Plain])

/-- This checks only the raw names and type spellings that bypass quoting.
It is deliberately weaker than C lexical, name-resolution or typing validity. -/
def ExprInputs : Expr → Prop
  | .id name | .sizeof name => Plain name.toList
  | .nat _ | .str _ => True
  | .bin _ a b | .index a b => ExprInputs a ∧ ExprInputs b
  | .not a | .deref a | .address a => ExprInputs a
  | .field a name _ | .cast name a => ExprInputs a ∧ Plain name.toList
  | .call fn args => ExprInputs fn ∧ ∀ arg ∈ args, ExprInputs arg

macro "c_preprocessing_parts" : tactic => `(tactic|
  (simp only [String.toList_append]
   repeat first
   | assumption
   | apply Stable.append
   | exact plain_stable (by simp [Plain])))

theorem expression_stable (expr : Expr) (valid : ExprInputs expr) :
    Stable expr.render.toList := by
  induction expr using Expr.rec (motive_2 := fun args =>
      ∀ arg ∈ args, ExprInputs arg → Stable arg.render.toList) with
  | id name => simpa only [Expr.render] using plain_stable (by simpa only [ExprInputs] using valid)
  | nat n => simpa only [Expr.render] using natural_stable n
  | str s => simpa only [Expr.render] using quote_stable s
  | bin op a b ha hb =>
      simp only [ExprInputs] at valid
      have left := ha valid.1
      have right := hb valid.2
      have operator := binOp_stable op
      simp only [Expr.render]
      c_preprocessing_parts
  | index a b ha hb =>
      simp only [ExprInputs] at valid
      have left := ha valid.1
      have right := hb valid.2
      simp only [Expr.render]
      c_preprocessing_parts
  | not a ha | deref a ha | address a ha =>
      simp only [ExprInputs] at valid
      have inner := ha valid
      simp only [Expr.render]
      c_preprocessing_parts
  | field a name pointer ha =>
      simp only [ExprInputs] at valid
      have inner := ha valid.1
      have member := plain_stable valid.2
      cases pointer <;> simp only [Expr.render, Bool.false_eq_true, ↓reduceIte] <;> c_preprocessing_parts
  | cast name a ha =>
      simp only [ExprInputs] at valid
      have inner := ha valid.1
      have typeName := plain_stable valid.2
      simp only [Expr.render]
      c_preprocessing_parts
  | sizeof name =>
      simp only [ExprInputs] at valid
      have typeName := plain_stable valid
      simp only [Expr.render]
      c_preprocessing_parts
  | call fn args hf ha =>
      simp only [ExprInputs] at valid
      have callee := hf valid.1
      have arguments := Stable.intercalate ", " (plain_stable (by simp [Plain]))
        (args.map Expr.render) (by
          intro text member
          obtain ⟨arg, occurs, rfl⟩ := List.mem_map.mp member
          exact ha arg occurs (valid.2 arg occurs))
      simp only [Expr.render]
      c_preprocessing_parts
  | nil => rename_i e member _; cases member
  | cons arg args he ha =>
      rename_i e member good
      rcases List.mem_cons.mp member with rfl | member
      · exact he good
      · exact ha e member good

theorem expression_preprocessed (expr : Expr) (valid : ExprInputs expr)
    (steps : Relation.ReflTransGen CString.Rewrite expr.render.toList out) :
    out = expr.render.toList :=
  (expression_stable expr valid).preprocessed steps

def StmtInputs : Stmt → Prop
  | .declare type name value => Plain type.toList ∧ Plain name.toList ∧ ExprInputs value
  | .assign target value => ExprInputs target ∧ ExprInputs value
  | .eval value | .ret (some value) => ExprInputs value
  | .ret none => True
  | .branch condition yes no => ExprInputs condition ∧
      (∀ stmt ∈ yes, StmtInputs stmt) ∧ ∀ stmt ∈ no, StmtInputs stmt
  | .whileLoop condition body => ExprInputs condition ∧ ∀ stmt ∈ body, StmtInputs stmt

theorem indent_stable (depth : Nat) :
    Stable (String.ofList (List.replicate (2 * depth) ' ')).toList := by
  apply plain_stable
  simp [Plain]

set_option maxHeartbeats 800000 in
theorem statement_stable (stmt : Stmt) (depth : Nat) (valid : StmtInputs stmt) :
    Stable (stmt.render depth).toList := by
  induction stmt using Stmt.rec (motive_2 := fun code =>
      ∀ stmt ∈ code, ∀ depth, StmtInputs stmt → Stable (stmt.render depth).toList)
      generalizing depth with
  | declare type name value =>
      simp only [StmtInputs] at valid
      have indentation := indent_stable depth
      have typeName := plain_stable valid.1
      have declared := plain_stable valid.2.1
      have expression := expression_stable value valid.2.2
      simp only [Stmt.render]
      c_preprocessing_parts
  | assign target value =>
      simp only [StmtInputs] at valid
      have indentation := indent_stable depth
      have left := expression_stable target valid.1
      have right := expression_stable value valid.2
      simp only [Stmt.render]
      c_preprocessing_parts
  | eval value =>
      have indentation := indent_stable depth
      have expression := expression_stable value (by simpa only [StmtInputs] using valid)
      simp only [Stmt.render]
      c_preprocessing_parts
  | ret value =>
      have indentation := indent_stable depth
      cases value with
      | none => simp only [Stmt.render]; c_preprocessing_parts
      | some value =>
          have expression := expression_stable value (by simpa only [StmtInputs] using valid)
          simp only [Stmt.render]
          c_preprocessing_parts
  | branch condition yes no hy hn =>
      simp only [StmtInputs] at valid
      have indentation := indent_stable depth
      have expression := expression_stable condition valid.1
      have whenTrue := Stable.join (yes.map (fun s => s.render (depth + 1))) (by
        intro text member
        obtain ⟨s, occurs, rfl⟩ := List.mem_map.mp member
        exact hy s occurs (depth + 1) (valid.2.1 s occurs))
      have whenFalse := Stable.join (no.map (fun s => s.render (depth + 1))) (by
        intro text member
        obtain ⟨s, occurs, rfl⟩ := List.mem_map.mp member
        exact hn s occurs (depth + 1) (valid.2.2 s occurs))
      simp only [Stmt.render]
      split <;> c_preprocessing_parts
  | whileLoop condition body hb =>
      simp only [StmtInputs] at valid
      have indentation := indent_stable depth
      have expression := expression_stable condition valid.1
      have contents := Stable.join (body.map (fun s => s.render (depth + 1))) (by
        intro text member
        obtain ⟨s, occurs, rfl⟩ := List.mem_map.mp member
        exact hb s occurs (depth + 1) (valid.2 s occurs))
      simp only [Stmt.render]
      c_preprocessing_parts
  | nil => rename_i s member _ _; cases member
  | cons stmt code hs hc =>
      rename_i s member depth good
      rcases List.mem_cons.mp member with rfl | member
      · exact hs depth good
      · exact hc s member depth good

def ParameterInputs (p : Parameter) : Prop := Plain p.type.toList ∧ Plain p.name.toList

instance (p : Parameter) : Decidable (ParameterInputs p) :=
  inferInstanceAs (Decidable (Plain p.type.toList ∧ Plain p.name.toList))

theorem parameter_stable (p : Parameter) (valid : ParameterInputs p) :
    Stable p.render.toList := by
  have typeName := plain_stable valid.1
  have name := plain_stable valid.2
  simp only [Parameter.render]
  split <;> c_preprocessing_parts

def SignatureInputs (s : Signature) : Prop :=
  Plain s.result.toList ∧ Plain s.name.toList ∧ ∀ p ∈ s.parameters, ParameterInputs p

instance (s : Signature) : Decidable (SignatureInputs s) :=
  inferInstanceAs (Decidable
    (Plain s.result.toList ∧ Plain s.name.toList ∧ ∀ p ∈ s.parameters, ParameterInputs p))

theorem signature_stable (s : Signature) (valid : SignatureInputs s) :
    Stable s.render.toList := by
  have result := plain_stable valid.1
  have name := plain_stable valid.2.1
  have parameters := Stable.intercalate ", " (plain_stable (by simp [Plain]))
    (s.parameters.map Parameter.render) (by
      intro text member
      obtain ⟨p, occurs, rfl⟩ := List.mem_map.mp member
      exact parameter_stable p (valid.2.2 p occurs))
  simp only [Signature.render]
  split <;> c_preprocessing_parts

def FunctionInputs (fn : Function) : Prop :=
  SignatureInputs fn.signature ∧ ∀ stmt ∈ fn.body, StmtInputs stmt

theorem function_stable (fn : Function) (valid : FunctionInputs fn) :
    Stable fn.render.toList := by
  have signature := signature_stable fn.signature valid.1
  have body := Stable.join (fn.body.map (fun stmt => stmt.render 1)) (by
    intro text member
    obtain ⟨stmt, occurs, rfl⟩ := List.mem_map.mp member
    exact statement_stable stmt 1 (valid.2 stmt occurs))
  simp only [Function.render]
  split <;> c_preprocessing_parts

/-- Every CTree constructor is covered, for arbitrary nested expressions,
statements and function bodies. This composes character safety, not C syntax
or execution; the latter obligations are supplied separately. -/
theorem function_preprocessed (fn : Function) (valid : FunctionInputs fn)
    (steps : Relation.ReflTransGen CString.Rewrite fn.render.toList out) :
    out = fn.render.toList :=
  (function_stable fn valid).preprocessed steps

end Rumoca.CTree.Preprocessing
