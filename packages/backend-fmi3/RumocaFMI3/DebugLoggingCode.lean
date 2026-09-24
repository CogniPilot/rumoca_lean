import RumocaC.LoopCode
import RumocaC.CountConditionCode

/-! FMI logging-category validation. String comparison has an explicit local
destination, and all declarations have function scope. The instance and
lifecycle prefix remains owned by the shared FMI runtime. -/
namespace Rumoca.FMI3.DebugLogging
open CTree

def failure (message : String) : Stmt :=
  .ret (some (.call (.id "fail") [.id "m", .str message]))

def missingWithConditions (countActive pointerMissing : Expr → Expr) : Stmt :=
  .branch (.bin .and (countActive (.id "nCategories")) (pointerMissing (.id "categories")))
  [failure "Missing log categories"] []

/-- Retained pointer-parametric, raw-count view. -/
def missingWith (pointerMissing : Expr → Expr) : Stmt :=
  missingWithConditions id pointerMissing

def category : Expr := .index (.id "categories") (.id "k")
def rejectNullWith (pointerMissing : Expr → Expr) : Stmt := .branch (pointerMissing category) [failure "Unknown log category"] []
def comparison : Stmt :=
  .assign (.id "difference") (.call (.id "strcmp") [category, .str "logStatus"])
def rejectDifference : Stmt := .branch (.bin .ne (.id "difference") (.nat 0))
  [failure "Unknown log category"] []
def iterationWith (pointerMissing : Expr → Expr) : List Stmt :=
  [rejectNullWith pointerMissing, comparison, rejectDifference]
def validationWith (pointerMissing : Expr → Expr) : Stmt :=
  CLoops.loop "k" (.id "nCategories") (iterationWith pointerMissing)
def writeLogging : Stmt := .assign (.field (.id "m") "logging" true) (.id "loggingOn")
def finish : List Stmt := [writeLogging, .ret (some (.id "fmi3OK"))]
def codeWithConditions (countActive pointerMissing : Expr → Expr) : List Stmt :=
  [missingWithConditions countActive pointerMissing, .declare "int" "difference" (.nat 0),
   .declare "size_t" "k" (.nat 0), validationWith pointerMissing] ++ finish

/-- Retained proof specialization; not another runtime function/table. -/
def codeWith (pointerMissing : Expr → Expr) : List Stmt :=
  codeWithConditions id pointerMissing

/-- Retained logical proof views; no separate runtime function or table. -/
def logicalMissing : Stmt := missingWith .not
def logicalRejectNull : Stmt := rejectNullWith .not
def logicalIteration : List Stmt := iterationWith .not
def logicalValidation : Stmt := validationWith .not
def logicalCode : List Stmt := codeWith .not

/-- Actual guards share one explicit-null predicate. -/
def explicitMissing (pointer : Expr) : Expr := .bin .eq pointer Expr.nullPointer
/-- Definitionally the preceding actual syntax, for helpers without size typing. -/
def rawCountMissing : Stmt := missingWith explicitMissing
def rawCountCode : List Stmt := codeWith explicitMissing
def missing : Stmt := missingWithConditions CCountConditions.nonzero explicitMissing
def rejectNull : Stmt := rejectNullWith explicitMissing
def iteration : List Stmt := iterationWith explicitMissing
def validation : Stmt := validationWith explicitMissing
def code : List Stmt := codeWithConditions CCountConditions.nonzero explicitMissing

end Rumoca.FMI3.DebugLogging
