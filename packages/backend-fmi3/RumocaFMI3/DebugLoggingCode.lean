import RumocaC.LoopCode

/-! FMI logging-category validation. String comparison has an explicit local
destination, and all declarations have function scope. The instance and
lifecycle prefix remains owned by the shared FMI runtime. -/
namespace Rumoca.FMI3.DebugLogging
open CTree

def failure (message : String) : Stmt :=
  .ret (some (.call (.id "fail") [.id "m", .str message]))

def missing : Stmt := .branch (.bin .and (.id "nCategories") (.not (.id "categories")))
  [failure "Missing log categories"] []

def category : Expr := .index (.id "categories") (.id "k")
def rejectNull : Stmt := .branch (.not category) [failure "Unknown log category"] []
def comparison : Stmt :=
  .assign (.id "difference") (.call (.id "strcmp") [category, .str "logStatus"])
def rejectDifference : Stmt := .branch (.bin .ne (.id "difference") (.nat 0))
  [failure "Unknown log category"] []
def iteration : List Stmt := [rejectNull, comparison, rejectDifference]
def validation : Stmt := CLoops.loop "k" (.id "nCategories") iteration
def writeLogging : Stmt := .assign (.field (.id "m") "logging" true) (.id "loggingOn")
def finish : List Stmt := [writeLogging, .ret (some (.id "fmi3OK"))]
def code : List Stmt := [missing, .declare "int" "difference" (.nat 0),
  .declare "size_t" "k" (.nat 0), validation] ++ finish

end Rumoca.FMI3.DebugLogging
