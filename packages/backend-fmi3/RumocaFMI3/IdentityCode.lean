import RumocaC.Tree

/-! Private factory validation with explicit string-library calls. The caller
supplies the prepared expected token and the whitespace literal; no source
names or model policy are resolved in this helper. Null checks precede every
string access. Emission by the complete factory requires its composed proof. -/
namespace Rumoca.FMI3.Identity
open CTree

def falseReturn : Stmt := .ret (some (.cast "fmi3Boolean" (.nat 0)))

def nullCheck (name : String) : Stmt :=
  .branch (.bin .eq (.id name) .nullPointer) [falseReturn] []

def measure : Stmt := .assign (.id "length") (.call (.id "strlen") [.id "name"])
def measurePrefix : Stmt := .assign (.id "prefix") (.call (.id "strspn") [.id "name", .id "whitespace"])
def blank : Stmt := .branch (.bin .eq (.id "prefix") (.id "length")) [falseReturn] []
def compareToken : Stmt :=
  .assign (.id "difference") (.call (.id "strcmp") [.id "token", .id "expected"])
def comparisonReturn : Stmt :=
  .ret (some (.cast "fmi3Boolean" (.bin .eq (.id "difference") (.nat 0))))

def function : Function := {
  signature := ⟨"fmi3Boolean", "rumoca_valid_identity",
    [⟨"const char *", "name", false⟩, ⟨"const char *", "token", false⟩,
     ⟨"const char *", "expected", false⟩, ⟨"const char *", "whitespace", false⟩]⟩
  body := [
    .declare "size_t" "length" (.nat 0),
    .declare "size_t" "prefix" (.nat 0),
    .declare "int" "difference" (.nat 0),
    nullCheck "name", nullCheck "token", nullCheck "expected", nullCheck "whitespace",
    measure, measurePrefix, blank, compareToken, comparisonReturn]
  static := true
}

end Rumoca.FMI3.Identity
