import RumocaC.Identifier

namespace Rumoca.FMI3

/-- The current grammar admits unqualified ASCII model names. Distinct names
receive distinct source-link namespaces; repeated instances share one namespace. -/
def modelIdentifier (modelName : String) : String := "Rumoca_" ++ modelName

/-- FMI 3.0.2 §2.2.2: the source prefix precedes the official FMI header.
The header's FMI3_OVERRIDE_FUNCTION_PREFIX mechanism selects the binary ABI. -/
def functionPrefix (modelName : String) : String :=
  "#define FMI3_FUNCTION_PREFIX " ++ modelIdentifier modelName ++ "_\n"

end Rumoca.FMI3
