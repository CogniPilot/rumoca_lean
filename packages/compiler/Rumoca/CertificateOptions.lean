import Lean

/-! A source snapshot's display identity is independent of its temporary I/O
location. The compiler supplies the original input name when checking staged
artifacts; direct checks default to the actual source path. It remains literal
data in the fixed proposition, not a producer-supplied proof or command. -/
register_option rumoca.certificate.sourceName : String :=
  { defValue := "", descr := "Original source identity for the independently read snapshot" }

namespace Rumoca.CertificateOptions

def sourceName (options : Lean.Options) (path : String) : String :=
  let name := rumoca.certificate.sourceName.get options
  if name.isEmpty then path else name

end Rumoca.CertificateOptions
