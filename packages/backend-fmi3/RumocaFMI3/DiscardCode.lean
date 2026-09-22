import RumocaFMI3.Runtime

/-! The reusable FMI discard diagnostic body.  The message is supplied by the
caller so numerical preflight sites can share the callback/status protocol. -/
namespace Rumoca.FMI3.Discard
open CTree

def body (message : String) : List Stmt := [
  Runtime.log "fmi3Discard" (.str message),
  Runtime.ret (Runtime.v "fmi3Discard")]

end Rumoca.FMI3.Discard
