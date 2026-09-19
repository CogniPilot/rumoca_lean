import RumocaFMI3.Runtime
import RumocaC.StatementPrinter
import RumocaC.Loops
import RumocaC.BodyEmbedding

/-! Profile-generic value-reference dispatch for the Float64 accessors.

Every adapter profile's `fmi3GetFloat64` / `fmi3SetFloat64` body dispatches one
array value reference to its instance region through the same shape: a right-
nested chain of equality guards `if valueReferences[0] == j then <arm> else
<next>`, ending in an "unknown reference" fallback. The chain is `dispatchChain`
below, folded over an ordered list of `(reference number, dispatch arm)` pairs;
the only structural difference between profiles is that list (the tensor getter
covers references `0..4`, the constant-rate getter `0..2`, and each setter its
writable subset). Printability of the whole chain is proved once here by
induction over the reference list, so a profile obtains it by supplying its list
and the printability of each arm rather than re-proving the nested branches. -/
noncomputable section
namespace Rumoca.FMI3.Float64Dispatch
open CTree

/-- The value-reference dispatch chain over an ordered list of guarded arms.
For `[(j₀, a₀), (j₁, a₁), …]` this builds
`[if vr == j₀ then a₀ else [if vr == j₁ then a₁ else … fallback]]`,
one right-nested `Runtime.branch` per reference, terminating in `fallback`. -/
def dispatchChain (vr : Expr) (arms : List (Nat × List Stmt)) (fallback : List Stmt) : List Stmt :=
  arms.foldr (fun a rest => [Runtime.branch (Runtime.eqv vr (Runtime.n a.1)) a.2 rest]) fallback

@[simp] theorem dispatchChain_nil (vr : Expr) (fallback : List Stmt) :
    dispatchChain vr [] fallback = fallback := rfl

theorem dispatchChain_cons (vr : Expr) (j : Nat) (arm : List Stmt) (arms : List (Nat × List Stmt))
    (fallback : List Stmt) :
    dispatchChain vr ((j, arm) :: arms) fallback =
      [Runtime.branch (Runtime.eqv vr (Runtime.n j)) arm (dispatchChain vr arms fallback)] := rfl

open Rumoca.CTree.Printer in
/-- Every statement of a dispatch chain prints its intended C token grammar,
given that the compared reference expression prints, each arm's statements
print, and the fallback statements print. Proved by induction over the
reference list; the per-profile accessors instantiate it with their own list. -/
theorem dispatchChain_printable (typedefs : List String) (vr : Expr)
    (arms : List (Nat × List Stmt)) (fallback : List Stmt)
    (hvr : Printable typedefs vr)
    (hfallback : ∀ stmt ∈ fallback, ItemPrintable typedefs stmt) :
    (∀ a ∈ arms, ∀ stmt ∈ a.2, ItemPrintable typedefs stmt) →
      ∀ stmt ∈ dispatchChain vr arms fallback, ItemPrintable typedefs stmt := by
  induction arms with
  | nil => intro _ stmt hmem; exact hfallback stmt hmem
  | cons a rest ih =>
    obtain ⟨j, arm⟩ := a
    intro harms stmt hmem
    rw [dispatchChain_cons, List.mem_singleton] at hmem
    subst hmem
    refine ItemPrintable.branch ?guard ?yes ?no
    case guard => exact Printable.binary hvr Printable.natural
    case yes => exact harms (j, arm) (by simp)
    case no => exact ih (fun b hb => harms b (List.mem_cons_of_mem _ hb))

end Rumoca.FMI3.Float64Dispatch
