import RumocaFMI3.DiscreteEvaluationContract

namespace Rumoca.FMI3.DiscreteEvaluation
open CMemory

/-- Both reference alternatives describe the same public call. The lifecycle
classifies them; the target contract derives the actual returned status. -/
inductive Request where
  | evaluate
  | reject

def Request.call (_ : Request) (p : Address) : String × List Value :=
  (signature.name, arguments (some p))

def Request.Allowed (request : Request) (kind : Kind) (mode : Mode) : Prop :=
  match request with
  | .evaluate => Reference.Allowed .evaluateDiscrete kind mode
  | .reject => ¬ Reference.Allowed .evaluateDiscrete kind mode

def Request.failed : Request → Bool
  | .evaluate => false
  | .reject => true

def classify (kind : Kind) (mode : Mode) : Request :=
  if allowed .evaluateDiscrete kind mode then .evaluate else .reject

theorem classify_correct (kind : Kind) (mode : Mode) :
    (classify kind mode).Allowed kind mode := by
  unfold classify
  split
  · rename_i accepted
    exact (allowed_correct .evaluateDiscrete kind mode).mp accepted
  · rename_i rejected
    exact fun permitted => rejected ((allowed_correct .evaluateDiscrete kind mode).mpr permitted)

theorem request_coverage (kind : Kind) (mode : Mode) :
    ∃ request : Request, request.Allowed kind mode :=
  ⟨classify kind mode, classify_correct kind mode⟩

end Rumoca.FMI3.DiscreteEvaluation
