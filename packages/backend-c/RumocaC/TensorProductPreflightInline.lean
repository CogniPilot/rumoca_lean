import RumocaC.TensorProductPreflight

/-! Inline composition of the shared product preflight. A surrounding function
supplies pointer/count expressions and fresh locals; the detector needs no new
callee lookup and preserves the heap before the interface chooses a policy. -/
noncomputable section
namespace Rumoca.CTensor.ProductPreflight.Inline
open CTree CMemory CMemory.TensorView CMemory.EncodedTensor
set_option maxRecDepth 10000

def setup (left right count : Expr) : List Stmt :=
  [.declare "const double *" "left" left, .declare "const double *" "right" right,
    .declare "size_t" "count" count]

def code (flagType : String) (left right count : Expr) : List Stmt :=
  setup left right count ++ FinitePreflight.segmentWith flagType ProductPreflight.value

def parameters (env : CBody.Locals) (left right : Option Address) (count : Nat) : CBody.Locals :=
  CBody.bind (CBody.bind (CBody.bind env "left" (.pointer left)) "right" (.pointer right))
    "count" (.integer count)

def types (prior : CLoops.Types) : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (CLoops.bindType prior "left" .pointer) "right" .pointer) "count" .size

def finalEnv (env : CBody.Locals) (left right : Option Address) (a b : Values shape) : CBody.Locals :=
  CLoops.counterEnv
    (FinitePreflight.locals (parameters env left right shape.volume) (MultiplicationTotal.result a b)
      shape.volume) "k" shape.volume

def finalTypes (prior : CLoops.Types) := FinitePreflight.localTypes (types prior)

def Fresh (env : CBody.Locals) : Prop :=
  ∀ name ∈ ["left", "right", "count", "sample", "valid", "k"], env name = none

variable [interface : CInterface]

theorem segment_reaches (flagType : String) (a b : Values shape) (heap : Heap)
    (left right : Option Address) (env : CBody.Locals) (prior : CLoops.Types) (rest : List Stmt)
    (fresh : Fresh env)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types flagType = some .int32)
    (double_type : interface.types "double" = some .float64) :
    Transition.Reaches CLoops.machine.step
      (.running (FinitePreflight.segmentWith flagType ProductPreflight.value ++ rest)
        (parameters env left right shape.volume) (types prior) heap)
      (.running rest (finalEnv env left right a b) (finalTypes prior) heap) := by
  apply FinitePreflight.segment_reaches flagType ProductPreflight.value (MultiplicationTotal.result a b)
    rest (parameters env left right shape.volume) (types prior) heap
    (by simp [parameters, CBody.bind, fresh "valid" (by simp)])
    (by simp [parameters, CBody.bind, fresh "k" (by simp)])
    (by simp [parameters, CBody.bind, fresh "sample" (by simp)])
    (by simp [parameters, CBody.bind]) bounded size_type int_type double_type
  intro i
  obtain ⟨leftBase, left_eq, leftRead⟩ := read_left i
  obtain ⟨rightBase, right_eq, rightRead⟩ := read_right i
  simp only [Fin.getElem_fin, finiteBits_get] at leftRead rightRead
  let current := CLoops.counterEnv
    (FinitePreflight.locals (parameters env left right shape.volume) (MultiplicationTotal.result a b) i.val)
    "k" i.val
  have counter : current "k" = some (.integer i.val) := by simp [current, CLoops.counterEnv, CBody.bind]
  have leftEval := index_eval current heap "left" leftBase i.val
    (by simp [current, CLoops.counterEnv, FinitePreflight.locals, CBody.bind, parameters, left_eq]) counter
  have rightEval := index_eval current heap "right" rightBase i.val
    (by simp [current, CLoops.counterEnv, FinitePreflight.locals, CBody.bind, parameters, right_eq]) counter
  simp only [Fin.getElem_fin, MultiplicationTotal.result_get]
  exact CArithmetic.eval_mul CBody.legacyExpressions current _ heap (indexed "left") (indexed "right")
    a[i] b[i] (leftEval.trans leftRead) (rightEval.trans rightRead)

omit interface in
theorem final_flag (env : CBody.Locals) (left right : Option Address) (a b : Values shape) :
    finalEnv env left right a b "valid" =
      some (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b))) := by
  simp [finalEnv, CLoops.counterEnv, FinitePreflight.locals, CBody.bind, FiniteScan.prefix_full]

theorem code_reaches (flagType : String) (leftExpr rightExpr countExpr : Expr)
    (a b : Values shape) (heap : Heap) (left right : Option Address)
    (env : CBody.Locals) (prior : CLoops.Types) (rest : List Stmt)
    (fresh : Fresh env)
    (leftEval : CLoops.eval env prior heap leftExpr = some (.pointer left))
    (rightEval : CLoops.eval (CBody.bind env "left" (.pointer left))
      (CLoops.bindType prior "left" .pointer) heap rightExpr = some (.pointer right))
    (countEval : CLoops.eval (CBody.bind (CBody.bind env "left" (.pointer left)) "right" (.pointer right))
      (CLoops.bindType (CLoops.bindType prior "left" .pointer) "right" .pointer) heap countExpr =
      some (.integer shape.volume))
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64)
    (pointer_type : interface.types "const double *" = some .pointer)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types flagType = some .int32)
    (double_type : interface.types "double" = some .float64) :
    Transition.Reaches CLoops.machine.step
      (.running (code flagType leftExpr rightExpr countExpr ++ rest) env prior heap)
      (.running rest (finalEnv env left right a b) (finalTypes prior) heap) := by
  let scan := FinitePreflight.segmentWith flagType ProductPreflight.value ++ rest
  have stepLeft := CLoops.declare_local env prior heap "const double *" "left" leftExpr
    (.declare "const double *" "right" rightExpr :: .declare "size_t" "count" countExpr :: scan)
    .pointer (.pointer left) (.pointer left) pointer_type (fresh "left" (by simp)) leftEval rfl
  have stepRight := CLoops.declare_local (CBody.bind env "left" (.pointer left))
    (CLoops.bindType prior "left" .pointer) heap "const double *" "right" rightExpr
    (.declare "size_t" "count" countExpr :: scan)
    .pointer (.pointer right) (.pointer right) pointer_type
    (by simp [CBody.bind, fresh "right" (by simp)]) rightEval rfl
  have stepCount := CLoops.declare_local
    (CBody.bind (CBody.bind env "left" (.pointer left)) "right" (.pointer right))
    (CLoops.bindType (CLoops.bindType prior "left" .pointer) "right" .pointer)
    heap "size_t" "count" countExpr scan .size (.integer shape.volume) (.integer shape.volume)
    size_type (by simp [CBody.bind, fresh "count" (by simp)]) countEval
    (CLoops.convert_size_nat _ bounded)
  exact .next stepLeft (.next stepRight (.next stepCount
    (segment_reaches flagType a b heap left right env prior rest fresh read_left read_right
      bounded size_type int_type double_type)))

omit interface in
theorem final_frame (env : CBody.Locals) (left right : Option Address) (a b : Values shape)
    (name : String) (outside : name ∉ ["left", "right", "count", "sample", "valid", "k"]) :
    finalEnv env left right a b name = env name := by
  simp only [List.mem_cons, not_or] at outside
  simp [finalEnv, CLoops.counterEnv, FinitePreflight.locals, parameters, CBody.bind,
    outside.1, outside.2.1, outside.2.2.1, outside.2.2.2.1, outside.2.2.2.2.1, outside.2.2.2.2.2]

end Rumoca.CTensor.ProductPreflight.Inline
