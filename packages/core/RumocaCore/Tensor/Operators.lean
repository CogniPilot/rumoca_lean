import RumocaCore.Tensor

/-! Shape-preserving pointwise tensor operators. Evaluation traverses dense
arrays; the operator itself is one node, independent of tensor volume. Scalar
arithmetic is supplied explicitly, so a target cannot accidentally use integer
bit-vector arithmetic as an interpretation of floating-point addition. The four
field operators and negation are provided so the reverse rules can be expressed
without a separate cotangent kernel. -/
namespace Rumoca.Tensor

inductive BinaryOp where
  | add
  | mul
  | sub
  | div
  deriving Repr, BEq, DecidableEq

structure ScalarOps (α : Type) where
  add : α → α → α
  mul : α → α → α
  sub : α → α → α
  div : α → α → α
  neg : α → α

def BinaryOp.scalar (ops : ScalarOps α) : BinaryOp → α → α → α
  | .add => ops.add
  | .mul => ops.mul
  | .sub => ops.sub
  | .div => ops.div

def Value.zipWith (f : α → β → γ) (x : Value α s) (y : Value β s) : Value γ s :=
  ⟨Vector.zipWith f x.data y.data⟩

@[simp] theorem Value.getElem_zipWith (f : α → β → γ) (x : Value α s) (y : Value β s)
    (hi : i < s.volume) : (x.zipWith f y)[i] = f x[i] y[i] := by
  change (Vector.zipWith f x.data y.data)[i] = _
  exact Vector.getElem_zipWith hi

def Value.mapWith (f : α → β) (x : Value α s) : Value β s := ⟨x.data.map f⟩

@[simp] theorem Value.getElem_mapWith (f : α → β) (x : Value α s) (hi : i < s.volume) :
    (x.mapWith f)[i] = f x[i] := by
  change (x.data.map f)[i] = _
  exact Vector.getElem_map ..

def BinaryOp.eval (ops : ScalarOps α) (op : BinaryOp) (x y : Value α s) : Value α s :=
  x.zipWith (op.scalar ops) y

def BinaryOp.denote (ops : ScalarOps α) (op : BinaryOp)
    (x y : Denotation α s) : Denotation α s := fun i => op.scalar ops (x i) (y i)

theorem BinaryOp.eval_correct (ops : ScalarOps α) (op : BinaryOp) (x y : Value α s)
    (i : Fin s.volume) : (op.eval ops x y)[i] = op.denote ops (fun j => x[j]) (fun j => y[j]) i :=
  Value.getElem_zipWith _ _ _ i.isLt

/-- A Jacobian-vector product rule, expressed in whole-tensor operations. The
quotient rule reuses the field operators so no extra scalar kernel is needed. -/
def BinaryOp.jvp (ops : ScalarOps α) (op : BinaryOp) (x y dx dy : Value α s) : Value α s :=
  match op with
  | .add => BinaryOp.eval ops .add dx dy
  | .mul => BinaryOp.eval ops .add (BinaryOp.eval ops .mul x dy) (BinaryOp.eval ops .mul y dx)
  | .sub => BinaryOp.eval ops .sub dx dy
  | .div => BinaryOp.eval ops .div
      (BinaryOp.eval ops .sub (BinaryOp.eval ops .mul dx y) (BinaryOp.eval ops .mul x dy))
      (BinaryOp.eval ops .mul y y)

/-- A transpose-Jacobian product returns one cotangent tensor per operand.
If operands alias, the program's reverse pass must accumulate both results.
The subtraction and division adjoints negate the right operand's contribution. -/
def BinaryOp.vjp (ops : ScalarOps α) (op : BinaryOp) (x y seed : Value α s) : Value α s × Value α s :=
  match op with
  | .add => (seed, seed)
  | .mul => (BinaryOp.eval ops .mul y seed, BinaryOp.eval ops .mul x seed)
  | .sub => (seed, seed.mapWith ops.neg)
  | .div => (BinaryOp.eval ops .div seed y,
      (BinaryOp.eval ops .div (BinaryOp.eval ops .mul x seed) (BinaryOp.eval ops .mul y y)).mapWith ops.neg)

end Rumoca.Tensor
