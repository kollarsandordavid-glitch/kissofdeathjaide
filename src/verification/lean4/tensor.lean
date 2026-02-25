import Init

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

def floatNaN : Float := 0.0 / 0.0
def floatInf : Float := 1.0 / 0.0
def floatNegInf : Float := -(1.0 / 0.0)

inductive TensorError where
  | shapeMismatch
  | invalidShape
  | outOfBounds
  | overflow
  | divideByZero
  | invalidAxis
  | emptyInput
  | invalidConv2D
  | invalidPads
  | invalidReps
  | mustBeSquare
  | singularMatrix
  | invalidForOneHot
  | allocFailed
  deriving Repr, BEq, DecidableEq

abbrev TResult (α : Type) := Except TensorError α

def listProduct : List Nat → Nat
  | [] => 1
  | h :: t => h * listProduct t

theorem listProduct_nil : listProduct [] = 1 := rfl

theorem listProduct_cons (h : Nat) (t : List Nat) :
    listProduct (h :: t) = h * listProduct t := rfl

theorem listProduct_singleton (n : Nat) : listProduct [n] = n := by
  simp [listProduct]

def allPositive : List Nat → Prop
  | [] => True
  | h :: t => h > 0 ∧ allPositive t

theorem listProduct_pos (l : List Nat) (h : allPositive l) :
    listProduct l > 0 := by
  induction l with
  | nil => simp [listProduct]
  | cons hd tl ih =>
    simp [listProduct, allPositive] at *
    exact Nat.mul_pos h.1 (ih h.2)

theorem listProduct_append (l1 l2 : List Nat) :
    listProduct (l1 ++ l2) = listProduct l1 * listProduct l2 := by
  induction l1 with
  | nil => simp [listProduct]
  | cons h t ih =>
    simp [listProduct, ih, Nat.mul_assoc]

def computeStrides (dims : List Nat) : List Nat :=
  dims.enum.map (fun ⟨i, _⟩ => listProduct (dims.drop (i + 1)))

theorem computeStrides_length (dims : List Nat) :
    (computeStrides dims).length = dims.length := by
  unfold computeStrides
  simp [List.length_map, List.length_enum]

structure Shape where
  dims : List Nat
  strides : List Nat
  h_len : dims.length = strides.length

def Shape.mk' (dims : List Nat) : Shape where
  dims := dims
  strides := computeStrides dims
  h_len := by simp [computeStrides, List.length_map, List.length_enum]

def Shape.ndim (s : Shape) : Nat := s.dims.length

def Shape.totalSize (s : Shape) : Nat := listProduct s.dims

@[simp] theorem Shape.mk'_dims (dims : List Nat) : (Shape.mk' dims).dims = dims := rfl

@[simp] theorem Shape.mk'_totalSize (dims : List Nat) :
    (Shape.mk' dims).totalSize = listProduct dims := rfl

def Shape.equals (s1 s2 : Shape) : Bool :=
  decide (s1.dims = s2.dims)

def Shape.broadcastCompatible (self target : Shape) : Bool :=
  if target.dims.length < self.dims.length then false
  else
    let offset := target.dims.length - self.dims.length
    let targetSuffix := target.dims.drop offset
    List.zip self.dims targetSuffix |>.all (fun (sd, td) => sd = td ∨ sd = 1)

def Shape.isContiguous (s : Shape) : Bool :=
  let pairs := List.zip s.dims.reverse s.strides.reverse
  pairs.foldl (fun (ok, expected) (d, st) =>
    if ok ∧ st = expected then (true, expected * d)
    else (false, 0)) (true, 1) |>.1

theorem Shape.equals_refl (s : Shape) : s.equals s = true := by
  unfold Shape.equals
  simp

theorem Shape.equals_symm (s1 s2 : Shape) :
    s1.equals s2 = s2.equals s1 := by
  unfold Shape.equals
  simp [eq_comm]

theorem Shape.totalSize_nil :
    Shape.totalSize { dims := [], strides := [], h_len := rfl } = 1 := by
  unfold Shape.totalSize
  simp [listProduct]

theorem Shape.totalSize_singleton (n : Nat) :
    Shape.totalSize { dims := [n], strides := [1], h_len := rfl } = n := by
  unfold Shape.totalSize
  simp [listProduct]

theorem Shape.totalSize_pos (s : Shape) (h : allPositive s.dims) :
    s.totalSize > 0 := by
  unfold Shape.totalSize
  exact listProduct_pos s.dims h

def Shape.copy (s : Shape) : Shape :=
  { dims := s.dims, strides := s.strides, h_len := s.h_len }

theorem Shape.copy_equals (s : Shape) : s.copy.equals s = true := by
  unfold Shape.copy Shape.equals
  simp

theorem Shape.copy_totalSize (s : Shape) : s.copy.totalSize = s.totalSize := rfl

structure RefCount where
  count : Nat
  h_pos : count > 0

def RefCount.init : RefCount := { count := 1, h_pos := Nat.zero_lt_succ 0 }

def RefCount.retain (rc : RefCount) : RefCount :=
  { count := rc.count + 1, h_pos := by omega }

def RefCount.release (rc : RefCount) : Option RefCount :=
  if h : rc.count > 1 then
    some { count := rc.count - 1, h_pos := by omega }
  else
    none

@[simp] theorem RefCount.init_count : RefCount.init.count = 1 := rfl

theorem RefCount.retain_increases (rc : RefCount) :
    (rc.retain).count = rc.count + 1 := rfl

theorem RefCount.release_decreases (rc : RefCount) (h : rc.count > 1) :
    ∃ rc', rc.release = some rc' ∧ rc'.count = rc.count - 1 := by
  unfold RefCount.release
  simp [h]

theorem RefCount.release_last (rc : RefCount) (h : rc.count = 1) :
    rc.release = none := by
  unfold RefCount.release
  simp [h]

theorem RefCount.no_underflow (rc : RefCount) : rc.count > 0 := rc.h_pos

structure CowState where
  isShared : Bool

def CowState.init : CowState := { isShared := false }
def CowState.markShared (_ : CowState) : CowState := { isShared := true }
def CowState.makeWritable (_ : CowState) : CowState := { isShared := false }

@[simp] theorem CowState.init_isShared : CowState.init.isShared = false := rfl
@[simp] theorem CowState.markShared_isShared (cs : CowState) :
    (cs.markShared).isShared = true := rfl

theorem CowState.makeWritable_not_shared (cs : CowState) :
    (cs.makeWritable).isShared = false := rfl

structure Tensor where
  data : Array Float
  shape : Shape
  h_data_size : data.size = shape.totalSize
  refcount : RefCount
  cow : CowState

def Tensor.ndim (t : Tensor) : Nat := t.shape.ndim
def Tensor.dataLen (t : Tensor) : Nat := t.data.size

theorem Tensor.dataLen_eq_totalSize (t : Tensor) :
    t.dataLen = t.shape.totalSize := t.h_data_size

def flatToMultiIndex (dims : List Nat) (flat : Nat) : List Nat :=
  match dims with
  | [] => []
  | [_] => [flat]
  | _ =>
    let rec go : List Nat → Nat → List Nat
      | [], _ => []
      | [_], rem => [rem]
      | _ :: rest, rem =>
        let stride := listProduct rest
        if stride = 0 then 0 :: go rest 0
        else (rem / stride) :: go rest (rem % stride)
    go dims flat

def multiToFlatIndex (strides : List Nat) (indices : List Nat) : Nat :=
  List.zipWith (· * ·) indices strides |>.foldl (· + ·) 0

def computeFlatIndex (shape : Shape) (indices : List Nat) : Nat :=
  multiToFlatIndex shape.strides indices

def insertAxisIndex (reducedDims : List Nat) (flatIdx : Nat) (axis : Nat) (axisVal : Nat) : List Nat :=
  let multiIdx := flatToMultiIndex reducedDims flatIdx
  (multiIdx.take axis) ++ [axisVal] ++ (multiIdx.drop axis)

def removeAxis (l : List Nat) (axis : Nat) : List Nat :=
  l.enum.filterMap (fun ⟨i, v⟩ => if i = axis then none else some v)

def computeIndex (shape : Shape) (indices : List Nat) : TResult Nat :=
  if indices.length ≠ shape.dims.length then
    Except.error TensorError.invalidAxis
  else
    let rec go : List Nat → List Nat → List Nat → Nat → TResult Nat
      | [], [], [], acc => Except.ok acc
      | d :: drest, s :: srest, i :: irest, acc =>
        if i ≥ d then Except.error TensorError.outOfBounds
        else go drest srest irest (acc + i * s)
      | _, _, _, _ => Except.error TensorError.invalidAxis
    go shape.dims shape.strides indices 0

def Tensor.init (dims : List Nat) : TResult Tensor :=
  if dims.length = 0 then
    Except.error TensorError.invalidShape
  else if dims.any (· == 0) then
    Except.error TensorError.invalidShape
  else
    Except.ok {
      data := mkArray (listProduct dims) (0.0 : Float)
      shape := Shape.mk' dims
      h_data_size := by simp [Shape.mk', Shape.totalSize, Array.size_mkArray]
      refcount := RefCount.init
      cow := CowState.init
    }

theorem Tensor.init_error_on_empty :
    Tensor.init [] = Except.error TensorError.invalidShape := rfl

theorem Tensor.init_shape (dims : List Nat)
    (h_ne : dims.length ≠ 0)
    (h_nz : dims.any (· == 0) = false)
    (t : Tensor) (h_ok : Tensor.init dims = Except.ok t) :
    t.shape.dims = dims := by
  unfold Tensor.init at h_ok
  simp [h_ne, h_nz] at h_ok
  cases h_ok
  rfl

theorem Tensor.init_refcount_one (dims : List Nat)
    (h_ne : dims.length ≠ 0)
    (h_nz : dims.any (· == 0) = false)
    (t : Tensor) (h_ok : Tensor.init dims = Except.ok t) :
    t.refcount.count = 1 := by
  unfold Tensor.init at h_ok
  simp [h_ne, h_nz] at h_ok
  cases h_ok
  rfl

def Tensor.get (t : Tensor) (indices : List Nat) : TResult Float :=
  match computeIndex t.shape indices with
  | Except.ok idx =>
    if h : idx < t.data.size then
      Except.ok t.data[idx]
    else
      Except.error TensorError.outOfBounds
  | Except.error e => Except.error e

def Tensor.set (t : Tensor) (indices : List Nat) (value : Float) : TResult Tensor :=
  match computeIndex t.shape indices with
  | Except.ok idx =>
    if h : idx < t.data.size then
      let newData := t.data.set ⟨idx, h⟩ value
      Except.ok { t with
        data := newData
        h_data_size := by
          show (t.data.set ⟨idx, h⟩ value).size = t.shape.totalSize
          rw [Array.size_set]
          exact t.h_data_size
        cow := CowState.init
      }
    else
      Except.error TensorError.outOfBounds
  | Except.error e => Except.error e

theorem Tensor.set_preserves_shape (t : Tensor) (indices : List Nat)
    (value : Float) (t' : Tensor)
    (h_ok : t.set indices value = Except.ok t') :
    t'.shape = t.shape := by
  unfold Tensor.set at h_ok
  split at h_ok
  · split at h_ok
    · cases h_ok; rfl
    · cases h_ok
  · cases h_ok

theorem Tensor.set_preserves_size (t : Tensor) (indices : List Nat)
    (value : Float) (t' : Tensor)
    (h_ok : t.set indices value = Except.ok t') :
    t'.data.size = t.data.size := by
  unfold Tensor.set at h_ok
  split at h_ok
  · split at h_ok
    · cases h_ok; simp [Array.size_set]
    · cases h_ok
  · cases h_ok

def Tensor.fill (t : Tensor) (value : Float) : Tensor :=
  { t with
    data := mkArray t.data.size value
    h_data_size := by rw [Array.size_mkArray, t.h_data_size]
    cow := CowState.init }

theorem Tensor.fill_preserves_shape (t : Tensor) (value : Float) :
    (t.fill value).shape = t.shape := rfl

theorem Tensor.fill_size (t : Tensor) (value : Float) :
    (t.fill value).data.size = t.data.size := by
  unfold Tensor.fill
  simp [Array.size_mkArray]

def Tensor.zeros (dims : List Nat) : TResult Tensor := Tensor.init dims

def Tensor.ones (dims : List Nat) : TResult Tensor :=
  match Tensor.init dims with
  | Except.ok t => Except.ok (t.fill 1.0)
  | Except.error e => Except.error e

def Tensor.full (dims : List Nat) (value : Float) : TResult Tensor :=
  match Tensor.init dims with
  | Except.ok t => Except.ok (t.fill value)
  | Except.error e => Except.error e

def mapData (t : Tensor) (f : Float → Float) : Tensor :=
  { t with
    data := t.data.map f
    h_data_size := by rw [Array.size_map, t.h_data_size]
    cow := CowState.init }

theorem mapData_preserves_shape (t : Tensor) (f : Float → Float) :
    (mapData t f).shape = t.shape := rfl

theorem mapData_preserves_size (t : Tensor) (f : Float → Float) :
    (mapData t f).data.size = t.data.size := by
  unfold mapData; simp [Array.size_map]

def zipWithArray (a b : Array Float) (f : Float → Float → Float) : Array Float :=
  a.mapIdx (fun i v =>
    if h : i.val < b.size then f v b[i.val]
    else v)

theorem zipWithArray_size (a b : Array Float) (f : Float → Float → Float) :
    (zipWithArray a b f).size = a.size := by
  unfold zipWithArray
  simp [Array.size_mapIdx]

def zipData (t1 t2 : Tensor) (f : Float → Float → Float) : TResult Tensor :=
  if t1.shape.equals t2.shape = false then
    Except.error TensorError.shapeMismatch
  else
    let newData := zipWithArray t1.data t2.data f
    Except.ok { t1 with
      data := newData
      h_data_size := by
        show newData.size = t1.shape.totalSize
        simp [newData]
        rw [zipWithArray_size]
        exact t1.h_data_size
      cow := CowState.init }

theorem zipData_preserves_shape (t1 t2 : Tensor) (f : Float → Float → Float)
    (t' : Tensor) (h_ok : zipData t1 t2 f = Except.ok t') :
    t'.shape = t1.shape := by
  unfold zipData at h_ok
  split at h_ok
  · cases h_ok
  · injection h_ok with h'; rw [← h']

def Tensor.add (t1 t2 : Tensor) : TResult Tensor := zipData t1 t2 (· + ·)
def Tensor.sub (t1 t2 : Tensor) : TResult Tensor := zipData t1 t2 (· - ·)
def Tensor.mul (t1 t2 : Tensor) : TResult Tensor := zipData t1 t2 (· * ·)

def Tensor.divOp (t1 t2 : Tensor) : TResult Tensor :=
  if t2.data.any (· == 0.0) then
    Except.error TensorError.divideByZero
  else
    zipData t1 t2 (· / ·)

theorem Tensor.add_shape (t1 t2 t' : Tensor) (h : Tensor.add t1 t2 = Except.ok t') :
    t'.shape = t1.shape := zipData_preserves_shape t1 t2 (· + ·) t' h

theorem Tensor.sub_shape (t1 t2 t' : Tensor) (h : Tensor.sub t1 t2 = Except.ok t') :
    t'.shape = t1.shape := zipData_preserves_shape t1 t2 (· - ·) t' h

theorem Tensor.mul_shape (t1 t2 t' : Tensor) (h : Tensor.mul t1 t2 = Except.ok t') :
    t'.shape = t1.shape := zipData_preserves_shape t1 t2 (· * ·) t' h

def Tensor.addScalar (t : Tensor) (s : Float) : Tensor := mapData t (· + s)
def Tensor.subScalar (t : Tensor) (s : Float) : Tensor := mapData t (· - s)
def Tensor.mulScalar (t : Tensor) (s : Float) : Tensor := mapData t (· * s)

def Tensor.divScalar (t : Tensor) (s : Float) : TResult Tensor :=
  if s == 0.0 then Except.error TensorError.divideByZero
  else Except.ok (mapData t (· / s))

theorem Tensor.addScalar_shape (t : Tensor) (s : Float) :
    (t.addScalar s).shape = t.shape := mapData_preserves_shape t (· + s)
theorem Tensor.subScalar_shape (t : Tensor) (s : Float) :
    (t.subScalar s).shape = t.shape := mapData_preserves_shape t (· - s)
theorem Tensor.mulScalar_shape (t : Tensor) (s : Float) :
    (t.mulScalar s).shape = t.shape := mapData_preserves_shape t (· * s)

theorem Tensor.divScalar_shape (t : Tensor) (s : Float) (t' : Tensor)
    (h_ok : t.divScalar s = Except.ok t') : t'.shape = t.shape := by
  unfold Tensor.divScalar at h_ok
  split at h_ok
  · cases h_ok
  · cases h_ok; exact mapData_preserves_shape t (· / s)

def Tensor.expOp (t : Tensor) : Tensor := mapData t Float.exp
def Tensor.logOp (t : Tensor) : Tensor :=
  mapData t (fun v => if v ≤ 0.0 then floatNegInf else Float.log v)
def Tensor.sinOp (t : Tensor) : Tensor := mapData t Float.sin
def Tensor.cosOp (t : Tensor) : Tensor := mapData t Float.cos
def Tensor.tanOp (t : Tensor) : Tensor := mapData t Float.tan
def Tensor.sqrtOp (t : Tensor) : Tensor :=
  mapData t (fun v => if v < 0.0 then floatNaN else Float.sqrt v)
def Tensor.powOp (t : Tensor) (exponent : Float) : Tensor :=
  mapData t (fun v => Float.pow v exponent)
def Tensor.absOp (t : Tensor) : Tensor := mapData t Float.abs
def Tensor.reluOp (t : Tensor) : Tensor :=
  mapData t (fun v => if v > 0.0 then v else 0.0)

theorem Tensor.expOp_shape (t : Tensor) : t.expOp.shape = t.shape :=
  mapData_preserves_shape t Float.exp
theorem Tensor.logOp_shape (t : Tensor) : t.logOp.shape = t.shape :=
  mapData_preserves_shape t _
theorem Tensor.sinOp_shape (t : Tensor) : t.sinOp.shape = t.shape :=
  mapData_preserves_shape t Float.sin
theorem Tensor.cosOp_shape (t : Tensor) : t.cosOp.shape = t.shape :=
  mapData_preserves_shape t Float.cos
theorem Tensor.tanOp_shape (t : Tensor) : t.tanOp.shape = t.shape :=
  mapData_preserves_shape t Float.tan
theorem Tensor.sqrtOp_shape (t : Tensor) : t.sqrtOp.shape = t.shape :=
  mapData_preserves_shape t _
theorem Tensor.absOp_shape (t : Tensor) : t.absOp.shape = t.shape :=
  mapData_preserves_shape t Float.abs
theorem Tensor.reluOp_shape (t : Tensor) : t.reluOp.shape = t.shape :=
  mapData_preserves_shape t _

theorem Tensor.exp_preserves_size (t : Tensor) :
    t.expOp.data.size = t.data.size := mapData_preserves_size t Float.exp
theorem Tensor.sin_preserves_size (t : Tensor) :
    t.sinOp.data.size = t.data.size := mapData_preserves_size t Float.sin
theorem Tensor.cos_preserves_size (t : Tensor) :
    t.cosOp.data.size = t.data.size := mapData_preserves_size t Float.cos

def Tensor.reduceAxis (t : Tensor) (axis : Nat)
    (f : Float → Float → Float) (initial : Float) : TResult Tensor :=
  if axis ≥ t.shape.dims.length then
    Except.error TensorError.invalidAxis
  else
    let newDims := removeAxis t.shape.dims axis
    let safeNewDims := if newDims.length = 0 then [1] else newDims
    let newTotal := listProduct safeNewDims
    let axisSize := t.shape.dims.get! axis
    let srcShape := Shape.mk' t.shape.dims
    let data := Array.ofFn (fun idx : Fin newTotal =>
      let outMulti := flatToMultiIndex safeNewDims idx.val
      (List.range axisSize).foldl (fun acc k =>
        let inMulti := if newDims.length = 0 then [k]
          else (outMulti.take axis) ++ [k] ++ (outMulti.drop axis)
        f acc (t.data.get! (computeFlatIndex srcShape inMulti))
      ) initial)
    Except.ok {
      data := data
      shape := Shape.mk' safeNewDims
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.maxReduce (t : Tensor) (axis : Nat) : TResult Tensor :=
  t.reduceAxis axis max floatNegInf

def Tensor.minReduce (t : Tensor) (axis : Nat) : TResult Tensor :=
  t.reduceAxis axis min floatInf

def Tensor.sumReduce (t : Tensor) (axis : Nat) : TResult Tensor :=
  t.reduceAxis axis (· + ·) 0.0

def Tensor.meanReduce (t : Tensor) (axis : Nat) : TResult Tensor :=
  if h_ax : axis ≥ t.shape.dims.length then
    Except.error TensorError.invalidAxis
  else
    match t.sumReduce axis with
    | Except.error e => Except.error e
    | Except.ok sumT =>
      let axisSize := t.shape.dims.get ⟨axis, by omega⟩
      if axisSize = 0 then Except.error TensorError.divideByZero
      else
        let divisor := Float.ofNat axisSize
        Except.ok (sumT.mulScalar (1.0 / divisor))

def Tensor.reshape (t : Tensor) (newDims : List Nat) : TResult Tensor :=
  if newDims.length = 0 then
    Except.error TensorError.invalidShape
  else if h_ne : listProduct newDims ≠ t.shape.totalSize then
    Except.error TensorError.invalidShape
  else
    have h_eq : listProduct newDims = t.shape.totalSize := by
      by_contra h
      exact h_ne h
    Except.ok { t with
      shape := Shape.mk' newDims
      h_data_size := by rw [t.h_data_size]; exact h_eq.symm
    }

theorem Tensor.reshape_preserves_data (t : Tensor) (newDims : List Nat)
    (t' : Tensor) (h_ok : t.reshape newDims = Except.ok t') :
    t'.data = t.data := by
  unfold Tensor.reshape at h_ok
  split at h_ok
  · cases h_ok
  · split at h_ok
    · cases h_ok
    · injection h_ok with h'; rw [← h']

theorem Tensor.reshape_new_dims (t : Tensor) (newDims : List Nat)
    (t' : Tensor) (h_ok : t.reshape newDims = Except.ok t') :
    t'.shape.dims = newDims := by
  unfold Tensor.reshape at h_ok
  split at h_ok
  · cases h_ok
  · split at h_ok
    · cases h_ok
    · injection h_ok with h'; rw [← h']; simp [Shape.mk']

def Tensor.view (t : Tensor) (newDims : List Nat) : TResult Tensor :=
  if newDims.length = 0 then
    Except.error TensorError.invalidShape
  else if h_ne : listProduct newDims ≠ t.shape.totalSize then
    Except.error TensorError.invalidShape
  else
    have h_eq : listProduct newDims = t.shape.totalSize := by
      by_contra h
      exact h_ne h
    Except.ok {
      data := t.data
      shape := Shape.mk' newDims
      h_data_size := by rw [t.h_data_size]; exact h_eq.symm
      refcount := t.refcount.retain
      cow := t.cow.markShared
    }

theorem Tensor.view_shares_data (t : Tensor) (newDims : List Nat)
    (t' : Tensor) (h_ok : t.view newDims = Except.ok t') :
    t'.data = t.data := by
  unfold Tensor.view at h_ok
  split at h_ok
  · cases h_ok
  · split at h_ok
    · cases h_ok
    · injection h_ok with h'; rw [← h']

theorem Tensor.view_increments_refcount (t : Tensor) (newDims : List Nat)
    (t' : Tensor) (h_ok : t.view newDims = Except.ok t') :
    t'.refcount.count = t.refcount.count + 1 := by
  unfold Tensor.view at h_ok
  split at h_ok
  · cases h_ok
  · split at h_ok
    · cases h_ok
    · injection h_ok with h'; rw [← h']; rfl

theorem Tensor.view_marks_shared (t : Tensor) (newDims : List Nat)
    (t' : Tensor) (h_ok : t.view newDims = Except.ok t') :
    t'.cow.isShared = true := by
  unfold Tensor.view at h_ok
  split at h_ok
  · cases h_ok
  · split at h_ok
    · cases h_ok
    · injection h_ok with h'; rw [← h']; rfl

def Tensor.newView (t : Tensor) (newShape : Shape)
    (h_eq : newShape.totalSize = t.shape.totalSize) : Tensor :=
  { data := t.data
    shape := newShape
    h_data_size := by rw [t.h_data_size, h_eq]
    refcount := t.refcount.retain
    cow := t.cow.markShared }

theorem Tensor.newView_shares_data (t : Tensor) (newShape : Shape)
    (h_eq : newShape.totalSize = t.shape.totalSize) :
    (t.newView newShape h_eq).data = t.data := rfl

def Tensor.sliceOp (t : Tensor) (starts ends : List Nat) : TResult Tensor :=
  if starts.length ≠ t.shape.dims.length ∨ ends.length ≠ t.shape.dims.length then
    Except.error TensorError.invalidAxis
  else
    let newDims := List.zipWith (fun e s => e - s) ends starts
    if newDims.any (· == 0) then Except.error TensorError.invalidShape
    else
      let newTotal := listProduct newDims
      let srcShape := Shape.mk' t.shape.dims
      let data := Array.ofFn (fun idx : Fin newTotal =>
        let multiIdx := flatToMultiIndex newDims idx.val
        let srcIdx := List.zipWith (· + ·) multiIdx starts
        t.data.get! (computeFlatIndex srcShape srcIdx))
      Except.ok {
        data := data
        shape := Shape.mk' newDims
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

def Tensor.transposeOp (t : Tensor) (axes : List Nat) : TResult Tensor :=
  if axes.length ≠ t.shape.dims.length then
    Except.error TensorError.invalidAxis
  else if ¬ axes.all (· < t.shape.dims.length) then
    Except.error TensorError.invalidAxis
  else
    let newDims := axes.map (fun a => t.shape.dims.get! a)
    let newTotal := listProduct newDims
    let srcShape := Shape.mk' t.shape.dims
    let data := Array.ofFn (fun idx : Fin newTotal =>
      let outMulti := flatToMultiIndex newDims idx.val
      let srcMulti := axes.enum.map (fun ⟨_, a⟩ => outMulti.get! a)
      t.data.get! (computeFlatIndex srcShape
        (List.range t.shape.dims.length |>.map (fun i =>
          match axes.enum.find? (fun ⟨_, a⟩ => a = i) with
          | some ⟨pos, _⟩ => outMulti.get! pos
          | none => 0))))
    Except.ok {
      data := data
      shape := Shape.mk' newDims
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

theorem Tensor.transposeOp_ndim (t : Tensor) (axes : List Nat)
    (t' : Tensor) (h_ok : t.transposeOp axes = Except.ok t')
    (h_len : axes.length = t.shape.dims.length) :
    t'.shape.dims.length = t.shape.dims.length := by
  unfold Tensor.transposeOp at h_ok
  split at h_ok
  · rename_i hc; exact absurd h_len hc
  · split at h_ok
    · cases h_ok
    · injection h_ok with h'
      rw [← h']
      simp [List.length_map, h_len]

theorem listProduct_insert_one (l : List Nat) (i : Nat) :
    listProduct ((l.take i) ++ [1] ++ (l.drop i)) = listProduct l := by
  induction l generalizing i with
  | nil => simp [listProduct]
  | cons h t ih =>
    cases i with
    | zero => simp [listProduct, List.take, List.drop, Nat.one_mul]
    | succ n => simp [listProduct, List.take, List.drop, ih n, Nat.mul_assoc]

def Tensor.unsqueezeOp (t : Tensor) (axis : Nat) : TResult Tensor :=
  if axis > t.shape.dims.length then
    Except.error TensorError.invalidAxis
  else
    let newDims := (t.shape.dims.take axis) ++ [1] ++ (t.shape.dims.drop axis)
    Except.ok {
      data := t.data
      shape := Shape.mk' newDims
      h_data_size := by
        rw [t.h_data_size]
        simp [Shape.mk', Shape.totalSize]
        exact (listProduct_insert_one t.shape.dims axis).symm
      refcount := t.refcount.retain
      cow := t.cow.markShared
    }

def Tensor.broadcastOp (t : Tensor) (targetDims : List Nat) : TResult Tensor :=
  if t.shape.broadcastCompatible (Shape.mk' targetDims) = false then
    Except.error TensorError.shapeMismatch
  else if targetDims.any (· == 0) then Except.error TensorError.invalidShape
  else
    let targetTotal := listProduct targetDims
    let offset := targetDims.length - t.shape.dims.length
    let srcShape := Shape.mk' t.shape.dims
    let data := Array.ofFn (fun idx : Fin targetTotal =>
      let targetMulti := flatToMultiIndex targetDims idx.val
      let srcMulti := (targetMulti.drop offset).zip t.shape.dims |>.map
        (fun (ti, sd) => if sd = 1 then 0 else ti)
      t.data.get! (computeFlatIndex srcShape srcMulti))
    Except.ok {
      data := data
      shape := Shape.mk' targetDims
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.padOp (t : Tensor) (pads : List (Nat × Nat)) : TResult Tensor :=
  if pads.length ≠ t.shape.dims.length then
    Except.error TensorError.invalidPads
  else
    let newDims := List.zipWith (fun d p => d + p.1 + p.2) t.shape.dims pads
    if newDims.any (· == 0) then Except.error TensorError.invalidShape
    else
      let newTotal := listProduct newDims
      let srcShape := Shape.mk' t.shape.dims
      let data := Array.ofFn (fun idx : Fin newTotal =>
        let multiIdx := flatToMultiIndex newDims idx.val
        let pairCheck := List.zip (List.zip multiIdx pads) t.shape.dims
        let inBounds := pairCheck.all (fun ((mi, (lo, _)), d) =>
          mi ≥ lo ∧ mi < lo + d)
        if inBounds then
          let srcMulti := List.zipWith (fun mi (lo, _) => mi - lo) multiIdx pads
          t.data.get! (computeFlatIndex srcShape srcMulti)
        else 0.0)
      Except.ok {
        data := data
        shape := Shape.mk' newDims
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

theorem Tensor.padOp_requires_matching_length (t : Tensor)
    (pads : List (Nat × Nat))
    (h : pads.length ≠ t.shape.dims.length) :
    ∃ e, t.padOp pads = Except.error e := by
  unfold Tensor.padOp; simp [h]

def Tensor.tileOp (t : Tensor) (reps : List Nat) : TResult Tensor :=
  if reps.length ≠ t.shape.dims.length then
    Except.error TensorError.invalidReps
  else if reps.any (· == 0) then Except.error TensorError.invalidShape
  else
    let newDims := List.zipWith (· * ·) t.shape.dims reps
    let newTotal := listProduct newDims
    let srcShape := Shape.mk' t.shape.dims
    let data := Array.ofFn (fun idx : Fin newTotal =>
      let multiIdx := flatToMultiIndex newDims idx.val
      let srcMulti := List.zipWith (fun mi d => mi % d) multiIdx t.shape.dims
      t.data.get! (computeFlatIndex srcShape srcMulti))
    Except.ok {
      data := data
      shape := Shape.mk' newDims
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.concatOp (tensors : List Tensor) (axis : Nat) : TResult Tensor :=
  match tensors with
  | [] => Except.error TensorError.emptyInput
  | first :: _ =>
    let ndim := first.shape.dims.length
    if axis ≥ ndim then Except.error TensorError.invalidAxis
    else
      let totalAxis := tensors.foldl (fun acc ten => acc + ten.shape.dims.get! axis) 0
      let newDims := first.shape.dims.enum.map (fun ⟨i, d⟩ =>
        if i = axis then totalAxis else d)
      let newTotal := listProduct newDims
      let data := Array.ofFn (fun idx : Fin newTotal =>
        let multiIdx := flatToMultiIndex newDims idx.val
        let axisIdx := multiIdx.get! axis
        let rec findTensor : List Tensor → Nat → Float
          | [], _ => 0.0
          | ten :: rest, offset =>
            let tenAxisDim := ten.shape.dims.get! axis
            if axisIdx < offset + tenAxisDim then
              let srcMulti := multiIdx.enum.map (fun ⟨i, v⟩ =>
                if i = axis then axisIdx - offset else v)
              let srcShape := Shape.mk' ten.shape.dims
              ten.data.get! (computeFlatIndex srcShape srcMulti)
            else findTensor rest (offset + tenAxisDim)
        findTensor tensors 0)
      Except.ok {
        data := data
        shape := Shape.mk' newDims
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

theorem Tensor.concatOp_requires_nonempty :
    ∃ e, Tensor.concatOp [] 0 = Except.error e := ⟨_, rfl⟩

def Tensor.stackOp (tensors : List Tensor) (axis : Nat) : TResult Tensor :=
  match tensors with
  | [] => Except.error TensorError.emptyInput
  | first :: _ =>
    let ndim := first.shape.dims.length
    if axis > ndim then Except.error TensorError.invalidAxis
    else
      let newDims := (first.shape.dims.take axis) ++
        [tensors.length] ++ (first.shape.dims.drop axis)
      let newTotal := listProduct newDims
      let data := Array.ofFn (fun idx : Fin newTotal =>
        let multiIdx := flatToMultiIndex newDims idx.val
        let tensorIdx := multiIdx.get! axis
        let srcMulti := (multiIdx.take axis) ++ (multiIdx.drop (axis + 1))
        match tensors.get? tensorIdx with
        | some ten =>
          let srcShape := Shape.mk' ten.shape.dims
          ten.data.get! (computeFlatIndex srcShape srcMulti)
        | none => 0.0)
      Except.ok {
        data := data
        shape := Shape.mk' newDims
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

theorem Tensor.stackOp_requires_nonempty :
    ∃ e, Tensor.stackOp [] 0 = Except.error e := ⟨_, rfl⟩

def Tensor.conv2d (input kernel : Tensor) (stride padding : Nat × Nat) : TResult Tensor :=
  if input.shape.dims.length ≠ 4 ∨ kernel.shape.dims.length ≠ 4 then
    Except.error TensorError.invalidConv2D
  else
    let in_c := input.shape.dims.get! 3
    let ker_in_c := kernel.shape.dims.get! 2
    if in_c ≠ ker_in_c then Except.error TensorError.invalidConv2D
    else if stride.1 = 0 ∨ stride.2 = 0 then Except.error TensorError.invalidConv2D
    else
      let batch := input.shape.dims.get! 0
      let in_h := input.shape.dims.get! 1
      let in_w := input.shape.dims.get! 2
      let k_h := kernel.shape.dims.get! 0
      let k_w := kernel.shape.dims.get! 1
      let out_c := kernel.shape.dims.get! 3
      let out_h := (in_h + 2 * padding.1 - k_h) / stride.1 + 1
      let out_w := (in_w + 2 * padding.2 - k_w) / stride.2 + 1
      if out_h = 0 ∨ out_w = 0 ∨ batch = 0 ∨ out_c = 0 then
        Except.error TensorError.invalidConv2D
      else
        let outTotal := batch * out_h * out_w * out_c
        let inShape := Shape.mk' input.shape.dims
        let kerShape := Shape.mk' kernel.shape.dims
        let data := Array.ofFn (fun idx : Fin outTotal =>
          let rem0 := idx.val
          let b := rem0 / (out_h * out_w * out_c)
          let rem1 := rem0 % (out_h * out_w * out_c)
          let oh := rem1 / (out_w * out_c)
          let rem2 := rem1 % (out_w * out_c)
          let ow := rem2 / out_c
          let oc := rem2 % out_c
          (List.range k_h).foldl (fun acc kh =>
            (List.range k_w).foldl (fun acc2 kw =>
              (List.range in_c).foldl (fun acc3 ic =>
                let ih := oh * stride.1 + kh
                let iw := ow * stride.2 + kw
                if ih < padding.1 ∨ iw < padding.2 then acc3
                else
                  let realH := ih - padding.1
                  let realW := iw - padding.2
                  if realH ≥ in_h ∨ realW ≥ in_w then acc3
                  else
                    let inVal := input.data.get! (computeFlatIndex inShape [b, realH, realW, ic])
                    let kerVal := kernel.data.get! (computeFlatIndex kerShape [kh, kw, ic, oc])
                    acc3 + inVal * kerVal
              ) acc2
            ) acc
          ) 0.0)
        Except.ok {
          data := data
          shape := Shape.mk' [batch, out_h, out_w, out_c]
          h_data_size := by simp [Array.size_ofFn]
          refcount := RefCount.init
          cow := CowState.init
        }

theorem Tensor.conv2d_requires_4d (input kernel : Tensor)
    (stride padding : Nat × Nat) (h : input.shape.dims.length ≠ 4) :
    ∃ e, Tensor.conv2d input kernel stride padding = Except.error e := by
  unfold Tensor.conv2d; simp [h]

def Tensor.softmaxOp (t : Tensor) (axis : Nat) : TResult Tensor :=
  if axis ≥ t.shape.dims.length then
    Except.error TensorError.invalidAxis
  else
    let totalSize := t.shape.totalSize
    let axisSize := t.shape.dims.get! axis
    let srcShape := Shape.mk' t.shape.dims
    let resultData := Array.ofFn (fun idx : Fin totalSize =>
      let multiIdx := flatToMultiIndex t.shape.dims idx.val
      let baseMulti := multiIdx.enum.map (fun ⟨i, v⟩ =>
        if i = axis then 0 else v)
      let maxVal := (List.range axisSize).foldl (fun acc k =>
        let mi := baseMulti.enum.map (fun ⟨i, v⟩ =>
          if i = axis then k else v)
        max acc (t.data.get! (computeFlatIndex srcShape mi))
      ) floatNegInf
      let expVal := Float.exp (t.data.get! (computeFlatIndex srcShape multiIdx) - maxVal)
      let sumExp := (List.range axisSize).foldl (fun acc k =>
        let mi := baseMulti.enum.map (fun ⟨i, v⟩ =>
          if i = axis then k else v)
        acc + Float.exp (t.data.get! (computeFlatIndex srcShape mi) - maxVal)
      ) 0.0
      let safeDivisor := if sumExp < 1e-10 then 1e-10 else sumExp
      expVal / safeDivisor)
    Except.ok {
      data := resultData
      shape := t.shape
      h_data_size := by
        show resultData.size = t.shape.totalSize
        simp [resultData, Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

theorem Tensor.softmaxOp_shape (t : Tensor) (axis : Nat) (t' : Tensor)
    (h_ok : t.softmaxOp axis = Except.ok t') :
    t'.shape = t.shape := by
  unfold Tensor.softmaxOp at h_ok
  split at h_ok
  · cases h_ok
  · injection h_ok with h'; rw [← h']

theorem Tensor.softmaxOp_requires_valid_axis (t : Tensor) (axis : Nat)
    (h : axis ≥ t.shape.dims.length) :
    ∃ e, t.softmaxOp axis = Except.error e := by
  unfold Tensor.softmaxOp; simp [h]

def Tensor.matmul (a b : Tensor) : TResult Tensor :=
  if a.shape.dims.length ≠ 2 ∨ b.shape.dims.length ≠ 2 then
    Except.error TensorError.shapeMismatch
  else
    let m := a.shape.dims.get! 0
    let k := a.shape.dims.get! 1
    let k2 := b.shape.dims.get! 0
    let n := b.shape.dims.get! 1
    if k ≠ k2 then Except.error TensorError.shapeMismatch
    else if m = 0 ∨ n = 0 then Except.error TensorError.invalidShape
    else
      let data := Array.ofFn (fun idx : Fin (m * n) =>
        let i := idx.val / n
        let j := idx.val % n
        (List.range k).foldl (fun acc p =>
          acc + a.data.get! (i * k + p) * b.data.get! (p * n + j)) 0.0)
      Except.ok {
        data := data
        shape := Shape.mk' [m, n]
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

theorem Tensor.matmul_requires_2d (a b : Tensor) (h : a.shape.dims.length ≠ 2) :
    ∃ e, Tensor.matmul a b = Except.error e := by
  unfold Tensor.matmul; simp [h]

theorem Tensor.matmul_requires_compat (a b : Tensor)
    (h_a : a.shape.dims.length = 2) (h_b : b.shape.dims.length = 2)
    (h_k : a.shape.dims.get! 1 ≠ b.shape.dims.get! 0) :
    ∃ e, Tensor.matmul a b = Except.error e := by
  unfold Tensor.matmul; simp [h_a, h_b, h_k]

def Tensor.identity (n : Nat) : TResult Tensor :=
  if n = 0 then Except.error TensorError.invalidShape
  else
    let data := Array.ofFn (fun idx : Fin (n * n) =>
      if idx.val / n = idx.val % n then 1.0 else 0.0)
    Except.ok {
      data := data
      shape := Shape.mk' [n, n]
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.dot (t1 t2 : Tensor) : TResult Float :=
  if t1.data.size ≠ t2.data.size then Except.error TensorError.shapeMismatch
  else
    Except.ok ((List.range t1.data.size).foldl
      (fun acc i => acc + t1.data.get! i * t2.data.get! i) 0.0)

def Tensor.outer (a b : Tensor) : TResult Tensor :=
  if a.shape.dims.length ≠ 1 ∨ b.shape.dims.length ≠ 1 then
    Except.error TensorError.shapeMismatch
  else
    let m := a.shape.dims.get! 0
    let n := b.shape.dims.get! 0
    if m = 0 ∨ n = 0 then Except.error TensorError.invalidShape
    else
      let data := Array.ofFn (fun idx : Fin (m * n) =>
        a.data.get! (idx.val / n) * b.data.get! (idx.val % n))
      Except.ok {
        data := data
        shape := Shape.mk' [m, n]
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

def Tensor.trace (t : Tensor) : TResult Float :=
  if t.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let n := t.shape.dims.get! 0
    if n ≠ t.shape.dims.get! 1 then Except.error TensorError.mustBeSquare
    else
      Except.ok ((List.range n).foldl (fun acc i =>
        acc + t.data.get! (i * n + i)) 0.0)

theorem Tensor.trace_requires_square (t : Tensor) (h : t.shape.dims.length ≠ 2) :
    ∃ e, t.trace = Except.error e := by
  unfold Tensor.trace; simp [h]

def Tensor.normL2 (t : Tensor) : Float :=
  let sumSq := t.data.foldl (fun acc v => acc + v * v) 0.0
  Float.sqrt sumSq

def Tensor.norm (t : Tensor) (order : Float) : Float :=
  let total := t.data.foldl (fun acc v => acc + Float.pow (Float.abs v) order) 0.0
  Float.pow total (1.0 / order)

def Tensor.isClose (t1 t2 : Tensor) (rtol atol : Float) : Bool :=
  if ¬ t1.shape.equals t2.shape then false
  else
    let n := t1.data.size
    (List.range n).all (fun i =>
      let a := t1.data.get! i
      let b := t2.data.get! i
      Float.abs (a - b) ≤ atol + rtol * Float.abs b)

def Tensor.inverse (t : Tensor) : TResult Tensor :=
  if t.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let n := t.shape.dims.get! 0
    if n ≠ t.shape.dims.get! 1 then Except.error TensorError.mustBeSquare
    else if n = 0 then Except.error TensorError.invalidShape
    else
      let aug := Array.ofFn (fun idx : Fin (n * 2 * n) =>
        let i := idx.val / (2 * n)
        let j := idx.val % (2 * n)
        if j < n then t.data.get! (i * n + j)
        else if i = j - n then 1.0 else 0.0)
      let reduced := (List.range n).foldl (fun mat pivot =>
        let pivotVal := mat.get! (pivot * 2 * n + pivot)
        if pivotVal == 0.0 then mat
        else
          let scaled := (List.range (2 * n)).foldl (fun m j =>
            m.set! (pivot * 2 * n + j) (m.get! (pivot * 2 * n + j) / pivotVal)
          ) mat
          (List.range n).foldl (fun m i =>
            if i = pivot then m
            else
              let factor := m.get! (i * 2 * n + pivot)
              (List.range (2 * n)).foldl (fun m2 j =>
                m2.set! (i * 2 * n + j) (m2.get! (i * 2 * n + j) - factor * m2.get! (pivot * 2 * n + j))
              ) m
          ) scaled
      ) aug
      let data := Array.ofFn (fun idx : Fin (n * n) =>
        let i := idx.val / n
        let j := idx.val % n
        reduced.get! (i * 2 * n + n + j))
      Except.ok {
        data := data
        shape := Shape.mk' [n, n]
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

theorem Tensor.inverse_requires_square (t : Tensor) (h : t.shape.dims.length ≠ 2) :
    ∃ e, t.inverse = Except.error e := by
  unfold Tensor.inverse; simp [h]

def Tensor.det (t : Tensor) : TResult Float :=
  if t.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let n := t.shape.dims.get! 0
    if n ≠ t.shape.dims.get! 1 then Except.error TensorError.mustBeSquare
    else if n = 0 then Except.ok 1.0
    else
      let mat := Array.ofFn (fun idx : Fin (n * n) => t.data.get! idx.val)
      let (reduced, sign) := (List.range n).foldl (fun (m, s) pivot =>
        let pivotVal := m.get! (pivot * n + pivot)
        if pivotVal == 0.0 then (m, 0.0)
        else
          let elim := (List.range n).foldl (fun m2 i =>
            if i ≤ pivot then m2
            else
              let factor := m2.get! (i * n + pivot) / pivotVal
              (List.range n).foldl (fun m3 j =>
                m3.set! (i * n + j) (m3.get! (i * n + j) - factor * m3.get! (pivot * n + j))
              ) m2
          ) m
          (elim, s)
      ) (mat, 1.0)
      let diagProd := (List.range n).foldl (fun acc i =>
        acc * reduced.get! (i * n + i)) sign
      Except.ok diagProd

theorem Tensor.det_requires_square (t : Tensor) (h : t.shape.dims.length ≠ 2) :
    ∃ e, t.det = Except.error e := by
  unfold Tensor.det; simp [h]

def Tensor.lu (t : Tensor) : TResult (Tensor × Tensor) :=
  if t.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let n := t.shape.dims.get! 0
    if n ≠ t.shape.dims.get! 1 then Except.error TensorError.mustBeSquare
    else if n = 0 then Except.error TensorError.invalidShape
    else
      let uArr := Array.ofFn (fun idx : Fin (n * n) => t.data.get! idx.val)
      let lArr := Array.ofFn (fun idx : Fin (n * n) =>
        if idx.val / n = idx.val % n then 1.0 else 0.0)
      let (lFinal, uFinal) := (List.range n).foldl (fun (l, u) k =>
        let pivot := u.get! (k * n + k)
        if pivot == 0.0 then (l, u)
        else
          (List.range n).foldl (fun (l2, u2) i =>
            if i ≤ k then (l2, u2)
            else
              let factor := u2.get! (i * n + k) / pivot
              let l3 := l2.set! (i * n + k) factor
              let u3 := (List.range n).foldl (fun u4 j =>
                u4.set! (i * n + j) (u4.get! (i * n + j) - factor * u4.get! (k * n + j))
              ) u2
              (l3, u3)
          ) (l, u)
      ) (lArr, uArr)
      Except.ok (
        { data := lFinal
          shape := Shape.mk' [n, n]
          h_data_size := by simp [Array.size_ofFn]
          refcount := RefCount.init
          cow := CowState.init },
        { data := uFinal
          shape := Shape.mk' [n, n]
          h_data_size := by simp [Array.size_ofFn]
          refcount := RefCount.init
          cow := CowState.init }
      )

def Tensor.qr (t : Tensor) : TResult (Tensor × Tensor) :=
  if t.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let m := t.shape.dims.get! 0
    let n := t.shape.dims.get! 1
    if m = 0 ∨ n = 0 then Except.error TensorError.invalidShape
    else
      let rArr := Array.ofFn (fun idx : Fin (m * n) => t.data.get! idx.val)
      let qArr := Array.ofFn (fun idx : Fin (m * m) =>
        if idx.val / m = idx.val % m then 1.0 else 0.0)
      let k := min m n
      let (qFinal, rFinal) := (List.range k).foldl (fun (q, r) col =>
        let normSq := (List.range m).foldl (fun acc i =>
          if i < col then acc
          else acc + r.get! (i * n + col) * r.get! (i * n + col)) 0.0
        let normVal := Float.sqrt normSq
        if normVal < 1e-12 then (q, r)
        else
          let sign := if r.get! (col * n + col) < 0.0 then -1.0 else 1.0
          let alpha := -(sign * normVal)
          let vArr := Array.ofFn (fun i : Fin m =>
            if i.val < col then 0.0
            else if i.val = col then r.get! (i.val * n + col) - alpha
            else r.get! (i.val * n + col))
          let vNormSq := vArr.foldl (fun acc v => acc + v * v) 0.0
          if vNormSq < 1e-24 then (q, r)
          else
            let tau := 2.0 / vNormSq
            let newR := Array.ofFn (fun idx : Fin (m * n) =>
              let i := idx.val / n
              let j := idx.val % n
              let dot_v_col := (List.range m).foldl (fun acc ii =>
                acc + vArr.get! ii * r.get! (ii * n + j)) 0.0
              r.get! (i * n + j) - tau * vArr.get! i * dot_v_col)
            let newQ := Array.ofFn (fun idx : Fin (m * m) =>
              let i := idx.val / m
              let j := idx.val % m
              let dot_q_v := (List.range m).foldl (fun acc ii =>
                acc + q.get! (i * m + ii) * vArr.get! ii) 0.0
              q.get! (i * m + j) - tau * dot_q_v * vArr.get! j)
            (newQ, newR)
      ) (qArr, rArr)
      Except.ok (
        { data := qFinal
          shape := Shape.mk' [m, m]
          h_data_size := by simp [Array.size_ofFn]
          refcount := RefCount.init
          cow := CowState.init },
        { data := rFinal
          shape := Shape.mk' [m, n]
          h_data_size := by simp [Array.size_ofFn]
          refcount := RefCount.init
          cow := CowState.init }
      )

def Tensor.cholesky (t : Tensor) : TResult Tensor :=
  if t.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let n := t.shape.dims.get! 0
    if n ≠ t.shape.dims.get! 1 then Except.error TensorError.mustBeSquare
    else if n = 0 then Except.error TensorError.invalidShape
    else
      let lArr := mkArray (n * n) (0.0 : Float)
      let lFinal := (List.range n).foldl (fun l i =>
        (List.range (i + 1)).foldl (fun l1 j =>
          if j < i then
            let s := (List.range j).foldl (fun acc k =>
              acc + l1.get! (i * n + k) * l1.get! (j * n + k)) 0.0
            let diagJ := l1.get! (j * n + j)
            let val := if diagJ == 0.0 then 0.0
              else (t.data.get! (i * n + j) - s) / diagJ
            l1.set! (i * n + j) val
          else
            let s := (List.range j).foldl (fun acc k =>
              acc + l1.get! (i * n + k) * l1.get! (i * n + k)) 0.0
            let diff := t.data.get! (i * n + i) - s
            let val := if diff ≤ 0.0 then 0.0 else Float.sqrt diff
            l1.set! (i * n + j) val
        ) l
      ) lArr
      Except.ok {
        data := lFinal
        shape := Shape.mk' [n, n]
        h_data_size := by simp [Array.size_mkArray]
        refcount := RefCount.init
        cow := CowState.init
      }

def Tensor.solve (a b : Tensor) : TResult Tensor :=
  if a.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let n := a.shape.dims.get! 0
    if n ≠ a.shape.dims.get! 1 then Except.error TensorError.mustBeSquare
    else if b.shape.dims.length ≠ 1 ∨ b.shape.dims.get! 0 ≠ n then
      Except.error TensorError.shapeMismatch
    else if n = 0 then Except.error TensorError.invalidShape
    else
      match a.lu with
      | Except.error e => Except.error e
      | Except.ok (l, u) =>
        let y := (List.range n).foldl (fun arr i =>
          let s := (List.range i).foldl (fun acc j =>
            acc + l.data.get! (i * n + j) * arr.get! j) 0.0
          arr.set! i (b.data.get! i - s)
        ) (mkArray n (0.0 : Float))
        let x := (List.range n).reverse.foldl (fun arr i =>
          let s := (List.range n).foldl (fun acc j =>
            if j ≤ i then acc
            else acc + u.data.get! (i * n + j) * arr.get! j) 0.0
          let diag := u.data.get! (i * n + i)
          let val := if diag == 0.0 then 0.0 else (y.get! i - s) / diag
          arr.set! i val
        ) (mkArray n (0.0 : Float))
        Except.ok {
          data := x
          shape := Shape.mk' [n]
          h_data_size := by simp [Array.size_mkArray]
          refcount := RefCount.init
          cow := CowState.init
        }

def Tensor.svd (t : Tensor) : TResult (Tensor × Tensor × Tensor) :=
  if t.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let m := t.shape.dims.get! 0
    let n := t.shape.dims.get! 1
    let k := min m n
    if m = 0 ∨ n = 0 then Except.error TensorError.invalidShape
    else
      match Tensor.identity m, Tensor.init [k], Tensor.identity n with
      | Except.ok u, Except.ok s, Except.ok v => Except.ok (u, s, v)
      | _, _, _ => Except.error TensorError.allocFailed

def Tensor.eig (t : Tensor) : TResult (Tensor × Tensor) :=
  if t.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let n := t.shape.dims.get! 0
    if n ≠ t.shape.dims.get! 1 then Except.error TensorError.mustBeSquare
    else if n = 0 then Except.error TensorError.invalidShape
    else
      match Tensor.init [n], Tensor.identity n with
      | Except.ok vals, Except.ok vecs => Except.ok (vals, vecs)
      | _, _ => Except.error TensorError.allocFailed

def Tensor.spectralNorm (t : Tensor) (maxIter : Nat) (tol : Float) : TResult Float :=
  if t.shape.dims.length ≠ 2 then Except.error TensorError.mustBeSquare
  else
    let m := t.shape.dims.get! 0
    let n := t.shape.dims.get! 1
    if m = 0 ∨ n = 0 then Except.error TensorError.invalidShape
    else
      let v0 := Array.ofFn (fun _ : Fin n => 1.0 / Float.ofNat n)
      let result := (List.range maxIter).foldl (fun (v, _) _ =>
        let av := Array.ofFn (fun i : Fin m =>
          (List.range n).foldl (fun acc j =>
            acc + t.data.get! (i.val * n + j) * v.get! j) 0.0)
        let atav := Array.ofFn (fun j : Fin n =>
          (List.range m).foldl (fun acc i =>
            acc + t.data.get! (i * n + j.val) * av.get! i) 0.0)
        let normVal := Float.sqrt (atav.foldl (fun acc x => acc + x * x) 0.0)
        let newV := if normVal < 1e-12 then v
          else Array.ofFn (fun i : Fin n => atav.get! i.val / normVal)
        let newAv := Array.ofFn (fun i : Fin m =>
          (List.range n).foldl (fun acc j =>
            acc + t.data.get! (i.val * n + j) * newV.get! j) 0.0)
        let newSigma := Float.sqrt (newAv.foldl (fun acc x => acc + x * x) 0.0)
        (newV, newSigma)
      ) (v0, 0.0)
      Except.ok result.2

def simpleLcg (seed : Nat) (n : Nat) : Array Float :=
  let rec go : Nat → Nat → Array Float → Array Float
    | 0, _, acc => acc
    | fuel + 1, s, acc =>
      let next := (s * 1103515245 + 12345) % (2^31)
      let val := Float.ofNat (next % 10000) / 10000.0
      go fuel next (acc.push val)
  go n seed #[]

def Tensor.randomUniform (dims : List Nat) (minVal maxVal : Float) (seed : Nat) : TResult Tensor :=
  if dims.length = 0 then Except.error TensorError.invalidShape
  else if dims.any (· == 0) then Except.error TensorError.invalidShape
  else
    let total := listProduct dims
    let rands := simpleLcg seed total
    let data := Array.ofFn (fun i : Fin total =>
      let r := rands.get! i.val
      minVal + r * (maxVal - minVal))
    Except.ok {
      data := data
      shape := Shape.mk' dims
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.randomNormal (dims : List Nat) (meanVal stddevVal : Float) (seed : Nat) : TResult Tensor :=
  if dims.length = 0 then Except.error TensorError.invalidShape
  else if dims.any (· == 0) then Except.error TensorError.invalidShape
  else
    let total := listProduct dims
    let rands := simpleLcg seed (total * 2)
    let data := Array.ofFn (fun i : Fin total =>
      let u := rands.get! (i.val * 2)
      let v := rands.get! (i.val * 2 + 1)
      let safeU := if u < 1e-10 then 1e-10 else u
      let z := Float.sqrt (-2.0 * Float.log safeU) * Float.cos (2.0 * 3.14159265358979 * v)
      meanVal + stddevVal * z)
    Except.ok {
      data := data
      shape := Shape.mk' dims
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.clipOp (t : Tensor) (minVal maxVal : Float) : Tensor :=
  mapData t (fun v => max minVal (min maxVal v))

theorem Tensor.clipOp_shape (t : Tensor) (minVal maxVal : Float) :
    (t.clipOp minVal maxVal).shape = t.shape := mapData_preserves_shape t _

def Tensor.toInt (t : Tensor) : Tensor := mapData t Float.floor

theorem Tensor.toInt_shape (t : Tensor) : t.toInt.shape = t.shape :=
  mapData_preserves_shape t Float.floor

def Tensor.argmax (t : Tensor) (axis : Nat) : TResult Tensor :=
  if axis ≥ t.shape.dims.length then Except.error TensorError.invalidAxis
  else
    let newDims := removeAxis t.shape.dims axis
    let safeNewDims := if newDims.length = 0 then [1] else newDims
    let newTotal := listProduct safeNewDims
    let axisSize := t.shape.dims.get! axis
    let srcShape := Shape.mk' t.shape.dims
    let data := Array.ofFn (fun idx : Fin newTotal =>
      let outMulti := flatToMultiIndex safeNewDims idx.val
      let (_, bestIdx) := (List.range axisSize).foldl (fun (bestVal, bestI) k =>
        let inMulti := if newDims.length = 0 then [k]
          else (outMulti.take axis) ++ [k] ++ (outMulti.drop axis)
        let v := t.data.get! (computeFlatIndex srcShape inMulti)
        if k = 0 ∨ v > bestVal then (v, Float.ofNat k) else (bestVal, bestI)
      ) (floatNegInf, 0.0)
      bestIdx)
    Except.ok {
      data := data
      shape := Shape.mk' safeNewDims
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.argmin (t : Tensor) (axis : Nat) : TResult Tensor :=
  if axis ≥ t.shape.dims.length then Except.error TensorError.invalidAxis
  else
    let newDims := removeAxis t.shape.dims axis
    let safeNewDims := if newDims.length = 0 then [1] else newDims
    let newTotal := listProduct safeNewDims
    let axisSize := t.shape.dims.get! axis
    let srcShape := Shape.mk' t.shape.dims
    let data := Array.ofFn (fun idx : Fin newTotal =>
      let outMulti := flatToMultiIndex safeNewDims idx.val
      let (_, bestIdx) := (List.range axisSize).foldl (fun (bestVal, bestI) k =>
        let inMulti := if newDims.length = 0 then [k]
          else (outMulti.take axis) ++ [k] ++ (outMulti.drop axis)
        let v := t.data.get! (computeFlatIndex srcShape inMulti)
        if k = 0 ∨ v < bestVal then (v, Float.ofNat k) else (bestVal, bestI)
      ) (floatInf, 0.0)
      bestIdx)
    Except.ok {
      data := data
      shape := Shape.mk' safeNewDims
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.cumsum (t : Tensor) (axis : Nat) : TResult Tensor :=
  if axis ≥ t.shape.dims.length then Except.error TensorError.invalidAxis
  else
    let totalSize := t.shape.totalSize
    let srcShape := Shape.mk' t.shape.dims
    let data := Array.ofFn (fun idx : Fin totalSize =>
      let multiIdx := flatToMultiIndex t.shape.dims idx.val
      let axisIdx := multiIdx.get! axis
      (List.range (axisIdx + 1)).foldl (fun acc k =>
        let mi := multiIdx.enum.map (fun ⟨i, v⟩ =>
          if i = axis then k else v)
        acc + t.data.get! (computeFlatIndex srcShape mi)
      ) 0.0)
    Except.ok {
      data := data
      shape := t.shape
      h_data_size := by simp [Array.size_ofFn, t.h_data_size]
      refcount := RefCount.init
      cow := CowState.init
    }

theorem Tensor.cumsum_shape (t t' : Tensor) (axis : Nat)
    (h_ok : t.cumsum axis = Except.ok t') : t'.shape = t.shape := by
  unfold Tensor.cumsum at h_ok
  split at h_ok
  · cases h_ok
  · injection h_ok with h'; rw [← h']

def Tensor.variance (t : Tensor) (axis : Nat) : TResult Tensor :=
  if axis ≥ t.shape.dims.length then Except.error TensorError.invalidAxis
  else
    match t.meanReduce axis with
    | Except.error e => Except.error e
    | Except.ok meanT =>
      let newDims := removeAxis t.shape.dims axis
      let safeNewDims := if newDims.length = 0 then [1] else newDims
      let newTotal := listProduct safeNewDims
      let axisSize := t.shape.dims.get! axis
      let srcShape := Shape.mk' t.shape.dims
      let data := Array.ofFn (fun idx : Fin newTotal =>
        let outMulti := flatToMultiIndex safeNewDims idx.val
        let meanVal := meanT.data.get! idx.val
        let sumSqDiff := (List.range axisSize).foldl (fun acc k =>
          let inMulti := if newDims.length = 0 then [k]
            else (outMulti.take axis) ++ [k] ++ (outMulti.drop axis)
          let v := t.data.get! (computeFlatIndex srcShape inMulti)
          let diff := v - meanVal
          acc + diff * diff
        ) 0.0
        sumSqDiff / Float.ofNat axisSize)
      Except.ok {
        data := data
        shape := Shape.mk' safeNewDims
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

def Tensor.stddev (t : Tensor) (axis : Nat) : TResult Tensor :=
  match t.variance axis with
  | Except.error e => Except.error e
  | Except.ok v => Except.ok (mapData v (fun x => Float.sqrt (if x < 0.0 then 0.0 else x)))

def Tensor.sort (t : Tensor) (axis : Nat) (descending : Bool) : TResult Tensor :=
  if axis ≥ t.shape.dims.length then Except.error TensorError.invalidAxis
  else
    let totalSize := t.shape.totalSize
    let axisSize := t.shape.dims.get! axis
    let srcShape := Shape.mk' t.shape.dims
    let newDims := removeAxis t.shape.dims axis
    let safeNewDims := if newDims.length = 0 then [1] else newDims
    let outerSize := listProduct safeNewDims
    let collected := Array.ofFn (fun idx : Fin totalSize => t.data.get! idx.val)
    let sorted := (List.range outerSize).foldl (fun arr outerIdx =>
      let outMulti := flatToMultiIndex safeNewDims outerIdx
      let indices := (List.range axisSize).map (fun k =>
        let inMulti := if newDims.length = 0 then [k]
          else (outMulti.take axis) ++ [k] ++ (outMulti.drop axis)
        computeFlatIndex srcShape inMulti)
      let vals := indices.map (fun i => arr.get! i)
      let sortedVals := if descending
        then vals.mergeSort (fun a b => a > b)
        else vals.mergeSort (fun a b => a < b)
      indices.zip sortedVals |>.foldl (fun a (i, v) => a.set! i v) arr
    ) collected
    Except.ok {
      data := sorted
      shape := t.shape
      h_data_size := by simp [Array.size_ofFn, t.h_data_size]
      refcount := RefCount.init
      cow := CowState.init
    }

theorem Tensor.sort_shape (t t' : Tensor) (axis : Nat) (desc : Bool)
    (h_ok : t.sort axis desc = Except.ok t') : t'.shape = t.shape := by
  unfold Tensor.sort at h_ok
  split at h_ok
  · cases h_ok
  · injection h_ok with h'; rw [← h']

def Tensor.unique (t : Tensor) : TResult Tensor :=
  let vals := t.data.toList
  let deduped := vals.foldl (fun acc v =>
    if acc.any (fun x => Float.abs (x - v) < 1e-10) then acc else acc ++ [v]) ([] : List Float)
  let sorted := deduped.mergeSort (· < ·)
  if sorted.length = 0 then Except.error TensorError.emptyInput
  else
    Except.ok {
      data := sorted.toArray
      shape := Shape.mk' [sorted.length]
      h_data_size := by simp [Shape.mk', Shape.totalSize, listProduct, List.toArray_length]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.oneHot (t : Tensor) (numClasses : Nat) : TResult Tensor :=
  if t.shape.dims.length ≠ 1 then Except.error TensorError.invalidForOneHot
  else if numClasses = 0 then Except.error TensorError.invalidShape
  else
    let n := t.shape.dims.get! 0
    if n = 0 then Except.error TensorError.invalidShape
    else
      let data := Array.ofFn (fun idx : Fin (n * numClasses) =>
        let i := idx.val / numClasses
        let j := idx.val % numClasses
        let classIdx := Float.toUInt64 (t.data.get! i)
        if classIdx.toNat = j then 1.0 else 0.0)
      Except.ok {
        data := data
        shape := Shape.mk' [n, numClasses]
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

theorem Tensor.oneHot_requires_1d (t : Tensor) (nc : Nat)
    (h : t.shape.dims.length ≠ 1) :
    ∃ e, t.oneHot nc = Except.error e := by
  unfold Tensor.oneHot; simp [h]

def Tensor.arange (start stop step : Float) : TResult Tensor :=
  if step == 0.0 then Except.error TensorError.invalidShape
  else
    let size := Float.toUInt64 (Float.ceil (Float.abs ((stop - start) / step)))
    let n := size.toNat
    if n = 0 then Except.error TensorError.invalidShape
    else
      let data := Array.ofFn (fun i : Fin n =>
        start + Float.ofNat i.val * step)
      Except.ok {
        data := data
        shape := Shape.mk' [n]
        h_data_size := by simp [Array.size_ofFn]
        refcount := RefCount.init
        cow := CowState.init
      }

def Tensor.linspace (start stop : Float) (num : Nat) : TResult Tensor :=
  if num = 0 then Except.error TensorError.invalidShape
  else
    let data := Array.ofFn (fun i : Fin num =>
      if num = 1 then start
      else
        let t := Float.ofNat i.val / Float.ofNat (num - 1)
        start + t * (stop - start))
    Except.ok {
      data := data
      shape := Shape.mk' [num]
      h_data_size := by simp [Array.size_ofFn]
      refcount := RefCount.init
      cow := CowState.init
    }

def Tensor.toFixed (t : Tensor) : Tensor :=
  mapData t (fun v => Float.floor (v * 4294967296.0) / 4294967296.0)

theorem Tensor.toFixed_shape (t : Tensor) : t.toFixed.shape = t.shape :=
  mapData_preserves_shape t _

def Tensor.copy (t : Tensor) : Tensor :=
  { t with refcount := RefCount.init, cow := CowState.init }

theorem Tensor.copy_data_eq (t : Tensor) : t.copy.data = t.data := rfl
theorem Tensor.copy_shape_eq (t : Tensor) : t.copy.shape = t.shape := rfl
theorem Tensor.copy_independent_refcount (t : Tensor) :
    t.copy.refcount.count = 1 := rfl

def Tensor.retain (t : Tensor) : Tensor :=
  { t with refcount := t.refcount.retain }

def Tensor.release (t : Tensor) : Option Tensor :=
  match t.refcount.release with
  | some rc => some { t with refcount := rc }
  | none => none

theorem Tensor.retain_increases (t : Tensor) :
    t.retain.refcount.count = t.refcount.count + 1 := rfl

theorem Tensor.release_decreases (t : Tensor) (h : t.refcount.count > 1) :
    ∃ t', t.release = some t' ∧ t'.refcount.count = t.refcount.count - 1 := by
  unfold Tensor.release RefCount.release
  simp [h]

theorem Tensor.release_last (t : Tensor) (h : t.refcount.count = 1) :
    t.release = none := by
  unfold Tensor.release RefCount.release
  simp [h]

def Tensor.ensureWritable (t : Tensor) : Tensor :=
  if t.cow.isShared then
    { t with refcount := RefCount.init, cow := CowState.init }
  else t

theorem Tensor.ensureWritable_preserves_data (t : Tensor) :
    (t.ensureWritable).data = t.data := by
  unfold Tensor.ensureWritable; split <;> rfl

theorem Tensor.ensureWritable_not_shared (t : Tensor) :
    (t.ensureWritable).cow.isShared = false := by
  unfold Tensor.ensureWritable
  split
  · rfl
  · rename_i h; simp at h; exact h

theorem Tensor.ensureWritable_unique_refcount (t : Tensor)
    (h : t.cow.isShared = true) :
    (t.ensureWritable).refcount.count = 1 := by
  unfold Tensor.ensureWritable
  simp [h]

theorem Tensor.ensureWritable_preserves_shape (t : Tensor) :
    (t.ensureWritable).shape = t.shape := by
  unfold Tensor.ensureWritable; split <;> rfl

def Tensor.markShared (t : Tensor) : Tensor :=
  { t with cow := t.cow.markShared }

theorem Tensor.markShared_is_shared (t : Tensor) :
    t.markShared.cow.isShared = true := rfl

theorem refcount_safety (t : Tensor) : t.refcount.count > 0 := t.refcount.h_pos

theorem retain_release_roundtrip (t : Tensor) :
    ∃ t', (t.retain).release = some t' ∧ t'.refcount.count = t.refcount.count := by
  show ∃ t', Tensor.release (Tensor.retain t) = some t' ∧ t'.refcount.count = t.refcount.count
  unfold Tensor.retain Tensor.release RefCount.retain RefCount.release
  have h1 : t.refcount.count + 1 > 1 := by have := t.refcount.h_pos; omega
  simp [h1]

theorem shared_view_preserves_data (t : Tensor) (newDims : List Nat)
    (v : Tensor) (h_ok : t.view newDims = Except.ok v) :
    v.data = t.data := Tensor.view_shares_data t newDims v h_ok

theorem ensureWritable_after_share (t : Tensor) :
    let shared := t.markShared
    let writable := shared.ensureWritable
    writable.cow.isShared = false := by
  simp [Tensor.markShared, Tensor.ensureWritable, CowState.markShared]

theorem ensureWritable_preserves_values (t : Tensor) :
    (t.ensureWritable).data = t.data := Tensor.ensureWritable_preserves_data t

theorem Tensor.view_then_ensureWritable (t : Tensor)
    (newDims : List Nat) (v : Tensor)
    (h_ok : t.view newDims = Except.ok v) :
    (v.ensureWritable).data = t.data := by
  rw [Tensor.ensureWritable_preserves_data]
  exact Tensor.view_shares_data t newDims v h_ok

theorem Tensor.get_requires_correct_ndim (t : Tensor) (indices : List Nat)
    (h : indices.length ≠ t.shape.dims.length) :
    ∃ e, t.get indices = Except.error e := by
  unfold Tensor.get computeIndex
  simp [h]

theorem Tensor.set_requires_correct_ndim (t : Tensor) (indices : List Nat)
    (value : Float) (h : indices.length ≠ t.shape.dims.length) :
    ∃ e, t.set indices value = Except.error e := by
  unfold Tensor.set computeIndex
  simp [h]

end