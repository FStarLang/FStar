module FStarC.MachineInts

open FStarC
open FStarC.Effect

module EMB = FStarC.Syntax.Embeddings
module NBE = FStarC.TypeChecker.NBETerm
module S  = FStarC.Syntax.Syntax
module Z = FStarC.BigInt

open FStarC.Class.Show

type machint_kind =
  | Int8
  | Int16
  | Int32
  | Int64
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | UInt128
  | SizeT

val all_machint_kinds : list machint_kind

val is_unsigned (k : machint_kind) : bool
val is_signed (k : machint_kind) : bool
val width (k : machint_kind) : int
val module_name_for (k:machint_kind) : string 
val mask (k:machint_kind) : Z.t

new val machint (k : machint_kind) : Type0

val mk (#k:_) (i : Z.t) (m : option S.meta_source_info) : machint k // no checks at all, use with care
val v #k (x : machint k) : Z.t
val meta #k (x : machint k) : option S.meta_source_info

(* Make a machint k copying the meta off an existing one *)
val make_as #k (x : machint k) (z : Z.t) : machint k

instance val showable_bounded_k k : Tot (showable (machint k))
instance val e_machint (k : machint_kind) : Tot (EMB.embedding (machint k))

instance val nbe_machint (k : machint_kind) : Tot (NBE.embedding (machint k))
// ^ This instance being here is slightly fishy. It blows up the dependency
// graph of this module.
