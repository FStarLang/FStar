module FStar.Compiler.MachineInts

open FStar
open FStar.Compiler
open FStar.Compiler.Effect

module EMB = FStar.Syntax.Embeddings
module NBE = FStar.TypeChecker.NBETerm
module S  = FStar.Syntax.Syntax
module Z = FStar.BigInt

open FStar.Class.Show

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
val widthn (k : machint_kind) : int
val module_name_for (k:machint_kind) : string 
val mask (k:machint_kind) : Z.t

new val machint (k : machint_kind) : Type0

val mk (#k:_) (i : Z.t) : machint k // no checks at all, use with care
val v #k (x : machint k) : Z.t
val int_to_t #k (i : Z.t) : machint k

(* Make a machint k copying the meta off an existing one *)
val make_as #k (x : machint k) (z : Z.t) : machint k

instance val showable_bounded_k k : Tot (showable (machint k))
instance val e_machint (k : machint_kind) : Tot (EMB.embedding (machint k))

instance val nbe_machint (k : machint_kind) : Tot (NBE.embedding (machint k))
// ^ This instance being here is slightly fishy. It blows up the dependency
// graph of this module.
