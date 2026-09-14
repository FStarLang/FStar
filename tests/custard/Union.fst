module Union

module U32 = FStar.UInt32
module U64 = FStar.UInt64

/// Sections 113 and 114.  The member of a tagged union is named after the
/// constructor alone, and a constructor carrying exactly one field is the
/// member itself.
///
/// The member used to carry the monomorphizer's specialization suffix, which
/// warning 377 says a consumer must not depend on -- and the escape the
/// warning offers, naming it once in a [typedef], exists for types and not
/// for members.  The member is already scoped by the union, whose arms are
/// the constructors of one variant and so distinct by construction, and the
/// enclosing struct's *type* name still carries the full specialization.

/// One field: the member is the payload.
type ei =
  | L : l:U32.t -> ei
  | R : r:U64.t -> ei

let get_ei (e : ei) : U64.t =
  match e with
  | L l -> FStar.Int.Cast.uint32_to_uint64 l
  | R r -> r

/// Two fields: the struct is what a struct is for, and stays.
type two =
  | A : x:U32.t -> y:U32.t -> two
  | B : z:U32.t -> two

let get_two (t : two) : U32.t =
  match t with
  | A x y -> U32.add_mod x y
  | B z -> z

/// A fieldless constructor alongside a payload one, which is [option]'s
/// shape and the commonest in generated parser output.
type opt =
  | Nothing
  | Just : v:U32.t -> opt

let get_opt (o : opt) : U32.t =
  match o with
  | Nothing -> 0ul
  | Just v -> v

/// The library [option], whose arm is the one that used to read
/// [.val.FStar_Pervasives_Native_Some__uint32_t.v].
let get_lib (o : option U32.t) : U32.t =
  match o with
  | None -> 0ul
  | Some v -> v

/// §107's generated equality reaches through the same selector, so a flat
/// arm has to be compared as the member rather than as a field of it.
let same (a : ei) (b : ei) : bool = a = b

let main () : FStar.All.ML FStar.Int32.t =
  if U64.eq (get_ei (L 4ul)) 4uL && U64.eq (get_ei (R 9uL)) 9uL &&
     U32.eq (get_two (A 1ul 2ul)) 3ul && U32.eq (get_two (B 5ul)) 5ul &&
     U32.eq (get_opt (Just 7ul)) 7ul && U32.eq (get_opt Nothing) 0ul &&
     U32.eq (get_lib (Some 8ul)) 8ul && same (L 4ul) (L 4ul) &&
     not (same (L 4ul) (R 4uL))
  then 0l else 1l
