(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Misc

(* Miscellaneous code snippets from ulib *)

(* TODO: move to FStar.Reflection.Basic? *)
(** [push_binder] extends the environment with a single binder. *)
let ne e1 e2 = CompProp e1 C_Ne e2

(* comment *)
assume new
type eq : #a: Type -> #m: nat -> #n: nat -> matrix2 m n a -> matrix2 m n a -> Type 

let ne e1 e2 = CompProp e1 C_Ne e2
let gt e1 e2 = CompProp e1 C_Gt e2
let ge e1 e2 = CompProp (Plus (Lit 1) e1) C_Gt e2
private
let return (x: 'a) : tm 'a = fun i -> Inr (x, i)
private
let bind (m: tm 'a) (f: ('a -> tm 'b)) : tm 'b =
  fun i ->
    match m i with
    | Inr (x, j) -> f x j
    | s ->
      // why? To have a catch-all pattern and thus an easy WP
      Inl (Inl?.v s)
private
let tm a = st -> Tac (either string (a * st))
private
let return (x: 'a) : tm 'a = fun i -> Inr (x, i)

(* Define a traversal monad! Makes exception handling and counter-keeping easy *)
let st = p: (nat * list term){fst p == List.length (snd p)}
let tm a = st -> Tac (either string (a * st))

let return (x: 'a) : tm 'a = fun i -> Inr (x, i)
let bind (m: tm 'a) (f: ('a -> tm 'b)) : tm 'b =
  fun i ->
    match m i with
    | Inr (x, j) -> f x j
    | s ->
      // why? To have a catch-all pattern and thus an easy WP
      Inl (Inl?.v s)
let tm a = st -> Tac (either string (a * st))
let return (x: 'a) : tm 'a = fun i -> Inr (x, i)

(* TODO: move to FStar.Reflection.Basic? *)
(** [push_binder] extends the environment with a single binder.
    This is useful as one traverses the syntax of a term,
    pushing binders as one traverses a binder in a lambda,
    match, etc. Note, the environment here is disconnected to
    (though perhaps derived from) the environment in the proofstate *)
assume
val push_binder: env -> binder -> env

(* TODO: move to FStar.Reflection.Basic? *)
(** [push_binder] extends the environment with a single binder.
    This is useful as one traverses the syntax of a term,
    pushing binders as one traverses a binder in a lambda,
    match, etc. Note, the environment here is disconnected to
    (though perhaps derived from) the environment in the proofstate *)
val push_binder: env -> binder -> env

(*
//  * AR: (may be this is an overkill)
 beforehand
//  *)
(** TODO: we need dependent functional extensionality *)


[@ "opaque_to_smt"]
unfold private
let equal_heap_dom (r: rid) (m0 m1: mem) : Type0 = Heap.equal_dom (Map.sel m0.h r) (Map.sel m1.h r)

(*** Semantics of pointers *)

(** Pointer paths *)

(* random comment *)
let step_sel = 1

(** TODO: we need dependent functional extensionality *)

assume
val equal_elim (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value)
    : Lemma (requires (equal m1 m2)) (ensures (m1 == m2)) [SMTPat (equal m1 m2)]

(** TODO: we need dependent functional extensionality *)
assume
val equal_elim (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value)
    : Lemma (requires (equal m1 m2)) (ensures (m1 == m2)) [SMTPat (equal m1 m2)]

(** TODO: we need dependent functional extensionality *)

val equal_elim (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value)
    : Lemma (requires (equal m1 m2)) (ensures (m1 == m2)) [SMTPat (equal m1 m2)]

let f (x y: int) = x + y

val admit_dump:
    #a: Type ->
    (#[(dump "Admitting";
        exact (quote (fun () -> admit #a () <: Admit a)))]
      x:
      (unit -> Admit a)) ->
    unit
  -> Admit a
let admit_dump #a #x () = x ()
unfold
let solve (#a: Type) (#[tcresolve ()] ev: a) : Tot a = ev

/// `slice v i j`:
///     the sub-vector of `v` starting from index `i` up to, but not including, `j`
unfold
let slice (#a: Type) (x: t a) (i: len_t) (j: len_t{let open U32 in v i <= v j /\ v j <= length x})
    : Tot (t a) = from_raw (sub (as_raw x) i j)
noeq
type mbuffer (a: Type0) (rrel: srel a) (rel: srel a) : Type0 =
  | Null
  | Buffer : 
      max_length: U32.t ->
      content:
        HST.mreference (Seq.lseq a (U32.v max_length)) (srel_to_lsrel (U32.v max_length) rrel) ->
      idx: U32.t ->
      length: U32.t{U32.v idx + U32.v length <= U32.v max_length} ->
      compatible:
        squash (Seq.compatible_sub_preorder (U32.v max_length)
              rrel
              //proof of compatibility
              (U32.v idx)
              (U32.v idx + U32.v length)
              rel)
    -> mbuffer a rrel rel

assume GhostExtensionality: forall (a: Type) (b: Type) (f: gfun a b) (g: gfun a b).
  {:pattern gfeq #a #b f g}
  gfeq #a #b f g <==> f == g

[@ (deprecated "FStar.HyperStack.ST.is_eternal_region")]
let is_eternal_region r = is_eternal_color (color r)

let string_of_matching_problem mp =
  let vars = String.concat ", " mp.mp_vars in
  let hyps =
    String.concat "\n        "
      (List.Tot.map (fun (nm, pat) -> nm ^ ": " ^ (string_of_pattern pat)) mp.mp_hyps)
  in
  let goal =
    match mp.mp_goal with
    | None -> "_"
    | Some pat -> string_of_pattern pat
  in
  "\n{ vars: " ^ vars ^ "\n" ^ "  hyps: " ^ hyps ^ "\n" ^ "  goal: " ^ goal ^ " }"
assume
val gsub_old_to_new (#t: Type0) (b: Old.buffer t) (i len: U32.t)
    : Lemma (requires (U32.v i + U32.v len <= Old.length b))
      (ensures (New.gsub (old_to_new_ghost b) i len == old_to_new_ghost (Old.sub b i len)))
      [
        SMTPatOr
        [
          [SMTPat (New.gsub (old_to_new_ghost b) i len)];
          [SMTPat (old_to_new_ghost (Old.sub b i len))]
        ]
      ]

[@ mark_for_norm]
unfold
let op_Slash (#sw: signed_width{sw <> Unsigned W128}) = ()

(** [zip3] takes a 3-tuple of list of the same length and returns
    the list of index-wise 3-tuples *)
val zip3 (#a1 #a2 #a3: Type) (l1: list a1) (l2: list a2) (l3: list a3)
    : Pure (list (a1 * a2 * a3))
      (requires
        (let n = length l1 in
          n == length l2 /\ n == length l3))
      (ensures (fun _ -> True))
let zip3 #a1 #a2 #a3 l1 l2 l3 = map3 (fun x y z -> x, y, z) l1 l2 l3

let op_Bang_Star (#a: Type0) (#rrel #rel: Seq.seq_pre a) (p: B.mpointer a rrel rel)
    : HST.Stack a
      (requires (fun h -> B.live h p))
      (ensures (fun h0 x h1 -> B.live h1 p /\ x == B.get h0 p 0 /\ h1 == h0)) = B.index p 0ul

#push-options "--z3rlimit 20"
let loc_includes_as_seq #_ #rrel1 #rrel2 #_ #_ h1 h2 larger smaller =
  if Null? smaller
  then ()
  else
    if Null? larger
    then
      (MG.loc_includes_none_elim (loc_buffer smaller);
        MG.loc_of_aloc_not_none #_
          #cls
          #(frameOf smaller)
          #(as_addr smaller)
          (ubuffer_of_buffer smaller))
    else
      (MG.loc_includes_aloc_elim #_
          #cls
          #(frameOf larger)
          #(frameOf smaller)
          #(as_addr larger)
          #(as_addr smaller)
          (ubuffer_of_buffer larger)
          (ubuffer_of_buffer smaller);
        assume (rrel1 == rrel2); //TODO: we should be able to prove this somehow in HS?
        let ul = Ghost.reveal (ubuffer_of_buffer larger) in
        let us = Ghost.reveal (ubuffer_of_buffer smaller) in
        assert (as_seq h1 smaller ==
            Seq.slice (as_seq h1 larger)
              (us.b_offset - ul.b_offset)
              (us.b_offset - ul.b_offset + length smaller));
        assert (as_seq h2 smaller ==
            Seq.slice (as_seq h2 larger)
              (us.b_offset - ul.b_offset)
              (us.b_offset - ul.b_offset + length smaller)))
#pop-options


(** Style guide examples *)

let s1 = "\n"
let s2 = "`"
let yikes = "\b\b\b\b"

(* let s1 = "\n"
let s2 = "\x60"
let yikes = "\b\b\b\b" *)


val on_domain (a: Type) (#b: (a -> Type)) (f: arrow a b) : Tot (arrow a b)

val idempotence_on_domain (#a: Type) (#b: (a -> Type)) (f: arrow a b)
    : Lemma (on_domain a (on_domain a f) == on_domain a f)

let idempotence_on_domain (#a: Type) (#b: (a -> Type)) (f: arrow a b)
    : Lemma (on_domain a (on_domain a f) == on_domain a f) = ()

val modifies_preserves_liveness
      (#aloc: aloc_t)
      (#c: cls aloc)
      (s1 s2: loc c)
      (h h': HS.mem)
      (#t: Type)
      (#pre: Preorder.preorder t)
      (r: HS.mreference t pre)
    : Lemma
      (requires
        (modifies (loc_union s1 s2) h h' /\ loc_disjoint s1 (loc_mreference r) /\
          loc_includes (address_liveness_insensitive_locs c) s2 /\ h `HS.contains` r))
      (ensures (h' `HS.contains` r))

val count: #a: eqtype -> a -> s: seq a -> Tot nat (decreases (length s))
let rec count #a x s =
  if length s = 0 then 0 else if head s = x then 1 + count x (tail s) else count x (tail s)
abstract
val mem: 'a -> set 'a -> Tot Type0
let mem x s = s x

(* constructors *)
abstract
val empty (#a: Type) : Tot (set a)
abstract
val singleton (#a: Type) (x: a) : Tot (set a)
abstract
val union (#a: Type) (x y: set a) : Tot (set a)
abstract
val intersect (#a: Type) (x y: set a) : Tot (set a)
abstract
val complement (#a: Type) (x: set a) : Tot (set a)

type map' (a: Type) (b: (a -> Type)) = f : (x: a -> Tot (option (b x)))
noeq
type mbuffer (a: Type0) (rrel: srel a) (rel: srel a) : Type0 =
  | Null
  | Buffer : 
      max_length: U32.t ->
      content:
        HST.mreference (Seq.lseq a (U32.v max_length)) (srel_to_lsrel (U32.v max_length) rrel) ->
      idx: U32.t ->
      length: U32.t{U32.v idx + U32.v length <= U32.v max_length} ->
      compatible:
        squash (compatible_sub_preorder (U32.v max_length)
              rrel
              //proof of compatibility
              (U32.v idx)
              (U32.v idx + U32.v length)
              rel)
    -> mbuffer a
        rrerrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrl
        rel
noeq private
type _buffer (a: Type) =
  | MkBuffer : 
      max_length: UInt32.t ->
      content: reference (s : lseq a (v max_length)) ->
      idx: UInt32.t ->
      length: UInt32.t{v idx + v length <= v max_length}
    -> _buffer a

val f: a -> b: t -> c: t -> d: t -> Tot nat (decreases (length s))
val f: a: t -> b -> c: t -> d: t -> Tot nat (decreases (length s))
val f: a: t -> b: t -> c -> d: t -> Tot nat (decreases (length s))
val f: a: t -> b: t -> c: t -> d -> Tot nat (decreases (length s))
val f (a b c d: t) : Tot nat (decreases (length s))
val f (a b c d: t) : Tot nat (decreases (length s))

val f (a: r) (b c d: t) : Tot nat (decreases (length s))
val f (a: t) (b: r) (c d: t) : Tot nat (decreases (length s))
val f (a b: t) (c: r) (d: t) : Tot nat (decreases (length s))
val f (a b c: t) (d: r) : Tot nat (decreases (length s))
val f (a b c d: t) : Tot nat (decreases (length s))
val f (#a #b c d: t) : Tot nat (decreases (length s))


val singleton (#a: Type) (x: a) : Tot (set a)
val singleton (#a: Type) (x: a) : Tot (set a)

let f: a -> b: t -> c: t -> d: t -> Tot nat (decreases (length s)) = ()
let f: a: t -> b -> c: t -> d: t -> Tot nat (decreases (length s)) = ()
let f: a: t -> b: t -> c -> d: t -> Tot nat (decreases (length s)) = ()
let f: a: t -> b: t -> c: t -> d -> Tot nat (decreases (length s)) = ()
let f: a: t -> b: t -> c: t -> d: t -> Tot nat (decreases (length s)) = ()
let f (a b c d: t) : Tot nat (decreases (length s)) = ()

let f: a: r -> b: t -> c: t -> d: t -> Tot nat (decreases (length s)) = ()
let f: a: t -> b: r -> c: t -> d: t -> Tot nat (decreases (length s)) = ()
let f: a: t -> b: t -> c: r -> d: t -> Tot nat (decreases (length s)) = ()
let f: a: t -> b: t -> c: t -> d: r -> Tot nat (decreases (length s)) = ()
let f: a: t -> b: t -> c: t -> d: t -> Tot nat (decreases (length s)) = ()
let f (#a #b c d: t) : Tot nat (decreases (length s)) = ()


val singleton (#a: Type) (x: a) : Tot (set a)
val singleton (#a: Type) (x: a) : Tot (set a)


val dummy:unit
abstract
val empty (#a: Type) : Tot (set a)


val modifies_preserves_liveness
      (#aloc: aloc_t)
      (#c: cls aloc)
      (s1 s2: loc c)
      (h h': HS.mem)
      (#t: Type)
      (#pre: Preorder.preorder t)
      (r: HS.mreference t pre)
    : Lemma
      (requires
        (modifies (loc_union s1 s2) h h' /\ loc_disjoint s1 (loc_mreference r) /\
          loc_includes (address_liveness_insensitive_locs c) s2 /\ h `HS.contains` r))
      (ensures (h' `HS.contains` r))

let x =
  match a with
  | 1 ->
    (match b with
      | 2 -> a
      | 3 -> a)
  | 2 -> 6

let tag_of_field_of_tag (#l: P.union_typ) (tgs: tags l) (t: UInt32.t)
    : Lemma (requires (List.Tot.mem t tgs))
      (ensures (List.Tot.mem t tgs /\ tag_of_field #l tgs (field_of_tag #l tgs t) == t))
      [SMTPat (tag_of_field #l tgs (field_of_tag #l tgs t))] = tag_of_field_of_tag' tgs t

val tag_of_field_of_tag (#l: P.union_typ) (tgs: tags l) (t: UInt32.t)
    : Lemma (requires (List.Tot.mem t tgs))
      (ensures (List.Tot.mem t tgs /\ tag_of_field #l tgs (field_of_tag #l tgs t) == t))
      [SMTPat (tag_of_field #l tgs (field_of_tag #l tgs t))]


let collect_prefix_stable
      (#a #b: Type)
      (#i: rid)
      (r: m_rref i (seq a) grows)
      (f: (a -> Tot (seq b)))
      (bs: seq b)
    : Lemma
    (collect_prefix r f bs h0 /\ grows (HS.sel h0 r) (HS.sel h1 r) ==> collect_prefix r f bs h1) =
  let aux: h0: mem -> h1: mem
    -> Lemma
      (collect_prefix r f bs h0 /\ grows (HS.sel h0 r) (HS.sel h1 r) ==> collect_prefix r f bs h1) =
    fun h0 h1 ->
      let s1 = HS.sel h0 r in
      let s3 = HS.sel h1 r in
      collect_grows f s1 s3
  in
  forall_intro_2 aux

val collect_prefix_stable
      (#a #b: Type)
      (#i: rid)
      (r: m_rref i (seq a) grows)
      (f: (a -> Tot (seq b)))
      (bs: seq b)
    : Lemma
    (collect_prefix r f bs h0 /\ grows (HS.sel h0 r) (HS.sel h1 r) ==> collect_prefix r f bs h1)


let f: a: t -> b: t -> c: t -> d: t -> Tot nat (decreases (length s)) = ()
let f (a b c d: t) : Tot nat (decreases (length s)) = ()

let f: a: t -> b: t -> c: t -> d: t -> Tot nat (decreases (length s)) = ()
let f (#a #b c d: t) : Tot nat (decreases (length s)) = ()

let f (a b: t) (c: r) (d: t) : Tot nat (decreases (length s)) = ()

let min x y = if x <= y then x else y

let return_squash (#a: Type) x = ()
let bind_squash (#a: Type) (#b: Type) f g = admit ()
let bind_squash (#a: Type) (#b: Type) f g = admit ()
let push_squash (#a: Type) (#b: (a -> Type)) f = admit ()

let return_squash (#a: Type) x : Tot unit = ()
let bind_squash (#a: Type) (#b: Type) f g : Tot unit = admit ()
let bind_squash (#a: Type) (#b: Type) f g : Tot unit = admit ()
let push_squash (#a: Type) (#b: (a -> Type)) f : Tot unit = admit ()

let as_buffer (#b: Type) (v: buffer b) = BufferView?.buf (dsnd v)

let collect_prefix_stable
      (#a #b: Type)
      (#i: rid)
      (r: m_rref i (seq a) grows)
      (f: (a -> Tot (seq b)))
      (bs: seq b)
    : Lemma (stable_on_t r (collect_prefix r f bs)) =
  let aux: h0: mem -> h1: mem
    -> Lemma
      (collect_prefix r f bs h0 /\ grows (HS.sel h0 r) (HS.sel h1 r) ==> collect_prefix r f bs h1) =
    fun h0 h1 ->
      let s1 = HS.sel h0 r in
      let s3 = HS.sel h1 r in
      collect_grows f s1 s3
  in
  forall_intro_2 aux

let forall_intro_2 #a #b #p f =
  let g: x: a -> Lemma (forall (y: b x). p x y) = fun x -> forall_intro (f x) in
  forall_intro g

val logxor_neq_nonzero (#n: pos) (a b: uint_t n) : Lemma (a <> b ==> logxor a b <> 0)
let logxor_neq_nonzero #n a b =
  let va = to_vec a in
  let vb = to_vec b in
  if logxor a b = 0
  then
    let open FStar.Seq in
    let f (i: nat{i < n}) : Lemma (not (nth #n 0 i)) = zero_nth_lemma #n i in
    Classical.forall_intro f;
    assert (forall (i: nat{i < n}). index va i = index vb i);
    lemma_eq_intro va vb;
    assert (from_vec va = from_vec vb)

let formula_as_term_view (f: formula) : Tot term_view =
  let mk_app' tv args = List.Tot.fold_left (fun tv a -> Tv_App (pack_ln tv) a) tv args in
  ()

val op_Slash
      (#sw: signed_width{sw <> Unsigned W128})
      (x: int_t sw)
      (y:
          int_t sw
            { 0 <> (v y <: Prims.int) /\
              (match sw with
                | Unsigned _ -> within_bounds sw (v x / v y)
                | Signed _ -> within_bounds sw ((v x) `FStar.Int.op_Slash` (v y))) })
    : Tot (int_t sw)

val op_Slash
      (#sw: signed_width{sw <> Unsigned W128})
      (x: int_t sw)
      (y:
          int_t sw
            { 0 <> (v y <: Prims.int) /\
              (match sw with
                | Unsigned _ -> within_bounds sw (v x / v y)
                | Signed _ -> within_bounds sw ((v x) `FStar.Int.op_Slash` (v y))) })
    : Tot (int_t sw)

