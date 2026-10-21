module FStarC.HashTable

(* Mutable hash tables over any key type with [deq] and [hashable] instances.

   The OCaml implementation (FStarC.HashTable-ocaml.fst) is an instance of
   OCaml's [Hashtbl.Make] per key type; the Cherry one
   (FStarC.HashTable-c.cherry.fst) is a hash table written in F*.  The
   operations are [inline_for_extraction] for the OCaml one: see there. *)

open FStarC.Effect
open FStarC.Class.Deq
open FStarC.Class.Hashable

inline_for_extraction
val t (k:Type0) {| deq k |} {| hashable k |} (v:Type0) : Type0

inline_for_extraction
val create (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (n:int) : ML (t k v)

inline_for_extraction
val clear (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML unit

inline_for_extraction
val copy (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML (t k v)

(* Replaces the current binding of the key, if any. *)
inline_for_extraction
val add (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) (value:v) : ML unit

inline_for_extraction
val remove (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) : ML unit

inline_for_extraction
val try_find (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) : ML (option v)

inline_for_extraction
val mem (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) : ML bool

inline_for_extraction
val iter (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0)
  (m:t k v) (f:k -> v -> ML unit) : ML unit

inline_for_extraction
val fold (#k:Type0) {| deq k |} {| hashable k |} (#v #a:Type0)
  (m:t k v) (f:k -> v -> a -> ML a) (init:a) : ML a

inline_for_extraction
val size (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML int

inline_for_extraction
val of_list (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (l:list (k & v)) : ML (t k v)

inline_for_extraction
val keys (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML (list k)
