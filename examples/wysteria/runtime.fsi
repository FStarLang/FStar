(*--build-config
   options:--admit_fsi FStar.Set --admit_fsi FStar.Seq --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins;
   variables:CONTRIB=../../contrib;
   other-files:classical.fst ext.fst set.fsi heap.fst st.fst all.fst seq.fsi seqproperties.fst ghost.fst ordset.fsi ordmap.fsi prins.fsi ast.fst $CONTRIB/Platform/fst/Bytes.fst
--*)

module Runtime

open Prins
open AST

open Platform.Bytes

type chan_in   // channel type to read input
type chan_out  // channel type to send output

type server_ret_type = Tuple6 prin redex prins varname exp dvalue

val establish_server: callback:(chan_in -> chan_out -> ML unit) -> port:nat -> ML unit
val open_connection : port:nat -> ML (chan_in * chan_out)

assume val random : l:nat -> Tot (lbytes l)

assume val marshal_s: #a:Type -> x:a -> GTot bytes
assume val unmarshal_s: #a:Type -> bytes -> GTot a

assume val marshal_unmarshal_inv_lemma:
  #a:Type -> x:a
  -> Lemma (requires (True)) (ensures (unmarshal_s #a (marshal_s #a x) = x))
    [SMTPat (unmarshal_s #a (marshal_s #a x))]
    
val marshal: #a:Type -> x:a -> Tot (b:bytes{b = marshal_s x})
val unmarshal: #a:Type -> b:bytes -> Tot (x:a{x = unmarshal_s #a b})

val send: chan_out -> bytes -> ML unit
val recv: chan_in -> ML bytes

val create_thread: f:(unit -> ML unit) -> ML unit

val is_server: unit -> ML bool
val me       : unit -> ML string

(**********)

val string_of_bytes: bytes -> Tot string
val bytes_of_string: string -> Tot bytes
val int_of_string: string -> int

(**********)
val rungmw: string -> string -> int -> list string
val list_to_int: list string -> int
