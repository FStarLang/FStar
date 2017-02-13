module Box.KeyScheme

//open FStar.HyperHeap
//open FStar.HyperStack

open FStar.Monotonic.RRef
open Platform.Bytes

noeq type plain_scheme =
  | PS: payload_type:Type ->
	length: (payload_type -> nat) ->
	coerce: (bytes -> payload_type) ->
	repr: (payload_type -> bytes) ->
	plain_scheme


noeq type id_scheme =
  | IS: id_type:(t:Type0{hasEq t}) ->
	dishonest: (id_type -> Type) ->
	dishonestST: (i:id_type -> St (b:bool{b ==> dishonest i})) ->
	honest: (id_type -> Type) ->
	honestST: (i:id_type -> St (b:bool{b ==> honest i})) ->
	fixed: (i:id_type -> t:Type{t ==> (honest i \/ dishonest i)}) ->
	id_scheme

noeq type id_combiner = 
  | IC: is1:id_scheme -> 
	is2:id_scheme -> 
	combine_ids: (is1.id_type -> is1.id_type -> is2.id_type) ->
	id_combiner



noeq type key_scheme =
  | KS: ks_is:id_scheme ->
	key_region:rid ->
        key_type:Type0 -> 
        get_key_index:(key_type -> ks_is.id_type) -> 
        key_gen: ((i:ks_is.id_type) -> ST key_type
          (requires (fun h0 -> True))
          (ensures (fun h0 k h1 -> True)) // implement restriction with key_region
        ) -> 
        coerce_key: ((i:ks_is.id_type{ks_is.dishonest i}) -> bytes -> St key_type) ->
        leak_key: ((k:key_type{ks_is.dishonest (get_key_index k)}) -> bytes) ->
        key_scheme
