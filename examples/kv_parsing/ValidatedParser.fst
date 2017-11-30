module ValidatedParser

open KeyValue
open Parsing
open IntegerParsing
open PureParser
open Validator
open Slice

open FStar.Seq
module List = FStar.List.Tot
open FStar.HyperStack
open FStar.HyperStack.ST

module B = FStar.Buffer

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

(*** API using validated but unparsed key-value buffer *)

val fold_left_store_aux: #t:Type -> f:(t -> encoded_entry -> t) -> t -> es:list encoded_entry -> Tot t
    (decreases es)
let rec fold_left_store_aux #t f acc es =
      match es with
      | [] -> acc
      | e::es -> fold_left_store_aux f (f acc e) es
      
// sufficient to expose iteration over the key-value pairs (specifically pointers to them)
// spec: fold over fully parsed store
val fold_left_store: #t:Type -> f:(t -> encoded_entry -> t) -> t -> s:store -> t
let fold_left_store #t f acc s = fold_left_store_aux f acc s.entries
    
// XXX: this is just computation, right?
assume val fold_left_empty (#t:Type) (f:(t -> encoded_entry -> t)) (acc:t) (s:store) :
  Lemma (requires (s.entries == []))
        (ensures (fold_left_store f acc s == acc))

val fold_left_store_n : #t:Type -> f:(t -> encoded_entry -> Tot t) -> acc:t ->
  es:list encoded_entry -> n:nat{n <= List.length es} -> Tot t (decreases n)
let rec fold_left_store_n #t f acc es n =
  match n with
  | 0 -> acc
  | _ -> let acc' = f acc (List.hd es) in
        fold_left_store_n f acc' (List.tail es) (n-1)

val fold_left_store_n_spec (f:('a -> encoded_entry -> 'a)) (acc:'a) (s:store) :
  Ghost unit
  (requires True)
  (ensures (fun _ -> fold_left_store_n f acc s.entries (U32.v s.num_entries) == fold_left_store f acc s))
  (decreases (List.length s.entries))
let rec fold_left_store_n_spec f acc s =
  match U32.v s.num_entries with
  | 0 -> fold_left_empty f acc s
  | _ ->
    let n' = U32.sub s.num_entries (U32.uint_to_t 1) in
    fold_left_store_n_spec f (f acc (List.hd s.entries)) (Store n' (List.tl s.entries))

// This is a stateful fold over pure entries - intended to be used as a
// specification, since we will not materialized [encoded_entry]s at runtime
val fold_left_entries_st : f:('a -> encoded_entry -> St 'a) -> acc:'a -> es:list encoded_entry -> St 'a
let rec fold_left_entries_st (f:('a -> encoded_entry -> St 'a)) (acc:'a)
    (es:list encoded_entry) : St 'a =
    match es with
    | [] -> acc
    | e::es -> let acc = f acc e in
             fold_left_entries_st f acc es

val fold_left_store_st : f:('a -> encoded_entry -> St 'a) -> acc:'a -> s:store -> St 'a
let fold_left_store_st f acc s = fold_left_entries_st f acc s.entries

// this is an old experiment with doing a fold_left over a buffer of bytes (pure
// validation); we now have a complete prototype of validators in Stack
val fold_left_buffer: #t:Type -> f:(t -> encoded_entry -> t) -> t -> b:bytes{length b < pow2 32} -> t
let fold_left_buffer #t f acc b =
    match parse_u32 b with
    | Some (num_entries, l) -> begin
       // we only parse up to n more entries from the buffer b
       let rec aux (n: nat) (b: bytes{length b < pow2 32}) acc : t =
         match n with
         | 0 -> acc
         | _ -> begin
           match parse_entry b with
           | Some (e, l) ->
             assert (n > 0);
             aux (n-1) (slice b l (length b)) (f acc e)
           | None -> acc
           end in
         aux (U32.v num_entries) (slice b l (length b)) acc
      end
    | None -> acc

#reset-options "--z3rlimit 30 --max_fuel 1 --max_ifuel 1"

val parse_num_entries_valid : input:bslice -> Stack (U32.t * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_abstract_store bs))))
  (ensures (fun h0 r h1 -> // note that live and Some? (parse_abstract_store bs)
                        // come for free due to h0 == h1, but the postcondition
                        // must typecheck without assuming the precondition, so
                        // we re-assert them to discharge obligations within
                        // this postcondition; their proofs should be trivial
                        // due to the function being read-only
                        live h1 input /\
                        modifies_none h0 h1 /\
                        begin
                          let bs = as_seq h1 input in
                          Some? (parse_abstract_store bs) /\
                          (let (s, _) = Some?.v (parse_abstract_store bs) in
                           let (rv, r_off) = r in
                           let bs' = slice bs (U32.v r_off) (length bs) in
                           rv == s.num_entries /\
                          (let parse_rest = parse_many parse_entry (U32.v rv) bs' in
                           Some? parse_rest /\
                           s.entries == parse_result parse_rest))
                        end))
let parse_num_entries_valid input =
  let (len, off) = parse_u32_st_nochk input in
  // TODO: fix this proof
  admit();
  (len, off)

let parse_entry_st_nochk : input:bslice -> Stack (entry_st * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_entry bs))))
  (ensures (fun h0 r h1 ->
                live h1 input /\
                modifies_none h0 h1 /\
                (let bs = B.as_seq h1 input.p in
                Some? (parse_entry bs) /\
                (let (v, n) = Some?.v (parse_entry bs) in
                  let (rv, off) = r in
                  entry_live h1 rv /\
                  as_entry h1 rv == v /\
                  n == U32.v off)))) = fun input ->
  let (key, off) = parse_u16_array_nochk input in
  let input = advance_slice input off in
  let (value, off') = parse_u32_array_nochk input in
  (EntrySt key value, U32.add off off')

let parse_many_next (#t:Type) (p:parser t) (n:nat{n>0}) (bs:bytes{length bs < pow2 32}) :
  Lemma (requires (Some? (parse_many p n bs)))
        (ensures (Some? (parse_many p n bs) /\
                  (let (vs, _) = Some?.v (parse_many p n bs) in
                   let (v, off) = Some?.v (p bs) in
                   let rest_parse = parse_many p (n-1) (slice bs off (length bs)) in
                   v == List.hd vs /\
                   Some? rest_parse /\
                   (let (vs', off') = Some?.v rest_parse in
                    vs' == List.tail vs)))) =
  ()

val parse_one_entry : n:U32.t{U32.v n > 0} -> input:bslice -> Stack (entry_st * off:U32.t{U32.v off <= U32.v input.len})
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                     let n = U32.v n in
                     Some? (parse_many parse_entry n bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                        modifies_none h0 h1 /\
                        begin
                          let bs = as_seq h1 input in
                          let n:(n:nat{n > 0}) = U32.v n in
                          Some? (parse_many parse_entry n bs) /\
                          begin
                            let (vs, _) = Some?.v (parse_many parse_entry n bs) in
                            let (rv, r_off) = r in
                            entry_live h1 rv /\
                            // as_entry h1 rv == parse_result (parse_entry bs) /\
                            as_entry h1 rv == List.hd vs /\
                            begin
                              let bs' = slice bs (U32.v r_off) (length bs) in
                              let parse_rest = parse_many parse_entry (n-1) bs' in
                              Some? parse_rest /\
                              parse_result parse_rest == List.tail vs
                            end
                          end
                        end))
let parse_one_entry n input =
  (let h = get() in
   let bs = as_seq h input in
   parse_many_next parse_entry (U32.v n) bs);
  parse_entry_st_nochk input

val fold_left_store_n_unfold1 (#t:Type) (f: (t -> encoded_entry -> t))
    (acc:t) (es:list encoded_entry) (n:nat{0 < n /\ n <= List.length es})
    : Lemma (fold_left_store_n f acc es n ==
             fold_left_store_n f (f acc (List.hd es)) (List.tail es) (n-1))
let fold_left_store_n_unfold1 #t f acc es n = ()

#reset-options "--z3rlimit 20"

val fold_left_buffer_n_mut_st: #t:Type ->
  f_spec:(t -> encoded_entry -> t) ->
  rel:(mem -> mem -> Type0){preorder rel} ->
  full_input:(unit -> GTot bslice) ->
  f:(acc:t -> e:entry_st -> Stack t
    (requires (fun h0 -> entry_live h0 e /\
                      live h0 (full_input ())))
    (ensures (fun h0 r h1 -> entry_live h1 e /\
                          rel h0 h1 /\
                          (let input = full_input () in
                          live h0 input /\
                          live h1 input /\
                          as_seq h0 input == as_seq h1 input /\
                          r == f_spec acc (as_entry h1 e))))) ->
  input:bslice{bslice_prefix input (full_input ())} ->
  acc:t -> n:U32.t -> Stack t
  (requires (fun h0 -> live h0 (full_input ()) /\
                    (let bs = as_seq h0 input in
                    let n = U32.v n in
                    Some? (parse_many parse_entry n bs))))
  (ensures (fun h0 r h1 -> rel h0 h1 /\
                        live h0 (full_input ()) /\
                        live h1 (full_input ()) /\
                        as_seq h0 (full_input ()) == as_seq h1 (full_input ()) /\
                        (let bs = as_seq h1 input in
                        let n = U32.v n in
                        Some? (parse_many parse_entry n bs) /\
                        r == fold_left_store_n f_spec acc (parse_result (parse_many parse_entry n bs)) n)))
let rec fold_left_buffer_n_mut_st #t f_spec rel full_input f input acc n =
    // TODO: this proof needs some work; unclear how much
    admit();
    if U32.eq n 0ul then acc
    else  begin
      let h0 = get() in
      let (e, off) = parse_one_entry n input in
      let input' = advance_slice input off in
      let n' = U32.sub n 1ul in
      let acc' = f acc e in
      let h1 = get() in
      (let bs1 = as_seq h1 input in
        let bs1' = as_seq h1 input' in
        let n = U32.v n in
        let n' = U32.v n' in
        assert (Some? (parse_many parse_entry n' bs1') /\
                parse_result (parse_many parse_entry n' bs1') ==
                List.tail (parse_result (parse_many parse_entry n bs1))));
      bslice_prefix_trans input' input (full_input ());
      let r = fold_left_buffer_n_mut_st f_spec rel full_input f input' acc' n' in
      (let h2 = get() in
      let bs0 = as_seq h0 input in
      let bs2 = as_seq h2 input in
      let bs2' = as_seq h2 input' in
      assert (rel h0 h2);
      assert (bs0 == bs2);
      assert (live h1 (full_input ()));
      assert (as_seq h0 (full_input ()) == as_seq h2 (full_input ()));
      assert (Some? (parse_many parse_entry (U32.v n') bs2') /\
              parse_result (parse_many parse_entry (U32.v n') bs2') ==
              List.tail (parse_result (parse_many parse_entry (U32.v n) bs2)));
      // XXX: this call doesn't work
      //fold_left_store_n_unfold1 f_spec acc (parse_result (parse_many parse_entry n' bs2')) n';
      ());
      r
    end

// TODO: doesn't extract, but count_entries_example' generates a call to it
[@"substitute"]
val fold_left_buffer_n_st: #t:Type -> f_spec:(t -> encoded_entry -> t) ->
  f:(acc:t -> e:entry_st -> Stack t
    (requires (fun h0 -> entry_live h0 e))
    (ensures (fun h0 r h1 -> entry_live h1 e /\
                          modifies_none h0 h1 /\
                          r == f_spec acc (as_entry h1 e)))) ->
  acc:t -> input:bslice -> n:U32.t -> Stack t
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    let n = U32.v n in
                    Some? (parse_many parse_entry n bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                        modifies_none h0 h1 /\
                        (let bs = as_seq h1 input in
                        let n = U32.v n in
                        Some? (parse_many parse_entry n bs) /\
                        r == fold_left_store_n f_spec acc (parse_result (parse_many parse_entry n bs)) n)))
let rec fold_left_buffer_n_st #t f_spec f acc input n =
    if U32.eq n 0ul then acc
    else  begin
      let (e, off) = parse_one_entry n input in
      let input = advance_slice input off in
      let n' = U32.sub n 1ul in
      let acc' = f acc e in
      let h = get() in
      assert (let bs = as_seq h input in
              Some? (parse_many parse_entry (U32.v n') bs));
      let r = fold_left_buffer_n_st f_spec f acc' input n' in
      r
    end

// TODO: doesn't extract, but count_entries_example generates a call to it
[@"substitute"]
val fold_left_buffer_st: #t:Type -> f_spec:(t -> encoded_entry -> t) ->
  f:(acc:t -> e:entry_st -> Stack t
    (requires (fun h0 -> entry_live h0 e))
    (ensures (fun h0 r h1 -> entry_live h1 e /\
                          modifies_none h0 h1 /\
                          r == f_spec acc (as_entry h1 e)))) ->
  acc:t -> input:bslice -> Stack t
  (requires (fun h0 -> live h0 input /\
                    (let bs = as_seq h0 input in
                    Some? (parse_abstract_store bs))))
  (ensures (fun h0 r h1 -> live h1 input /\
                        modifies_none h0 h1 /\
                        (let bs = as_seq h1 input in
                        Some? (parse_abstract_store bs) /\
                        r == fold_left_store f_spec acc (parse_result (parse_abstract_store bs)))))
let fold_left_buffer_st #t f_spec f acc input =
  let (num_entries, off) = parse_num_entries_valid input in
  (let h = get() in
   let bs = as_seq h input in
   let (s, _) = Some?.v (parse_abstract_store bs) in
   fold_left_store_n_spec f_spec acc s;
   assert (num_entries == s.num_entries));
  let input = advance_slice input off in
  fold_left_buffer_n_st f_spec f acc input num_entries

val fold_left_n_count : es:list encoded_entry -> acc:U32.t ->
    Lemma (requires (U32.v acc + List.length es < pow2 32))
          (ensures (U32.v acc + List.length es < pow2 32 /\
                   fold_left_store_n (fun acc e -> U32.add_mod acc 1ul) acc es (List.length es) ==
                   U32.uint_to_t (U32.v acc + List.length es)))
let rec fold_left_n_count es acc = match es with
                              | [] -> ()
                              | e::es -> assert (U32.v (U32.add_mod acc 1ul) == U32.v acc + 1);
                                       assert (U32.v acc + 1 + List.length es < pow2 32);
                                       fold_left_n_count es (U32.add_mod acc 1ul)

val fold_left_count : s:store ->
    Lemma (fold_left_store (fun acc e -> U32.add_mod acc 1ul) 0ul s == s.num_entries)
let fold_left_count s = fold_left_n_count s.entries 0ul;
                        fold_left_store_n_spec (fun acc e -> U32.add_mod acc 1ul) 0ul s

val count_entries_example (input:bslice) : Stack U32.t
    (requires (fun h0 -> live h0 input /\
                      (let bs = as_seq h0 input in
                        Some? (parse_abstract_store bs))))
    (ensures (fun h0 r h1 -> live h1 input /\
                          modifies_none h0 h1 /\
                          (let bs = as_seq h1 input in
                          Some? (parse_abstract_store bs) /\
                          r == (parse_result (parse_abstract_store bs)).num_entries)))
let count_entries_example input =
    let r = fold_left_buffer_st
       // pure spec
      (fun acc e -> U32.add_mod acc 1ul)
      // implementation
      (fun acc e -> U32.add_mod acc 1ul)
      0ul input in
    begin
      let h = get() in
      let bs = as_seq h input in
      fold_left_count (parse_result (parse_abstract_store bs))
    end;
    r

let count_entries_example' input =
    let (num_entries, _) = parse_num_entries_valid input in
    fold_left_buffer_n_st (fun acc e -> U32.add_mod acc 1ul) (fun acc e -> U32.add_mod acc 1ul) 0ul input num_entries
