open Prims
type ('a, 's1, 's2) grows_aux = unit
type ('a, 'uuuuu, 'uuuuu1) grows = unit
type rid = unit
let snoc : 'a . 'a FStar_Seq_Base.seq -> 'a -> 'a FStar_Seq_Base.seq =
  fun s ->
    fun x -> FStar_Seq_Base.append s (FStar_Seq_Base.create Prims.int_one x)
let alloc_mref_seq :
  'a .
    unit ->
      'a FStar_Seq_Base.seq ->
        (unit, 'a FStar_Seq_Base.seq, ('a, unit, unit) grows)
          FStar_HyperStack_ST.m_rref
  = fun r -> fun init -> FStar_HyperStack_ST.ralloc () init
type ('a, 'i, 'n, 'x, 'r, 'h) at_least = unit
let write_at_end :
  'a .
    unit ->
      (unit, 'a FStar_Seq_Base.seq, ('a, unit, unit) grows)
        FStar_HyperStack_ST.m_rref -> 'a -> unit
  =
  fun i ->
    fun r ->
      fun x ->
        FStar_HyperStack_ST.recall r;
        (let s0 = FStar_HyperStack_ST.op_Bang r in
         let n = FStar_Seq_Base.length s0 in
         FStar_HyperStack_ST.op_Colon_Equals r
           (FStar_Seq_Properties.snoc s0 x);
         FStar_HyperStack_ST.mr_witness () () () (Obj.magic r) ())
type ('a, 'p, 's1, 's2) grows_p = unit
type ('r, 'a, 'p) i_seq =
  (unit, 'a FStar_Seq_Base.seq, unit) FStar_HyperStack_ST.m_rref
let alloc_mref_iseq :
  'a 'p . unit -> 'a FStar_Seq_Base.seq -> (unit, 'a, 'p) i_seq =
  fun r -> fun init -> FStar_HyperStack_ST.ralloc () init
type ('r, 'a, 'p, 'n, 'x, 'm, 'h) i_at_least = unit
type ('r, 'a, 'p, 'x, 'is, 'h) int_at_most = unit
let i_read : 'a 'p . unit -> (unit, 'a, 'p) i_seq -> 'a FStar_Seq_Base.seq =
  fun r -> fun m -> FStar_HyperStack_ST.op_Bang m
type ('r, 'a, 'p, 'm, 'h) i_contains = unit
let i_write_at_end : 'a 'p . unit -> (unit, 'a, 'p) i_seq -> 'a -> unit =
  fun rgn ->
    fun r ->
      fun x ->
        FStar_HyperStack_ST.recall r;
        (let s0 = FStar_HyperStack_ST.op_Bang r in
         let n = FStar_Seq_Base.length s0 in
         FStar_HyperStack_ST.op_Colon_Equals r
           (FStar_Seq_Properties.snoc s0 x);
         FStar_HyperStack_ST.mr_witness () () () (Obj.magic r) ())
type 's invariant = unit
let (test0 :
  unit ->
    (unit, Prims.nat FStar_Seq_Base.seq, (Prims.nat, unit, unit) grows)
      FStar_HyperStack_ST.m_rref -> Prims.nat -> unit)
  =
  fun r ->
    fun a ->
      fun k ->
        let h0 = FStar_HyperStack_ST.get () in
        FStar_HyperStack_ST.mr_witness () () () (Obj.magic a) ()
let (itest :
  unit -> (unit, Prims.nat, unit invariant) i_seq -> Prims.nat -> unit) =
  fun r ->
    fun a ->
      fun k ->
        let h0 = FStar_HyperStack_ST.get () in
        FStar_HyperStack_ST.mr_witness () () () (Obj.magic a) ()
let un_snoc : 'a . 'a FStar_Seq_Base.seq -> ('a FStar_Seq_Base.seq * 'a) =
  fun s ->
    let last = (FStar_Seq_Base.length s) - Prims.int_one in
    ((FStar_Seq_Base.slice s Prims.int_zero last),
      (FStar_Seq_Base.index s last))
let rec map :
  'a 'b . ('a -> 'b) -> 'a FStar_Seq_Base.seq -> 'b FStar_Seq_Base.seq =
  fun f ->
    fun s ->
      if (FStar_Seq_Base.length s) = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let uu___1 = un_snoc s in
         match uu___1 with
         | (prefix, last) ->
             FStar_Seq_Properties.snoc (map f prefix) (f last))
let op_At :
  'uuuuu .
    'uuuuu FStar_Seq_Base.seq ->
      'uuuuu FStar_Seq_Base.seq -> 'uuuuu FStar_Seq_Base.seq
  = fun s1 -> fun s2 -> FStar_Seq_Base.append s1 s2
type ('a, 'b, 'i, 'r, 'f, 'bs, 'h) map_prefix = unit
type ('a, 'b, 'i, 'r, 'f, 'n, 'v, 'h) map_has_at_index = unit
let rec collect :
  'a 'b .
    ('a -> 'b FStar_Seq_Base.seq) ->
      'a FStar_Seq_Base.seq -> 'b FStar_Seq_Base.seq
  =
  fun f ->
    fun s ->
      if (FStar_Seq_Base.length s) = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let uu___1 = un_snoc s in
         match uu___1 with
         | (prefix, last) ->
             FStar_Seq_Base.append (collect f prefix) (f last))
type ('a, 'b, 'i, 'r, 'f, 'bs, 'h) collect_prefix = unit
type ('a, 'b, 'i, 'r, 'f, 'n, 'v, 'h) collect_has_at_index = unit
type ('i, 'a) log_t =
  (unit, 'a FStar_Seq_Base.seq, unit) FStar_HyperStack_ST.m_rref
type ('x, 'y) increases = unit
type ('l, 'a, 'x, 'log, 'h) at_most_log_len = unit
type ('l, 'a, 'i, 'log, 'max) seqn_val = Prims.nat
type ('l, 'a, 'i, 'log, 'max) seqn =
  (unit, (unit, 'a, unit, unit, unit) seqn_val, unit)
    FStar_HyperStack_ST.m_rref
let new_seqn :
  'a .
    unit ->
      Prims.nat ->
        unit ->
          Prims.nat -> (unit, 'a) log_t -> (unit, 'a, unit, unit, unit) seqn
  =
  fun l ->
    fun max ->
      fun i ->
        fun init ->
          fun log ->
            FStar_HyperStack_ST.recall log;
            FStar_HyperStack_ST.recall_region ();
            FStar_HyperStack_ST.mr_witness () () () (Obj.magic log) ();
            FStar_HyperStack_ST.ralloc () init
let increment_seqn :
  'a .
    unit ->
      Prims.nat ->
        unit -> (unit, 'a) log_t -> (unit, 'a, unit, unit, unit) seqn -> unit
  =
  fun l ->
    fun max ->
      fun i ->
        fun log ->
          fun c ->
            FStar_HyperStack_ST.recall c;
            FStar_HyperStack_ST.recall log;
            (let n =
               let uu___2 = FStar_HyperStack_ST.op_Bang c in
               uu___2 + Prims.int_one in
             FStar_HyperStack_ST.mr_witness () () () (Obj.magic log) ();
             FStar_HyperStack_ST.op_Colon_Equals c n)
let testify_seqn :
  'a .
    unit ->
      unit ->
        (unit, 'a) log_t ->
          Prims.nat -> (unit, 'a, unit, unit, unit) seqn -> unit
  =
  fun i ->
    fun l ->
      fun log ->
        fun max ->
          fun ctr ->
            let n = FStar_HyperStack_ST.op_Bang ctr in
            FStar_HyperStack_ST.testify ()