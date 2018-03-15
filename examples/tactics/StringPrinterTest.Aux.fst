module StringPrinterTest.Aux
include StringPrinter.RecC

module Ca = FStar.Int.Cast
module U32 = FStar.UInt32
module T = FStar.Tactics
module HST = FStar.HyperStack.ST
module B = FStar.Buffer

#reset-options "--use_two_phase_tc true --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let rec example (x: U32.t) : Tot (m unit) (decreases (U32.v x)) =
  _ <-- print_char (Ca.uint32_to_uint8 x) ;
  if U32.lt x 256ul
  then ret ()
  else example (U32.div x 256ul)

let example_do_while : (x: U32.t) -> Tot (y: m unit { y () == example x () } ) =
  T.synth_by_tactic (fun () -> mk_do_while example )

inline_for_extraction
let example_sz (x: U32.t) : Tot (m_sz (example x)) =
  coerce_sz
    _
    (example_do_while x)
    (T.synth_by_tactic (fun () -> mk_sz 4 (example_do_while x)))
    (example x)
    ()

inline_for_extraction
let example_st (x: U32.t) : Tot (m_st (example x)) =
  coerce_st
    _
    (example_do_while x)
    (T.synth_by_tactic (fun () -> mk_st 4 (example_do_while x)))
    (example x)
    ()

inline_for_extraction
let example_test (x: U32.t) : HST.ST (option unit) (requires (fun _ -> True)) (ensures (fun h _ h' -> B.modifies_0 h h')) =
  phi
    (example x)
    (example_sz x)
    (example_st x)
    ()

let _ = T.assert_by_tactic True (fun () -> T.print "EOF")
