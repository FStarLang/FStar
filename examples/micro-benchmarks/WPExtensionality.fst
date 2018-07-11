module WPExtensionality

open FStar.Tactics

assume val wp1 : (int -> Type0) -> Type0
assume val wp2 : (int -> unit -> Type0) -> Type0

(* 1 arg direct *)
let direct_1 ()
= assert_by_tactic True
        (fun () -> let tm = quote (forall p. (forall x. p x) ==> wp1 p) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp1 (fun (_:int) -> True)))
                   then ()
                   else fail "failed")

(* 2 arg direct *)
let direct_2 ()
= assert_by_tactic True
        (fun () -> let tm = quote (forall p. (forall x y. p x y) ==> wp2 p) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> True)))
                   then ()
                   else fail "failed")

(* 1 arg indirect *)
let indirect_1
= assert_by_tactic True
        (fun () -> admit();
                   let tm = quote (forall p. (forall x. p x <==> True) ==> wp1 p) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp1 (fun (_:int) -> True)))
                   then ()
                   else fail "failed")

(* 2 arg indirect *)
let indirect_2 ()
= assert_by_tactic True
        (fun () -> admit ();
                   let tm = quote (forall p. (forall x y. p x y <==> True) ==> wp2 p) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> True)))
                   then ()
                   else fail "failed")

(* 1 arg negated direct *)
let neg_direct_1 ()
= assert_by_tactic True
        (fun () -> let tm = quote (forall p. (forall x. ~(p x)) ==> wp1 p) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp1 (fun (_:int) -> False)))
                   then ()
                   else fail "failed")

(* 2 arg negated direct *)
let neg_direct_2 ()
= assert_by_tactic True
        (fun () -> let tm = quote (forall p. (forall x y. ~(p x y)) ==> wp2 p) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> False)))
                   then ()
                   else fail "failed")

(* 1 arg negated indirect *)
let neg_indirect_1 ()
= assert_by_tactic True
        (fun () -> admit();
                   let tm = quote (forall p. (forall x. p x <==> False) ==> wp1 p) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp1 (fun (_:int) -> False)))
                   then ()
                   else fail "failed")

(* 2 arg negated indirect *)
let neg_indirect_2 ()
= assert_by_tactic True
        (fun () -> admit ();
                   let tm = quote (forall p. (forall x y. p x y <==> False) ==> wp2 p) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> False)))
                   then ()
                   else fail "failed")

// Bug reported by Jay
[@expect_failure]
let bug () : Lemma False =
   ((if true then () else ()); ())
