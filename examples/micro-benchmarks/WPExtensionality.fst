module WPExtensionality

open FStar.Tactics

assume val wp1 : (int -> Type0) -> Type0
assume val wp2 : (int -> unit -> Type0) -> Type0

(* 1 arg direct *)
let direct_1 (post1 : int -> Type0)
= assert_by_tactic True
        (fun () -> let tm = quote ((forall x. post1 x) ==> wp1 post1) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp1 (fun (_:int) -> True)))
                   then ()
                   else fail "failed")

(* 2 arg direct *)
let direct_2 (post2 : int -> unit -> Type)
= assert_by_tactic True
        (fun () -> let tm = quote ((forall x y. post2 x y) ==> wp2 post2) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> True)))
                   then ()
                   else fail "failed")

(* 1 arg indirect *)
let indirect_1 (post1 : int -> Type0)
= assert_by_tactic True
        (fun () -> admit();
                   let tm = quote ((forall x. post1 x <==> True) ==> wp1 post1) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp1 (fun (_:int) -> True)))
                   then ()
                   else fail "failed")

(* 2 arg indirect *)
let indirect_2 (post2 : int -> unit -> Type)
= assert_by_tactic True
        (fun () -> admit ();
                   let tm = quote ((forall x y. post2 x y <==> True) ==> wp2 post2) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> True)))
                   then ()
                   else fail "failed")

(* 1 arg negated direct *)
let neg_direct_1 (post1 : int -> Type0)
= assert_by_tactic True
        (fun () -> let tm = quote ((forall x. ~(post1 x)) ==> wp1 post1) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp1 (fun (_:int) -> False)))
                   then ()
                   else fail "failed")

(* 2 arg negated direct *)
let neg_direct_2 (post2 : int -> unit -> Type)
= assert_by_tactic True
        (fun () -> let tm = quote ((forall x y. ~(post2 x y)) ==> wp2 post2) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> False)))
                   then ()
                   else fail "failed")

(* 1 arg negated indirect *)
let neg_indirect_1 (post1 : int -> Type0)
= assert_by_tactic True
        (fun () -> admit();
                   let tm = quote ((forall x. post1 x <==> False) ==> wp1 post1) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp1 (fun (_:int) -> False)))
                   then ()
                   else fail "failed")

(* 2 arg negated indirect *)
let neg_indirect_2 (post2 : int -> unit -> Type)
= assert_by_tactic True
        (fun () -> admit ();
                   let tm = quote ((forall x y. post2 x y <==> False) ==> wp2 post2) in
                   debug ("before = " ^ term_to_string tm);
                   let tm' = norm_term [simplify] tm in
                   debug ("after= " ^ term_to_string tm');
                   if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> False)))
                   then ()
                   else fail "failed")
