module Bug590

open FStar.List.Tot


let transport (a b:Type) (x:a) : Pure b (requires (a == b)) (ensures (fun y -> a == b /\ y == x)) = x

let rec coerce (#a:Type) (ss:list (s:(list a){Cons? s}))
  : Pure (list (list a)) (requires True)
                         (ensures (fun (ss':list (list a)) -> ss === ss')) =
  match ss with
  | [] -> let x : list (list a) = Nil #(list a) in admit(); x (* F* can't prove that      Nil #(list a) === Nil #(s:(list a){Cons? s}) *)
  | h::t -> 
            //assert(eq2 (list (list a)) (list (s:(list a){Cons? s}))); // -- at least this one fails
            ignore(coerce t); assert(eq2 (list (list a)) (list (s:(list a){Cons? s}))); // -- but it works as soon as we call coerce
            // this is in fact inconsistent 
            //assert(False); -- but F* needs a little help to prove it
            assert (Cons? (Cons?.hd (transport (list (list a)) (list (s:(list a){Cons? s})) [[]])));
            assert(False);
            // the following could be proved though even without the False
            assert(eq2 #(list (list a)) (Cons #(list a) h (coerce t)) (Cons #(s:(list a){Cons? s}) h (coerce t)));
            assert(eq2 #(list (s:(list a){Cons? s})) (Cons #(list a) h (coerce t)) (Cons #(s:(list a){Cons? s}) h (coerce t)));
            assert(eq2 #(list (list a)) (Cons #(list a) h (coerce t)) (Cons #(s:(list a){Cons? s}) h t));
            assert(eq2 #(list (s:(list a){Cons? s})) (Cons #(list a) h (coerce t)) (Cons #(s:(list a){Cons? s}) h t));
            assert(Cons #(list a) h (coerce t) === Cons #(s:(list a){Cons? s}) h (coerce t));
            Cons #(list a) h (coerce t)                       (* F* can   prove that Cons #(list a) ... === Cons #(s:(list a){Cons? s}) ... *)

let blah (x:nat) (y:int) =
  //assert(eq2 x y); // typechecks + assertion fails
  //assert(eq2 y x); // typechecks + assertion fails
  //assert(eq2 #nat x y) // typechecks -- seems wrong, errors displayed out of order!?
  //eq2 #nat x y // fails to typecheck, as it should
  eq2 #int x y // type-checks as it should

let blah2 (a:Type) (h:(s:list a{Cons? s})) (t:list ((s:list a{Cons? s}))) =
            // assert(eq2 #(list (list a)) (Nil #(list a)) (Nil #(s:(list a){Cons? s})));
            // assert(eq2 #(list (s:(list a){Cons? s})) (Nil #(list a)) (Nil #(s:(list a){Cons? s})));
            // assert(eq2 #(list (list a)) (Cons #(list a) h t) (Cons #(s:(list a){Cons? s}) h t));
            // assert(eq2 #(list (s:(list a){Cons? s})) (Cons #(list a) h t) (Cons #(s:(list a){Cons? s}) h t));
            assert(eq2 #(list (list a)) (Cons #(list a) h (coerce t)) (Cons #(s:(list a){Cons? s}) h t));
            assert(eq2 #(list (s:(list a){Cons? s})) (Cons #(list a) h (coerce t)) (Cons #(s:(list a){Cons? s}) h t));
            assert(Cons #(list a) h (coerce t) === Cons #(s:(list a){Cons? s}) h t);
            Cons #(list a) h (coerce t)                       (* F* can   prove that Cons #(list a) ... === Cons #(s:(list a){Cons? s}) ... *)

let flatten_lemma (a:Type) (ss:list (s:list a {Cons? s}) {Cons? ss}) :
  Lemma (requires True) (ensures (Cons? (flatten (coerce ss)))) = ()

(* original code *)
(* assume Flatten: forall (a:Type) (ss:list (s:list a) {Cons? ss}) . *)
(*     Cons? (flatten ss) *)
