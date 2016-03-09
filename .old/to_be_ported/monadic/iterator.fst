(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module TestIterator

(* Canonical type with 2-state post-conditions *)
val iter: 'a::*
       -> 'PreF::('a => heap => E)
       -> 'PostF::('a => unit => heap => heap => E)
       -> 'Post::(list 'a => unit => heap => heap => E)
       -> 'Inv::(list 'a => heap => E)
      ==> (forall (h1:heap) (h2:heap) (h3:heap) (hd:'a) (tl:list 'a). 
             ('Inv [] h1 => 'Post [] () h1 h1) && 
             ('Inv (hd::tl) h1 => 'PreF hd h1) && 
             ('Inv (hd::tl) h1 && 'PostF hd () h1 h2 => Inv tl h2) &&
             ('Inv (hd::tl) h1 && 'PostF hd () h1 h2 && 'Post tl () h2 h3 => 'Post (hd::tl) () h1 h3))
       -> f:(x:'a -> ST ('PreF x) unit ('PostF x)
       -> l:list 'a
       -> ST ('Inv l) unit ('Post l)

--------------------------------------------------------------------------------

val iter: 'a::*
       -> 'PreF::('a => (unit => heap => E) => heap => E)
       -> 'Post::(unit => heap => E)
       -> 'Inv::(list 'a => heap => E)
      ==> ((forall (h1:heap). 'Inv [] h1 => 'Post () h1) &&
           (forall (h1:heap) (hd:'a) (tl:list 'a). 
              ('Inv (hd::tl) h1 => 'PreF hd (fun () => Inv tl) h1)))
       -> f:('PostF::(unit => heap => E) 
             -> x:'a 
             -> ST ('PreF x 'PostF) unit 'PostF)
       -> l:list 'a
       -> ST ('Inv l) unit 'Post 
let rec iter f l = match l with 
  | [] -> ()
  | hd::tl ->  
      let _ = f<fun (x:unit) => Inv tl> hd in (* Inv tl *)
        iter f tl

type MapGT0 :: list int => E

let client = 
  let x = ref 150 in 
  let divx<'PostF::unit => heap => E> i 
    : ST (fun (h:heap) => i > 0 && 'PostF () (Update x ((Select x h) / i) h)) 
         unit
         'PostF = x := (divide x i) in
  let _ = 
    iter<'PreF=(fun (i:'a) ('PostF::unit => heap => E) (h:heap) => i > 0 && 'PostF () (Update x ((Select x h) / i) h)), 
         'Post=(fun () (h:heap) => (Select x h) >= 0), 
         'Inv=(fun (l:list int) (h:heap) => MapGT0 l && (Select x h) >= 0)> divx [1;2;3;4;5] in 
    assert<Select x h >= 0> ()
  



================================================================================
val iter: 'a::*
       -> 'PreF::('a => heap => E)
       -> 'PostF::('a => unit => heap => E)
       -> 'Post::(list 'a => unit => heap => E)
       -> 'Inv::(list 'a => heap => E)
      ==> (forall (h:heap) (h':heap) (hd:'a) (tl:list 'a). 
             ('Inv [] h => 'Post [] () h) && 
             ('Inv (hd::tl) h => 'PreF hd h) && 
             ('Inv (hd::tl) h && 'PostF hd () h' => Inv tl h') &&
             ('Inv (hd::tl) h && 'PostF hd () h' && 'Post tl () h')


       -> f:(x:'a -> ST ('PreF x) unit 'PostF)
       -> l:list 'a
       -> ST ('Inv l) unit 'Post


(x:unit{ ('Inv pl) &&
                   ('Inv [] => 'Post [] []) &&
                   (forall (hd:'a) (tl:list 'a). 'Inv (hd::tl) => 'PreF hd) &&
                   (forall (hd:'a) (hd' :'a) (tl:list 'a). ('Inv (hd::tl) && 'PostF hd hd') => 'Inv tl) &&
                   (forall (hd:'a) (tl:list 'a) (hd' :'a) (tl':list 'a).
                              ('PostF hd hd' && 'Post tl tl') => 'Post (hd::tl) (hd'::tl')) })
       >> (r:unit * pl':list 'a * tpl:valid (list 'a) pl' *  (x:unit{'Post pl pl'}))
let rec iter f pl tpl ig =
  if isNil pl then (), pl, tpl, ()
  else if isCons pl then
    let hd, tl, thd, ttl, _ = unCons pl tpl () in
      assert<(pl=(hd::tl))>();
      assert<('Inv pl)>();
      assert<('Inv (hd::tl))>();
      let _, hd', thd', _ = f hd thd () in
        assert<('Inv tl)>();
        let _, tl', ttl', _ = iter<'a, 'PreF, 'PostF, 'Inv, 'Post> f tl ttl () in
        let pl', tpl', _ = mkCons hd' tl' thd' ttl' in
          (), pl', tpl', ()
  else 
    (assert<(forall (hd:'a) (tl:list 'a). (not(pl=[])) && not (pl=(hd::tl)))> ();
     assume ((pl=[]) || (exists (hd:'a) (tl:list 'a). (pl=(hd::tl)))); (* can't seem to specialize List_exhaustive properly here. *)
     impos ())
end

