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
(* Stateful iterators in the style of FX (PLPV '11) *)

module FXPrims 
private type valid :: 'a::* => 'a => A = 
   | MkToken : 'a::* -> x:'a -> valid 'a x

type nat =
  | O : nat
  | S : nat -> nat
  | P : nat -> nat  (* extending nat with a "prev" construction *)

type GT :: nat => nat => P
 
val plus: x:nat -> y:nat -> z:nat { GT y O => GT z x}

val impos: 'a::A -> (x:unit{False}) -> 'a
end 

(* ******************************************************************************** *)

module FXList : FXPrims
open FXPrims
(* assume List_exhaustive:forall (x:list 'a). (x=[]) || (exists (hd:'a) (tl:list 'a). x=(hd::tl)) *)

val mkNil: unit -> (p:list 'a * valid (list 'a) p * (x:unit{p=[]}))
let mkNil x =
  let l = ([]:list 'a) in
    (l, MkToken l, ())

val isNil: p:list 'a -> (b:bool{b=true <=> (p=[])})
let isNil p = match p with
  | [] -> true
  | hd::tl -> false

val mkCons: hd:'a
          -> tl:list 'a
          -> valid 'a hd
          -> valid (list 'a) tl
          >> (p:list 'a * tok:valid (list 'a) p * (x:unit{p=(hd::tl)}))
let mkCons hd tl t_hd t_tl =
  let p = hd::tl in
    (p, MkToken p, ())

val isCons: p:list 'a
         -> (b:bool{b=true <=> exists (hd:'a) (tl:list 'a). p=(hd::tl)})
let isCons = function
  | [] -> false
  | hd::tl -> true

val unCons: p:list 'a
          -> valid (list 'a) p
          -> (x:unit{exists (hd:'a) (tl:list 'a). p=(hd::tl)})
          >> (hd:'a * tl:list 'a * thd:valid 'a hd * ttl:valid (list 'a) tl * (x:unit{p=(hd::tl)}))
let unCons p t_p x = match p with
  | hd::tl -> hd, tl, MkToken hd, MkToken tl, ()
  | [] -> impos ()
    
val iter: 'a::*
       -> 'PreF::('a => E)
       -> 'PostF::('a => 'a => E)
       -> 'Inv::(list 'a => E)
       -> 'Post::(list 'a => list 'a => E)
       -> f:(p:'a -> valid 'a p -> (x:unit{'PreF p}) >> (r:unit * q:'a * tp:valid 'a q * (z:unit{'PostF p q})))
       -> pl:list 'a
       -> valid (list 'a) pl
       -> (x:unit{ ('Inv pl) &&
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
      assert (pl=(hd::tl));
      assert ('Inv pl);
      assert ('Inv (hd::tl));
      let _, hd', thd', _ = f hd thd () in
        assert ('Inv tl);
        let _, tl', ttl', _ = iter<'a, 'PreF, 'PostF, 'Inv, 'Post> f tl ttl () in
        let pl', tpl', _ = mkCons hd' tl' thd' ttl' in
          (), pl', tpl', ()
  else 
    (assert (forall (hd:'a) (tl:list 'a). (not(pl=[])) && not (pl=(hd::tl)));
     assume ((pl=[]) || (exists (hd:'a) (tl:list 'a). (pl=(hd::tl)))); (* can't seem to specialize List_exhaustive properly here. *)
     impos ())
end

(* ******************************************************************************** *)
module Point : FXPrims
open FXPrims

type pt = {x:nat; y:nat}

val mkPt: x:nat
       -> y:nat
       -> (p:pt * tok:valid pt p * (z:unit{p.x=x && p.y=y}))
let mkPt x y =
  let p = {x=x; y=y} in
    (p, MkToken p, ())

val setPtX: p:pt
         -> x:nat
         -> valid pt p
         -> (p':pt * tp':valid pt p' * (z:unit{p'.x=x && p'.y=p.y}))
let setPtX p x tok  =
  let p' = {p with x=x} in
    (p', MkToken p', ())

end

(* ******************************************************************************** *)

module Client
open FXPrims
open FXList
open Point

type plist = list pt

type IncrX :: plist => plist => E
assume IX_nil: IncrX [] []
assume IX_cons: forall (hd:pt) (hd':pt) (tl:plist) (tl':plist) (ll:plist) (ll':plist).
  ((ll=(hd::tl)) && (ll'=(hd'::tl')) && (GT hd'.x hd.x) && (IncrX tl tl')) =>
  (IncrX ll ll')

type Y_GT_O :: plist => E
assume (Y_GT_O [])
assume (forall (hd:pt) (tl:plist). (GT hd.y O && Y_GT_O tl) <=> Y_GT_O (hd::tl))

val incrx: p:pt -> valid pt p -> (x:unit{GT p.y O}) >> (r:unit * p':pt * tp':valid pt p' * (x:unit{GT p'.x p.x}))
let incrx p tok ig =
  let x' = (plus p.x p.y) in
    assert (GT x' p.x);
    let p', tok, _ = setPtX p x' tok in
      (), p', tok, ()

val call_iter: l:plist{Y_GT_O l}
            -> valid plist l
            >> (r:unit * l':plist * tl':valid plist l' * (x:unit{IncrX l l'}))
let call_iter l tl =
  let _, l', tl', _ =
    iter<pt, (fun (p:pt) => GT p.y O),
             (fun (p:pt) (p':pt) => GT p'.x p.x),
         Y_GT_O, IncrX> incrx l tl () in
    (), l', tl', ()

end
