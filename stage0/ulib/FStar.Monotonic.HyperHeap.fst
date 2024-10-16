(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi, and Microsoft Research

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
module FStar.Monotonic.HyperHeap

module Set = FStar.Set
module Map = FStar.Map

open FStar.Monotonic.Heap
open FStar.Ghost

(*
 * This is a temporary assumption, we should fix the model to get rid of it
 *)
assume HasEq_rid: hasEq (erased (list (int & int & bool)))

let rid = erased (list (int & int & bool))

let reveal r = FStar.List.Tot.map (fun (i, j, _) -> i, j) (reveal r)

let color r =
  match reveal r with
  | [] -> 0
  | (c, _)::_ -> c

let rid_freeable r =
  match Ghost.reveal r with
  | [] -> false
  | (_, _, b)::_ -> b

let root = hide []

let root_last_component () = ()

let lemma_root_has_color_zero _ = ()

let root_is_not_freeable () = ()

let rid_length r = List.Tot.length (reveal r)

let rid_tail (r:rid{rid_length r > 0}) = elift1_p (tot_to_gtot Cons?.tl) r

let rec includes r1 r2 =
  if r1 = r2 then true
  else if rid_length r2 > rid_length r1
  then includes r1 (rid_tail r2)
  else false

private let rec lemma_aux (k:rid) (i:rid)
  :Lemma  (requires (rid_length k > 0 /\
                     rid_length k <= rid_length i /\
                     includes k i /\
                     not (includes (rid_tail k) i)))
          (ensures False)
          (decreases (rid_length i))
  = lemma_aux k (rid_tail i)

let rec lemma_disjoint_includes i j k =
  if rid_length k <= rid_length j
  then ()
  else (lemma_disjoint_includes i j (rid_tail k);
        if rid_length i <= rid_length (rid_tail k)
        then ()
        else (if includes k i
              then lemma_aux k i
              else ()))

let extends r0 r1 = Cons? (reveal r0) && rid_tail r0 = r1

let parent r = rid_tail r

let lemma_includes_refl _ = ()

let lemma_extends_includes _ _ = ()

let lemma_includes_anti_symmetric _ _ = ()

let lemma_extends_disjoint _ _ _ = ()

let lemma_extends_parent _ = ()

let lemma_extends_not_root _ _ = ()

let lemma_extends_only_parent _ _ = ()

private let test0 :unit =
  assert (includes (hide [(0, 1, false) ; (1, 0, false)]) (hide [(2, 2, false); (0, 1, false); (1, 0, false)]))

private let test1 (r1:rid) (r2:rid{includes r1 r2}) :unit = assert (includes r1 (hide ((0, 0, false)::(Ghost.reveal r2))))

let mod_set _ = magic ()

let rec lemma_includes_trans i j k =
  if j = k then ()
  else match Ghost.reveal k with
        | hd::tl -> lemma_includes_trans i j (hide tl)

let lemma_modset _ _ = ()

let lemma_modifies_includes _ _ _ _ = ()

let lemma_modifies_includes2 _ _ _ _ = ()

let lemma_disjoint_parents _ _ _ _ = ()

let lemma_include_cons _ _ = ()

let extends_parent  _ _ = ()

let includes_child _ _ = ()

let root_is_root _ = ()

let extend r n c =
  elift1 (fun r ->
    let freeable = rid_freeable (hide r) in
    (c, n, freeable)::r
  ) r

let extend_monochrome_freeable r n freeable =
  elift1 (fun r ->
    let c = color (hide r) in
    (c, n, freeable)::r
  ) r

let extend_monochrome r n = extend_monochrome_freeable r n (rid_freeable r)

