(*
   Copyright 2020 Microsoft Research

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

module Pulse.Lib.PCM.Product

//
// A PCM for product of two PCMs
//   with composability and op defined pointwise
//
// Given frame preserving updates for the two PCMs,
//   we can construct a frame preserving update for the product PCM
//
// As a corollary, given a frame preserving update for one of the PCMs,
//   we can construct a frame preserving update for the product PCM that
//   does not change the other component
//

open FStar.PCM

module G = FStar.Ghost

let composable (#a #b:Type) (pa:pcm a) (pb:pcm b) : symrel (a & b) =
  fun (x1, y1) (x2, y2) -> pa.p.composable x1 x2 /\ pb.p.composable y1 y2

let op (#a #b:Type) (pa:pcm a) (pb:pcm b) (p1:a & b) (p2:a & b { composable pa pb p1 p2 })
  : a & b =
  pa.p.op  (fst p1) (fst p2),
  pb.p.op  (snd p1) (snd p2)

let comm #a #b #pa #pb (p1:a & b) (p2:a & b { composable pa pb p1 p2 })
  : Lemma (op pa pb p1 p2 == op pa pb p2 p1) =
  pa.comm (fst p1) (fst p2);
  pb.comm (snd p1) (snd p2)

let pcm_prod #a #b (pa:pcm a) (pb:pcm b) : pcm (a & b) =
  {
    p = {
      composable = composable pa pb;
      op = op pa pb;
      one = (pa.p.one, pb.p.one);
    };
    comm = (fun (x1, y1) (x2, y2) ->
      pa.comm x1 x2;
      pb.comm y1 y2);
    assoc = (fun(x1, y1)(x2, y2) (x3, y3) ->
      pa.assoc x1 x2 x3;
      pb.assoc y1 y2 y3);
    assoc_r = (fun(x1, y1)(x2, y2) (x3, y3) ->
      pa.assoc_r x1 x2 x3;
      pb.assoc_r y1 y2 y3);
    is_unit = (fun (x, y) ->
      pa.is_unit x;
      pb.is_unit y);
    refine = (fun (x, y) -> pa.refine x /\ pb.refine y);
  }

let compatible_intro #a #b #pa #pb (p1 p2:a & b)
  : Lemma (requires compatible pa (fst p1) (fst p2) /\ compatible pb (snd p1) (snd p2))
          (ensures compatible (pcm_prod pa pb) p1 p2)
          [SMTPat (compatible (pcm_prod pa pb) p1 p2)] =
  
  let goal = compatible (pcm_prod pa pb) p1 p2 in
  compatible_elim pa (fst p1) (fst p2)
    goal
    (fun f_a ->
     compatible_elim pb (snd p1) (snd p2)
       goal
       (fun f_b -> compatible_intro (pcm_prod pa pb) p1 p2 (f_a, f_b)))

#push-options "--warn_error -271"
let mk_frame_preserving_upd #a #b #pa #pb
  (p1:G.erased (a & b))
  (p2:a & b)
  (fp_upd_a:frame_preserving_upd pa (fst (G.reveal p1)) (fst p2))
  (fp_upd_b:frame_preserving_upd pb (snd (G.reveal p1)) (snd p2))
  : frame_preserving_upd (pcm_prod pa pb) (G.reveal p1) p2 =
  fun (vx, vy) ->
  let p = pcm_prod pa pb in
  let r = fp_upd_a vx, fp_upd_b vy in
  let aux (frame:a & b)
    : Lemma (requires PCM.composable (pcm_prod pa pb) p1 frame)
            (ensures
               PCM.composable (pcm_prod pa pb) p2 frame /\
               (PCM.op (pcm_prod pa pb) p1 frame == (vx, vy) ==> PCM.op (pcm_prod pa pb) p2 frame == r))
            [SMTPat ()] =
    assert (PCM.composable pa (fst (G.reveal p1)) (fst frame));
    assert (PCM.composable pb (snd (G.reveal p1)) (snd frame))
  in
  r
#pop-options

let mk_frame_preserving_upd_fst #a #b #pa #pb
  (x1:G.erased a)
  (x2:a)
  (y:b)
  (fp_upd_a:frame_preserving_upd pa (G.reveal x1) x2)
  : frame_preserving_upd (pcm_prod pa pb) (G.reveal x1, y) (x2, y) =
  mk_frame_preserving_upd
    (G.hide (G.reveal x1, y))
    (x2, y)
    fp_upd_a
    (no_op_is_frame_preserving pb y)

let mk_frame_preserving_upd_snd #a #b #pa #pb
  (x:a)
  (y1:G.erased b)
  (y2:b)
  (fp_upd_b:frame_preserving_upd pb (G.reveal y1) y2)
  : frame_preserving_upd (pcm_prod pa pb) (x, G.reveal y1) (x, y2) =
  mk_frame_preserving_upd
    (G.hide (x, G.reveal y1))
    (x, y2)
    (no_op_is_frame_preserving pa x)
    fp_upd_b
