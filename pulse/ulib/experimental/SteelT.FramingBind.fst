module SteelT.FramingBind
open Steel.Memory
irreducible
let resolve_framing : unit = ()
irreducible
let resolve_framing_forall : unit = ()


type pre_t = hprop u#1
type post_t (a:Type) = a -> hprop u#1

type repr (a:Type u#a) (pre:pre_t) (post:post_t a) = unit -> unit

let returnc (a:Type u#a) (x:a) (#[@resolve_framing] p:a -> hprop)
: repr a (p x) p
= admit()

open Steel.Memory.Tactics

let can_be_split_into_forall (#a:Type) (outer inner delta:post_t a)
  = forall (x:a). can_be_split_into (outer x) (inner x) (delta x)

let can_be_split_into_forall_2 (#a #b:Type)
  (outer:post_t b) (inner:a -> post_t b) (delta:post_t a)
  = forall (x:a) (y:b). can_be_split_into (outer y) (inner x y) (delta x)

(*
outer_pre <==>
pre_f * frame_f               // emp * emp

x := f ()

post_f x * frame_f            // ref x * emp

<==>

pre_g x * frame_g x           // emp * ref x

y := g x ()

post_g x y * frame_g x        // ref y * ref x

<==> outer_post y
*)
let bind (a:Type) (b:Type)
  (#[@resolve_framing] outer_pre:pre_t)
  (#[@resolve_framing] pre_f:pre_t)
  (#[@resolve_framing] frame_f:hprop)
  (#[@resolve_framing] _u:squash (can_be_split_into outer_pre pre_f frame_f))

  (#[@resolve_framing] post_f:post_t a)
  (#[@resolve_framing] pre_g:post_t a)
  (#[@resolve_framing] frame_g:post_t a)
  (#[@resolve_framing] _v:squash (can_be_split_into_forall
    (fun x -> post_f x `star` frame_f) pre_g frame_g))

  (#[@resolve_framing] post_g:a -> post_t b)
  (#[@resolve_framing] outer_post:post_t b)
  (#[@resolve_framing] _w:squash (can_be_split_into_forall_2 outer_post post_g frame_g))

  (f:repr a pre_f post_f)
  (g:(x:a -> repr b (pre_g x) (post_g x)))
: repr b outer_pre outer_post
= admit()

let subcomp
  (a:Type) (pre:pre_t) (post:post_t a)
  (f:repr a pre post)
: Pure (repr a pre post)
  (requires True)
  (ensures fun _ -> True)
= admit() //f


let if_then_else (a:Type) (pre:pre_t) (post:post_t a)
  (f:repr a pre post)
  (g:repr a pre post)
  (p:Type0)
: Type
= repr a pre post

#push-options "--lax"
reifiable reflectable
layered_effect {
  SteelT : a:Type -> pre:pre_t -> post:post_t a -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}
#pop-options

let bind_pure_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b)
  (f:unit -> PURE a wp) (g:(x:a -> repr b pre_g post_g))
: repr b pre_g post_g
= admit()

polymonadic_bind (PURE, SteelT) |> SteelT = bind_pure_steel

let bind_steel_pure (a:Type) (b:Type)
    (pre_f:pre_t) (post_f:hprop)
    (wp_g:a -> pure_wp b)
    (f:repr a pre_f (fun _ -> post_f))
    (g:(x:a -> unit -> PURE b (wp_g x)))
: repr b pre_f (fun _ -> post_f)
= admit()

polymonadic_bind (SteelT, PURE) |> SteelT = bind_steel_pure

open FStar.Tactics
module T = FStar.Tactics

inline_for_extraction noextract let resolve_frame () : Tac unit =
  let open FStar.Algebra.CommMonoid.Equiv in
  norm [delta_only [`%can_be_split_into]];
  norm [delta_attr [`%__reduce__];
        delta_only [
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta];
  canon()

inline_for_extraction noextract let resolve_frame_forall () : Tac unit =
  ignore (forall_intro ());
  resolve_frame()

inline_for_extraction noextract let resolve_frame_forall_2 () : Tac unit =
  ignore (forall_intro ());
  ignore (forall_intro ());
  resolve_frame()


[@(resolve_implicits)
  (resolve_framing)]
let resolve () : Tac unit =
    let rec aux (i:int) : Tac unit =
    T.dump ("State: " ^ string_of_int i);
    match T.goals () with
    | [] -> ()
    | g :: _ ->
      let f = T.term_as_formula' (goal_type g) in
//      T.print ("Goal formula is " ^ (formula_to_string f));
      match f with
      | Comp (Eq _) _ _ ->
//        T.print "Solving equality goal\n";
        T.trefl();
        aux (i + 1)

      | App t t' ->
//        T.print "Solving app goal\n";
        begin
        match T.inspect t' with
        | Tv_App hd _ ->
          begin
          match T.inspect hd with
          | Tv_App hd _ -> begin
            match T.inspect hd with
            | Tv_App hd _ ->
              if T.term_eq hd (quote (can_be_split_into)) then (
                T.focus resolve_frame;
                aux (i+1)
              ) else begin
                match T.inspect hd with
                | Tv_App hd _ ->
                  if T.term_eq hd (quote (can_be_split_into_forall)) then (
                    T.focus resolve_frame_forall;
                    aux (i+1)
                  ) else begin
                    match T.inspect hd with
                    | Tv_App hd _ ->
                    if T.term_eq hd (quote (can_be_split_into_forall_2)) then (
                      T.focus resolve_frame_forall_2;
                      aux (i+1)
                    ) else  T.fail "this is not an equality or a framing goal 1"
                    | _ -> T.fail "this is not an equality or a framing goal 2"
                  end
                | _ -> T.fail "this is not an equality or a framing goal 3"
                end
            | _ -> T.fail "this is not an equality or a framing goal 4"
          end
          | _ -> T.fail "this is not an equality or a framing goal 5"
          end
        | _ -> T.fail "this is not an equality or a framing goal 6"
        end

      | _ -> // framing should have been handled beforehand
        T.fail "this is not an equality or a framing goal 7"
  in
  aux 0

assume
val myref : Type0

assume
val myref_hprop (x:myref) : hprop

assume
val dependent_provides (_:unit)
  : SteelT myref emp myref_hprop

assume
val nop (_:unit) : SteelT unit emp (fun c -> emp)

assume
val h_admit (#a:Type)
             (#[@resolve_framing] p:hprop)
             (#[@resolve_framing] q:a -> hprop)
             (_:unit) : SteelT a p q

//#push-options "--print_implicits --debug_level ResolveImplicitsHook"
assume
val ret (#a:Type) (x:a) (p:a -> hprop)
  : SteelT a (p x) p

val test_ok1 (_:unit)
  : SteelT myref emp (fun x -> myref_hprop x)

let test_ok1 _
  = let tr = dependent_provides () in
    // h_admit #_ #(myref_hprop tr) #myref_hprop ()
    // AF: This does not work because of scoping issues on myref_hprop tr
    nop();

    ret tr myref_hprop

    // nop ();
    // tr
