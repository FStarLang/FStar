module FStarC.TypeChecker.Primops.Array

open FStarC
open FStarC.Effect
open FStarC.Errors
open FStarC.Class.Monad
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings

open FStarC.TypeChecker.Primops.Base

module BU      = FStarC.Util
module EMB     = FStarC.Syntax.Embeddings
module NBETerm = FStarC.TypeChecker.NBETerm
module PC      = FStarC.Parser.Const
module S       = FStarC.Syntax.Syntax
module SS      = FStarC.Syntax.Subst
module U       = FStarC.Syntax.Util
module Z       = FStarC.BigInt

let as_primitive_step is_strong (l, arity, u_arity, f, f_nbe) =
  FStarC.TypeChecker.Primops.Base.as_primitive_step_nbecbs is_strong (l, arity, u_arity, f, (fun cb univs args -> f_nbe univs args))

let arg_as_int (a:arg) : option Z.t = fst a |> try_unembed_simple

let arg_as_list {|e:EMB.embedding 'a|} (a:arg)
: option (list 'a)
  = fst a |> try_unembed_simple

let mixed_binary_op
  (as_a : arg -> option 'a)
  (as_b : arg -> option 'b)
  (embed_c : Range.range -> 'c -> term)
  (f : Range.range -> universes -> 'a -> 'b -> option 'c)
  (psc : psc)
  (norm_cb : EMB.norm_cb)
  (univs : universes)
  (args : args)
  : option term
  = match args with
    | [a;b] ->
       begin
       match as_a a, as_b b with
       | Some a, Some b ->
         (match f psc.psc_range univs a b with
          | Some c -> Some (embed_c psc.psc_range c)
          | _ -> None)
       | _ -> None
       end
    | _ -> None

let mixed_ternary_op
  (as_a : arg -> option 'a)
  (as_b : arg -> option 'b)
  (as_c : arg -> option 'c)
  (embed_d : Range.range -> 'd -> term)
  (f : Range.range -> universes -> 'a -> 'b -> 'c -> option 'd)
  (psc : psc)
  (norm_cb : EMB.norm_cb)
  (univs : universes)
  (args : args)
  : option term
  = match args with
    | [a;b;c] ->
       begin
       match as_a a, as_b b, as_c c with
       | Some a, Some b, Some c ->
         (match f psc.psc_range univs a b c with
          | Some d -> Some (embed_d psc.psc_range d)
          | _ -> None)
       | _ -> None
       end
    | _ -> None


let bogus_cbs = {
    NBETerm.iapp = (fun h _args -> h);
    NBETerm.translate = (fun _ -> failwith "bogus_cbs translate");
}

let ops : list primitive_step =
  let of_list_op =
    let emb_typ t = ET_app(PC.immutable_array_t_lid |> Ident.string_of_lid, [t]) in
    let un_lazy universes t l r =
      S.mk_Tm_app
        (S.mk_Tm_uinst (U.fvar_const PC.immutable_array_of_list_lid) universes)
        [S.iarg t; S.as_arg l]
        r
    in
    (  PC.immutable_array_of_list_lid, 2, 1,
       mixed_binary_op
          (fun (elt_t, _) -> Some elt_t) //the first arg of of_list is the element type
          (fun (l, q) -> //2nd arg: try_unembed_simple as a list term
            match arg_as_list #_ #FStarC.Syntax.Embeddings.e_any (l, q) with
            | Some lst -> Some (l, lst)
            | _ -> None)
          (fun r (universes, elt_t, (l, blob)) ->
            //embed the result back as a Tm_lazy with the `ImmutableArray.t term` as the blob
            //The kind records the type of the blob as IA.t "any"
            //and the interesting thing here is that the thunk represents the blob back as pure F* term
            //IA.of_list u#universes elt_t l.
            //This unreduced representation can be used in a context where the blob doesn't make sense,
            //e.g., in the SMT encoding, we represent the blob computed by of_list l
            //just as the unreduced term `of_list l`
            S.mk (Tm_lazy { blob;
                            lkind=Lazy_embedding (emb_typ EMB.(emb_typ_of _ #e_any ()), Thunk.mk (fun _ -> un_lazy universes elt_t l r));
                            ltyp=S.mk_Tm_app (S.mk_Tm_uinst (U.fvar_const PC.immutable_array_t_lid) universes) [S.as_arg elt_t] r;
                            rng=r }) r)
          (fun r universes elt_t (l, lst) ->
            //The actual primitive step computing the IA.t blob
             let blob = FStar.ImmutableArray.Base.of_list #term lst in
             Some (universes, elt_t, (l, FStarC.Dyn.mkdyn blob))),
       NBETerm.mixed_binary_op
         (fun (elt_t, _) -> Some elt_t)
         (fun (l, q) ->
           match NBETerm.arg_as_list NBETerm.e_any (l, q) with
           | None -> None
           | Some lst -> Some (l, lst))
         (fun (universes, elt_t, (l, blob)) ->
           //The embedding is similar to the non-NBE case
           //But, this time the thunk is the NBE.t representation of `of_list l`
           NBETerm.mk_t <|
           NBETerm.Lazy (Inr (blob, emb_typ EMB.(emb_typ_of _ #e_any ())),
                         Thunk.mk (fun _ ->
                           NBETerm.mk_t <| NBETerm.FV (S.lid_as_fv PC.immutable_array_of_list_lid None,
                                                      universes,
                                                      [NBETerm.as_arg l]))))
         (fun  universes elt_t (l, lst) ->
            let blob = FStar.ImmutableArray.Base.of_list #NBETerm.t lst in
            Some (universes, elt_t, (l, FStarC.Dyn.mkdyn blob))))
  in
  let arg1_as_elt_t (x:arg) : option term = Some (fst x) in
  let arg2_as_blob (x:arg) : option FStarC.Dyn.dyn =
      //try_unembed_simple an arg as a IA.t blob if the emb_typ
      //of the lkind tells us it has the right type
      match (SS.compress (fst x)).n with
      | Tm_lazy {blob=blob; lkind=Lazy_embedding (ET_app(head, _), _)}
        when head=Ident.string_of_lid PC.immutable_array_t_lid -> Some blob
      | _ -> None
  in
  let arg2_as_blob_nbe (x:NBETerm.arg) : option FStarC.Dyn.dyn =
      //try_unembed_simple an arg as a IA.t blob if the emb_typ
      //tells us it has the right type
      let open FStarC.TypeChecker.NBETerm in
      match (fst x).nbe_t with
      | Lazy (Inr (blob, ET_app(head, _)), _)
        when head=Ident.string_of_lid PC.immutable_array_t_lid -> Some blob
      | _ -> None
  in
  let length_op =
    let embed_int (r:Range.range) (i:Z.t) : term = embed_simple r i in
    let run_op (blob:FStarC.Dyn.dyn) : option Z.t =
        Some (BU.array_length #term (FStarC.Dyn.undyn blob))
    in
    ( PC.immutable_array_length_lid, 2, 1,
      mixed_binary_op arg1_as_elt_t //1st arg of length is the type
                      arg2_as_blob //2nd arg is the IA.t term blob
                      embed_int //the result is just an int, so embed it back
                      (fun _r _universes _ blob -> run_op blob),
      //NBE case is similar
      NBETerm.mixed_binary_op
         (fun (elt_t, _) -> Some elt_t)
         arg2_as_blob_nbe
         (fun (i:Z.t) -> NBETerm.embed NBETerm.e_int bogus_cbs i)
         (fun _universes _ blob -> run_op blob) )
  in
  let index_op =
      (PC.immutable_array_index_lid, 3, 1,
       mixed_ternary_op arg1_as_elt_t //1st arg of index is the type
                        arg2_as_blob //2nd arg is the `IA.t term` blob
                        arg_as_int //3rd arg is an int
                        (fun r tm -> tm) //the result is just a term, so the embedding is the identity
                        (fun r _universes _t blob i -> Some (BU.array_index #term (FStarC.Dyn.undyn blob) i)),
      NBETerm.mixed_ternary_op
         (fun (elt_t, _) -> Some elt_t)
         arg2_as_blob_nbe //2nd arg is an `IA.t NBEterm.t` blob
         NBETerm.arg_as_int
         (fun tm -> tm) //In this case, the result is a NBE.t, so embedding is the identity
         (fun _universes _t blob i  -> Some (BU.array_index #NBETerm.t (FStarC.Dyn.undyn blob) i)))
  in
  List.map (as_primitive_step true)
  [of_list_op; length_op; index_op]
