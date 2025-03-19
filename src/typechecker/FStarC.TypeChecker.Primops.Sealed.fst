module FStarC.TypeChecker.Primops.Sealed

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax

open FStarC.TypeChecker.Primops.Base

module EMB     = FStarC.Syntax.Embeddings
module NBETerm = FStarC.TypeChecker.NBETerm
module PC      = FStarC.Parser.Const
module S       = FStarC.Syntax.Syntax
module U       = FStarC.Syntax.Util

let bogus_cbs = {
    NBETerm.iapp = (fun h _args -> h);
    NBETerm.translate = (fun _ -> failwith "bogus_cbs translate");
}

let ops =
  List.map (fun p -> { as_primitive_step_nbecbs true p with renorm_after = true}) [
    (PC.map_seal_lid, 4, 2,
      (fun psc univs cbs args ->
        match args with
        | [(ta, _); (tb, _); (s, _); (f, _)] ->
          begin
          let open EMB in
          let try_unembed (#a:Type) (e:embedding a) (x:term) : option a =
              try_unembed x id_norm_cb
          in
          match try_unembed e_any ta,
                try_unembed e_any tb,
                try_unembed (e_sealed e_any) s,
                try_unembed e_any f with
          | Some ta, Some tb, Some s, Some f ->
            let r = U.mk_app f [S.as_arg (Sealed.unseal s)] in
            let emb = set_type ta e_any in
            Some (embed_simple psc.psc_range (Sealed.seal r))
          | _ -> None
          end
        | _ -> None),
      (fun cb univs args ->
        match args with
        | [(ta, _); (tb, _); (s, _); (f, _)] ->
          begin
          let open FStarC.TypeChecker.NBETerm in
          let try_unembed (#a:Type) (e:embedding a) (x:NBETerm.t) : option a =
              unembed e bogus_cbs x
          in
          match try_unembed e_any ta,
                try_unembed e_any tb,
                try_unembed (e_sealed e_any) s,
                try_unembed e_any f with
          | Some ta, Some tb, Some s, Some f ->
            let r = cb.iapp f [as_arg (Sealed.unseal s)] in
            let emb = set_type ta e_any in
            Some (embed (e_sealed emb) cb (Sealed.seal r))
          | _ -> None
          end
        | _ -> None
        ));
    (PC.bind_seal_lid, 4, 2,
      (fun psc univs cbs args ->
        match args with
        | [(ta, _); (tb, _); (s, _); (f, _)] ->
          begin
          let open EMB in
          let try_unembed (#a:Type) (e:embedding a) (x:term) : option a =
              try_unembed x id_norm_cb
          in
          match try_unembed e_any ta,
                try_unembed e_any tb,
                try_unembed (e_sealed e_any) s,
                try_unembed e_any f with
          | Some ta, Some tb, Some s, Some f ->
            let r = U.mk_app f [S.as_arg (Sealed.unseal s)] in
            Some (embed_simple #_ #e_any psc.psc_range r)
          | _ -> None
          end
        | _ -> None),
      (fun cb univs args ->
        match args with
        | [(ta, _); (tb, _); (s, _); (f, _)] ->
          begin
          let open FStarC.TypeChecker.NBETerm in
          let try_unembed (#a:Type) (e:embedding a) (x:NBETerm.t) : option a =
              unembed e bogus_cbs x
          in
          match try_unembed e_any ta,
                try_unembed e_any tb,
                try_unembed (e_sealed e_any) s,
                try_unembed e_any f with
          | Some ta, Some tb, Some s, Some f ->
            let r = cb.iapp f [as_arg (Sealed.unseal s)] in
            let emb = set_type ta e_any in
            Some (embed emb cb r)
          | _ -> None
          end
        | _ -> None
        ));
  ]
