module DocsSplice

open FStar.Tactics.V2

let make_type () : Tac (list sigelt) =
  let ty : term = pack (Tv_FVar (pack_fv (explode_qn "DocsSplice.generated"))) in
  let ctor : ctor = (["DocsSplice"; "Generated"], ty) in
  let se =
    pack_sigelt (
      Sg_Inductive {
        nm = explode_qn "DocsSplice.generated";
        univs = [];
        params = [];
        typ = `Type0;
        ctors = [ctor]
      })
  in
  [se]

[@@doc "Documentation on a splice must not be inherited by its generated type."]
%splice[generated; Generated] (make_type ())
