open Prims
let int1 m f ua em r args =
  match args with
  | (a,uu____52)::[] ->
      let uu____65 =
        let uu____66 = let uu____67 = ua a  in f uu____67  in em uu____66  in
      Some uu____65
  | uu____68 -> None 
let int2 m f ua ub em r args =
  match args with
  | (a,uu____137)::(b,uu____139)::[] ->
      let uu____160 =
        let uu____161 =
          let uu____162 = ua a  in
          let uu____163 = ub b  in f uu____162 uu____163  in
        em uu____161  in
      Some uu____160
  | uu____164 -> None 
let reflection_primops :
  FStar_TypeChecker_Normalize.primitive_step Prims.list =
  let mklid nm = FStar_Reflection_Data.fstar_refl_syntax_lid nm  in
  let mk1 l arity fn =
    {
      FStar_TypeChecker_Normalize.name = l;
      FStar_TypeChecker_Normalize.arity = arity;
      FStar_TypeChecker_Normalize.strong_reduction_ok = false;
      FStar_TypeChecker_Normalize.interpretation = fn
    }  in
  let mk11 nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____291 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view
     in
  let uu____292 =
    let uu____294 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term
       in
    let uu____295 =
      let uu____297 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          (FStar_Reflection_Basic.embed_list
             FStar_Reflection_Basic.embed_string
             FStar_TypeChecker_Common.t_string)
         in
      let uu____299 =
        let uu____301 =
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv
            (FStar_Reflection_Basic.unembed_list
               FStar_Reflection_Basic.unembed_string)
            FStar_Reflection_Basic.embed_fvar
           in
        let uu____303 =
          let uu____305 =
            mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
              FStar_Reflection_Basic.unembed_binder
              FStar_Reflection_Basic.embed_string
             in
          let uu____306 =
            let uu____308 =
              mk2 "__compare_binder" FStar_Reflection_Basic.order_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.embed_order
               in
            let uu____309 =
              let uu____311 =
                mk11 "__type_of_binder"
                  (fun uu____316  ->
                     match uu____316 with
                     | (b,q) -> b.FStar_Syntax_Syntax.sort)
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Reflection_Basic.embed_term
                 in
              let uu____323 =
                let uu____325 =
                  mk2 "__is_free" FStar_Reflection_Basic.is_free
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_bool
                   in
                let uu____326 =
                  let uu____328 =
                    mk11 "__fresh_binder"
                      (fun t  ->
                         let uu____333 =
                           FStar_Syntax_Syntax.gen_bv "__refl" None t  in
                         (uu____333, None))
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_binder
                     in
                  let uu____335 =
                    let uu____337 =
                      mk2 "__term_eq" FStar_Syntax_Util.term_eq
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.embed_bool
                       in
                    let uu____342 =
                      let uu____344 =
                        mk11 "__term_to_string"
                          FStar_Syntax_Print.term_to_string
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_string
                         in
                      [uu____344]  in
                    uu____337 :: uu____342  in
                  uu____328 :: uu____335  in
                uu____325 :: uu____326  in
              uu____311 :: uu____323  in
            uu____308 :: uu____309  in
          uu____305 :: uu____306  in
        uu____301 :: uu____303  in
      uu____297 :: uu____299  in
    uu____294 :: uu____295  in
  uu____291 :: uu____292 