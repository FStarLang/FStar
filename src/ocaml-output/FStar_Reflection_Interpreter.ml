open Prims
let int1 m f ua em r args =
  match args with
  | (a,uu____52)::[] ->
      let uu____65 =
        let uu____66 = let uu____67 = ua a in f uu____67 in em uu____66 in
      Some uu____65
  | uu____68 -> None
let int2 m f ua ub em r args =
  match args with
  | (a,uu____137)::(b,uu____139)::[] ->
      let uu____160 =
        let uu____161 =
          let uu____162 = ua a in
          let uu____163 = ub b in f uu____162 uu____163 in
        em uu____161 in
      Some uu____160
  | uu____164 -> None
let reflection_primops: FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  let mklid nm = FStar_Reflection_Data.fstar_refl_syntax_lid nm in
  let mk1 l arity fn =
    {
      FStar_TypeChecker_Normalize.name = l;
      FStar_TypeChecker_Normalize.arity = arity;
      FStar_TypeChecker_Normalize.strong_reduction_ok = false;
      FStar_TypeChecker_Normalize.interpretation = fn
    } in
  let mk11 nm f u1 em =
    let l = mklid nm in mk1 l (Prims.parse_int "1") (int1 l f u1 em) in
  let mk2 nm f u1 u2 em =
    let l = mklid nm in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em) in
  let uu____291 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view in
  let uu____292 =
    let uu____294 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        (FStar_Reflection_Basic.embed_option
           FStar_Reflection_Basic.embed_term
           FStar_Reflection_Data.fstar_refl_term) in
    let uu____296 =
      let uu____298 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          (FStar_Reflection_Basic.embed_list
             FStar_Reflection_Basic.embed_string
             FStar_TypeChecker_Common.t_string) in
      let uu____300 =
        let uu____302 =
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv
            (FStar_Reflection_Basic.unembed_list
               FStar_Reflection_Basic.unembed_string)
            FStar_Reflection_Basic.embed_fvar in
        let uu____304 =
          let uu____306 =
            mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
              FStar_Reflection_Basic.unembed_binder
              FStar_Reflection_Basic.embed_string in
          let uu____307 =
            let uu____309 =
              mk2 "__compare_binder" FStar_Reflection_Basic.order_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.embed_order in
            let uu____310 =
              let uu____312 =
                mk11 "__type_of_binder"
                  (fun uu____317  ->
                     match uu____317 with
                     | (b,q) -> b.FStar_Syntax_Syntax.sort)
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Reflection_Basic.embed_term in
              let uu____324 =
                let uu____326 =
                  mk11 "__term_to_string" FStar_Syntax_Print.term_to_string
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_string in
                [uu____326] in
              uu____312 :: uu____324 in
            uu____309 :: uu____310 in
          uu____306 :: uu____307 in
        uu____302 :: uu____304 in
      uu____298 :: uu____300 in
    uu____294 :: uu____296 in
  uu____291 :: uu____292