open Prims
let int1 m f ua em r args =
  match args with
  | (a,uu____60)::[] ->
      let uu____69 =
        let uu____70 = let uu____71 = ua a in f uu____71 in em uu____70 in
      FStar_Pervasives_Native.Some uu____69
  | uu____72 -> FStar_Pervasives_Native.None
let int2 m f ua ub em r args =
  match args with
  | (a,uu____151)::(b,uu____153)::[] ->
      let uu____167 =
        let uu____168 =
          let uu____169 = ua a in
          let uu____170 = ub b in f uu____169 uu____170 in
        em uu____168 in
      FStar_Pervasives_Native.Some uu____167
  | uu____171 -> FStar_Pervasives_Native.None
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
  let uu____298 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view in
  let uu____299 =
    let uu____301 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term in
    let uu____302 =
      let uu____304 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          FStar_Reflection_Basic.embed_string_list in
      let uu____306 =
        let uu____308 =
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv
            (FStar_Reflection_Basic.unembed_list
               FStar_Reflection_Basic.unembed_string)
            FStar_Reflection_Basic.embed_fvar in
        let uu____310 =
          let uu____312 =
            mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
              FStar_Reflection_Basic.unembed_binder
              FStar_Reflection_Basic.embed_string in
          let uu____313 =
            let uu____315 =
              mk2 "__compare_binder" FStar_Reflection_Basic.order_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.embed_order in
            let uu____316 =
              let uu____318 =
                mk11 "__type_of_binder"
                  (fun uu____325  ->
                     match uu____325 with
                     | (b,q) -> b.FStar_Syntax_Syntax.sort)
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Reflection_Basic.embed_term in
              let uu____331 =
                let uu____333 =
                  mk2 "__is_free" FStar_Reflection_Basic.is_free
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_bool in
                let uu____334 =
                  let uu____336 =
                    mk11 "__fresh_binder"
                      (fun t  ->
                         let uu____343 =
                           FStar_Syntax_Syntax.gen_bv "__refl"
                             FStar_Pervasives_Native.None t in
                         (uu____343, FStar_Pervasives_Native.None))
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_binder in
                  let uu____345 =
                    let uu____347 =
                      mk2 "__term_eq" FStar_Syntax_Util.term_eq
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.embed_bool in
                    let uu____350 =
                      let uu____352 =
                        mk11 "__term_to_string"
                          FStar_Syntax_Print.term_to_string
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_string in
                      let uu____353 =
                        let uu____355 =
                          mk11 "__binders_of_env"
                            FStar_TypeChecker_Env.all_binders
                            FStar_Reflection_Basic.unembed_env
                            FStar_Reflection_Basic.embed_binders in
                        let uu____356 =
                          let uu____358 =
                            mk2 "__lookup_typ"
                              FStar_Reflection_Basic.lookup_typ
                              FStar_Reflection_Basic.unembed_env
                              FStar_Reflection_Basic.unembed_string_list
                              FStar_Reflection_Basic.embed_sigelt_view in
                          [uu____358] in
                        uu____355 :: uu____356 in
                      uu____352 :: uu____353 in
                    uu____347 :: uu____350 in
                  uu____336 :: uu____345 in
                uu____333 :: uu____334 in
              uu____318 :: uu____331 in
            uu____315 :: uu____316 in
          uu____312 :: uu____313 in
        uu____308 :: uu____310 in
      uu____304 :: uu____306 in
    uu____301 :: uu____302 in
  uu____298 :: uu____299