module IfCascadeNoSMT

open Pulse
#lang-pulse

// A variable guard uses its rewrites_to hypothesis directly. This cascade
// must therefore elaborate without solver-backed branch rewrites.
#push-options "--no_smt"

assume val p ([@@@mkey] b:bool) : slprop
assume val q : slprop
assume val on_true () : stt_ghost unit [] (p true) (fun _ -> q)
assume val on_false () : stt_ghost unit [] (p false) (fun _ -> q)

fn if_cascade_no_smt
  (b0:bool)
  (b1:bool)
  (b2:bool)
  (b3:bool)
  (b4:bool)
  (b5:bool)
  (b6:bool)
  (b7:bool)
  (b8:bool)
  (b9:bool)
  (b10:bool)
  (b11:bool)
  (b12:bool)
  (b13:bool)
  (b14:bool)
  (b15:bool)
  returns r:nat
{
  let mut result : nat = 0;
  if (b0)
  ensures exists* v. result |-> v
  {
    result := 1;
  } else {
    if (b1) {
      result := 1;
    } else {
      if (b2) {
        result := 1;
      } else {
        if (b3) {
          result := 1;
        } else {
          if (b4) {
            result := 1;
          } else {
            if (b5) {
              result := 1;
            } else {
              if (b6) {
                result := 1;
              } else {
                if (b7) {
                  result := 1;
                } else {
                  if (b8) {
                    result := 1;
                  } else {
                    if (b9) {
                      result := 1;
                    } else {
                      if (b10) {
                        result := 1;
                      } else {
                        if (b11) {
                          result := 1;
                        } else {
                          if (b12) {
                            result := 1;
                          } else {
                            if (b13) {
                              result := 1;
                            } else {
                              if (b14) {
                                result := 1;
                              } else {
                                if (b15) {
                                  result := 1;
                                } else {};
                              };
                            };
                          };
                        };
                      };
                    };
                  };
                };
              };
            };
          };
        };
      };
    };
  };
  !result
}

fn if_compound_no_smt (b:bool)
  requires p (not b)
  ensures q
{
  if (not b) {
    on_true ();
  } else {
    on_false ();
  }
}

#pop-options
