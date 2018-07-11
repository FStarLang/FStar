module Alt

open FStar.Tactics

let tfail s () = fail s

let _ = assert True by (tfail "1" <|> tfail "2" <|> tfail "3" <|> trivial)

let _ = assert True by (fun () -> let i =
                                    Tactics.first [(fun () -> fail "1"; 1);
                                                   (fun () -> fail "2"; 2);
                                                   (fun () -> fail "3"; 3);
                                                   (fun () ->           4);
                                                   (fun () -> fail "5"; 5);
                                                   (fun () ->           6);
                                                   ]
                                   in guard (i = 4))
