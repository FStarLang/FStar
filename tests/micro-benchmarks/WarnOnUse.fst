module WarnOnUse

//I'm using report_assumes error so that expect_falure traps them
//There's also `--report_assumes warn`

#push-options "--report_assumes error"
[@(expect_failure [334])] //raised once, only in the first phase or in lax mode
let f (x:int) : False = admit()
#pop-options

#push-options "--report_assumes error"
#push-options "--warn_error -334" //this is accepted, but is a noop
                                  //cannot be overridden if report_assumes is set
                                  //I don't want the use of "--report_assumes warn" on the cmd line
                                  //to break code that may otherwise be using --warn_error on 334
[@(expect_failure [334])]
let f (x:int) : False = admit()
#pop-options
#pop-options

#push-options "--warn_error @334" //can be turned on directly
[@(expect_failure [334])]
let f (x:int) : False = admit()

#push-options "--warn_error -334" //and then turned off
let f (x:int) : False = admit()
#pop-options
#pop-options

#push-options "--report_assumes warn"
#push-options "--admit_smt_queries true" //triggers a warning
#pop-options

#push-options "--report_assumes error"
[@(expect_failure [334])]
let ff (x:int) : False = admit()

#push-options "--report_assumes warn" //can't downgrade --report_assumes
[@(expect_failure [334])]
let ff (x:int) : False = admit()
#pop-options
