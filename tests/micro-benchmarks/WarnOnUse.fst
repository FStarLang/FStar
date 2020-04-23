module WarnOnUse

//I'm using report_assumes error so that expect_falure traps them
//There's also `--report_assumes warn`

#push-options "--report_assumes error"
[@(expect_failure [335])] //raised once, only in the first phase or in lax mode
let f (x:int) : False = admit()
#pop-options

#push-options "--report_assumes error"
#push-options "--warn_error -335" //this is accepted, but is a noop
                                  //cannot be overridden if report_assumes is set
                                  //I don't want the use of "--report_assumes warn" on the cmd line
                                  //to break code that may otherwise be using --warn_error on 335
[@(expect_failure [335])]
let f (x:int) : False = admit()
#pop-options
#pop-options

#push-options "--warn_error @335" //can be turned on directly
[@(expect_failure [335])]
let f (x:int) : False = admit()

#push-options "--warn_error -335" //and then turned off
let f (x:int) : False = admit()
#pop-options
#pop-options

#push-options "--report_assumes warn"
#push-options "--admit_smt_queries true" //triggers a warning
#pop-options

#push-options "--report_assumes error"
[@(expect_failure [335])]
let ff (x:int) : False = admit()

#push-options "--report_assumes warn" //can't downgrade --report_assumes
[@(expect_failure [335])]
let ff (x:int) : False = admit()
#pop-options
