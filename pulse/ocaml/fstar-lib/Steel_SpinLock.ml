type lock_t = Mutex.t

type 'a lock = lock_t

let new_lock (_:unit) : 'unit lock = Mutex.create ()

let acquire (_:unit) (l:unit lock) = Mutex.lock l

let release (_:unit) (l:unit lock) = Mutex.unlock l
