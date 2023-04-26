#lang forge

option problem_type temporal
option max_tracelength 14
option min_tracelength 3

sig VirtualAddress {}

sig Page {}

abstract sig Process {
    pid : one Int,
    var pagetable : pfunc VirtualAddress -> Page
}

sig UserProcess extends Process {}

one sig Kernel extends Process {
    var active : set Process,
    var available : set Page
}

pred init {
    no UserProcess.pagetable // no mappings in user process' pagetable yet
    some Kernel.pagetable
    some Kernel.available
    no Kernel.active
}

pred wellformed {
    
    // a page is available iff it is not mapped to by any process
    all page : Page | {
        {page in Kernel.available} <=> {all p : Process | (no va: VirtualAddress | p.pagetable[va] = page)}
    }

    // in a single process, at most one va should map to a page
    all proc : Process | {
        all page: Page | {
            
            // proc only has one virtual address mapping to the page
            all disj va, va2 : VirtualAddress | (proc.pagetable[va] = page) => {
                proc.pagetable[va2] != page
            }
            
            // process isolation: no process should share pages with another process
            some va: VirtualAddress | proc.pagetable[va] = page => {
                no proc2 : Process | {
                    some va2 : VirtualAddress | proc2.pagetable[va2] = page
                }
            }
        }
    }
    
    // no two processes have the same PID
    all disj p1, p2: Process | {
        p1.pid != p2.pid
    }

    // kernel has PID 0, all others are > 0
    Kernel.pid = 0
    all uproc : UserProcess | uproc.pid > 0
}

pred maintenance[proc: Process] {
    all p: Process | (p != proc) => {
        p.pagetable' = p.pagetable
    }
    Kernel.active' = Kernel.active
}

// TODO: nothing is getting allocated in traces even when we call this on kalloc[proc, proc]
pred kalloc[proc : Process, caller : Process] {
    (proc = caller) => {
        some page : Page | (page in Kernel.available) => {
            some va2 : VirtualAddress | caller.pagetable' = caller.pagetable + (va2 -> page)
            Kernel.available' = Kernel.available - page
        }
    } else {
        // not allowed to allocate a page to another process; do nothing
        // TODO: can't allocate two different pages to a process at a time b/c we're saying that everything must
        // remain the same if *this* kalloc call fails, but what if another one should succeed?
        proc.pagetable' = proc.pagetable
        Kernel.available' = Kernel.available  
    }

    maintenance[caller]
}

pred kfree[page : Page, caller : Process] {
    
    some va : VirtualAddress | caller.pagetable[va] = page => {
        Kernel.available' = Kernel.available + page
        caller.pagetable' = caller.pagetable - (va -> page)
    } else {
        Kernel.available' = Kernel.available
    }

    maintenance[caller]
}

pred exit[proc : UserProcess] {
    // kfree all pages mapped to by proc
    all page : Page | {
        some va : VirtualAddress | (proc.pagetable[va] = page) => {
            kfree[page, proc]
        }
    } 
    no proc.pagetable'
    Kernel.active' = Kernel.active - proc
    
}

pred doNothing {
    // GUARD: all UserProcesses have exited
    no Kernel.active
    // ACTION: maintain everything
    Kernel.active' = Kernel.active
    Kernel.available' = Kernel.available
}

pred traces {
    init
    always(wellformed)
    always(

        // multiple processes can do stuff at a time, but the same process can't do two things at a time
        all proc : Process | {
            // MODELING CHOICE : every process is always doing something
            some proc2 : Process | {
                //kalloc[proc, proc]

                // TODO : figure out why the below is unsat
                //{kalloc[proc, proc2] and (no p : Page | kfree[p, proc])}
                //or
                //{not kalloc[proc, proc2] and (some p : Page | kfree[p, proc])}
            }
        } or
        doNothing
    )
}


run {
    traces
} for exactly 2 UserProcess, exactly 5 Page, exactly 5 VirtualAddress