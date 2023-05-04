#lang forge

option problem_type temporal
option max_tracelength 14
option min_tracelength 6

sig VirtualAddress {}

sig Page {}

abstract sig Process {
    var pagetable : pfunc VirtualAddress -> Page
}

sig UserProcess extends Process {}

one sig Kernel extends Process {
    var active : set UserProcess,
    var available : set Page
}

pred init {
    no UserProcess.pagetable // no mappings in user process' pagetable yet
    some Kernel.pagetable
    some Kernel.available
    all p : UserProcess | p in Kernel.active
    
    all page : Page | {
        // page is available iff it's not mapped to by the kernel
        {page in Kernel.available} <=> {(no va: VirtualAddress | Kernel.pagetable[va] = page)}
        // no two virtual addresses map to the same page
        all disj va, va2 : VirtualAddress | (Kernel.pagetable[va] = page) => {
            Kernel.pagetable[va2] != page
        }
    }
}

// pred wellformed {
    
//     // a page is available iff it is not mapped to by any process
//     all page : Page | {
//         {page in Kernel.available} <=> {all p : Process | (no va: VirtualAddress | p.pagetable[va] = page)}
//     }

//     // in a single process, at most one va should map to a page
//     all proc : Process | {
//         all page: Page | {
            
//             // proc only has one virtual address mapping to the page
//             all disj va, va2 : VirtualAddress | (proc.pagetable[va] = page) => {
//                 proc.pagetable[va2] != page
//             }
            
//             // process isolation: no process should share pages with another process
//             some va: VirtualAddress | proc.pagetable[va] = page => {
//                 no proc2 : Process | {
//                     some va2 : VirtualAddress | proc2.pagetable[va2] = page
//                 }
//             }
//         }
//     }
// }

pred maintainPagetables[proc: Process] {
    all p: Process | (p != proc) => {
        p.pagetable' = p.pagetable
    }
}

pred kalloc[proc : Process, caller : Process] {
    // GUARD
    proc = caller // extra restriction b/c it doesn't make sense for Kernel to allocate pages that a process hasn't asked for
    caller = Kernel or caller in Kernel.active
    proc in Kernel.active
    
    // ACTION
    some page : Page | {
        page in Kernel.available
        (VirtualAddress -> page) not in proc.pagetable
        some va2 : VirtualAddress | {
            (va2 -> Page) not in proc.pagetable
            proc.pagetable' = proc.pagetable + (va2 -> page)
        }
        Kernel.available' = Kernel.available - page
    }
    
    // MAINTAIN
    maintainPagetables[proc]
    Kernel.active' = Kernel.active
}

pred kfree[page : Page, caller : Process] {
    // GUARD
    caller in Kernel.active or caller = Kernel
    
    // ACTION
    some va : VirtualAddress | {
        caller.pagetable[va] = page 
        Kernel.available' = Kernel.available + page
        caller.pagetable' = caller.pagetable - (va -> page)
    }

    // MAINTAIN
    maintainPagetables[caller]
    Kernel.active' = Kernel.active
}

pred exit[proc : UserProcess, caller : Process] {
    // GUARD
    proc != Kernel // kernel never exits
    proc in Kernel.active
    caller = proc or caller = Kernel

    // ACTION
    some proc.pagetable implies {
        all page : Page | (VirtualAddress -> page) in proc.pagetable => { 
            page in Kernel.available'
        } 
    }
    no proc.pagetable'
    Kernel.active' = Kernel.active - proc
    
    // MAINTAIN
    maintainPagetables[proc]
    //all avail : Page | (avail in Kernel.available) implies (avail in Kernel.available')
    Kernel.available' = Kernel.available + {page : Page | (VirtualAddress -> page) in proc.pagetable} // => { page in Kernel.available'}}
}

pred doNothing {
    // MAINTAIN
    Kernel.active' = Kernel.active
    Kernel.available' = Kernel.available
    pagetable = pagetable'
}

pred traces {
    init
    always(
        some proc1, proc2 : Process | {
            kalloc[proc1, proc2] or
            (some p : Page | kfree[p, proc1]) or
            exit[proc1, proc2]
        }
        or doNothing
    )
}


// run {
//     traces
// } for exactly 2 UserProcess, exactly 5 Page, exactly 5 VirtualAddress

// CASE : UP has mappings then exits (multi-free)
// run {
//     traces
//     some p : UserProcess | eventually (some p.pagetable and exit[p, p])
// } for exactly 2 UserProcess, exactly 5 Page, exactly 5 VirtualAddress

run {
    traces
    some p : UserProcess | eventually (some p.pagetable and kalloc[p, p])
} for exactly 2 UserProcess, exactly 5 Page, exactly 5 VirtualAddress