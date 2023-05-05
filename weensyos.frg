#lang forge

option problem_type temporal
option max_tracelength 5 // the tests will take longer if this increases
// option min_tracelength 4 // comment this in to get more interesting Sterling traces

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

pred maintainPagetables[proc: Process] {
    all p: Process | (p != proc) => {
        p.pagetable' = p.pagetable
    }
}

pred kalloc[proc : Process, caller : Process] {
    // GUARD
    proc = caller
    caller = Kernel or caller in Kernel.active
    proc in Kernel.active
    
    // ACTION
    some page : Page | {
        page in Kernel.available
        (no va: VirtualAddress | proc.pagetable[va] = page)
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
        caller.pagetable[va] = page // caller can only free its own page
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
        all page : Page | (some va : VirtualAddress | proc.pagetable[va] = page) => { 
            page in Kernel.available'
        } 
    }
    no proc.pagetable'
    Kernel.active' = Kernel.active - proc
    
    // MAINTAIN
    maintainPagetables[proc]
    Kernel.available' = Kernel.available + {page : Page | (some va : VirtualAddress | proc.pagetable[va] = page)} // => { page in Kernel.available'}}
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

--- TRACES
// These are some example traces to understand our model. Feel free to play around with the min/max tracelengths at the top of the file,
// but keep in mind that changing those values will affect the test runtimes. You can also grab the code from any of the tests and generate a trace with it
// (see the last run statement for an example).

// CASE : basic trace
run {
    traces
} for exactly 2 UserProcess, exactly 5 Page, exactly 5 VirtualAddress

// CASE : User process has mappings then exits
// run {
//     traces
//     some p : UserProcess | eventually (some p.pagetable and exit[p, p])
// } for exactly 2 UserProcess, exactly 5 Page, exactly 5 VirtualAddress

// CASE : kalloc gets called
// run {
//     traces
//     some p : UserProcess | eventually (some p.pagetable and kalloc[p, p])
// } for exactly 2 UserProcess, exactly 5 Page, exactly 5 VirtualAddress

// CASE : kfree gets called
// run {
//     traces
//     some page : Page, p : Process | eventually(kfree[page, p])
// } for exactly 2 UserProcess, exactly 5 Page, exactly 5 VirtualAddress

// CASE : Virtual Address is shared between processes (traces and sameVA from tests)
// run {
//     traces
//     eventually (
//         some disj p1, p2 : UserProcess | {
//             some va : VirtualAddress | (some p1.pagetable[va]) and (some p2.pagetable[va])
//         } 
//     )
// } for exactly 3 UserProcess, exactly 5 Page, exactly 5 VirtualAddress
