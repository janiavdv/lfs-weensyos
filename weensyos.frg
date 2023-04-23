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
    no Kernel.active
}

pred wellformed {
    
    // in a single process, at most one va should map to a page
    all proc : Process | {
        all page: Page | {
            some va: VirtualAddress | proc.pagetable[va] = page => {
                no va2: VirtualAddress | (va != va2) => {
                    proc.pagetable[va2] = page
                }
            }
            // every page is either in available pages or in a proc's pages or in kernel's pages
            page in Kernel.available => {no va : VirtualAddress | (Kernel.pagetable[va] = page) or (proc.pagetable[va] = page)}
            // if page isn't mapped to by the kernel, it must be available
            {no v : VirtualAddress | Kernel.pagetable[v] = page} <=> {page in Kernel.available}
            // if page is mapped to by the kernel, it must not be available
            // {some v : VirtualAddress | Kernel.pagetable[v] = page} <=> {page not in Kernel.available}
        }

    // TODO: process isolation: no process should share pages with another process
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

pred kalloc[proc : Process, caller : Process] {
    (proc = caller) => {
        some page : Page | (no va : VirtualAddress | caller.pagetable[va] = page) => {
            some va : VirtualAddress | caller.pagetable' = caller.pagetable + (va -> page)
            Kernel.available' = Kernel.available - page
        } 
    } else {
        // not allowed to allocate a page to another process; do nothing
        caller.pagetable' = caller.pagetable
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

pred enter {}

pred exit[proc : Process] {}

pred traces {
    init
    always(wellformed)
    always(
        // enter or 
        //some proc : UserProcess | exit[proc] or kalloc[proc] or
        //some p : Page | kfree[p]

        // TODO: need to tell it that only one process can do these at a time??
        some proc1, proc2 : UserProcess | {
            kalloc[proc1, proc2] or (some p : Page | kfree[p, proc1])
        }
    )
}


run {
    traces
} for exactly 2 UserProcess, exactly 5 Page