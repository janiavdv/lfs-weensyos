#lang forge

open "weensyos.frg"

// VACUITY / SATISFIABILITY
test expect {
    vacuityTraces: {traces} is sat
    satInit: {init} is sat
    satKalloc: {some p1, p2 : Process | kalloc[p1,p2]} is sat
    satKfree: {some proc : Process, page : Page | kfree[page,proc]} is sat
    satExit: {some p1, p2 : Process | exit[p1,p2]} is sat
}

-----------------------------------
// ACTIVE/INACTIVE
// All processes with active memory allocations must be recognized by the kernel as active processes
pred hasPagesIsActive {
    always (
        all up : UserProcess | (some up.pagetable) implies (up in Kernel.active)
    )
}

// No inactive processes have mappings
pred isInactiveNoPages {
    always (
        all up : UserProcess | (up not in Kernel.active) implies (no up.pagetable)
    )
}

test expect {
    pageActive : {
        traces implies hasPagesIsActive
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is theorem

    inactiveNoPage : {
        traces implies isInactiveNoPages
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is theorem
}

-----------------------------------
// PROCESS ISOLATION -- Memory cells belong to exactly one process; there is no sharing of memory between processes or the kernel.

// No user processes should share mappings to the same page
pred noSharedPages {
    always (
        no disj p1, p2 : Process | {
            some p : Page | {
                some va : VirtualAddress | p1.pagetable[va] = p
                some va : VirtualAddress | p2.pagetable[va] = p
            }
        }
    )
}

// Processes can't access kernel memory
pred kernelIsolation {
    always (
        no (Kernel.pagetable & UserProcess.pagetable)
    )
}

test expect {
    uniqueMem: {
        traces implies noSharedPages
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is theorem
    
    disjoint : {
        traces implies kernelIsolation
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is theorem
}

-----------------------------------
// MEMORY MANAGEMENT
// Kernel’s set of available memory is disjoint from all pages set for processes
pred availOrAlloc {
    always (
        all p: Page | {
            (p in Kernel.available) implies (no va : VirtualAddress | Process.pagetable[va] = p)
        }
    )
    always (
        some p : Page | {
            (some va : VirtualAddress | Process.pagetable[va] = p) implies (p not in Kernel.available)
        }
    )
}

// Memory can be reused by another process if it’s been freed.
pred canReuse {
    eventually (
        some p : Page | {
            some disj proc1, proc2 : Process | {
                once(kfree[p, proc1]) and (some va : VirtualAddress | proc2.pagetable[va] = p)
            }
        }
    )
}

// Multiple processes can use the same virtual address
pred sameVA {
    eventually (
        some disj p1, p2 : UserProcess | {
            some va : VirtualAddress | (some p1.pagetable[va]) and (some p2.pagetable[va])
        } 
    )
}

// A user process has a page mapped to it if kalloc was called before
pred kallocAllocates {
    always (
        some p : UserProcess | (some p.pagetable) implies {
            once(kalloc[p, p])
        }
    )
}

// If all pages are mapped to, that means that kalloc is always false in the next state
pred memoryFull {
    always (
        (no Kernel.available) implies next_state(not kalloc[Process, Process])
    )
}

test expect {
    pageDisj: {
        traces implies availOrAlloc
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is theorem

    twoPagesOneVA : {
        traces and sameVA
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is sat
    
    freeThenReuse : {
        traces and canReuse
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is sat

    allocation : {
        traces implies kallocAllocates
    } for exactly 3 UserProcess, 3 Page, 3 VirtualAddress is theorem // use exactly so there's at least one UserProcess

    allUsed : {
        traces implies memoryFull
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is theorem
}
    
-----------------------------------
// PERMISSIONS/SECURITY
// A user process shouldn’t be able to free pages that don't belong to it
pred belongOnlyKfree {
    always (
        all p : Page, proc : UserProcess | {
            (no va: VirtualAddress | proc.pagetable[va] = p) implies (not kfree[p, proc])
        }
    )
}

// Shouldn’t be able to allocate memory to a process that isn’t yourself (caller)
pred callerOnlyKalloc {
    always (
        all disj p1, p2 : Process {
            not kalloc[p1,p2]
        }
    )
}

// Other user processes shouldn’t be able to kill a user process (only kernel and self can exit a user process)
pred callerOnlyExit {
    always (
        all disj p1, p2 : UserProcess {
            not exit[p1,p2]
        }
    )
}

// Kernel is allowed to exit a process
pred kernelCanKill {
    eventually (
        some up : UserProcess | {
            exit[up, Kernel]
        }
    )
}

test expect {
    freeOwn : {
        traces implies belongOnlyKfree 
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is theorem
    
    allocSelf : {
        traces implies callerOnlyKalloc 
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is theorem

    exitSelf : {
        traces implies callerOnlyExit
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is theorem

    kernelKill : {
        traces and kernelCanKill
    } for 3 UserProcess, 3 Page, 3 VirtualAddress is sat
}