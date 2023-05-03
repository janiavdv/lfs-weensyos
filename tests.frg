#lang forge

open "weensyos.frg"

// VACUITY / SATISFIABILITY
// test expect {
//     vacuityTraces: {traces} is sat
//     satInit: {init} is sat
//     satWellformed: {wellformed} is sat
//     satKalloc: {some p1, p2 : Process | kalloc[p1,p2]} is sat
//     satKfree: {some proc : Process, page : Page | kfree[page,proc]} is sat
//     satExit: {some p1, p2 : Process | exit[p1,p2]} is sat
// }

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

// test expect {
//     pageActive : {
//         traces implies hasPagesIsActive
//     } is theorem

//     inactiveNoPage : {
//         traces implies isInactiveNoPages
//     } is theorem
// }

-----------------------------------
// PROCESS ISOLATION -- Memory cells belong to exactly one process; there is no sharing of memory between processes or the kernel.

// No user processes should share mappings to the same page
pred noSharedPages {
    always (
        no disj p1, p2 : Process | {
            some p : Page | {
                (VirtualAddress -> p) in p1.pagetable
                (VirtualAddress -> p) in p2.pagetable
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

// test expect {
//     uniqueMem: {
//         traces implies noSharedPages
//     } is theorem
    
//     disjoint : {
//         traces implies kernelIsolation
//     } is theorem
// }

-----------------------------------
// MEMORY MANAGEMENT
// Kernel’s set of available memory is disjoint from all pages set for processes
pred availOrAlloc {
    always (
        all p: Page | {
            (p in Kernel.available) implies ((VirtualAddress -> p) not in Process.pagetable)
        }
        some p : Page | {
            ((VirtualAddress -> p) in Process.pagetable) implies (p not in Kernel.available)
        }
    )
}

// Memory can be reused by another process if it’s been freed.
pred canReuse {
    some p : Page, proc : Process | once(kfree[p, proc]) and eventually(p not in Kernel.available)
}

// Multiple processes can use the same virtual address
pred sameVA {
    some disj p1, p2 : Process | {
        some va : VirtualAddress | {
            (va -> Page) in p1.pagetable and (va -> Page) in p2.pagetable
        }
    } 
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

// If there are no user processes, must always doNothing from that point forward
pred noActiveDN {
    always (
        (no Kernel.active) implies (always doNothing)
    )
}

test expect {
    
    pageDisj: {
        traces implies availOrAlloc
    } is theorem

    // twoPagesOneVA : {
    //     traces and sameVA
    // } is sat
    
    // freeThenReuse : {
    //     traces and canReuse
    // } is sat

    // allocation : {
    //     traces implies kallocAllocates
    // } is theorem

    // allUsed : {
    //     traces implies memoryFull
    // } is theorem

    // noActive : {
    //     traces implies noActiveDN
    // } is theorem
}
    
-----------------------------------
// PERMISSIONS/SECURITY
// Shouldn’t be able to free pages that don't belong to the calling process
pred belongOnlyKfree {
    always (
        all p : Page, proc : Process | {
            p not in proc.pagetable => not kfree[p, proc]
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
    some up : UserProcess | {
        exit[up, Kernel]
    }
}

// test expect {
//     freeOwn : {
//         traces implies belongOnlyKfree 
//     } is theorem
    
//     allocSelf : {
//         traces implies callerOnlyKalloc 
//     } is theorem

//     exitSelf : {
//         traces implies callerOnlyExit
//     } is theorem

//     kernelKill : {
//         traces and kernelCanKill
//     } is sat
// }