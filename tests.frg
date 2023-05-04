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
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem

    inactiveNoPage : {
        traces implies isInactiveNoPages
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem
}

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

test expect {
    uniqueMem: {
        traces implies noSharedPages
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem
    
    disjoint : {
        traces implies kernelIsolation
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem
}

-----------------------------------
// MEMORY MANAGEMENT
// Kernel’s set of available memory is disjoint from all pages set for processes
pred availOrAlloc {
    always (
        all p: Page | {
            (p in Kernel.available) implies ((VirtualAddress -> p) not in Process.pagetable)
        }
    )
    always (
        some p : Page | {
            ((VirtualAddress -> p) in Process.pagetable) implies (p not in Kernel.available)
        }
    )
}

// Memory can be reused by another process if it’s been freed.
pred canReuse {
    eventually (some p : Page, proc : Process | once(kfree[p, proc]) and eventually(p not in Kernel.available))
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
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem

    twoPagesOneVA : {
        traces and sameVA
    } is sat
    
    freeThenReuse : {
        traces and canReuse
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is sat

    allocation : {
        traces implies kallocAllocates
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem

    allUsed : {
        traces implies memoryFull
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem
}
    
-----------------------------------
// PERMISSIONS/SECURITY
// A user process shouldn’t be able to free pages that don't belong to it
pred belongOnlyKfree {
    always (
        all p : Page, proc : UserProcess | {
            (no va: VirtualAddress | proc.pagetable[va] = p) implies (not kfree[p, proc])
            // (VirtualAddress -> p) not in proc.pagetable) 
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
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem
    
    allocSelf : {
        traces implies callerOnlyKalloc 
    } for exactly 2  UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem

    exitSelf : {
        traces implies callerOnlyExit
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is theorem

    kernelKill : {
        traces and kernelCanKill
    } for exactly 2 UserProcess, exactly 2 Page, exactly 2 VirtualAddress is sat
}