#lang forge

option problem_type temporal
option max_tracelength 14

sig VirtualAddress {}

sig Page {}

abstract sig Process {
    var pid : one Int,
    var pagetable : pfunc VirtualAddress -> Page
}

sig UserProcess extends Process {}

one sig Kernel extends Process {
    var active : set Process,
    var available : set Page
}

pred init {
    no Process.pages
    no Kernel.active
    all page : Page | {
        page not in Kernel.kpages <=> page in Kernel.available_mem
        page in Kernel.kpages <=> page not in Kernel.available_mem
    }
}

pred wellformed {
    // every cell is either in available cells or in a proc's pages or in kernel's pages
}

// can't allocate a page already assigned to another process
pred kalloc[proc : Process] {}

// security issue: processes shouldn't be allowed to free other proc's pages. 
// should also take in the proc that's trying to free and check that the page belongs to it
pred kfree[page : Page] {
    // free page
    Kernel.available' = Kernel.available + page
    all proc : Process | {
        // proc.pid' = proc.pid
        page in proc.pages => {
            proc.pages' = proc.pages - page
        } else {
            // maintain
            proc.pages' = proc.pages
        }
    }
    pid' = pid
    Kernel.active' = Kernel.active
}

pred enter {}

pred exit[proc : Process] {}

pred traces {
    init[]
    always(wellformed[])
    always(
        enter[] or 
        some proc : Process | exit[proc] or kalloc[proc] or
        some p : Page | kfree[p]
    )
}