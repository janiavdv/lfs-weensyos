# CSCI 1710 Final Project: Operating System Model

## Project Details
We would recommend reading this document in our [GitHub repository](https://github.com/janiavdv/lfs-weensyos) for easier readability. Also, see our trace video with annotations at [this link](https://drive.google.com/file/d/14rLqGMLefDRt9AwCw5eF_RSMHEkGOSRD/view?usp=sharing).

Our final project models [cs300's WeensyOS](https://cs.brown.edu/courses/csci0300/2023/assign/projects/project4.html) project, which requires students to implement a small ("weensy") operating system. This involves virtual memory and pagetables, enforcing kernel/process isolation, and the functions `kalloc()`, `kfree()`, and `exit()`. 

The fundamental predicates in our model are:
- `init`: enforces the OS' structure in state 0. All `UserProcess`es are active, and there are `Page`s in the `Kernel`'s `pagetable` and in its `available` set. 
- `kalloc[proc : Process, caller : Process]`: allocates a `Page` from the `available` set to `proc`, if `caller = proc` (security enforcement). If there are no `available` `Page`s, it is unsat.
- `kfree[page : Page, caller : Process]`: frees `page` from `caller` if `page` is currently mapped to by `caller`. 
- `exit[proc : UserProcess, caller : Process]`: removes `proc` from the `active` set of `UserProcess`es and frees all of the `Page`s it currently maps to (if `proc = caller`). 
- `doNothing`: maintains the `active` and `available` sets between two states, as well as all `Process`es' `pagetable`s. Sometimes operating systems are doing things other than allocating/freeing memory or exiting processes--this predicate reflects that.
- `traces`: ensures the first state satisfies `init`, then for the rest of the states, either `kalloc`s, `kfree`s, `exit`s, or does `doNothing`. 

## Tradeoffs/Abstraction Choices
- We did not implement `fork()`, or a way for a `UserProcess` to be created. We decided to create them in `init`, only giving them the ability to `exit` after that. This is because the focus of our model was more to discover properties about virtual memory and page allocation, rather than how many processes were being created. 
    - Furthermore, the interesting part about `fork()` to us is copying over the memory of the parent process, but since our `Page` has no notion of "content", we chose not to focus on this aspect of operating systems. 
- We did not model features of processes/pages that weren't relevant to the properties we wanted to verify. For example, we did not assign process ids to `Process`es, and we did not assign permission bits to `Page`s. Those pieces of data would have made the Sterling instance much more crowded, and it's not very interesting to verify that process ids are unique or that `Pages` are writable, etc.
    - These abstraction choices limit our model in some ways. Real-life operating systems do allow processes to share read-only pages. Our model does not allow processes to share pages because we decided not to include permissions for pages.
    - We also decided not to model segments of memory (stack, heap, etc.), despite considering it in the first draft of our project proposal. Now, we just have the representation of a `Page`. This means that we cannot represent how the kernel handles allocation of memory for those segments differently (their layout in memory, permission bits, direction of heap/stack growth, etc.). This would be an interesting potential extension of our project!

## Design Choices: Security
We introduced a notion of security for our predicates:
- We enforce in `kalloc` that the caller process is the same as the process for whom the memory is requested. It doesn't make sense for a user process to request memory for another process. It is also wasteful for the kernel to give a user process memory that it hasn't asked for.
- We enforce in `kfree` that the page being freed belongs to the calling process. We don't want a user process to be able to free another process's pages; otherwise, a malicious process could kill another process by freeing all of its pages. It also doesn't make sense for the kernel to free a page for a user process when the user process hasn't asked it to do so--the user process is likely still using that memory! Note that the kernel can still free pages in `exit` to kill a process--this restriction just means that the kernel can't free arbitrary pages belonging to another process.
- We enforce in `exit` that either the caller process and the process being exited are the same or the caller process is the `Kernel`. A user process should be able to request to exit once it's finished running, but a user process should not be able to kill another process. We also wanted the kernel to be able to kill a user process at any time because in real-life operating systems, the kernel will often kill a process as punishment for misbehaving (e.g., segmentation fault).


## Goal Evaluation
We ended up achieving *all* our foundation, target, and reach goals, with the exception of omitting the ability for a new `UserProcess` to be created (details about this omission can be found above). We are particularly psyched about the fact that we were able to implement virtual memory and pagetables, since this definitely began as a reach goal for us! :)

## Visualization
We completed the entirety of our model and property testing using Sterling's default visualization, never encountering any issues with complexity of our model and the way it was represented by the graph. In fact, we found it to be a great representation of our system! 

During our second design check, Megan suggested that we try to write a custom visualization. After thinking about what an ideal visualization would look like, we realized that it would look very similar to the default, in that it would be a mind map style graph with arrows showing pagetable and set membership. A huge part of our discussion involved the fact that the default graph was _so_ helpful when we were initially creating our model. We thought this was the ideal representation because it makes it very easy to track changes between states and to visually verify some of the most important properties about our model--like process isolation--by just tracking the arrows. Based on these factors, we decided that we would __not have a custom visualization in the final version of our project__. We are happy to talk more about our decision in our presentation!
