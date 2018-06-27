# Making everything lock-free

The current implementation is wait-free on the side of load, but locked in case
of swap (any suspended lock can hold it forever).

There's another idea how to make both lock-free (speed must still be
considered).

## Scratch space

We would like to keep a kind of scratch space around, in the form of linked
list. However, there are two problems:

* We want to be able to also run our operations at times when we can't allocate.
* Deallocation is super-hard.

Solution:

* Each thread has one linked-list node in its thread-local storage.
* When the thread dies, it puts it into a recycling area, new threads can take
  from here.
* Usually, we keep some amount of extra „recycled“ nodes in there to pull on in
  the allocation-less situations (eg. signal handlers).

In signal handlers, we need to instead pull from the recycled area always
instead of using the TLS. The allocation strategy can be solved by extra
parameter (and having methods with & without the parameter).

## Debt lists

The problem we have, we may for a short time owe a reference to a specific
pointer. So each ArcSwap keeps a list of related debts ‒ each debt is a node
with the pointer in it.

The idea is, singly-linked with anchored head and tail should be enough.

### Load

* Fetch the pointer value.
* Reserve a debt ‒ put the pointer into the node and link the node into the
  list.
* Check the pointer is the same. If not, retry.
* Turn it into arc, bump the ref count.
* Try to exchange the pointer in the debt with NULL. If fails (someone else
  paid), dec the ref count again.
* By removing paid debts and skipping the active ones, find our own and unlink.
  - TODO: This might be a bit tricky ‒ maybe have to try from the start again
    sometimes.
* Return.

### Swap

* Swap pointer.
* Start iterating the debt list, paying off debts of the current pointer.
* When reaching the end, everything is paid off (nothing could have been created
  before), and replacing them with NULL.
  - TODO: Need to solve a problem when a node is removed while being traversed &
    is put into another list. We need to retry, but for that we need to detect
    it.
