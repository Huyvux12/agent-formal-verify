---- MODULE BoundedQueue ----
(* Copyright (c) 2026 Michael Denyer
   SPDX-License-Identifier: GPL-3.0-only

   An ordered bounded queue. Each worker thread claims the next item number
   under the mutex, builds the item without it, and publishes the item under
   the mutex. At most Window claimed items may wait for the consumer. The one
   consumer calls next(), which returns the items in claim order, then the
   end, or the error of the first item whose build failed. It may stop
   calling, call next() again after the end or an error, and call close()
   whenever no call is in progress. close() wakes every waiter, waits for
   every worker to exit, and frees the items the consumer never took.
   Building an item in FailAt fails.

   Each critical section under the mutex is one atomic step, so no two
   threads hold the mutex at once and the spec needs no lock variable.
   Building is the unlocked phase between a claim and its publish. A thread that must wait
   parks on the one condition variable, which publishing, taking an item and
   closing broadcast. A parked thread leaves only on a broadcast or a spurious
   wakeup, then retakes the mutex and rereads the state, so a lost wakeup
   shows as a liveness violation rather than a TLC deadlock.

   Assumptions: one condition variable serves every wait; spurious wakeups
   and the consumer's choice of call have no fairness; every other step is
   weakly fair.

   The window arithmetic is the one ../lean-template/Model/BoundedQueue.lean
   proves for every size; this spec checks the threads around it for the
   instances in BoundedQueue.matrix. BoundedQueue.mutations lists the bugs
   its properties must detect.

   To adapt it, replace this header with the source files and line ranges
   the model follows, the functions and shared variables it covers, the
   commit they were read at as `Source read at <commit>`, and each
   assumption. Keep the top-level formula named Spec, which tlc-matrix.sh
   checks. *)
EXTENDS Naturals, Sequences

CONSTANTS Workers, Window, Items, FailAt

VARIABLES next, consumed, slot, out, wpc, item, cpc, parked, closed
\* The variables each worker and the consumer own, and the queue state under the mutex.
worker == <<wpc, item>>
consumer == <<cpc, out>>
queue == <<next, consumed, slot, closed>>
vars == <<queue, parked, worker, consumer>>

Consumer == "consumer"
Indices == 0..(Items - 1)

Init == /\ next = 0
        /\ consumed = 0
        /\ slot = [i \in Indices |-> "free"]
        /\ out = <<>>
        /\ wpc = [w \in Workers |-> "claim"]
        /\ item = [w \in Workers |-> 0]
        /\ cpc = "idle"
        /\ parked = {}
        /\ closed = FALSE

\* A worker takes the mutex to claim the next item. It waits while the window
\* is full, and exits once the queue is closed or every item is claimed.
Claim(w) ==
  /\ wpc[w] \in {"claim", "wait"}
  /\ w \notin parked
  /\ IF closed \/ next = Items
     THEN /\ wpc' = [wpc EXCEPT ![w] = "exit"]
          /\ UNCHANGED <<next, slot, item, parked>>
     ELSE IF next < consumed + Window
     THEN /\ slot' = [slot EXCEPT ![next] = "building"]
          /\ item' = [item EXCEPT ![w] = next]
          /\ next' = next + 1
          /\ wpc' = [wpc EXCEPT ![w] = "publish"]
          /\ UNCHANGED parked
     ELSE /\ parked' = parked \cup {w}
          /\ wpc' = [wpc EXCEPT ![w] = "wait"]
          /\ UNCHANGED <<next, slot, item>>
  /\ UNCHANGED <<consumed, closed, consumer>>

\* After building its item, a worker takes the mutex to publish it and wakes every waiter.
Publish(w) ==
  /\ wpc[w] = "publish"
  /\ slot' = [slot EXCEPT ![item[w]] = IF item[w] \in FailAt THEN "failed" ELSE "ready"]
  /\ parked' = {}
  /\ wpc' = [wpc EXCEPT ![w] = "claim"]
  /\ UNCHANGED <<next, consumed, closed, item, consumer>>

\* A parked thread wakes without a broadcast.
Spurious(t) ==
  /\ t \in parked
  /\ parked' = parked \ {t}
  /\ UNCHANGED <<queue, worker, consumer>>

\* When no call is in progress, the consumer may call next() or close(), or stop calling.
Call(c) ==
  /\ cpc \in {"idle", "end", "error"}
  /\ cpc' = c
  /\ UNCHANGED <<queue, parked, worker, out>>

\* next() takes the mutex and returns the next item, the end or the error, or
\* waits until the next item is published.
TakeNext ==
  /\ cpc \in {"next", "wait"}
  /\ Consumer \notin parked
  /\ IF consumed = Items
     THEN /\ cpc' = "end"
          /\ UNCHANGED <<consumed, slot, out, parked>>
     ELSE IF slot[consumed] = "ready"
     THEN /\ slot' = [slot EXCEPT ![consumed] = "taken"]
          /\ out' = Append(out, consumed)
          /\ consumed' = consumed + 1
          /\ parked' = {}
          /\ cpc' = "idle"
     ELSE IF slot[consumed] = "failed"
     THEN /\ cpc' = "error"
          /\ UNCHANGED <<consumed, slot, out, parked>>
     ELSE /\ parked' = parked \cup {Consumer}
          /\ cpc' = "wait"
          /\ UNCHANGED <<consumed, slot, out>>
  /\ UNCHANGED <<next, closed, worker>>

\* close() marks the queue closed and wakes every waiter under the mutex, then
\* joins the workers and frees the items that were published but never taken.
Close ==
  /\ cpc = "close"
  /\ closed' = TRUE
  /\ parked' = {}
  /\ cpc' = "join"
  /\ UNCHANGED <<next, consumed, slot, worker, out>>

Exited == \A w \in Workers : wpc[w] = "exit"

Join ==
  /\ cpc = "join"
  /\ Exited
  /\ slot' = [i \in Indices |-> IF slot[i] \in {"ready", "failed"} THEN "freed" ELSE slot[i]]
  /\ cpc' = "closed"
  /\ UNCHANGED <<next, consumed, closed, parked, worker, out>>

\* Stutter once closed, so that the end of a run is not reported as a deadlock.
Done == cpc = "closed" /\ UNCHANGED vars

Next == \/ \E w \in Workers : Claim(w) \/ Publish(w)
        \/ \E t \in parked : Spurious(t)
        \/ \E c \in {"next", "close"} : Call(c)
        \/ TakeNext \/ Close \/ Join \/ Done

Spec == /\ Init /\ [][Next]_vars
        /\ \A w \in Workers : WF_vars(Claim(w)) /\ WF_vars(Publish(w))
        /\ WF_vars(TakeNext) /\ WF_vars(Close) /\ WF_vars(Join)

TypeOK == /\ next \in 0..Items /\ consumed \in 0..Items
          /\ slot \in [Indices -> {"free", "building", "ready", "failed", "taken", "freed"}]
          /\ wpc \in [Workers -> {"claim", "wait", "publish", "exit"}]
          /\ item \in [Workers -> 0..Items]
          /\ cpc \in {"idle", "next", "wait", "end", "error", "close", "join", "closed"}
          /\ parked \subseteq Workers \cup {Consumer}
          /\ closed \in BOOLEAN
InWindow == consumed <= next /\ next <= consumed + Window
\* Each item is unclaimed, held by exactly one worker while it is built, published, taken by the
\* consumer, or freed by close().
Owned == /\ \A i \in Indices : (slot[i] = "free") = (i >= next)
         /\ \A i \in Indices : (slot[i] = "taken") = (i < consumed)
         /\ \A i \in Indices : (slot[i] = "building") = (\E w \in Workers : wpc[w] = "publish" /\ item[w] = i)
         /\ \A v, w \in Workers : v # w /\ wpc[v] = "publish" /\ wpc[w] = "publish" => item[v] # item[w]
InOrder == out = [k \in 1..consumed |-> k - 1]
\* next() reports an error only for the next item, after every item ahead of it.
ErrorInOrder == cpc = "error" => slot[consumed] = "failed"
\* next() delivers no item after the first one whose build failed.
NoDeliveryAfterError == \A k \in 1..Len(out) : \A i \in FailAt : out[k] < i
\* Once close() returns, every worker has exited and every item is unclaimed, taken or freed.
NoLeak == cpc = "closed" => /\ Exited
                            /\ \A i \in Indices : slot[i] \in {"free", "taken", "freed"}

\* Each wait in next() returns, close() returns, and a consumer that keeps calling next() reaches the end or the error.
NextReturns == cpc = "wait" ~> cpc # "wait"
CloseReturns == cpc = "close" ~> cpc = "closed"
AllConsumed == []<>(cpc = "next") => <>(cpc \in {"end", "error"})

\* States that the properties depend on, for the matrix's reach checks.
WindowFull == next = consumed + Window
WorkerParked == parked \cap Workers # {}
ConsumerParked == Consumer \in parked
Failed == cpc = "error"
====
