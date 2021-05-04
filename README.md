# Zab TLA+ Spec

This repository contains a TLA+ specification for the Zookeeper atomic broadcast (Zab) protocol as described in the technical report ["Dissecting Zab"](https://cwiki.apache.org/confluence/download/attachments/24193444/yl-2010-007.pdf). This spec was originally created as a project for a Formal Verification of Distributed Systems course. The spec uses pluscal which is then used to generate the TLA+ spec.

## Zab Overview
Zab is the atomic broadcast protocol used by Zookeeper. Each server can run a follower process and a leader process. Zab works in three phases: Discovery, Synchronization, and Broadcast. 

Leader election comprises the first two phases. At any time, a process may drop the current iteration of the protocol and start a new one. Zab broadcast transactions are totally ordered with respect to the Zookeeper transaction ID (zxid). Zxids consist of a epoch number and counter. At most one process can broadcast transactions during each epoch, so the epoch number is incremented when a new epoch is proposed. When a leader is elected, it sends out an initial history that contains the latest history of any follower, thus bringing the quorum up-to-date with the latest history before accepting new transactions. Leaders are elected by majority quorum, so at most one leader can be elected for each epoch.

Once a leader has been established, new transactions can be proposed by the leader. Transaction proposals must be ackd by a quorum of followers before they can be committed. Transactions are delivered in-order by the followers once they receive a commit message.

## TLA+ Model of Zab
This spec uses a Crash-Recovery model for Zab. That is, at any step of the protocol, any process may crash or recover from a crash.

### Leader Oracle
Followers and leaders both use the same leader oracle to determine a candidate leader. The oracle simply chooses a server from the set of servers.

### Followers and Leaders
This spec models the follower processes and leader processes separately in pluscal. Each server has an associated follower process and leader process. Each of these processes goes through the three phases of the protocol independently and in-order.

### Messages
Messages between processes are modeled using message queues. Communication is only ever done between a leader process and a follower process. Each pair of processes has its own pair of unidirectional message queues. Messages are lost upon a crash.

### Crashing
Crashes and reboots are modeled using the Crash and Recover macros. Currently, only messages in the queues for the crashing process are lost upon crashing. All other state is assumed to be persisted to non-volatile storage. The Crash action should always be enabled for a process that is not crashed. The Recover action should only be enabled for a crashed process. 

### Zab steps
The Zab protocol proceeds in two main phases: leader election (discovery and synchronization) and broadcast. Each process proceeds through leader election to the broadcast phase unless a crash occurs. A process remains in the broadcast phase until a crash occurs. When a process recovers from a crash, it starts anew the leader election phase. The steps for these phases are often described as procedures. To allow for crashes between steps, these procedures have only one atomic step. A custom phase tracker is used in each process to determine the next step that can be taken. This phase tracker was introduced to avoid needing to describe crash steps multiple times.

### Invariants
The spec currently specifies four protocol invariants and a type invariant. 

The `PrimaryUniqueness` invariant ensures that no more than one process is elected leader (calls the `ready()` function) for each epoch.

The `BroadcastIntegrity` invariant ensures that every delivered transaction was broadcast by a leader.

The `Agreement` invariant ensures that for every pair of followers, at least one of the followers has only delivered a subset of messages of the other. More formally, this invariant requires that if a follower f delivers transaction t, and follower f' delivers transaction t', then f' delivers t or f delivers t'.
    
The `TotalOrder` invariant ensures that transactions are delivered in-order according to a total order amongst all the followers.  More formally, this invariant requires that if some follower delivers <v,z> before <v',z'>, then any follower that delivers <v',z'> must also deliver <v,z> and deliver it before <v', z'>.

## Model checking
This spec is model checked using TLC. Future work includes adapting the spec to be able to use the Apalache model checker. A few tricks are used to reduce the state space the model checker needs to explore.

The spec defines the servers to be a symmetry set. This dramatically reduces the state space since it doesn't matter if follower 1 or follower 2 crash if they have the same follower state.

The spec also introduces constraints on the number of messages in a queue, the epoch number, the counter number, and the number of crashes. These constraints ensure that the states that violate the constraints are not reached. However, TLC checks invariants before it checks constraints, so it is important to ensure that either invariants are specified to hold outside the constraints, or that the invariants are implied only when the constraints hold. This spec uses the latter approach. 

## Pluscal & TLA+ limitations
Through the process of this project, I encountered several limitations or frustrations with Pluscal and TLA+. They are detailed below to potentially inspire future improvements and for consideration when designing new spec languages.

### Type Support
TLA+ is untyped, but adding TypeOK invariants is considered a best practice. Ideally typing should be built in since adding type invariants results in extra boilerplate and repetition. 

For example, I defined operators for each message type that could be used to construct message objects (`CepochMessage(from, last_epoch) == [from |-> from, type |-> CEPOCH, last_epoch |-> last_epoch]`). These couldn't be used as type invariants, so I needed to then define a separate operator for the message type (`CepochMessageType == [from : FollowerProcesses, type : {CEPOCH}, last_epoch : Epochs]`). 

Support for sub-typing would also be desirable since I ended up defining leader and follower messages separately to reduce the state space the model checker needed to explore (`FollowerMessageType == UNION { CepochMessageType, AckEpochMessageType, AckLeaderMessageType, AckProposalMessageType }`).

### Pluscal Crash support
Writing crashes to occur after every step requires either not using procedures, adding in many "either crash or" statements, or introducing a custom program counter like the phase tracker in this spec. Ideally there should be a convenient pluscal syntax that allows an action to occur at any step of a process. This would make crash and recover models easier to implement in large specs.

### Pluscal multi-update support
Pluscal currently only allows a single update to each state variable per step. However, in many cases we want to receive a message then send out a message in the same step. This can result in either chaining operators (`with_message(m, pop_message(msgs))`) or introducing macros to do a combination of the steps together (`DoRecvThenSend(m)`). Both of these approaches make the spec harder to understand. One alternative could be to allow multiple assignment statements in a single step that would be executed consecutively as a single assignment. E.g. `msgs := Recv(msgs); msgs := Send(m, msgs);` could be converted to `msgs := Send(m, Recv(msgs))` before being translated to TLA+.

### Pluscal temporary variable support
Pluscal does not allow for temporary variables that are not persisted in state. Allowing temporary variables would make cases like the aforementioned multi-update case easier to write. For example, instead of `msgs := Send(m, Recv(msgs))`, one could write something like: `tmp_msgs :=: Recv(msgs); msgs := Send(m, tmp_msgs);`.
