---- MODULE zab_pluscal ----

EXTENDS Sequences, Integers, TLC, FiniteSets


\* Set of server IDs
CONSTANTS Servers

\* Differentiates between leader and follower processes
CONSTANTS Leader, Follower

\* Message types, correspond to those in the "Dissecting Zab" tech report
CONSTANTS CEPOCH, NEWEPOCH, ACK_E,
          NEWLEADER, ACK_LD, COMMIT_LD,
          PROPOSE, ACK_P, COMMIT

\* Set of values that can be proposed. Should be a finite set to allow for exhaustive model checking
CONSTANTS Values

\* Limits to use for type checking
CONSTANTS MAX_COUNTER
CONSTANTS MAX_EPOCHS
CONSTANTS MAX_HISTORY_LENGTH
CONSTANTS MAX_MESSAGES

(* --algorithm zab_algo

\* Represents messages sent from one server to another. Each process has its own channel with each other process.
\* Maps from the receiver process to the sender process to the messages
variables messages = [receiver \in Processes |-> [sender \in Processes |-> <<>>]],
          message = [receiver \in Processes |-> {}],              \* Used to temporarily hold a received message
          primaries = [epoch \in Epochs |-> {}],        \* Maps each epoch to the primaries for that epoch (meaning the processes that call ready)
          broadcast_transactions = {};                  \* Tracks all the transactions that have ever been broadcast

define
    \*** Data Structures:
    Zxid(epoch, counter) == [epoch |-> epoch, counter |-> counter]

    ZxidGreaterThan(left, right) == \/ left.epoch > right.epoch
                                    \/ /\ left.epoch = right.epoch
                                       /\ left.counter > right.counter

    Transaction(value, zxid) == [value |-> value, zxid |-> zxid]

    Process(server, role) == [server |-> server, role |-> role]
    FollowerProc(server) == Process(server, Follower)
    LeaderProc(server) == Process(server, Leader)

    \*** Types:
    Epochs == 0..MAX_EPOCHS
    Counters == 0..MAX_COUNTER
    Zxids == {Zxid(epoch, counter) : epoch \in Epochs, counter \in Counters}
    Transactions == {Transaction(value, zxid) : value \in Values, zxid \in Zxids}
    Histories == UNION {[1..i -> Transactions] : i \in 0..MAX_HISTORY_LENGTH}
    LeaderProcesses == {LeaderProc(s) : s \in Servers}
    FollowerProcesses == {FollowerProc(s) : s \in Servers}
    Processes == LeaderProcesses \union FollowerProcesses

    \*** Permutations used to define symmetry sets
    ServerPerms == Permutations(Servers)

    SymmetrySets == ServerPerms

    \*** Helper operators for the Zab message queue, written in TLA+ for potential extraction to a new module

    Send(to, m, _messages) == [_messages EXCEPT ![to] = [_messages[to] EXCEPT ![m.from] = Append(_messages[to][m.from], m)]]

    \* Returns an updated messages with a message sent to every process in the specified set
    RECURSIVE SendToSet(_, _, _)
    SendToSet(set, m, _messages) == IF Cardinality(set) = 0
                                    THEN _messages
                                    ELSE
                                        LET to == CHOOSE to \in set : TRUE
                                            others == set \ {to}
                                        IN Send(to, m, SendToSet(others, m, _messages))

    \* returns a tuple of <<message, messages>> where messages is the updated messages structure without the received message
    Recv(proc, from, _messages) == <<Head(_messages[proc][from]), [_messages EXCEPT ![proc] = [_messages[proc] EXCEPT ![from] = Tail(_messages[proc][from])]]>>

    \* returns the next message in the queue without removing it
    PeekMessage(proc, from, _messages) == Head(_messages[proc][from])

    CanRecvFrom(proc, from, _messages) == Len(_messages[proc][from]) > 0
    CanRecv(proc, _messages) == \E from \in Processes : CanRecvFrom(proc, from, _messages)

    ReceivableMessages(proc, _messages) == {PeekMessage(proc, from, _messages) : from \in {p \in Processes : CanRecvFrom(proc, p, _messages)}}

    \* Message types:
    CepochMessage(from, last_epoch) == [from |-> from, type |-> CEPOCH, last_epoch |-> last_epoch]
    NewEpochMessage(from, epoch) == [from |-> from, type |-> NEWEPOCH, epoch |-> epoch]
    AckEpochMessage(from, last_leader, history) == [from |-> from, type |-> ACK_E, last_leader |-> last_leader, history |-> history]
    NewLeaderMessage(from, epoch, initial_history) == [from |-> from, type |-> NEWLEADER, epoch |-> epoch, initial_history |-> initial_history]
    AckLeaderMessage(from, epoch) == [from |-> from, type |-> ACK_LD, epoch |-> epoch]
    CommitLeaderMessage(from, epoch) == [from |-> from, type |-> COMMIT_LD, epoch |-> epoch]
    ProposalMessage(from, epoch, transaction) == [from |-> from, type |-> PROPOSE, epoch |-> epoch, transaction |-> transaction]
    AckProposalMessage(from, epoch, transaction) == [from |-> from, type |-> ACK_P, epoch |-> epoch, transaction |-> transaction]
    CommitProposalMessage(from, epoch, transaction) == [from |-> from, type |-> COMMIT, epoch |-> epoch, transaction |-> transaction]

    \* Message types used for type checking
    CepochMessageType == [from : FollowerProcesses, type : {CEPOCH}, last_epoch : Epochs]
    NewEpochMessageType == [from : LeaderProcesses, type : {NEWEPOCH}, epoch : Epochs]
    AckEpochMessageType == [from : FollowerProcesses, type : {ACK_E}, last_leader : Epochs, history : Histories]
    NewLeaderMessageType == [from : LeaderProcesses, type : {NEWLEADER}, epoch : Epochs, initial_history : Histories]
    AckLeaderMessageType == [from : FollowerProcesses, type : {ACK_LD}, epoch : Epochs]
    CommitLeaderMessageType == [from : LeaderProcesses, type : {COMMIT_LD}, epoch : Epochs]
    ProposalMessageType == [from : LeaderProcesses, type : {PROPOSE}, epoch : Epochs, transaction : Transactions]
    AckProposalMessageType == [from : FollowerProcesses, type : {ACK_P}, epoch : Epochs, transaction : Transactions]
    CommitProposalMessageType == [from : LeaderProcesses, type : {COMMIT}, epoch : Epochs, transaction : Transactions]

    \* Messages sent from leaders to followers
    LeaderMessageType == UNION {
        NewEpochMessageType,
        NewLeaderMessageType,
        CommitLeaderMessageType,
        ProposalMessageType,
        CommitProposalMessageType
    }

    \* Messages sent from followers to leaders
    FollowerMessageType == UNION {
        CepochMessageType,
        AckEpochMessageType,
        AckLeaderMessageType,
        AckProposalMessageType
    }


    \*** Other Helpers

    IsQuorum(subset, set) == 2 * Cardinality(subset) > Cardinality(set)

    Max(a, b) == IF b > a THEN b ELSE a

    Range(seq) == {seq[i] : i \in DOMAIN seq}

    \* Returns the set of indices for the value x in the sequence
    Indices(x, seq) == {i \in DOMAIN seq : seq[i] = x}

    \* Returns the last element in the sequence, or the provided default if the sequence is empty
    LastOrDefault(seq, default) == IF Len(seq) = 0 THEN default ELSE seq[Len(seq)]


    \*** Phase 0: Leader oracle

    \* TODO: does the oracle only produce a single result for each epoch? How should the leader oracle best be represented?
    \* TODO: should we include a refinement that chooses the server with the latest zxid (as used in the zookeeper implemenation)?
    LeaderOracle(epoch) == CHOOSE s \in Servers : TRUE

end define;

\* Wraps the Send() operator to update the messages structure
macro DoSend(to, m)
begin
    messages := Send(to, m, messages);
end macro;

macro DoSendToSet(to_procs, m)
begin
    messages := SendToSet(to_procs, m, messages);
end macro;

\* Wraps the Recv() operator to set the message variable to the next message and update the messages structure
macro DoRecv()
begin
    assert CanRecv(self, messages);
    \* TODO: is there a more elegant way to get the next value from a sequence while removing it?
    with from \in {p \in Processes : CanRecvFrom(self, p, messages)} do
        message[self] := Recv(self, from, messages)[1] || messages := Recv(self, from, messages)[2];
    end with;
end macro;

\* Meant to be used with PeekMessage or DoPeekMessage. Dequeues the specified message from the message queue.
macro DoRecvMessage(m)
begin
    assert CanRecvFrom(self, m.from, messages);
    message[self] := Recv(self, m.from, messages)[1] || messages := Recv(self, m.from, messages)[2];
    assert message[self] = m;
end macro;

\* The Zab specification states that the input buffer of a process contains messages from at most one iteration of each process.
\* FlushMessages clears out the message buffer for a process.
macro FlushMessages(proc)
begin
    messages := [messages EXCEPT ![proc] = [sender \in Processes |-> <<>>]]
end macro;

\* Follower Phase 1: Discovery
procedure FP1()
begin
    Notify:
        DoSend(LeaderProc(candidate), CepochMessage(self, last_epoch));
    GetAckEpochMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = NEWEPOCH /\ m.from = LeaderProc(candidate);
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = NEWEPOCH /\ msg.from = LeaderProc(candidate)} do
            DoRecvMessage(m);
        end with;
    HandleAckEpochMessage:
        if last_epoch < message[self].epoch then
            last_epoch := message[self].epoch;
            DoSend(LeaderProc(candidate), AckEpochMessage(self, last_leader, history));
        else
            \* TODO: under what conditions should we not check for the next message, e.g. restart leader election?
            goto GetAckEpochMessage;
        end if;
    End_FP1:
        return;
end procedure;

\* Leader Phase 1: Discovery
procedure LP1()
variables confirmed = {},
          latest_epoch = 0;
begin
    GatherQuorum:
        while ~IsQuorum(followers, Servers) do
                await \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH;
                with m \in {msg \in ReceivableMessages(self, messages) : msg.type = CEPOCH} do
                    DoRecvMessage(m);
                end with;

                \* TODO: under what conditions should we not check for the next message, e.g. restart leader election?
                \* latest epoch seen by followers in quorum
                latest_epoch := Max(latest_epoch, message[self].last_epoch);
                if message[self].from.server \notin followers then
                    followers := followers \union {message[self].from.server};
                end if;
        end while;

        assert IsQuorum(followers, Servers);
        new_epoch := latest_epoch + 1;
    NewEpoch:
        DoSendToSet({FollowerProc(f) : f \in followers}, NewEpochMessage(self, new_epoch));
    HistorySelection:
        while confirmed /= followers do
                await \E m \in ReceivableMessages(self, messages) : m.type = ACK_E;
                with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_E} do
                    DoRecvMessage(m);
                end with;

                confirmed := confirmed \union {message[self].from.server};

                if  \/ message[self].last_leader > selected_history.last_leader
                    \/  /\ message[self].last_leader = selected_history.last_leader
                        /\ ZxidGreaterThan(LastOrDefault(message[self].history, [zxid |-> Zxid(0,0)]).zxid, LastOrDefault(selected_history.history, [zxid |-> Zxid(0,0)]).zxid) then
                    selected_history := [last_leader |-> message[self].last_leader, history |-> message[self].history];
                end if;
        end while;

        return;
end procedure;

\* Follower Phase 2: Synchronization
procedure FP2()
begin
    GetNewLeaderMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = NEWLEADER;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = NEWLEADER} do
            DoRecvMessage(m);
        end with;
    HandleNewLeaderMessage:
        if last_epoch = message[self].epoch then
            last_leader := message[self].epoch;
            \* TODO: do we need to separately accept each value, zxid pair? Or can we just set the history
            history := message[self].initial_history;
            DoSend(LeaderProc(candidate), AckLeaderMessage(self, message[self].epoch))
        else
            \* should start the protocol over again if the last acknowledged epoch proposal is different than the specified epoch
            \* TODO: how should we structure the spec to be able to jump back to the beginning of the process?
            restart := TRUE;
            goto End_FP2;
        end if;
    GetCommitLDMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = COMMIT_LD;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = COMMIT_LD} do
            DoRecvMessage(m);
        end with;

        delivered := delivered \o history;
    End_FP2:
        return;
end procedure;

\* Leader Phase 2: Synchronization
procedure LP2()
variables confirmed = {};   \* followers that have ack'd the new leader message
begin
    LP2Start:
        assert IsQuorum(followers, Servers);
        DoSendToSet({FollowerProc(f) : f \in followers}, NewLeaderMessage(self, new_epoch, selected_history.history));
    AwaitCommit:
        while ~IsQuorum(confirmed, Servers) do
                await \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD;
                with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_LD} do
                    DoRecvMessage(m);
                end with;

                confirmed := confirmed \union {message[self].from.server};
        end while;
    SendCommitLeader:
        \* Send commit to all followers, not just those in the quorum
        DoSendToSet({FollowerProc(s) : s \in Servers}, CommitLeaderMessage(self, new_epoch));

        return;
end procedure;

\* Follower Phase 3: Broadcast
procedure FollowerBroadcastAccept()
begin
    GetProposalMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = PROPOSE /\ m.from = LeaderProc(candidate);
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = PROPOSE /\ msg.from = LeaderProc(candidate)} do
            DoRecvMessage(m);
        end with;

    HandleProposal:
        \* TODO: should we do epoch and zxid checks before appending?
        history := Append(history, message[self].transaction);

        DoSend(LeaderProc(candidate), AckProposalMessage(self, message[self].epoch, message[self].transaction));

        return;
end procedure;

procedure FollowerBroadcastCommit()
begin
    GetCommitMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = COMMIT /\ m.from = LeaderProc(candidate);
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = COMMIT /\ msg.from = LeaderProc(candidate)} do
            DoRecvMessage(m);
        end with;

        \* TODO: if all previous transactions have not been delivered yet, should we discard the COMMIT message or try to save it for later?
        \* Only deliver if all previous transactions in the history have been delivered as per zxid
        \* TODO: It's not specified in the "Dissecting Zab" paper that a follower must have added a transaction to its
        \*  history before it can commit that transaction, but this is needed for agreement.
        \* TODO: It's not specified in the "Dissecting Zab" paper that a follower should ignore commit messages for
        \*  transactions it has already delivered, but this is needed for the total order invariant.
        if  /\ message[self].transaction \in Range(history)
            /\ message[self].transaction \notin Range(delivered)
            /\ \A trans \in Range(history) : ZxidGreaterThan(message[self].transaction.zxid, trans.zxid) => trans \in Range(delivered)
        then
            delivered := Append(delivered, message[self].transaction);
        end if;

        return;
end procedure;

\* Leader Phase 3: Broadcast
procedure LeaderPropose(v)
begin
    SendProposal:
        assert IsQuorum(followers, Servers);

        DoSendToSet({FollowerProc(f) : f \in followers}, ProposalMessage(self, new_epoch, Transaction(v, Zxid(new_epoch, counter))));
        proposed := Append(proposed, Transaction(v, Zxid(new_epoch, counter)));
        broadcast_transactions := broadcast_transactions \union {Transaction(v, Zxid(new_epoch, counter))};
        counter := counter + 1;

        return;
end procedure;

procedure LeaderCommit()
begin
    GetProposeAckMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = ACK_P;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_P} do
            DoRecvMessage(m);
        end with;

        proposal_acks[message[self].transaction, message[self].epoch] := proposal_acks[message[self].transaction, message[self].epoch] \union {message[self].from.server};

    SendCommit:
        \* TODO: should probably only send commit message once
        if IsQuorum(proposal_acks[message[self].transaction, message[self].epoch], Servers) then
            \* Send to all followers, not just those that have ackd
            DoSendToSet({FollowerProc(f) : f \in followers}, CommitProposalMessage(self, new_epoch, message[self].transaction));
        end if;

    End_LeaderCommit:
        return;
end procedure;

procedure LeaderSetupNewFollower()
begin
    GetNewCepochMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = CEPOCH} do
            DoRecvMessage(m);
        end with;

        if message[self].last_epoch < new_epoch then
            SendNewEpoch:
                DoSend(message[self].from, NewEpochMessage(self, new_epoch));
            SendNewLeader:
                DoSend(message[self].from, NewLeaderMessage(self, new_epoch, selected_history.history \o proposed));
        else
            \* TODO: what to do if the epoch in the CEPOCH message is greater than the current epoch? Restart the discovery process?
            skip;
        end if;

    End_LeaderSetupNewFollower:
        return;
end procedure;

procedure LeaderAddFollowerToQuorum()
begin
    GetAckNewLeaderMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_LD} do
            DoRecvMessage(m);
        end with;
    HandleAckLeader:
        \* TODO: Potential bug with Zab protocol (agreement propert) if:
        \*  1) Followers 1 and 2 added to quorum, then sent, ack and commit a transaction.
        \*  2) Follower 3 responds to the original NEWLEADER message which includes an empty history. Gets added to
        \*      quorum during leader's broadcast phase.
        \*  3) Leader proposes new transaction, all 3 followers ack and commit. Now Follower 3 has delivered a
        \*      different set of messages than Followers 1 and 2.
        \*  Could maybe be fixed by modifying the ACK_LD message to also include the set of transactions in the
        \*  initial history. The leader would then only send a COMMIT message if the initial history matched up with
        \*  the history so far.
        if message[self].epoch = new_epoch then
            DoSend(message[self].from, CommitLeaderMessage(self, new_epoch));
            followers := followers \union {message[self].from.server};
        end if;

    return;
end procedure;

procedure IgnoreAckEpoch()
begin
    DiscardAckEpochMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = ACK_E;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_E} do
            DoRecvMessage(m);
        end with;

        return;
end procedure;

\* Models follower thread for each process
process follower \in FollowerProcesses
variables last_epoch = 0,       \* Last new epoch proposol acknowledged
          last_leader = 0,      \* Last new leader proposal acknowledged
          history = <<>>,              \* In-order record of all the accepted value proposals
          candidate,            \* Candidate selected by leader oracle
          delivered = <<>>,       \* Tracks the transactions that have been delivered to the application by Zab
          \* TODO: how should we structure the spec to be able to jump back to the beginning of the process? Right now we use a flag
          restart = FALSE;
begin
    \* TODO: need to run multiple iterations, should include a loop
    FollowerDiscover:
        candidate := LeaderOracle(last_epoch + 1);
        call FP1();

    FollowerSynchronize:
        call FP2();
    FollowerSynchronizeCheckRestart:
        if restart then
            goto End_Follower;
        end if;

    SetReady:
        if candidate = self.server then
            primaries := [primaries EXCEPT ![last_epoch] = primaries[last_epoch] \union {self.server}];
        end if;

    FollowerBroadcast:
        while TRUE do
                either
                    await \E m \in ReceivableMessages(self, messages) : m.type = PROPOSE /\ m.from = LeaderProc(candidate);
                    call FollowerBroadcastAccept();
                or
                    await \E m \in ReceivableMessages(self, messages) : m.type = COMMIT /\ m.from = LeaderProc(candidate);
                    call FollowerBroadcastCommit();
                end either;
        end while;

    End_Follower:
        skip;
end process;

\* Models leader thread for each process
process leader \in LeaderProcesses
variables leader_candidate,            \* Candidate selected by leader oracle
          followers = {},     \* tracks the followers committed to a leader
          selected_history = [last_leader |-> 0, history |-> <<>>],     \* tracks the selected initial history
          new_epoch = 0,
          counter = 0,          \* Incremented for each proposal, used to generate monotonically increasing zxid
          proposed = <<>>,      \* Tracks the transactions proposed by the leader for the current epoch
          proposal_acks = [t \in Transactions, e \in Epochs |-> {}];   \* Tracks acks for proposed transactions
begin
    \* TODO: need to run multiple iterations, should include a loop
    LeaderDiscover:
        leader_candidate := LeaderOracle(last_epoch + 1);
        if leader_candidate = self.server then
            call LP1();

        LeaderSynchronize:
            call LP2();

        LeaderBroadcast:
            while TRUE do
                    either
                        with val \in Values do
                            call LeaderPropose(val);
                        end with;
                    or
                        await \E m \in ReceivableMessages(self, messages) : m.type = ACK_P;
                        call LeaderCommit();
                    or
                        await \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH;
                        call LeaderSetupNewFollower();
                    or
                        await \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD;
                        call LeaderAddFollowerToQuorum();
                    or
                        \* TODO: the zab protocol doesn't state how ack epoch messages should be handled in this phase. Should they just be ignored?
                        await \E m \in ReceivableMessages(self, messages) : m.type = ACK_E;
                        call IgnoreAckEpoch();
                    end either
            end while;
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2bdc4f54" /\ chksum(tla) = "9cc6f359")
\* Procedure variable confirmed of procedure LP1 at line 211 col 11 changed to confirmed_
CONSTANT defaultInitValue
VARIABLES messages, message, primaries, broadcast_transactions, pc, stack

(* define statement *)
Zxid(epoch, counter) == [epoch |-> epoch, counter |-> counter]

ZxidGreaterThan(left, right) == \/ left.epoch > right.epoch
                                \/ /\ left.epoch = right.epoch
                                   /\ left.counter > right.counter

Transaction(value, zxid) == [value |-> value, zxid |-> zxid]

Process(server, role) == [server |-> server, role |-> role]
FollowerProc(server) == Process(server, Follower)
LeaderProc(server) == Process(server, Leader)


Epochs == 0..MAX_EPOCHS
Counters == 0..MAX_COUNTER
Zxids == {Zxid(epoch, counter) : epoch \in Epochs, counter \in Counters}
Transactions == {Transaction(value, zxid) : value \in Values, zxid \in Zxids}
Histories == UNION {[1..i -> Transactions] : i \in 0..MAX_HISTORY_LENGTH}
LeaderProcesses == {LeaderProc(s) : s \in Servers}
FollowerProcesses == {FollowerProc(s) : s \in Servers}
Processes == LeaderProcesses \union FollowerProcesses


ServerPerms == Permutations(Servers)

SymmetrySets == ServerPerms



Send(to, m, _messages) == [_messages EXCEPT ![to] = [_messages[to] EXCEPT ![m.from] = Append(_messages[to][m.from], m)]]


RECURSIVE SendToSet(_, _, _)
SendToSet(set, m, _messages) == IF Cardinality(set) = 0
                                THEN _messages
                                ELSE
                                    LET to == CHOOSE to \in set : TRUE
                                        others == set \ {to}
                                    IN Send(to, m, SendToSet(others, m, _messages))


Recv(proc, from, _messages) == <<Head(_messages[proc][from]), [_messages EXCEPT ![proc] = [_messages[proc] EXCEPT ![from] = Tail(_messages[proc][from])]]>>


PeekMessage(proc, from, _messages) == Head(_messages[proc][from])

CanRecvFrom(proc, from, _messages) == Len(_messages[proc][from]) > 0
CanRecv(proc, _messages) == \E from \in Processes : CanRecvFrom(proc, from, _messages)

ReceivableMessages(proc, _messages) == {PeekMessage(proc, from, _messages) : from \in {p \in Processes : CanRecvFrom(proc, p, _messages)}}


CepochMessage(from, last_epoch) == [from |-> from, type |-> CEPOCH, last_epoch |-> last_epoch]
NewEpochMessage(from, epoch) == [from |-> from, type |-> NEWEPOCH, epoch |-> epoch]
AckEpochMessage(from, last_leader, history) == [from |-> from, type |-> ACK_E, last_leader |-> last_leader, history |-> history]
NewLeaderMessage(from, epoch, initial_history) == [from |-> from, type |-> NEWLEADER, epoch |-> epoch, initial_history |-> initial_history]
AckLeaderMessage(from, epoch) == [from |-> from, type |-> ACK_LD, epoch |-> epoch]
CommitLeaderMessage(from, epoch) == [from |-> from, type |-> COMMIT_LD, epoch |-> epoch]
ProposalMessage(from, epoch, transaction) == [from |-> from, type |-> PROPOSE, epoch |-> epoch, transaction |-> transaction]
AckProposalMessage(from, epoch, transaction) == [from |-> from, type |-> ACK_P, epoch |-> epoch, transaction |-> transaction]
CommitProposalMessage(from, epoch, transaction) == [from |-> from, type |-> COMMIT, epoch |-> epoch, transaction |-> transaction]


CepochMessageType == [from : FollowerProcesses, type : {CEPOCH}, last_epoch : Epochs]
NewEpochMessageType == [from : LeaderProcesses, type : {NEWEPOCH}, epoch : Epochs]
AckEpochMessageType == [from : FollowerProcesses, type : {ACK_E}, last_leader : Epochs, history : Histories]
NewLeaderMessageType == [from : LeaderProcesses, type : {NEWLEADER}, epoch : Epochs, initial_history : Histories]
AckLeaderMessageType == [from : FollowerProcesses, type : {ACK_LD}, epoch : Epochs]
CommitLeaderMessageType == [from : LeaderProcesses, type : {COMMIT_LD}, epoch : Epochs]
ProposalMessageType == [from : LeaderProcesses, type : {PROPOSE}, epoch : Epochs, transaction : Transactions]
AckProposalMessageType == [from : FollowerProcesses, type : {ACK_P}, epoch : Epochs, transaction : Transactions]
CommitProposalMessageType == [from : LeaderProcesses, type : {COMMIT}, epoch : Epochs, transaction : Transactions]


LeaderMessageType == UNION {
    NewEpochMessageType,
    NewLeaderMessageType,
    CommitLeaderMessageType,
    ProposalMessageType,
    CommitProposalMessageType
}


FollowerMessageType == UNION {
    CepochMessageType,
    AckEpochMessageType,
    AckLeaderMessageType,
    AckProposalMessageType
}




IsQuorum(subset, set) == 2 * Cardinality(subset) > Cardinality(set)

Max(a, b) == IF b > a THEN b ELSE a

Range(seq) == {seq[i] : i \in DOMAIN seq}


Indices(x, seq) == {i \in DOMAIN seq : seq[i] = x}


LastOrDefault(seq, default) == IF Len(seq) = 0 THEN default ELSE seq[Len(seq)]






LeaderOracle(epoch) == CHOOSE s \in Servers : TRUE

VARIABLES confirmed_, latest_epoch, confirmed, v, last_epoch, last_leader,
          history, candidate, delivered, restart, leader_candidate, followers,
          selected_history, new_epoch, counter, proposed, proposal_acks

vars == << messages, message, primaries, broadcast_transactions, pc, stack,
           confirmed_, latest_epoch, confirmed, v, last_epoch, last_leader,
           history, candidate, delivered, restart, leader_candidate,
           followers, selected_history, new_epoch, counter, proposed,
           proposal_acks >>

ProcSet == (FollowerProcesses) \cup (LeaderProcesses)

Init == (* Global variables *)
        /\ messages = [receiver \in Processes |-> [sender \in Processes |-> <<>>]]
        /\ message = [receiver \in Processes |-> {}]
        /\ primaries = [epoch \in Epochs |-> {}]
        /\ broadcast_transactions = {}
        (* Procedure LP1 *)
        /\ confirmed_ = [ self \in ProcSet |-> {}]
        /\ latest_epoch = [ self \in ProcSet |-> 0]
        (* Procedure LP2 *)
        /\ confirmed = [ self \in ProcSet |-> {}]
        (* Procedure LeaderPropose *)
        /\ v = [ self \in ProcSet |-> defaultInitValue]
        (* Process follower *)
        /\ last_epoch = [self \in FollowerProcesses |-> 0]
        /\ last_leader = [self \in FollowerProcesses |-> 0]
        /\ history = [self \in FollowerProcesses |-> <<>>]
        /\ candidate = [self \in FollowerProcesses |-> defaultInitValue]
        /\ delivered = [self \in FollowerProcesses |-> <<>>]
        /\ restart = [self \in FollowerProcesses |-> FALSE]
        (* Process leader *)
        /\ leader_candidate = [self \in LeaderProcesses |-> defaultInitValue]
        /\ followers = [self \in LeaderProcesses |-> {}]
        /\ selected_history = [self \in LeaderProcesses |-> [last_leader |-> 0, history |-> <<>>]]
        /\ new_epoch = [self \in LeaderProcesses |-> 0]
        /\ counter = [self \in LeaderProcesses |-> 0]
        /\ proposed = [self \in LeaderProcesses |-> <<>>]
        /\ proposal_acks = [self \in LeaderProcesses |-> [t \in Transactions, e \in Epochs |-> {}]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in FollowerProcesses -> "FollowerDiscover"
                                        [] self \in LeaderProcesses -> "LeaderDiscover"]

Notify(self) == /\ pc[self] = "Notify"
                /\ messages' = Send((LeaderProc(candidate[self])), (CepochMessage(self, last_epoch[self])), messages)
                /\ pc' = [pc EXCEPT ![self] = "GetAckEpochMessage"]
                /\ UNCHANGED << message, primaries, broadcast_transactions,
                                stack, confirmed_, latest_epoch, confirmed, v,
                                last_epoch, last_leader, history, candidate,
                                delivered, restart, leader_candidate,
                                followers, selected_history, new_epoch,
                                counter, proposed, proposal_acks >>

GetAckEpochMessage(self) == /\ pc[self] = "GetAckEpochMessage"
                            /\ \E m \in ReceivableMessages(self, messages) : m.type = NEWEPOCH /\ m.from = LeaderProc(candidate[self])
                            /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = NEWEPOCH /\ msg.from = LeaderProc(candidate[self])}:
                                 /\ Assert(CanRecvFrom(self, m.from, messages),
                                           "Failure of assertion at line 175, column 5 of macro called at line 195, column 13.")
                                 /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                    /\ messages' = Recv(self, m.from, messages)[2]
                                 /\ Assert(message'[self] = m,
                                           "Failure of assertion at line 177, column 5 of macro called at line 195, column 13.")
                            /\ pc' = [pc EXCEPT ![self] = "HandleAckEpochMessage"]
                            /\ UNCHANGED << primaries, broadcast_transactions,
                                            stack, confirmed_, latest_epoch,
                                            confirmed, v, last_epoch,
                                            last_leader, history, candidate,
                                            delivered, restart,
                                            leader_candidate, followers,
                                            selected_history, new_epoch,
                                            counter, proposed, proposal_acks >>

HandleAckEpochMessage(self) == /\ pc[self] = "HandleAckEpochMessage"
                               /\ IF last_epoch[self] < message[self].epoch
                                     THEN /\ last_epoch' = [last_epoch EXCEPT ![self] = message[self].epoch]
                                          /\ messages' = Send((LeaderProc(candidate[self])), (AckEpochMessage(self, last_leader[self], history[self])), messages)
                                          /\ pc' = [pc EXCEPT ![self] = "End_FP1"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "GetAckEpochMessage"]
                                          /\ UNCHANGED << messages, last_epoch >>
                               /\ UNCHANGED << message, primaries,
                                               broadcast_transactions, stack,
                                               confirmed_, latest_epoch,
                                               confirmed, v, last_leader,
                                               history, candidate, delivered,
                                               restart, leader_candidate,
                                               followers, selected_history,
                                               new_epoch, counter, proposed,
                                               proposal_acks >>

End_FP1(self) == /\ pc[self] = "End_FP1"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << messages, message, primaries,
                                 broadcast_transactions, confirmed_,
                                 latest_epoch, confirmed, v, last_epoch,
                                 last_leader, history, candidate, delivered,
                                 restart, leader_candidate, followers,
                                 selected_history, new_epoch, counter,
                                 proposed, proposal_acks >>

FP1(self) == Notify(self) \/ GetAckEpochMessage(self)
                \/ HandleAckEpochMessage(self) \/ End_FP1(self)

GatherQuorum(self) == /\ pc[self] = "GatherQuorum"
                      /\ IF ~IsQuorum(followers[self], Servers)
                            THEN /\ \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH
                                 /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = CEPOCH}:
                                      /\ Assert(CanRecvFrom(self, m.from, messages),
                                                "Failure of assertion at line 175, column 5 of macro called at line 218, column 21.")
                                      /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                         /\ messages' = Recv(self, m.from, messages)[2]
                                      /\ Assert(message'[self] = m,
                                                "Failure of assertion at line 177, column 5 of macro called at line 218, column 21.")
                                 /\ latest_epoch' = [latest_epoch EXCEPT ![self] = Max(latest_epoch[self], message'[self].last_epoch)]
                                 /\ IF message'[self].from.server \notin followers[self]
                                       THEN /\ followers' = [followers EXCEPT ![self] = followers[self] \union {message'[self].from.server}]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED followers
                                 /\ pc' = [pc EXCEPT ![self] = "GatherQuorum"]
                                 /\ UNCHANGED new_epoch
                            ELSE /\ Assert(IsQuorum(followers[self], Servers),
                                           "Failure of assertion at line 229, column 9.")
                                 /\ new_epoch' = [new_epoch EXCEPT ![self] = latest_epoch[self] + 1]
                                 /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                                 /\ UNCHANGED << messages, message,
                                                 latest_epoch, followers >>
                      /\ UNCHANGED << primaries, broadcast_transactions, stack,
                                      confirmed_, confirmed, v, last_epoch,
                                      last_leader, history, candidate,
                                      delivered, restart, leader_candidate,
                                      selected_history, counter, proposed,
                                      proposal_acks >>

NewEpoch(self) == /\ pc[self] = "NewEpoch"
                  /\ messages' = SendToSet(({FollowerProc(f) : f \in followers[self]}), (NewEpochMessage(self, new_epoch[self])), messages)
                  /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                  /\ UNCHANGED << message, primaries, broadcast_transactions,
                                  stack, confirmed_, latest_epoch, confirmed,
                                  v, last_epoch, last_leader, history,
                                  candidate, delivered, restart,
                                  leader_candidate, followers,
                                  selected_history, new_epoch, counter,
                                  proposed, proposal_acks >>

HistorySelection(self) == /\ pc[self] = "HistorySelection"
                          /\ IF confirmed_[self] /= followers[self]
                                THEN /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_E
                                     /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_E}:
                                          /\ Assert(CanRecvFrom(self, m.from, messages),
                                                    "Failure of assertion at line 175, column 5 of macro called at line 237, column 21.")
                                          /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                             /\ messages' = Recv(self, m.from, messages)[2]
                                          /\ Assert(message'[self] = m,
                                                    "Failure of assertion at line 177, column 5 of macro called at line 237, column 21.")
                                     /\ confirmed_' = [confirmed_ EXCEPT ![self] = confirmed_[self] \union {message'[self].from.server}]
                                     /\ IF \/ message'[self].last_leader > selected_history[self].last_leader
                                           \/  /\ message'[self].last_leader = selected_history[self].last_leader
                                               /\ ZxidGreaterThan(LastOrDefault(message'[self].history, [zxid |-> Zxid(0,0)]).zxid, LastOrDefault(selected_history[self].history, [zxid |-> Zxid(0,0)]).zxid)
                                           THEN /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> message'[self].last_leader, history |-> message'[self].history]]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED selected_history
                                     /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                                     /\ UNCHANGED << stack, latest_epoch >>
                                ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ confirmed_' = [confirmed_ EXCEPT ![self] = Head(stack[self]).confirmed_]
                                     /\ latest_epoch' = [latest_epoch EXCEPT ![self] = Head(stack[self]).latest_epoch]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                     /\ UNCHANGED << messages, message,
                                                     selected_history >>
                          /\ UNCHANGED << primaries, broadcast_transactions,
                                          confirmed, v, last_epoch,
                                          last_leader, history, candidate,
                                          delivered, restart, leader_candidate,
                                          followers, new_epoch, counter,
                                          proposed, proposal_acks >>

LP1(self) == GatherQuorum(self) \/ NewEpoch(self) \/ HistorySelection(self)

GetNewLeaderMessage(self) == /\ pc[self] = "GetNewLeaderMessage"
                             /\ \E m \in ReceivableMessages(self, messages) : m.type = NEWLEADER
                             /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = NEWLEADER}:
                                  /\ Assert(CanRecvFrom(self, m.from, messages),
                                            "Failure of assertion at line 175, column 5 of macro called at line 258, column 13.")
                                  /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                     /\ messages' = Recv(self, m.from, messages)[2]
                                  /\ Assert(message'[self] = m,
                                            "Failure of assertion at line 177, column 5 of macro called at line 258, column 13.")
                             /\ pc' = [pc EXCEPT ![self] = "HandleNewLeaderMessage"]
                             /\ UNCHANGED << primaries, broadcast_transactions,
                                             stack, confirmed_, latest_epoch,
                                             confirmed, v, last_epoch,
                                             last_leader, history, candidate,
                                             delivered, restart,
                                             leader_candidate, followers,
                                             selected_history, new_epoch,
                                             counter, proposed, proposal_acks >>

HandleNewLeaderMessage(self) == /\ pc[self] = "HandleNewLeaderMessage"
                                /\ IF last_epoch[self] = message[self].epoch
                                      THEN /\ last_leader' = [last_leader EXCEPT ![self] = message[self].epoch]
                                           /\ history' = [history EXCEPT ![self] = message[self].initial_history]
                                           /\ messages' = Send((LeaderProc(candidate[self])), (AckLeaderMessage(self, message[self].epoch)), messages)
                                           /\ pc' = [pc EXCEPT ![self] = "GetCommitLDMessage"]
                                           /\ UNCHANGED restart
                                      ELSE /\ restart' = [restart EXCEPT ![self] = TRUE]
                                           /\ pc' = [pc EXCEPT ![self] = "End_FP2"]
                                           /\ UNCHANGED << messages,
                                                           last_leader,
                                                           history >>
                                /\ UNCHANGED << message, primaries,
                                                broadcast_transactions, stack,
                                                confirmed_, latest_epoch,
                                                confirmed, v, last_epoch,
                                                candidate, delivered,
                                                leader_candidate, followers,
                                                selected_history, new_epoch,
                                                counter, proposed,
                                                proposal_acks >>

GetCommitLDMessage(self) == /\ pc[self] = "GetCommitLDMessage"
                            /\ \E m \in ReceivableMessages(self, messages) : m.type = COMMIT_LD
                            /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = COMMIT_LD}:
                                 /\ Assert(CanRecvFrom(self, m.from, messages),
                                           "Failure of assertion at line 175, column 5 of macro called at line 275, column 13.")
                                 /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                    /\ messages' = Recv(self, m.from, messages)[2]
                                 /\ Assert(message'[self] = m,
                                           "Failure of assertion at line 177, column 5 of macro called at line 275, column 13.")
                            /\ delivered' = [delivered EXCEPT ![self] = delivered[self] \o history[self]]
                            /\ pc' = [pc EXCEPT ![self] = "End_FP2"]
                            /\ UNCHANGED << primaries, broadcast_transactions,
                                            stack, confirmed_, latest_epoch,
                                            confirmed, v, last_epoch,
                                            last_leader, history, candidate,
                                            restart, leader_candidate,
                                            followers, selected_history,
                                            new_epoch, counter, proposed,
                                            proposal_acks >>

End_FP2(self) == /\ pc[self] = "End_FP2"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << messages, message, primaries,
                                 broadcast_transactions, confirmed_,
                                 latest_epoch, confirmed, v, last_epoch,
                                 last_leader, history, candidate, delivered,
                                 restart, leader_candidate, followers,
                                 selected_history, new_epoch, counter,
                                 proposed, proposal_acks >>

FP2(self) == GetNewLeaderMessage(self) \/ HandleNewLeaderMessage(self)
                \/ GetCommitLDMessage(self) \/ End_FP2(self)

LP2Start(self) == /\ pc[self] = "LP2Start"
                  /\ Assert(IsQuorum(followers[self], Servers),
                            "Failure of assertion at line 288, column 9.")
                  /\ messages' = SendToSet(({FollowerProc(f) : f \in followers[self]}), (NewLeaderMessage(self, new_epoch[self], selected_history[self].history)), messages)
                  /\ pc' = [pc EXCEPT ![self] = "AwaitCommit"]
                  /\ UNCHANGED << message, primaries, broadcast_transactions,
                                  stack, confirmed_, latest_epoch, confirmed,
                                  v, last_epoch, last_leader, history,
                                  candidate, delivered, restart,
                                  leader_candidate, followers,
                                  selected_history, new_epoch, counter,
                                  proposed, proposal_acks >>

AwaitCommit(self) == /\ pc[self] = "AwaitCommit"
                     /\ IF ~IsQuorum(confirmed[self], Servers)
                           THEN /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD
                                /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_LD}:
                                     /\ Assert(CanRecvFrom(self, m.from, messages),
                                               "Failure of assertion at line 175, column 5 of macro called at line 294, column 21.")
                                     /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                        /\ messages' = Recv(self, m.from, messages)[2]
                                     /\ Assert(message'[self] = m,
                                               "Failure of assertion at line 177, column 5 of macro called at line 294, column 21.")
                                /\ confirmed' = [confirmed EXCEPT ![self] = confirmed[self] \union {message'[self].from.server}]
                                /\ pc' = [pc EXCEPT ![self] = "AwaitCommit"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "SendCommitLeader"]
                                /\ UNCHANGED << messages, message, confirmed >>
                     /\ UNCHANGED << primaries, broadcast_transactions, stack,
                                     confirmed_, latest_epoch, v, last_epoch,
                                     last_leader, history, candidate,
                                     delivered, restart, leader_candidate,
                                     followers, selected_history, new_epoch,
                                     counter, proposed, proposal_acks >>

SendCommitLeader(self) == /\ pc[self] = "SendCommitLeader"
                          /\ messages' = SendToSet(({FollowerProc(s) : s \in Servers}), (CommitLeaderMessage(self, new_epoch[self])), messages)
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ confirmed' = [confirmed EXCEPT ![self] = Head(stack[self]).confirmed]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << message, primaries,
                                          broadcast_transactions, confirmed_,
                                          latest_epoch, v, last_epoch,
                                          last_leader, history, candidate,
                                          delivered, restart, leader_candidate,
                                          followers, selected_history,
                                          new_epoch, counter, proposed,
                                          proposal_acks >>

LP2(self) == LP2Start(self) \/ AwaitCommit(self) \/ SendCommitLeader(self)

GetProposalMessage(self) == /\ pc[self] = "GetProposalMessage"
                            /\ \E m \in ReceivableMessages(self, messages) : m.type = PROPOSE /\ m.from = LeaderProc(candidate[self])
                            /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = PROPOSE /\ msg.from = LeaderProc(candidate[self])}:
                                 /\ Assert(CanRecvFrom(self, m.from, messages),
                                           "Failure of assertion at line 175, column 5 of macro called at line 312, column 13.")
                                 /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                    /\ messages' = Recv(self, m.from, messages)[2]
                                 /\ Assert(message'[self] = m,
                                           "Failure of assertion at line 177, column 5 of macro called at line 312, column 13.")
                            /\ pc' = [pc EXCEPT ![self] = "HandleProposal"]
                            /\ UNCHANGED << primaries, broadcast_transactions,
                                            stack, confirmed_, latest_epoch,
                                            confirmed, v, last_epoch,
                                            last_leader, history, candidate,
                                            delivered, restart,
                                            leader_candidate, followers,
                                            selected_history, new_epoch,
                                            counter, proposed, proposal_acks >>

HandleProposal(self) == /\ pc[self] = "HandleProposal"
                        /\ history' = [history EXCEPT ![self] = Append(history[self], message[self].transaction)]
                        /\ messages' = Send((LeaderProc(candidate[self])), (AckProposalMessage(self, message[self].epoch, message[self].transaction)), messages)
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << message, primaries,
                                        broadcast_transactions, confirmed_,
                                        latest_epoch, confirmed, v, last_epoch,
                                        last_leader, candidate, delivered,
                                        restart, leader_candidate, followers,
                                        selected_history, new_epoch, counter,
                                        proposed, proposal_acks >>

FollowerBroadcastAccept(self) == GetProposalMessage(self)
                                    \/ HandleProposal(self)

GetCommitMessage(self) == /\ pc[self] = "GetCommitMessage"
                          /\ \E m \in ReceivableMessages(self, messages) : m.type = COMMIT /\ m.from = LeaderProc(candidate[self])
                          /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = COMMIT /\ msg.from = LeaderProc(candidate[self])}:
                               /\ Assert(CanRecvFrom(self, m.from, messages),
                                         "Failure of assertion at line 175, column 5 of macro called at line 329, column 13.")
                               /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                  /\ messages' = Recv(self, m.from, messages)[2]
                               /\ Assert(message'[self] = m,
                                         "Failure of assertion at line 177, column 5 of macro called at line 329, column 13.")
                          /\ IF /\ message'[self].transaction \in Range(history[self])
                                /\ message'[self].transaction \notin Range(delivered[self])
                                /\ \A trans \in Range(history[self]) : ZxidGreaterThan(message'[self].transaction.zxid, trans.zxid) => trans \in Range(delivered[self])
                                THEN /\ delivered' = [delivered EXCEPT ![self] = Append(delivered[self], message'[self].transaction)]
                                ELSE /\ TRUE
                                     /\ UNCHANGED delivered
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << primaries, broadcast_transactions,
                                          confirmed_, latest_epoch, confirmed,
                                          v, last_epoch, last_leader, history,
                                          candidate, restart, leader_candidate,
                                          followers, selected_history,
                                          new_epoch, counter, proposed,
                                          proposal_acks >>

FollowerBroadcastCommit(self) == GetCommitMessage(self)

SendProposal(self) == /\ pc[self] = "SendProposal"
                      /\ Assert(IsQuorum(followers[self], Servers),
                                "Failure of assertion at line 352, column 9.")
                      /\ messages' = SendToSet(({FollowerProc(f) : f \in followers[self]}), (ProposalMessage(self, new_epoch[self], Transaction(v[self], Zxid(new_epoch[self], counter[self])))), messages)
                      /\ proposed' = [proposed EXCEPT ![self] = Append(proposed[self], Transaction(v[self], Zxid(new_epoch[self], counter[self])))]
                      /\ broadcast_transactions' = (broadcast_transactions \union {Transaction(v[self], Zxid(new_epoch[self], counter[self]))})
                      /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ v' = [v EXCEPT ![self] = Head(stack[self]).v]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << message, primaries, confirmed_,
                                      latest_epoch, confirmed, last_epoch,
                                      last_leader, history, candidate,
                                      delivered, restart, leader_candidate,
                                      followers, selected_history, new_epoch,
                                      proposal_acks >>

LeaderPropose(self) == SendProposal(self)

GetProposeAckMessage(self) == /\ pc[self] = "GetProposeAckMessage"
                              /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_P
                              /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_P}:
                                   /\ Assert(CanRecvFrom(self, m.from, messages),
                                             "Failure of assertion at line 175, column 5 of macro called at line 367, column 13.")
                                   /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                      /\ messages' = Recv(self, m.from, messages)[2]
                                   /\ Assert(message'[self] = m,
                                             "Failure of assertion at line 177, column 5 of macro called at line 367, column 13.")
                              /\ proposal_acks' = [proposal_acks EXCEPT ![self][message'[self].transaction, message'[self].epoch] = proposal_acks[self][message'[self].transaction, message'[self].epoch] \union {message'[self].from.server}]
                              /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                              /\ UNCHANGED << primaries,
                                              broadcast_transactions, stack,
                                              confirmed_, latest_epoch,
                                              confirmed, v, last_epoch,
                                              last_leader, history, candidate,
                                              delivered, restart,
                                              leader_candidate, followers,
                                              selected_history, new_epoch,
                                              counter, proposed >>

SendCommit(self) == /\ pc[self] = "SendCommit"
                    /\ IF IsQuorum(proposal_acks[self][message[self].transaction, message[self].epoch], Servers)
                          THEN /\ messages' = SendToSet(({FollowerProc(f) : f \in followers[self]}), (CommitProposalMessage(self, new_epoch[self], message[self].transaction)), messages)
                          ELSE /\ TRUE
                               /\ UNCHANGED messages
                    /\ pc' = [pc EXCEPT ![self] = "End_LeaderCommit"]
                    /\ UNCHANGED << message, primaries, broadcast_transactions,
                                    stack, confirmed_, latest_epoch, confirmed,
                                    v, last_epoch, last_leader, history,
                                    candidate, delivered, restart,
                                    leader_candidate, followers,
                                    selected_history, new_epoch, counter,
                                    proposed, proposal_acks >>

End_LeaderCommit(self) == /\ pc[self] = "End_LeaderCommit"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << messages, message, primaries,
                                          broadcast_transactions, confirmed_,
                                          latest_epoch, confirmed, v,
                                          last_epoch, last_leader, history,
                                          candidate, delivered, restart,
                                          leader_candidate, followers,
                                          selected_history, new_epoch, counter,
                                          proposed, proposal_acks >>

LeaderCommit(self) == GetProposeAckMessage(self) \/ SendCommit(self)
                         \/ End_LeaderCommit(self)

GetNewCepochMessage(self) == /\ pc[self] = "GetNewCepochMessage"
                             /\ \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH
                             /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = CEPOCH}:
                                  /\ Assert(CanRecvFrom(self, m.from, messages),
                                            "Failure of assertion at line 175, column 5 of macro called at line 388, column 13.")
                                  /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                     /\ messages' = Recv(self, m.from, messages)[2]
                                  /\ Assert(message'[self] = m,
                                            "Failure of assertion at line 177, column 5 of macro called at line 388, column 13.")
                             /\ IF message'[self].last_epoch < new_epoch[self]
                                   THEN /\ pc' = [pc EXCEPT ![self] = "SendNewEpoch"]
                                   ELSE /\ TRUE
                                        /\ pc' = [pc EXCEPT ![self] = "End_LeaderSetupNewFollower"]
                             /\ UNCHANGED << primaries, broadcast_transactions,
                                             stack, confirmed_, latest_epoch,
                                             confirmed, v, last_epoch,
                                             last_leader, history, candidate,
                                             delivered, restart,
                                             leader_candidate, followers,
                                             selected_history, new_epoch,
                                             counter, proposed, proposal_acks >>

SendNewEpoch(self) == /\ pc[self] = "SendNewEpoch"
                      /\ messages' = Send((message[self].from), (NewEpochMessage(self, new_epoch[self])), messages)
                      /\ pc' = [pc EXCEPT ![self] = "SendNewLeader"]
                      /\ UNCHANGED << message, primaries,
                                      broadcast_transactions, stack,
                                      confirmed_, latest_epoch, confirmed, v,
                                      last_epoch, last_leader, history,
                                      candidate, delivered, restart,
                                      leader_candidate, followers,
                                      selected_history, new_epoch, counter,
                                      proposed, proposal_acks >>

SendNewLeader(self) == /\ pc[self] = "SendNewLeader"
                       /\ messages' = Send((message[self].from), (NewLeaderMessage(self, new_epoch[self], selected_history[self].history \o proposed[self])), messages)
                       /\ pc' = [pc EXCEPT ![self] = "End_LeaderSetupNewFollower"]
                       /\ UNCHANGED << message, primaries,
                                       broadcast_transactions, stack,
                                       confirmed_, latest_epoch, confirmed, v,
                                       last_epoch, last_leader, history,
                                       candidate, delivered, restart,
                                       leader_candidate, followers,
                                       selected_history, new_epoch, counter,
                                       proposed, proposal_acks >>

End_LeaderSetupNewFollower(self) == /\ pc[self] = "End_LeaderSetupNewFollower"
                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    /\ UNCHANGED << messages, message,
                                                    primaries,
                                                    broadcast_transactions,
                                                    confirmed_, latest_epoch,
                                                    confirmed, v, last_epoch,
                                                    last_leader, history,
                                                    candidate, delivered,
                                                    restart, leader_candidate,
                                                    followers,
                                                    selected_history,
                                                    new_epoch, counter,
                                                    proposed, proposal_acks >>

LeaderSetupNewFollower(self) == GetNewCepochMessage(self)
                                   \/ SendNewEpoch(self)
                                   \/ SendNewLeader(self)
                                   \/ End_LeaderSetupNewFollower(self)

GetAckNewLeaderMessage(self) == /\ pc[self] = "GetAckNewLeaderMessage"
                                /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD
                                /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_LD}:
                                     /\ Assert(CanRecvFrom(self, m.from, messages),
                                               "Failure of assertion at line 175, column 5 of macro called at line 410, column 13.")
                                     /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                        /\ messages' = Recv(self, m.from, messages)[2]
                                     /\ Assert(message'[self] = m,
                                               "Failure of assertion at line 177, column 5 of macro called at line 410, column 13.")
                                /\ pc' = [pc EXCEPT ![self] = "HandleAckLeader"]
                                /\ UNCHANGED << primaries,
                                                broadcast_transactions, stack,
                                                confirmed_, latest_epoch,
                                                confirmed, v, last_epoch,
                                                last_leader, history,
                                                candidate, delivered, restart,
                                                leader_candidate, followers,
                                                selected_history, new_epoch,
                                                counter, proposed,
                                                proposal_acks >>

HandleAckLeader(self) == /\ pc[self] = "HandleAckLeader"
                         /\ IF message[self].epoch = new_epoch[self]
                               THEN /\ messages' = Send((message[self].from), (CommitLeaderMessage(self, new_epoch[self])), messages)
                                    /\ followers' = [followers EXCEPT ![self] = followers[self] \union {message[self].from.server}]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << messages, followers >>
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << message, primaries,
                                         broadcast_transactions, confirmed_,
                                         latest_epoch, confirmed, v,
                                         last_epoch, last_leader, history,
                                         candidate, delivered, restart,
                                         leader_candidate, selected_history,
                                         new_epoch, counter, proposed,
                                         proposal_acks >>

LeaderAddFollowerToQuorum(self) == GetAckNewLeaderMessage(self)
                                      \/ HandleAckLeader(self)

DiscardAckEpochMessage(self) == /\ pc[self] = "DiscardAckEpochMessage"
                                /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_E
                                /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_E}:
                                     /\ Assert(CanRecvFrom(self, m.from, messages),
                                               "Failure of assertion at line 175, column 5 of macro called at line 435, column 13.")
                                     /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                        /\ messages' = Recv(self, m.from, messages)[2]
                                     /\ Assert(message'[self] = m,
                                               "Failure of assertion at line 177, column 5 of macro called at line 435, column 13.")
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << primaries,
                                                broadcast_transactions,
                                                confirmed_, latest_epoch,
                                                confirmed, v, last_epoch,
                                                last_leader, history,
                                                candidate, delivered, restart,
                                                leader_candidate, followers,
                                                selected_history, new_epoch,
                                                counter, proposed,
                                                proposal_acks >>

IgnoreAckEpoch(self) == DiscardAckEpochMessage(self)

FollowerDiscover(self) == /\ pc[self] = "FollowerDiscover"
                          /\ candidate' = [candidate EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP1",
                                                                   pc        |->  "FollowerSynchronize" ] >>
                                                               \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "Notify"]
                          /\ UNCHANGED << messages, message, primaries,
                                          broadcast_transactions, confirmed_,
                                          latest_epoch, confirmed, v,
                                          last_epoch, last_leader, history,
                                          delivered, restart, leader_candidate,
                                          followers, selected_history,
                                          new_epoch, counter, proposed,
                                          proposal_acks >>

FollowerSynchronize(self) == /\ pc[self] = "FollowerSynchronize"
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP2",
                                                                      pc        |->  "FollowerSynchronizeCheckRestart" ] >>
                                                                  \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "GetNewLeaderMessage"]
                             /\ UNCHANGED << messages, message, primaries,
                                             broadcast_transactions,
                                             confirmed_, latest_epoch,
                                             confirmed, v, last_epoch,
                                             last_leader, history, candidate,
                                             delivered, restart,
                                             leader_candidate, followers,
                                             selected_history, new_epoch,
                                             counter, proposed, proposal_acks >>

FollowerSynchronizeCheckRestart(self) == /\ pc[self] = "FollowerSynchronizeCheckRestart"
                                         /\ IF restart[self]
                                               THEN /\ pc' = [pc EXCEPT ![self] = "End_Follower"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "SetReady"]
                                         /\ UNCHANGED << messages, message,
                                                         primaries,
                                                         broadcast_transactions,
                                                         stack, confirmed_,
                                                         latest_epoch,
                                                         confirmed, v,
                                                         last_epoch,
                                                         last_leader, history,
                                                         candidate, delivered,
                                                         restart,
                                                         leader_candidate,
                                                         followers,
                                                         selected_history,
                                                         new_epoch, counter,
                                                         proposed,
                                                         proposal_acks >>

SetReady(self) == /\ pc[self] = "SetReady"
                  /\ IF candidate[self] = self.server
                        THEN /\ primaries' = [primaries EXCEPT ![last_epoch[self]] = primaries[last_epoch[self]] \union {self.server}]
                        ELSE /\ TRUE
                             /\ UNCHANGED primaries
                  /\ pc' = [pc EXCEPT ![self] = "FollowerBroadcast"]
                  /\ UNCHANGED << messages, message, broadcast_transactions,
                                  stack, confirmed_, latest_epoch, confirmed,
                                  v, last_epoch, last_leader, history,
                                  candidate, delivered, restart,
                                  leader_candidate, followers,
                                  selected_history, new_epoch, counter,
                                  proposed, proposal_acks >>

FollowerBroadcast(self) == /\ pc[self] = "FollowerBroadcast"
                           /\ \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = PROPOSE /\ m.from = LeaderProc(candidate[self])
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FollowerBroadcastAccept",
                                                                          pc        |->  "FollowerBroadcast" ] >>
                                                                      \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "GetProposalMessage"]
                              \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = COMMIT /\ m.from = LeaderProc(candidate[self])
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FollowerBroadcastCommit",
                                                                          pc        |->  "FollowerBroadcast" ] >>
                                                                      \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "GetCommitMessage"]
                           /\ UNCHANGED << messages, message, primaries,
                                           broadcast_transactions, confirmed_,
                                           latest_epoch, confirmed, v,
                                           last_epoch, last_leader, history,
                                           candidate, delivered, restart,
                                           leader_candidate, followers,
                                           selected_history, new_epoch,
                                           counter, proposed, proposal_acks >>

End_Follower(self) == /\ pc[self] = "End_Follower"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << messages, message, primaries,
                                      broadcast_transactions, stack,
                                      confirmed_, latest_epoch, confirmed, v,
                                      last_epoch, last_leader, history,
                                      candidate, delivered, restart,
                                      leader_candidate, followers,
                                      selected_history, new_epoch, counter,
                                      proposed, proposal_acks >>

follower(self) == FollowerDiscover(self) \/ FollowerSynchronize(self)
                     \/ FollowerSynchronizeCheckRestart(self)
                     \/ SetReady(self) \/ FollowerBroadcast(self)
                     \/ End_Follower(self)

LeaderDiscover(self) == /\ pc[self] = "LeaderDiscover"
                        /\ leader_candidate' = [leader_candidate EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                        /\ IF leader_candidate'[self] = self.server
                              THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP1",
                                                                            pc        |->  "LeaderSynchronize",
                                                                            confirmed_ |->  confirmed_[self],
                                                                            latest_epoch |->  latest_epoch[self] ] >>
                                                                        \o stack[self]]
                                   /\ confirmed_' = [confirmed_ EXCEPT ![self] = {}]
                                   /\ latest_epoch' = [latest_epoch EXCEPT ![self] = 0]
                                   /\ pc' = [pc EXCEPT ![self] = "GatherQuorum"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << stack, confirmed_,
                                                   latest_epoch >>
                        /\ UNCHANGED << messages, message, primaries,
                                        broadcast_transactions, confirmed, v,
                                        last_epoch, last_leader, history,
                                        candidate, delivered, restart,
                                        followers, selected_history, new_epoch,
                                        counter, proposed, proposal_acks >>

LeaderSynchronize(self) == /\ pc[self] = "LeaderSynchronize"
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP2",
                                                                    pc        |->  "LeaderBroadcast",
                                                                    confirmed |->  confirmed[self] ] >>
                                                                \o stack[self]]
                           /\ confirmed' = [confirmed EXCEPT ![self] = {}]
                           /\ pc' = [pc EXCEPT ![self] = "LP2Start"]
                           /\ UNCHANGED << messages, message, primaries,
                                           broadcast_transactions, confirmed_,
                                           latest_epoch, v, last_epoch,
                                           last_leader, history, candidate,
                                           delivered, restart,
                                           leader_candidate, followers,
                                           selected_history, new_epoch,
                                           counter, proposed, proposal_acks >>

LeaderBroadcast(self) == /\ pc[self] = "LeaderBroadcast"
                         /\ \/ /\ \E val \in Values:
                                    /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderPropose",
                                                                                pc        |->  "LeaderBroadcast",
                                                                                v         |->  v[self] ] >>
                                                                            \o stack[self]]
                                       /\ v' = [v EXCEPT ![self] = val]
                                    /\ pc' = [pc EXCEPT ![self] = "SendProposal"]
                            \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_P
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderCommit",
                                                                        pc        |->  "LeaderBroadcast" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "GetProposeAckMessage"]
                               /\ v' = v
                            \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderSetupNewFollower",
                                                                        pc        |->  "LeaderBroadcast" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "GetNewCepochMessage"]
                               /\ v' = v
                            \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderAddFollowerToQuorum",
                                                                        pc        |->  "LeaderBroadcast" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "GetAckNewLeaderMessage"]
                               /\ v' = v
                            \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_E
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "IgnoreAckEpoch",
                                                                        pc        |->  "LeaderBroadcast" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "DiscardAckEpochMessage"]
                               /\ v' = v
                         /\ UNCHANGED << messages, message, primaries,
                                         broadcast_transactions, confirmed_,
                                         latest_epoch, confirmed, last_epoch,
                                         last_leader, history, candidate,
                                         delivered, restart, leader_candidate,
                                         followers, selected_history,
                                         new_epoch, counter, proposed,
                                         proposal_acks >>

leader(self) == LeaderDiscover(self) \/ LeaderSynchronize(self)
                   \/ LeaderBroadcast(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ FP1(self) \/ LP1(self) \/ FP2(self)
                               \/ LP2(self) \/ FollowerBroadcastAccept(self)
                               \/ FollowerBroadcastCommit(self)
                               \/ LeaderPropose(self) \/ LeaderCommit(self)
                               \/ LeaderSetupNewFollower(self)
                               \/ LeaderAddFollowerToQuorum(self)
                               \/ IgnoreAckEpoch(self))
           \/ (\E self \in FollowerProcesses: follower(self))
           \/ (\E self \in LeaderProcesses: leader(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION




\* Type invariant checks
\* TODO: ensure that the queue is a sequence
LeaderMessagesOK(proc, queue) == /\ proc \in LeaderProcesses
                                 /\ \A from \in DOMAIN queue:
                                    /\ from \in Processes
                                    /\ \A m \in Range(queue[from]):
                                        m \in FollowerMessageType

FollowerMessagesOK(proc, queue) ==  /\ proc \in FollowerProcesses
                                    /\ \A from \in DOMAIN queue:
                                        /\ from \in Processes
                                        /\ \A m \in Range(queue[from]):
                                            m \in LeaderMessageType

\* Leaders should only receive messages from followers, and vice versa
MessagesOK == \A proc \in DOMAIN messages:
                \/ proc.role = Leader /\ LeaderMessagesOK(proc, messages[proc])
                \/ proc.role = Follower /\ FollowerMessagesOK(proc, messages[proc])

FollowersOK == \A proc \in DOMAIN followers:
                    /\ proc \in LeaderProcesses
                    /\ followers[proc] \in SUBSET Servers

TypeOK == /\ MessagesOK
          /\ FollowersOK


\** Protocol invariants
\* Claim 29 in "Dissecting Zab"
PrimaryUniqueness == \A epoch \in DOMAIN primaries : Cardinality(primaries[epoch]) <= 1

\* Claim 30 in "Dissecting Zab"
BroadcastIntegrity == \A proc \in DOMAIN delivered :
                        \A transaction \in Range(delivered[proc]) :
                            transaction \in broadcast_transactions

\* Claim 31 in "Dissecting Zab"
\* If a follower f delivers transaction t, and follower f' delivers transaction t', then f' delivers t or f delivers t'
Agreement == \A p_1 \in DOMAIN delivered, p_2 \in DOMAIN delivered :
                \/ p_1 = p_2
                \/ \A t_1 \in Range(delivered[p_1]), t_2 \in Range(delivered[p_2]) :
                    \/ t_1 = t_2
                    \/ t_1 \in Range(delivered[p_2])
                    \/ t_2 \in Range(delivered[p_1])

\* Claim 32 in "Dissecting Zab"
\* If some follower delivers <v,z> before <v',z'>, then any follower that delivers <v',z'> must also deliver <v,z> and
\* deliver it before <v', z'>.
\* TODO: potential bug in protocol:
\*  1) Leader moves to broadcast phase with followers 1 and 2, proposes several transactions.
\*  2) Follower 3 added to Leader quorum with initial history containing the proposed transactions (as per step l.3.3).
\*      This history is then delivered (effectively committed) as per step f.2.2. This can occur before any of those
\*      transactions are ever ack'd by the quorum.
\*  3) Crashes result in a new leader before the quorum receives commit messages. A new epoch is started. Due to
\*      crashes, follower 3 does not join the initial quorum. An empty history is selected as the initial history.
\*  4) New transactions are proposed, ack'd, committed, and delivered. Now followers 1 and 2 have delivered different
\*      transactions than follower 3.
TotalOrder == \A p_1 \in DOMAIN delivered, p_2 \in DOMAIN delivered :
                \/ p_1 = p_2
                \/ \A i \in 1..Len(delivered[p_1]) : \A j \in i..Len(delivered[p_1]) :
                    LET t == delivered[p_1][i]
                        t_p == delivered[p_1][j]
                        \* indices of the transactions in the second follower
                        i_t_2 == Indices(t, delivered[p_2])
                        i_t_p_2 == Indices(t_p, delivered[p_2])
                    IN  \/ t = t_p
                        \/ t_p \in Range(delivered[p_2]) =>
                            /\ t \in Range(delivered[p_2])
                            /\ \A a \in i_t_2, b \in i_t_p_2 : a < b

\** Debugging checks
ProgressCheck == /\ \E proc \in DOMAIN delivered: Len(delivered[proc]) < 2



\* Type checker constraints
MessageLenConstraint == \A proc \in DOMAIN messages: \A sender \in DOMAIN messages[proc] : Len(messages[proc][sender]) <= MAX_MESSAGES
EpochConstraint == \A proc \in DOMAIN new_epoch : new_epoch[proc] <= MAX_EPOCHS
CounterConstraint == \A proc \in DOMAIN counter : counter[proc] <= MAX_COUNTER


====
