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
CONSTANTS MAX_NUM_CRASHES

(* --algorithm zab_algo

\* Represents messages sent from one server to another. Each process has its own channel with each other process.
\* Maps from the receiver process to the sender process to the messages
variables messages = [receiver \in Processes |-> [sender \in Processes |-> <<>>]],
          message = [receiver \in Processes |-> <<>>],              \* Used to temporarily hold a received message
          primaries = [epoch \in Epochs |-> {}],        \* Maps each epoch to the primaries for that epoch (meaning the processes that call ready)
          broadcast_transactions = {},                  \* Tracks all the transactions that have ever been broadcast
          crashed = [proc \in Processes |-> FALSE],     \* Tracks if a process has crashed
          num_crashes = 0,                              \* Tracks total number of crashes, used for model checking constraints
          phase = [proc \in Processes |-> ""];          \* Used to track what phase each process is in while allowing crashes in-between

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

    \* Returns an updated messages with the set of messages sent to the specified process
    RECURSIVE SendMessages(_, _, _)
    SendMessages(to, to_send, _messages) == IF Cardinality(to_send) = 0
                                    THEN _messages
                                    ELSE
                                        LET msg == CHOOSE msg \in to_send : TRUE
                                            others == to_send \ {msg}
                                        IN Send(to, msg, SendMessages(to, others, _messages))

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

macro DoSendMessages(to, msgs)
begin
    messages := SendMessages(to, msgs, messages);
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

\* Removes a message and sends another message in one step. Meant to be used with PeekMessage or DoPeekMessage.
macro DoRemoveThenSend(m, to_proc, msg)
begin
    assert CanRecvFrom(self, m.from, messages);
    messages := Send(to_proc, msg, Recv(self, m.from, messages)[2]);
end macro;

\* Removes a message and sends another message to a set of processes in one step. Meant to be used with PeekMessage
\* or DoPeekMessage.
macro DoRemoveThenSendToSet(m, to_procs, msg)
begin
    assert CanRecvFrom(self, m.from, messages);
    messages := SendToSet(to_procs, msg, Recv(self, m.from, messages)[2]);
end macro;

macro DoRemoveThenSendMessages(m, to, msgs)
begin
    assert CanRecvFrom(self, m.from, messages);
    messages := SendMessages(to, msgs, Recv(self, m.from, messages)[2]);
end macro;

\* Removes a message from the message queue. Meant to be used with PeekMessage or DoPeekMessage.
macro DoRemoveMessage(m)
begin
    assert CanRecvFrom(self, m.from, messages);
    messages := Recv(self, m.from, messages)[2];
end macro;

\* The Zab specification states that the input buffer of a process contains messages from at most one iteration of each process.
\* FlushMessages clears out the message buffer for a process.
macro FlushMessages(proc)
begin
    messages := [messages EXCEPT ![proc] = [sender \in Processes |-> <<>>]]
end macro;

\*** Crash and Recover macros
macro Crash(proc)
begin
    await ~crashed[proc];
    crashed := [crashed EXCEPT ![proc] = TRUE];
    num_crashes := num_crashes + 1;
end macro;

\* We wipe state in Recover() rather than in Crash() to ensure we wipe messages sent to a crashed process
macro Recover(proc)
begin
    await crashed[proc];
    crashed := [crashed EXCEPT ![proc] = FALSE];
    FlushMessages(proc);
end macro;

\* Follower Phase 1: Discovery
procedure FP1_1()
begin
    HandleAckEpochMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = NEWEPOCH /\ m.from = LeaderProc(candidate);
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = NEWEPOCH /\ msg.from = LeaderProc(candidate)} do
            if last_epoch < m.epoch then
                last_epoch := m.epoch;
                DoRemoveThenSend(m, LeaderProc(candidate), AckEpochMessage(self, last_leader, history));
                phase[self] := "FP2_0";
            else
                \* TODO: under what conditions should we not check for the next message, e.g. restart leader election?
                \* Ignore messages with a smaller epoch
                DoRemoveMessage(m);
            end if;
        end with;

    return;
end procedure;

\* Leader Phase 1: Discovery
procedure LP1_0()
begin
    GatherQuorum:
        assert \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = CEPOCH} do
            \* TODO: under what conditions should we not check for the next message, e.g. restart leader election?
            \* latest epoch seen by followers in quorum
            latest_epoch := Max(latest_epoch, m.last_epoch);
            if m.from.server \notin followers then
                followers := followers \union {m.from.server};
            end if;

            if IsQuorum(followers, Servers) then
                new_epoch := latest_epoch + 1;
                DoRemoveThenSendToSet(m, {FollowerProc(f) : f \in followers}, NewEpochMessage(self, new_epoch));
                phase[self] := "LP1_1";
            else
                DoRemoveMessage(m);
            end if;
        end with;

    return;
end procedure;

procedure LP1_1()
begin
    HistorySelection:
        assert \E m \in ReceivableMessages(self, messages) : m.type = ACK_E;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_E} do
            confirmed_epoch := confirmed_epoch \union {m.from.server};

            if  \/ m.last_leader > selected_history.last_leader
                \/  /\ m.last_leader = selected_history.last_leader
                    /\ ZxidGreaterThan(LastOrDefault(m.history, [zxid |-> Zxid(0,0)]).zxid, LastOrDefault(selected_history.history, [zxid |-> Zxid(0,0)]).zxid) then
                selected_history := [last_leader |-> m.last_leader, history |-> m.history];
            end if;

            DoRemoveMessage(m);
        end with;

        if confirmed_epoch = followers then
            phase[self] := "LP2_0";
        end if;

        return;
end procedure;

\* Follower Phase 2: Synchronization
procedure FP2_0()
begin
    HandleNewLeaderMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = NEWLEADER;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = NEWLEADER} do
            if last_epoch = m.epoch then
                last_leader := m.epoch;
                \* TODO: do we need to separately accept each value, zxid pair? Or can we just set the history
                history := m.initial_history;
                DoRemoveThenSend(m, LeaderProc(candidate), AckLeaderMessage(self, m.epoch));
                phase[self] := "FP2_1";
            else
                \* Should start the protocol over again if the last acknowledged epoch proposal is different than the specified epoch
                \* TODO: how should we structure the spec to be able to jump back to the beginning of the process?
                phase[self] := "FP1_0";
            end if;
        end with;

    return;
end procedure;

procedure FP2_1()
begin
    GetCommitLDMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = COMMIT_LD;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = COMMIT_LD} do
            delivered := delivered \o history;
            DoRemoveMessage(m);
            phase[self] := "FP3_0";
        end with;

    return;
end procedure;

\* Leader Phase 2: Synchronization
procedure LP2_1()
begin
    AwaitCommit:
        assert \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_LD} do
            confirmed_leader := confirmed_leader \union {m.from.server};

            if IsQuorum(confirmed_leader, Servers) then
                \* Send commit to all followers, not just those in the quorum
                DoRemoveThenSendToSet(m, {FollowerProc(s) : s \in Servers}, CommitLeaderMessage(self, new_epoch));
                phase[self] := "LP3_0";
            else
                DoRemoveMessage(m);
            end if;
        end with;

    return;
end procedure;

\* Follower Phase 3: Broadcast
procedure FollowerBroadcastAccept()
begin
    GetProposalMessage:
        either
            await ~crashed[self];
            Crash(self);
            restart := TRUE;
            goto End_FollowerBroadcastAccept;
        or
            await \E m \in ReceivableMessages(self, messages) : m.type = PROPOSE /\ m.from = LeaderProc(candidate);
            with m \in {msg \in ReceivableMessages(self, messages) : msg.type = PROPOSE /\ msg.from = LeaderProc(candidate)} do
                DoRecvMessage(m);
            end with;
        end either;

    HandleProposal:
        either
            await ~crashed[self];
            Crash(self);
            restart := TRUE;
            goto End_FollowerBroadcastAccept;
        or
            \* TODO: should we do epoch and zxid checks before appending?
            history := Append(history, message[self].transaction);

            DoSend(LeaderProc(candidate), AckProposalMessage(self, message[self].epoch, message[self].transaction));
        end either;

    End_FollowerBroadcastAccept:
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
    AwaitAckProposal:
        assert \E m \in ReceivableMessages(self, messages) : m.type = ACK_P;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_P} do
            proposal_acks[m.transaction, m.epoch] := proposal_acks[m.transaction, m.epoch] \union {m.from.server};

            \* TODO: should probably only send commit message once
            if IsQuorum(proposal_acks[m.transaction, m.epoch], Servers) then
                \* Send to all followers, not just those that have ackd
                DoRemoveThenSendToSet(m, {FollowerProc(f) : f \in followers}, CommitProposalMessage(self, new_epoch, m.transaction));
            else
                DoRemoveMessage(m);
            end if;
        end with;

    return;
end procedure;

procedure LeaderSetupNewFollower()
begin
    GetNewCepochMessage:
        assert \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = CEPOCH} do
            if m.last_epoch < new_epoch then
                DoRemoveThenSendMessages(m, m.from, {
                    NewEpochMessage(self, new_epoch),
                    NewLeaderMessage(self, new_epoch, selected_history.history \o proposed)
                });
            else
                \* TODO: what to do if the epoch in the CEPOCH message is greater than the current epoch? Restart
                \*  the discovery process?
                DoRemoveMessage(m);
            end if;
        end with;

    return;
end procedure;

procedure LeaderAddFollowerToQuorum()
begin
    \* TODO: Potential bug with Zab protocol (agreement property) if:
    \*  1) Followers 1 and 2 added to quorum, then sent, ack and commit a transaction.
    \*  2) Follower 3 responds to the original NEWLEADER message which includes an empty history. Gets added to
    \*      quorum during leader's broadcast phase.
    \*  3) Leader proposes new transaction, all 3 followers ack and commit. Now Follower 3 has delivered a
    \*      different set of messages than Followers 1 and 2.
    \*  Could maybe be fixed by modifying the ACK_LD message to also include the set of transactions in the
    \*  initial history. The leader would then only send a COMMIT message if the initial history matched up with
    \*  the history so far.
    GetAckNewLeaderMessage:
        assert \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_LD} do
            if m.epoch = new_epoch then
                DoRemoveThenSend(m, m.from, CommitLeaderMessage(self, new_epoch));
                followers := followers \union {m.from.server};
            else
                DoRemoveMessage(m);
            end if;
        end with;

    return;
end procedure;

procedure IgnoreAckEpoch()
begin
    DiscardAckEpochMessage:
        await \E m \in ReceivableMessages(self, messages) : m.type = ACK_E;
        with m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_E} do
            DoRemoveMessage(m);
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
    FollowerDiscover:
        restart := FALSE;
        phase[self] := "FP1_0";

    FollowerSynchronize:
        while phase[self] /= "FP3_1" do
            either
                await ~crashed[self];
                Crash(self);
                goto FollowerCrashed;
            or
                await phase[self] = "FP1_0";
                NotifyLeader:
                    candidate := LeaderOracle(last_epoch + 1);
                    DoSend(LeaderProc(candidate), CepochMessage(self, last_epoch));
                    phase[self] := "FP1_1"
            or
                await phase[self] = "FP1_1";
                await \E m \in ReceivableMessages(self, messages) : m.type = NEWEPOCH /\ m.from = LeaderProc(candidate);
                call FP1_1();
            or
                await phase[self] = "FP2_0";
                await \E m \in ReceivableMessages(self, messages) : m.type = NEWLEADER;
                call FP2_0();
            or
                await phase[self] = "FP2_1";
                await \E m \in ReceivableMessages(self, messages) : m.type = COMMIT_LD;
                call FP2_1();
            or
                await phase[self] = "FP3_0";
                SetReady:
                    if candidate = self.server then
                        primaries := [primaries EXCEPT ![last_epoch] = primaries[last_epoch] \union {self.server}];
                    end if;
                    phase[self] := "FP3_1";
            end either;
        end while;

    FollowerBroadcast:
        while TRUE do
                either
                    await ~crashed[self];
                    Crash(self);
                    goto FollowerCrashed;
                or
                    await \E m \in ReceivableMessages(self, messages) : m.type = PROPOSE /\ m.from = LeaderProc(candidate);
                    call FollowerBroadcastAccept();

                    FollowerBroadcastAcceptCheckRestart:
                        if restart then
                            if crashed[self] then
                                goto FollowerCrashed;
                            else
                                goto FollowerDiscover;
                            end if;
                        end if;
                or
                    await \E m \in ReceivableMessages(self, messages) : m.type = COMMIT /\ m.from = LeaderProc(candidate);
                    call FollowerBroadcastCommit();

                    FollowerBroadcastCommitCheckRestart:
                        if restart then
                            if crashed[self] then
                                goto FollowerCrashed;
                            else
                                goto FollowerDiscover;
                            end if;
                        end if;
                end either;
        end while;

    FollowerCrashed:
        await crashed[self];
        Recover(self);
        goto FollowerDiscover;

end process;

\* Models leader thread for each process
process leader \in LeaderProcesses
variables followers = {},     \* tracks the followers committed to a leader
          selected_history = [last_leader |-> 0, history |-> <<>>],     \* tracks the selected initial history
          new_epoch = 0,
          counter = 0,          \* Incremented for each proposal, used to generate monotonically increasing zxid
          proposed = <<>>,      \* Tracks the transactions proposed by the leader for the current epoch
          proposal_acks = [t \in Transactions, e \in Epochs |-> {}],   \* Tracks acks for proposed transactions
          confirmed_epoch = {},     \* Used in to track followers that ack epoch proposals
          confirmed_leader = {},    \* Used in to track followers that ack leader proposals
          latest_epoch = 0;     \* Used to track the latest proposal from followers
begin
    LeaderStart:
        phase[self] := "LP1_0";
        followers := {};
        confirmed_epoch := {};
        confirmed_leader := {};
        latest_epoch := 0;
        selected_history := [last_leader |-> 0, history |-> <<>>];

    LeaderSynchronize:
        while phase[self] /= "LP3_0" do
            either
                await ~crashed[self];
                Crash(self);
                goto LeaderCrashed;
            or
                await phase[self] = "LP1_0";
                await LeaderOracle(last_epoch + 1) = self.server;
                await \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH;
                call LP1_0();
            or
                await phase[self] = "LP1_1";
                await \E m \in ReceivableMessages(self, messages) : m.type = ACK_E;
                call LP1_1();
            or
                await phase[self] = "LP2_0";
                assert IsQuorum(followers, Servers);
                DoSendToSet({FollowerProc(f) : f \in followers}, NewLeaderMessage(self, new_epoch, selected_history.history));
                phase[self] := "LP2_1";
            or
                await phase[self] = "LP2_1";
                await \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD;
                call LP2_1();
            end either;
        end while;

    LeaderBroadcast:
        while TRUE do
            either
                await ~crashed[self];
                Crash(self);
                goto LeaderCrashed;
            or
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

    LeaderCrashed:
        assert crashed[self];
        Recover(self);
        goto LeaderStart;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a4c402cd" /\ chksum(tla) = "71dcf668")
CONSTANT defaultInitValue
VARIABLES messages, message, primaries, broadcast_transactions, crashed,
          num_crashes, phase, pc, stack

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


RECURSIVE SendMessages(_, _, _)
SendMessages(to, to_send, _messages) == IF Cardinality(to_send) = 0
                                THEN _messages
                                ELSE
                                    LET msg == CHOOSE msg \in to_send : TRUE
                                        others == to_send \ {msg}
                                    IN Send(to, msg, SendMessages(to, others, _messages))


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

VARIABLES v, last_epoch, last_leader, history, candidate, delivered, restart,
          followers, selected_history, new_epoch, counter, proposed,
          proposal_acks, confirmed_epoch, confirmed_leader, latest_epoch

vars == << messages, message, primaries, broadcast_transactions, crashed,
           num_crashes, phase, pc, stack, v, last_epoch, last_leader, history,
           candidate, delivered, restart, followers, selected_history,
           new_epoch, counter, proposed, proposal_acks, confirmed_epoch,
           confirmed_leader, latest_epoch >>

ProcSet == (FollowerProcesses) \cup (LeaderProcesses)

Init == (* Global variables *)
        /\ messages = [receiver \in Processes |-> [sender \in Processes |-> <<>>]]
        /\ message = [receiver \in Processes |-> <<>>]
        /\ primaries = [epoch \in Epochs |-> {}]
        /\ broadcast_transactions = {}
        /\ crashed = [proc \in Processes |-> FALSE]
        /\ num_crashes = 0
        /\ phase = [proc \in Processes |-> ""]
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
        /\ followers = [self \in LeaderProcesses |-> {}]
        /\ selected_history = [self \in LeaderProcesses |-> [last_leader |-> 0, history |-> <<>>]]
        /\ new_epoch = [self \in LeaderProcesses |-> 0]
        /\ counter = [self \in LeaderProcesses |-> 0]
        /\ proposed = [self \in LeaderProcesses |-> <<>>]
        /\ proposal_acks = [self \in LeaderProcesses |-> [t \in Transactions, e \in Epochs |-> {}]]
        /\ confirmed_epoch = [self \in LeaderProcesses |-> {}]
        /\ confirmed_leader = [self \in LeaderProcesses |-> {}]
        /\ latest_epoch = [self \in LeaderProcesses |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in FollowerProcesses -> "FollowerDiscover"
                                        [] self \in LeaderProcesses -> "LeaderStart"]

HandleAckEpochMessage(self) == /\ pc[self] = "HandleAckEpochMessage"
                               /\ \E m \in ReceivableMessages(self, messages) : m.type = NEWEPOCH /\ m.from = LeaderProc(candidate[self])
                               /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = NEWEPOCH /\ msg.from = LeaderProc(candidate[self])}:
                                    IF last_epoch[self] < m.epoch
                                       THEN /\ last_epoch' = [last_epoch EXCEPT ![self] = m.epoch]
                                            /\ Assert(CanRecvFrom(self, m.from, messages),
                                                      "Failure of assertion at line 201, column 5 of macro called at line 257, column 17.")
                                            /\ messages' = Send((LeaderProc(candidate[self])), (AckEpochMessage(self, last_leader[self], history[self])), Recv(self, m.from, messages)[2])
                                            /\ phase' = [phase EXCEPT ![self] = "FP2_0"]
                                       ELSE /\ Assert(CanRecvFrom(self, m.from, messages),
                                                      "Failure of assertion at line 222, column 5 of macro called at line 262, column 17.")
                                            /\ messages' = Recv(self, m.from, messages)[2]
                                            /\ UNCHANGED << phase, last_epoch >>
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << message, primaries,
                                               broadcast_transactions, crashed,
                                               num_crashes, v, last_leader,
                                               history, candidate, delivered,
                                               restart, followers,
                                               selected_history, new_epoch,
                                               counter, proposed,
                                               proposal_acks, confirmed_epoch,
                                               confirmed_leader, latest_epoch >>

FP1_1(self) == HandleAckEpochMessage(self)

GatherQuorum(self) == /\ pc[self] = "GatherQuorum"
                      /\ Assert(\E m \in ReceivableMessages(self, messages) : m.type = CEPOCH,
                                "Failure of assertion at line 273, column 9.")
                      /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = CEPOCH}:
                           /\ latest_epoch' = [latest_epoch EXCEPT ![self] = Max(latest_epoch[self], m.last_epoch)]
                           /\ IF m.from.server \notin followers[self]
                                 THEN /\ followers' = [followers EXCEPT ![self] = followers[self] \union {m.from.server}]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED followers
                           /\ IF IsQuorum(followers'[self], Servers)
                                 THEN /\ new_epoch' = [new_epoch EXCEPT ![self] = latest_epoch'[self] + 1]
                                      /\ Assert(CanRecvFrom(self, m.from, messages),
                                                "Failure of assertion at line 209, column 5 of macro called at line 284, column 17.")
                                      /\ messages' = SendToSet(({FollowerProc(f) : f \in followers'[self]}), (NewEpochMessage(self, new_epoch'[self])), Recv(self, m.from, messages)[2])
                                      /\ phase' = [phase EXCEPT ![self] = "LP1_1"]
                                 ELSE /\ Assert(CanRecvFrom(self, m.from, messages),
                                                "Failure of assertion at line 222, column 5 of macro called at line 287, column 17.")
                                      /\ messages' = Recv(self, m.from, messages)[2]
                                      /\ UNCHANGED << phase, new_epoch >>
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << message, primaries,
                                      broadcast_transactions, crashed,
                                      num_crashes, v, last_epoch, last_leader,
                                      history, candidate, delivered, restart,
                                      selected_history, counter, proposed,
                                      proposal_acks, confirmed_epoch,
                                      confirmed_leader >>

LP1_0(self) == GatherQuorum(self)

HistorySelection(self) == /\ pc[self] = "HistorySelection"
                          /\ Assert(\E m \in ReceivableMessages(self, messages) : m.type = ACK_E,
                                    "Failure of assertion at line 297, column 9.")
                          /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_E}:
                               /\ confirmed_epoch' = [confirmed_epoch EXCEPT ![self] = confirmed_epoch[self] \union {m.from.server}]
                               /\ IF \/ m.last_leader > selected_history[self].last_leader
                                     \/  /\ m.last_leader = selected_history[self].last_leader
                                         /\ ZxidGreaterThan(LastOrDefault(m.history, [zxid |-> Zxid(0,0)]).zxid, LastOrDefault(selected_history[self].history, [zxid |-> Zxid(0,0)]).zxid)
                                     THEN /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> m.last_leader, history |-> m.history]]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED selected_history
                               /\ Assert(CanRecvFrom(self, m.from, messages),
                                         "Failure of assertion at line 222, column 5 of macro called at line 307, column 13.")
                               /\ messages' = Recv(self, m.from, messages)[2]
                          /\ IF confirmed_epoch'[self] = followers[self]
                                THEN /\ phase' = [phase EXCEPT ![self] = "LP2_0"]
                                ELSE /\ TRUE
                                     /\ phase' = phase
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << message, primaries,
                                          broadcast_transactions, crashed,
                                          num_crashes, v, last_epoch,
                                          last_leader, history, candidate,
                                          delivered, restart, followers,
                                          new_epoch, counter, proposed,
                                          proposal_acks, confirmed_leader,
                                          latest_epoch >>

LP1_1(self) == HistorySelection(self)

HandleNewLeaderMessage(self) == /\ pc[self] = "HandleNewLeaderMessage"
                                /\ \E m \in ReceivableMessages(self, messages) : m.type = NEWLEADER
                                /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = NEWLEADER}:
                                     IF last_epoch[self] = m.epoch
                                        THEN /\ last_leader' = [last_leader EXCEPT ![self] = m.epoch]
                                             /\ history' = [history EXCEPT ![self] = m.initial_history]
                                             /\ Assert(CanRecvFrom(self, m.from, messages),
                                                       "Failure of assertion at line 201, column 5 of macro called at line 327, column 17.")
                                             /\ messages' = Send((LeaderProc(candidate[self])), (AckLeaderMessage(self, m.epoch)), Recv(self, m.from, messages)[2])
                                             /\ phase' = [phase EXCEPT ![self] = "FP2_1"]
                                        ELSE /\ phase' = [phase EXCEPT ![self] = "FP1_0"]
                                             /\ UNCHANGED << messages,
                                                             last_leader,
                                                             history >>
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << message, primaries,
                                                broadcast_transactions,
                                                crashed, num_crashes, v,
                                                last_epoch, candidate,
                                                delivered, restart, followers,
                                                selected_history, new_epoch,
                                                counter, proposed,
                                                proposal_acks, confirmed_epoch,
                                                confirmed_leader, latest_epoch >>

FP2_0(self) == HandleNewLeaderMessage(self)

GetCommitLDMessage(self) == /\ pc[self] = "GetCommitLDMessage"
                            /\ \E m \in ReceivableMessages(self, messages) : m.type = COMMIT_LD
                            /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = COMMIT_LD}:
                                 /\ delivered' = [delivered EXCEPT ![self] = delivered[self] \o history[self]]
                                 /\ Assert(CanRecvFrom(self, m.from, messages),
                                           "Failure of assertion at line 222, column 5 of macro called at line 345, column 13.")
                                 /\ messages' = Recv(self, m.from, messages)[2]
                                 /\ phase' = [phase EXCEPT ![self] = "FP3_0"]
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << message, primaries,
                                            broadcast_transactions, crashed,
                                            num_crashes, v, last_epoch,
                                            last_leader, history, candidate,
                                            restart, followers,
                                            selected_history, new_epoch,
                                            counter, proposed, proposal_acks,
                                            confirmed_epoch, confirmed_leader,
                                            latest_epoch >>

FP2_1(self) == GetCommitLDMessage(self)

AwaitCommit(self) == /\ pc[self] = "AwaitCommit"
                     /\ Assert(\E m \in ReceivableMessages(self, messages) : m.type = ACK_LD,
                               "Failure of assertion at line 356, column 9.")
                     /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_LD}:
                          /\ confirmed_leader' = [confirmed_leader EXCEPT ![self] = confirmed_leader[self] \union {m.from.server}]
                          /\ IF IsQuorum(confirmed_leader'[self], Servers)
                                THEN /\ Assert(CanRecvFrom(self, m.from, messages),
                                               "Failure of assertion at line 209, column 5 of macro called at line 362, column 17.")
                                     /\ messages' = SendToSet(({FollowerProc(s) : s \in Servers}), (CommitLeaderMessage(self, new_epoch[self])), Recv(self, m.from, messages)[2])
                                     /\ phase' = [phase EXCEPT ![self] = "LP3_0"]
                                ELSE /\ Assert(CanRecvFrom(self, m.from, messages),
                                               "Failure of assertion at line 222, column 5 of macro called at line 365, column 17.")
                                     /\ messages' = Recv(self, m.from, messages)[2]
                                     /\ phase' = phase
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << message, primaries,
                                     broadcast_transactions, crashed,
                                     num_crashes, v, last_epoch, last_leader,
                                     history, candidate, delivered, restart,
                                     followers, selected_history, new_epoch,
                                     counter, proposed, proposal_acks,
                                     confirmed_epoch, latest_epoch >>

LP2_1(self) == AwaitCommit(self)

GetProposalMessage(self) == /\ pc[self] = "GetProposalMessage"
                            /\ \/ /\ ~crashed[self]
                                  /\ ~crashed[self]
                                  /\ crashed' = [crashed EXCEPT ![self] = TRUE]
                                  /\ num_crashes' = num_crashes + 1
                                  /\ restart' = [restart EXCEPT ![self] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "End_FollowerBroadcastAccept"]
                                  /\ UNCHANGED <<messages, message>>
                               \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = PROPOSE /\ m.from = LeaderProc(candidate[self])
                                  /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = PROPOSE /\ msg.from = LeaderProc(candidate[self])}:
                                       /\ Assert(CanRecvFrom(self, m.from, messages),
                                                 "Failure of assertion at line 193, column 5 of macro called at line 384, column 17.")
                                       /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                          /\ messages' = Recv(self, m.from, messages)[2]
                                       /\ Assert(message'[self] = m,
                                                 "Failure of assertion at line 195, column 5 of macro called at line 384, column 17.")
                                  /\ pc' = [pc EXCEPT ![self] = "HandleProposal"]
                                  /\ UNCHANGED <<crashed, num_crashes, restart>>
                            /\ UNCHANGED << primaries, broadcast_transactions,
                                            phase, stack, v, last_epoch,
                                            last_leader, history, candidate,
                                            delivered, followers,
                                            selected_history, new_epoch,
                                            counter, proposed, proposal_acks,
                                            confirmed_epoch, confirmed_leader,
                                            latest_epoch >>

HandleProposal(self) == /\ pc[self] = "HandleProposal"
                        /\ \/ /\ ~crashed[self]
                              /\ ~crashed[self]
                              /\ crashed' = [crashed EXCEPT ![self] = TRUE]
                              /\ num_crashes' = num_crashes + 1
                              /\ restart' = [restart EXCEPT ![self] = TRUE]
                              /\ pc' = [pc EXCEPT ![self] = "End_FollowerBroadcastAccept"]
                              /\ UNCHANGED <<messages, history>>
                           \/ /\ history' = [history EXCEPT ![self] = Append(history[self], message[self].transaction)]
                              /\ messages' = Send((LeaderProc(candidate[self])), (AckProposalMessage(self, message[self].epoch, message[self].transaction)), messages)
                              /\ pc' = [pc EXCEPT ![self] = "End_FollowerBroadcastAccept"]
                              /\ UNCHANGED <<crashed, num_crashes, restart>>
                        /\ UNCHANGED << message, primaries,
                                        broadcast_transactions, phase, stack,
                                        v, last_epoch, last_leader, candidate,
                                        delivered, followers, selected_history,
                                        new_epoch, counter, proposed,
                                        proposal_acks, confirmed_epoch,
                                        confirmed_leader, latest_epoch >>

End_FollowerBroadcastAccept(self) == /\ pc[self] = "End_FollowerBroadcastAccept"
                                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                     /\ UNCHANGED << messages, message,
                                                     primaries,
                                                     broadcast_transactions,
                                                     crashed, num_crashes,
                                                     phase, v, last_epoch,
                                                     last_leader, history,
                                                     candidate, delivered,
                                                     restart, followers,
                                                     selected_history,
                                                     new_epoch, counter,
                                                     proposed, proposal_acks,
                                                     confirmed_epoch,
                                                     confirmed_leader,
                                                     latest_epoch >>

FollowerBroadcastAccept(self) == GetProposalMessage(self)
                                    \/ HandleProposal(self)
                                    \/ End_FollowerBroadcastAccept(self)

GetCommitMessage(self) == /\ pc[self] = "GetCommitMessage"
                          /\ \E m \in ReceivableMessages(self, messages) : m.type = COMMIT /\ m.from = LeaderProc(candidate[self])
                          /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = COMMIT /\ msg.from = LeaderProc(candidate[self])}:
                               /\ Assert(CanRecvFrom(self, m.from, messages),
                                         "Failure of assertion at line 193, column 5 of macro called at line 410, column 13.")
                               /\ /\ message' = [message EXCEPT ![self] = Recv(self, m.from, messages)[1]]
                                  /\ messages' = Recv(self, m.from, messages)[2]
                               /\ Assert(message'[self] = m,
                                         "Failure of assertion at line 195, column 5 of macro called at line 410, column 13.")
                          /\ IF /\ message'[self].transaction \in Range(history[self])
                                /\ message'[self].transaction \notin Range(delivered[self])
                                /\ \A trans \in Range(history[self]) : ZxidGreaterThan(message'[self].transaction.zxid, trans.zxid) => trans \in Range(delivered[self])
                                THEN /\ delivered' = [delivered EXCEPT ![self] = Append(delivered[self], message'[self].transaction)]
                                ELSE /\ TRUE
                                     /\ UNCHANGED delivered
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << primaries, broadcast_transactions,
                                          crashed, num_crashes, phase, v,
                                          last_epoch, last_leader, history,
                                          candidate, restart, followers,
                                          selected_history, new_epoch, counter,
                                          proposed, proposal_acks,
                                          confirmed_epoch, confirmed_leader,
                                          latest_epoch >>

FollowerBroadcastCommit(self) == GetCommitMessage(self)

SendProposal(self) == /\ pc[self] = "SendProposal"
                      /\ Assert(IsQuorum(followers[self], Servers),
                                "Failure of assertion at line 433, column 9.")
                      /\ messages' = SendToSet(({FollowerProc(f) : f \in followers[self]}), (ProposalMessage(self, new_epoch[self], Transaction(v[self], Zxid(new_epoch[self], counter[self])))), messages)
                      /\ proposed' = [proposed EXCEPT ![self] = Append(proposed[self], Transaction(v[self], Zxid(new_epoch[self], counter[self])))]
                      /\ broadcast_transactions' = (broadcast_transactions \union {Transaction(v[self], Zxid(new_epoch[self], counter[self]))})
                      /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ v' = [v EXCEPT ![self] = Head(stack[self]).v]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << message, primaries, crashed, num_crashes,
                                      phase, last_epoch, last_leader, history,
                                      candidate, delivered, restart, followers,
                                      selected_history, new_epoch,
                                      proposal_acks, confirmed_epoch,
                                      confirmed_leader, latest_epoch >>

LeaderPropose(self) == SendProposal(self)

AwaitAckProposal(self) == /\ pc[self] = "AwaitAckProposal"
                          /\ Assert(\E m \in ReceivableMessages(self, messages) : m.type = ACK_P,
                                    "Failure of assertion at line 446, column 9.")
                          /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_P}:
                               /\ proposal_acks' = [proposal_acks EXCEPT ![self][m.transaction, m.epoch] = proposal_acks[self][m.transaction, m.epoch] \union {m.from.server}]
                               /\ IF IsQuorum(proposal_acks'[self][m.transaction, m.epoch], Servers)
                                     THEN /\ Assert(CanRecvFrom(self, m.from, messages),
                                                    "Failure of assertion at line 209, column 5 of macro called at line 453, column 17.")
                                          /\ messages' = SendToSet(({FollowerProc(f) : f \in followers[self]}), (CommitProposalMessage(self, new_epoch[self], m.transaction)), Recv(self, m.from, messages)[2])
                                     ELSE /\ Assert(CanRecvFrom(self, m.from, messages),
                                                    "Failure of assertion at line 222, column 5 of macro called at line 455, column 17.")
                                          /\ messages' = Recv(self, m.from, messages)[2]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << message, primaries,
                                          broadcast_transactions, crashed,
                                          num_crashes, phase, v, last_epoch,
                                          last_leader, history, candidate,
                                          delivered, restart, followers,
                                          selected_history, new_epoch, counter,
                                          proposed, confirmed_epoch,
                                          confirmed_leader, latest_epoch >>

LeaderCommit(self) == AwaitAckProposal(self)

GetNewCepochMessage(self) == /\ pc[self] = "GetNewCepochMessage"
                             /\ Assert(\E m \in ReceivableMessages(self, messages) : m.type = CEPOCH,
                                       "Failure of assertion at line 465, column 9.")
                             /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = CEPOCH}:
                                  IF m.last_epoch < new_epoch[self]
                                     THEN /\ Assert(CanRecvFrom(self, m.from, messages),
                                                    "Failure of assertion at line 215, column 5 of macro called at line 468, column 17.")
                                          /\ messages' = SendMessages((m.from), (                                    {
                                                             NewEpochMessage(self, new_epoch[self]),
                                                             NewLeaderMessage(self, new_epoch[self], selected_history[self].history \o proposed[self])
                                                         }), Recv(self, m.from, messages)[2])
                                     ELSE /\ Assert(CanRecvFrom(self, m.from, messages),
                                                    "Failure of assertion at line 222, column 5 of macro called at line 475, column 17.")
                                          /\ messages' = Recv(self, m.from, messages)[2]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << message, primaries,
                                             broadcast_transactions, crashed,
                                             num_crashes, phase, v, last_epoch,
                                             last_leader, history, candidate,
                                             delivered, restart, followers,
                                             selected_history, new_epoch,
                                             counter, proposed, proposal_acks,
                                             confirmed_epoch, confirmed_leader,
                                             latest_epoch >>

LeaderSetupNewFollower(self) == GetNewCepochMessage(self)

GetAckNewLeaderMessage(self) == /\ pc[self] = "GetAckNewLeaderMessage"
                                /\ Assert(\E m \in ReceivableMessages(self, messages) : m.type = ACK_LD,
                                          "Failure of assertion at line 494, column 9.")
                                /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_LD}:
                                     IF m.epoch = new_epoch[self]
                                        THEN /\ Assert(CanRecvFrom(self, m.from, messages),
                                                       "Failure of assertion at line 201, column 5 of macro called at line 497, column 17.")
                                             /\ messages' = Send((m.from), (CommitLeaderMessage(self, new_epoch[self])), Recv(self, m.from, messages)[2])
                                             /\ followers' = [followers EXCEPT ![self] = followers[self] \union {m.from.server}]
                                        ELSE /\ Assert(CanRecvFrom(self, m.from, messages),
                                                       "Failure of assertion at line 222, column 5 of macro called at line 500, column 17.")
                                             /\ messages' = Recv(self, m.from, messages)[2]
                                             /\ UNCHANGED followers
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << message, primaries,
                                                broadcast_transactions,
                                                crashed, num_crashes, phase, v,
                                                last_epoch, last_leader,
                                                history, candidate, delivered,
                                                restart, selected_history,
                                                new_epoch, counter, proposed,
                                                proposal_acks, confirmed_epoch,
                                                confirmed_leader, latest_epoch >>

LeaderAddFollowerToQuorum(self) == GetAckNewLeaderMessage(self)

DiscardAckEpochMessage(self) == /\ pc[self] = "DiscardAckEpochMessage"
                                /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_E
                                /\ \E m \in {msg \in ReceivableMessages(self, messages) : msg.type = ACK_E}:
                                     /\ Assert(CanRecvFrom(self, m.from, messages),
                                               "Failure of assertion at line 222, column 5 of macro called at line 512, column 13.")
                                     /\ messages' = Recv(self, m.from, messages)[2]
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << message, primaries,
                                                broadcast_transactions,
                                                crashed, num_crashes, phase, v,
                                                last_epoch, last_leader,
                                                history, candidate, delivered,
                                                restart, followers,
                                                selected_history, new_epoch,
                                                counter, proposed,
                                                proposal_acks, confirmed_epoch,
                                                confirmed_leader, latest_epoch >>

IgnoreAckEpoch(self) == DiscardAckEpochMessage(self)

FollowerDiscover(self) == /\ pc[self] = "FollowerDiscover"
                          /\ restart' = [restart EXCEPT ![self] = FALSE]
                          /\ phase' = [phase EXCEPT ![self] = "FP1_0"]
                          /\ pc' = [pc EXCEPT ![self] = "FollowerSynchronize"]
                          /\ UNCHANGED << messages, message, primaries,
                                          broadcast_transactions, crashed,
                                          num_crashes, stack, v, last_epoch,
                                          last_leader, history, candidate,
                                          delivered, followers,
                                          selected_history, new_epoch, counter,
                                          proposed, proposal_acks,
                                          confirmed_epoch, confirmed_leader,
                                          latest_epoch >>

FollowerSynchronize(self) == /\ pc[self] = "FollowerSynchronize"
                             /\ IF phase[self] /= "FP3_1"
                                   THEN /\ \/ /\ ~crashed[self]
                                              /\ ~crashed[self]
                                              /\ crashed' = [crashed EXCEPT ![self] = TRUE]
                                              /\ num_crashes' = num_crashes + 1
                                              /\ pc' = [pc EXCEPT ![self] = "FollowerCrashed"]
                                              /\ stack' = stack
                                           \/ /\ phase[self] = "FP1_0"
                                              /\ pc' = [pc EXCEPT ![self] = "NotifyLeader"]
                                              /\ UNCHANGED <<crashed, num_crashes, stack>>
                                           \/ /\ phase[self] = "FP1_1"
                                              /\ \E m \in ReceivableMessages(self, messages) : m.type = NEWEPOCH /\ m.from = LeaderProc(candidate[self])
                                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP1_1",
                                                                                       pc        |->  "FollowerSynchronize" ] >>
                                                                                   \o stack[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "HandleAckEpochMessage"]
                                              /\ UNCHANGED <<crashed, num_crashes>>
                                           \/ /\ phase[self] = "FP2_0"
                                              /\ \E m \in ReceivableMessages(self, messages) : m.type = NEWLEADER
                                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP2_0",
                                                                                       pc        |->  "FollowerSynchronize" ] >>
                                                                                   \o stack[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "HandleNewLeaderMessage"]
                                              /\ UNCHANGED <<crashed, num_crashes>>
                                           \/ /\ phase[self] = "FP2_1"
                                              /\ \E m \in ReceivableMessages(self, messages) : m.type = COMMIT_LD
                                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP2_1",
                                                                                       pc        |->  "FollowerSynchronize" ] >>
                                                                                   \o stack[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "GetCommitLDMessage"]
                                              /\ UNCHANGED <<crashed, num_crashes>>
                                           \/ /\ phase[self] = "FP3_0"
                                              /\ pc' = [pc EXCEPT ![self] = "SetReady"]
                                              /\ UNCHANGED <<crashed, num_crashes, stack>>
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "FollowerBroadcast"]
                                        /\ UNCHANGED << crashed, num_crashes,
                                                        stack >>
                             /\ UNCHANGED << messages, message, primaries,
                                             broadcast_transactions, phase, v,
                                             last_epoch, last_leader, history,
                                             candidate, delivered, restart,
                                             followers, selected_history,
                                             new_epoch, counter, proposed,
                                             proposal_acks, confirmed_epoch,
                                             confirmed_leader, latest_epoch >>

NotifyLeader(self) == /\ pc[self] = "NotifyLeader"
                      /\ candidate' = [candidate EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                      /\ messages' = Send((LeaderProc(candidate'[self])), (CepochMessage(self, last_epoch[self])), messages)
                      /\ phase' = [phase EXCEPT ![self] = "FP1_1"]
                      /\ pc' = [pc EXCEPT ![self] = "FollowerSynchronize"]
                      /\ UNCHANGED << message, primaries,
                                      broadcast_transactions, crashed,
                                      num_crashes, stack, v, last_epoch,
                                      last_leader, history, delivered, restart,
                                      followers, selected_history, new_epoch,
                                      counter, proposed, proposal_acks,
                                      confirmed_epoch, confirmed_leader,
                                      latest_epoch >>

SetReady(self) == /\ pc[self] = "SetReady"
                  /\ IF candidate[self] = self.server
                        THEN /\ primaries' = [primaries EXCEPT ![last_epoch[self]] = primaries[last_epoch[self]] \union {self.server}]
                        ELSE /\ TRUE
                             /\ UNCHANGED primaries
                  /\ phase' = [phase EXCEPT ![self] = "FP3_1"]
                  /\ pc' = [pc EXCEPT ![self] = "FollowerSynchronize"]
                  /\ UNCHANGED << messages, message, broadcast_transactions,
                                  crashed, num_crashes, stack, v, last_epoch,
                                  last_leader, history, candidate, delivered,
                                  restart, followers, selected_history,
                                  new_epoch, counter, proposed, proposal_acks,
                                  confirmed_epoch, confirmed_leader,
                                  latest_epoch >>

FollowerBroadcast(self) == /\ pc[self] = "FollowerBroadcast"
                           /\ \/ /\ ~crashed[self]
                                 /\ ~crashed[self]
                                 /\ crashed' = [crashed EXCEPT ![self] = TRUE]
                                 /\ num_crashes' = num_crashes + 1
                                 /\ pc' = [pc EXCEPT ![self] = "FollowerCrashed"]
                                 /\ stack' = stack
                              \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = PROPOSE /\ m.from = LeaderProc(candidate[self])
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FollowerBroadcastAccept",
                                                                          pc        |->  "FollowerBroadcastAcceptCheckRestart" ] >>
                                                                      \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "GetProposalMessage"]
                                 /\ UNCHANGED <<crashed, num_crashes>>
                              \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = COMMIT /\ m.from = LeaderProc(candidate[self])
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FollowerBroadcastCommit",
                                                                          pc        |->  "FollowerBroadcastCommitCheckRestart" ] >>
                                                                      \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "GetCommitMessage"]
                                 /\ UNCHANGED <<crashed, num_crashes>>
                           /\ UNCHANGED << messages, message, primaries,
                                           broadcast_transactions, phase, v,
                                           last_epoch, last_leader, history,
                                           candidate, delivered, restart,
                                           followers, selected_history,
                                           new_epoch, counter, proposed,
                                           proposal_acks, confirmed_epoch,
                                           confirmed_leader, latest_epoch >>

FollowerBroadcastAcceptCheckRestart(self) == /\ pc[self] = "FollowerBroadcastAcceptCheckRestart"
                                             /\ IF restart[self]
                                                   THEN /\ IF crashed[self]
                                                              THEN /\ pc' = [pc EXCEPT ![self] = "FollowerCrashed"]
                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "FollowerDiscover"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "FollowerBroadcast"]
                                             /\ UNCHANGED << messages, message,
                                                             primaries,
                                                             broadcast_transactions,
                                                             crashed,
                                                             num_crashes,
                                                             phase, stack, v,
                                                             last_epoch,
                                                             last_leader,
                                                             history,
                                                             candidate,
                                                             delivered,
                                                             restart,
                                                             followers,
                                                             selected_history,
                                                             new_epoch,
                                                             counter, proposed,
                                                             proposal_acks,
                                                             confirmed_epoch,
                                                             confirmed_leader,
                                                             latest_epoch >>

FollowerBroadcastCommitCheckRestart(self) == /\ pc[self] = "FollowerBroadcastCommitCheckRestart"
                                             /\ IF restart[self]
                                                   THEN /\ IF crashed[self]
                                                              THEN /\ pc' = [pc EXCEPT ![self] = "FollowerCrashed"]
                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "FollowerDiscover"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "FollowerBroadcast"]
                                             /\ UNCHANGED << messages, message,
                                                             primaries,
                                                             broadcast_transactions,
                                                             crashed,
                                                             num_crashes,
                                                             phase, stack, v,
                                                             last_epoch,
                                                             last_leader,
                                                             history,
                                                             candidate,
                                                             delivered,
                                                             restart,
                                                             followers,
                                                             selected_history,
                                                             new_epoch,
                                                             counter, proposed,
                                                             proposal_acks,
                                                             confirmed_epoch,
                                                             confirmed_leader,
                                                             latest_epoch >>

FollowerCrashed(self) == /\ pc[self] = "FollowerCrashed"
                         /\ crashed[self]
                         /\ crashed[self]
                         /\ crashed' = [crashed EXCEPT ![self] = FALSE]
                         /\ messages' = [messages EXCEPT ![self] = [sender \in Processes |-> <<>>]]
                         /\ pc' = [pc EXCEPT ![self] = "FollowerDiscover"]
                         /\ UNCHANGED << message, primaries,
                                         broadcast_transactions, num_crashes,
                                         phase, stack, v, last_epoch,
                                         last_leader, history, candidate,
                                         delivered, restart, followers,
                                         selected_history, new_epoch, counter,
                                         proposed, proposal_acks,
                                         confirmed_epoch, confirmed_leader,
                                         latest_epoch >>

follower(self) == FollowerDiscover(self) \/ FollowerSynchronize(self)
                     \/ NotifyLeader(self) \/ SetReady(self)
                     \/ FollowerBroadcast(self)
                     \/ FollowerBroadcastAcceptCheckRestart(self)
                     \/ FollowerBroadcastCommitCheckRestart(self)
                     \/ FollowerCrashed(self)

LeaderStart(self) == /\ pc[self] = "LeaderStart"
                     /\ phase' = [phase EXCEPT ![self] = "LP1_0"]
                     /\ followers' = [followers EXCEPT ![self] = {}]
                     /\ confirmed_epoch' = [confirmed_epoch EXCEPT ![self] = {}]
                     /\ confirmed_leader' = [confirmed_leader EXCEPT ![self] = {}]
                     /\ latest_epoch' = [latest_epoch EXCEPT ![self] = 0]
                     /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> 0, history |-> <<>>]]
                     /\ pc' = [pc EXCEPT ![self] = "LeaderSynchronize"]
                     /\ UNCHANGED << messages, message, primaries,
                                     broadcast_transactions, crashed,
                                     num_crashes, stack, v, last_epoch,
                                     last_leader, history, candidate,
                                     delivered, restart, new_epoch, counter,
                                     proposed, proposal_acks >>

LeaderSynchronize(self) == /\ pc[self] = "LeaderSynchronize"
                           /\ IF phase[self] /= "LP3_0"
                                 THEN /\ \/ /\ ~crashed[self]
                                            /\ ~crashed[self]
                                            /\ crashed' = [crashed EXCEPT ![self] = TRUE]
                                            /\ num_crashes' = num_crashes + 1
                                            /\ pc' = [pc EXCEPT ![self] = "LeaderCrashed"]
                                            /\ UNCHANGED <<messages, phase, stack>>
                                         \/ /\ phase[self] = "LP1_0"
                                            /\ LeaderOracle(last_epoch[self] + 1) = self.server
                                            /\ \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP1_0",
                                                                                     pc        |->  "LeaderSynchronize" ] >>
                                                                                 \o stack[self]]
                                            /\ pc' = [pc EXCEPT ![self] = "GatherQuorum"]
                                            /\ UNCHANGED <<messages, crashed, num_crashes, phase>>
                                         \/ /\ phase[self] = "LP1_1"
                                            /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_E
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP1_1",
                                                                                     pc        |->  "LeaderSynchronize" ] >>
                                                                                 \o stack[self]]
                                            /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                                            /\ UNCHANGED <<messages, crashed, num_crashes, phase>>
                                         \/ /\ phase[self] = "LP2_0"
                                            /\ Assert(IsQuorum(followers[self], Servers),
                                                      "Failure of assertion at line 643, column 17.")
                                            /\ messages' = SendToSet(({FollowerProc(f) : f \in followers[self]}), (NewLeaderMessage(self, new_epoch[self], selected_history[self].history)), messages)
                                            /\ phase' = [phase EXCEPT ![self] = "LP2_1"]
                                            /\ pc' = [pc EXCEPT ![self] = "LeaderSynchronize"]
                                            /\ UNCHANGED <<crashed, num_crashes, stack>>
                                         \/ /\ phase[self] = "LP2_1"
                                            /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP2_1",
                                                                                     pc        |->  "LeaderSynchronize" ] >>
                                                                                 \o stack[self]]
                                            /\ pc' = [pc EXCEPT ![self] = "AwaitCommit"]
                                            /\ UNCHANGED <<messages, crashed, num_crashes, phase>>
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "LeaderBroadcast"]
                                      /\ UNCHANGED << messages, crashed,
                                                      num_crashes, phase,
                                                      stack >>
                           /\ UNCHANGED << message, primaries,
                                           broadcast_transactions, v,
                                           last_epoch, last_leader, history,
                                           candidate, delivered, restart,
                                           followers, selected_history,
                                           new_epoch, counter, proposed,
                                           proposal_acks, confirmed_epoch,
                                           confirmed_leader, latest_epoch >>

LeaderBroadcast(self) == /\ pc[self] = "LeaderBroadcast"
                         /\ \/ /\ ~crashed[self]
                               /\ ~crashed[self]
                               /\ crashed' = [crashed EXCEPT ![self] = TRUE]
                               /\ num_crashes' = num_crashes + 1
                               /\ pc' = [pc EXCEPT ![self] = "LeaderCrashed"]
                               /\ UNCHANGED <<stack, v>>
                            \/ /\ \E val \in Values:
                                    /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderPropose",
                                                                                pc        |->  "LeaderBroadcast",
                                                                                v         |->  v[self] ] >>
                                                                            \o stack[self]]
                                       /\ v' = [v EXCEPT ![self] = val]
                                    /\ pc' = [pc EXCEPT ![self] = "SendProposal"]
                               /\ UNCHANGED <<crashed, num_crashes>>
                            \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_P
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderCommit",
                                                                        pc        |->  "LeaderBroadcast" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "AwaitAckProposal"]
                               /\ UNCHANGED <<crashed, num_crashes, v>>
                            \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = CEPOCH
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderSetupNewFollower",
                                                                        pc        |->  "LeaderBroadcast" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "GetNewCepochMessage"]
                               /\ UNCHANGED <<crashed, num_crashes, v>>
                            \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_LD
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderAddFollowerToQuorum",
                                                                        pc        |->  "LeaderBroadcast" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "GetAckNewLeaderMessage"]
                               /\ UNCHANGED <<crashed, num_crashes, v>>
                            \/ /\ \E m \in ReceivableMessages(self, messages) : m.type = ACK_E
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "IgnoreAckEpoch",
                                                                        pc        |->  "LeaderBroadcast" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "DiscardAckEpochMessage"]
                               /\ UNCHANGED <<crashed, num_crashes, v>>
                         /\ UNCHANGED << messages, message, primaries,
                                         broadcast_transactions, phase,
                                         last_epoch, last_leader, history,
                                         candidate, delivered, restart,
                                         followers, selected_history,
                                         new_epoch, counter, proposed,
                                         proposal_acks, confirmed_epoch,
                                         confirmed_leader, latest_epoch >>

LeaderCrashed(self) == /\ pc[self] = "LeaderCrashed"
                       /\ Assert(crashed[self],
                                 "Failure of assertion at line 680, column 9.")
                       /\ crashed[self]
                       /\ crashed' = [crashed EXCEPT ![self] = FALSE]
                       /\ messages' = [messages EXCEPT ![self] = [sender \in Processes |-> <<>>]]
                       /\ pc' = [pc EXCEPT ![self] = "LeaderStart"]
                       /\ UNCHANGED << message, primaries,
                                       broadcast_transactions, num_crashes,
                                       phase, stack, v, last_epoch,
                                       last_leader, history, candidate,
                                       delivered, restart, followers,
                                       selected_history, new_epoch, counter,
                                       proposed, proposal_acks,
                                       confirmed_epoch, confirmed_leader,
                                       latest_epoch >>

leader(self) == LeaderStart(self) \/ LeaderSynchronize(self)
                   \/ LeaderBroadcast(self) \/ LeaderCrashed(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ FP1_1(self) \/ LP1_0(self) \/ LP1_1(self)
                               \/ FP2_0(self) \/ FP2_1(self) \/ LP2_1(self)
                               \/ FollowerBroadcastAccept(self)
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



\* Type checker constraints
MessageLenConstraint == \A proc \in DOMAIN messages: \A sender \in DOMAIN messages[proc] : Len(messages[proc][sender]) <= MAX_MESSAGES
EpochConstraint == \A proc \in DOMAIN new_epoch : new_epoch[proc] <= MAX_EPOCHS
CounterConstraint == \A proc \in DOMAIN counter : counter[proc] <= MAX_COUNTER
NumCrashesConstraint == num_crashes <= MAX_NUM_CRASHES


====
