---- MODULE zab_pluscal ----

EXTENDS Sequences, Integers, TLC, FiniteSets


\* Set of server IDs
CONSTANTS Servers

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

\* Represents messages sent from one server to another
\* Maps from the destination server to the message in the format <<from, type, contents>>
variable messages = [s \in Servers |-> <<>>]

define
    \*** Data Structures:
    Zxid(epoch, counter) == [epoch |-> epoch, counter |-> counter]

    ZxidGreaterThan(left, right) == \/ left.epoch > right.epoch
                                    \/ /\ left.epoch = right.epoch
                                       /\ left.counter > right.counter

    Transaction(value, zxid) == [value |-> value, zxid |-> zxid]

    \*** Types:
    Epochs == 0..MAX_EPOCHS
    Counters == 0..MAX_COUNTER
    Zxids == {Zxid(epoch, counter) : epoch \in Epochs, counter \in Counters}
    Transactions == {Transaction(value, zxid) : value \in Values, zxid \in Zxids}
    Histories == [1..MAX_HISTORY_LENGTH -> Transactions]

    \*** Helper operators for the Zab message queue, written in TLA+ for potential extraction to a new module

    \* returns a tuple of <<message, messages>> where messages is the updated messages structure without the received message
    Send(to, m, _messages) == [_messages EXCEPT ![to] = Append(_messages[to], m)]

    \* returns a tuple of <<message, messages>> where messages is the updated messages structure without the received message
    Recv(server, _messages) == <<Head(_messages[server]), [_messages EXCEPT ![server] = Tail(_messages[server])]>>

    CanRecv(server, _messages) == Len(_messages[server]) > 0

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
    CepochMessageType == [from : Servers, type : {CEPOCH}, last_epoch : Epochs]
    NewEpochMessageType == [from : Servers, type : {NEWEPOCH}, epoch : Epochs]
    AckEpochMessageType == [from : Servers, type : {ACK_E}, last_leader : Epochs, history : Histories]
    NewLeaderMessageType == [from : Servers, type : {NEWLEADER}, epoch : Epochs, initial_history : Histories]
    AckLeaderMessageType == [from : Servers, type : {ACK_LD}, epoch : Epochs]
    CommitLeaderMessageType == [from : Servers, type : {COMMIT_LD}, epoch : Epochs]
    ProposalMessageType == [from : Servers, type : {PROPOSE}, epoch : Epochs, transaction : Transactions]
    AckProposalMessageType == [from : Servers, type : {ACK_P}, epoch : Epochs, transaction : Transactions]
    CommitProposalMessageType == [from : Servers, type : {COMMIT}, epoch : Epochs, transaction : Transactions]

    MessageType == UNION {
            CepochMessageType,
            NewEpochMessageType,
            AckEpochMessageType,
            NewLeaderMessageType,
            AckLeaderMessageType,
            CommitLeaderMessageType,
            ProposalMessageType,
            AckProposalMessageType,
            CommitProposalMessageType
    }


    \*** Other Helpers

    IsQuorum(subset, set) == 2 * Cardinality(subset) > Cardinality(set)

    Max(a, b) == IF b > a THEN b ELSE a

    Range(seq) == {seq[i] : i \in DOMAIN seq}

    Last(seq) == seq[Len(seq)]


    \*** Phase 0: Leader oracle

    \* TODO: does the oracle only produce a single result for each epoch? How should the leader oracle best be represented?
    \* TODO: should we include a refinement that chooses the server with the latest zxid (as used in the zookeeper implemenation)?
    LeaderOracle(epoch) == CHOOSE s \in Servers : TRUE


    \* Type invariant checks
    TypeOK == messages \in [Servers -> UNION {[1..m -> MessageType] : m \in 0..MAX_MESSAGES}]

end define;

\* Wraps the Send() operator to update the messages structure
macro DoSend(to, m)
begin
    messages := Send(to, m, messages);
end macro;

\* Wraps the Recv() operator to set the message variable to the next message and update the messages structure
macro DoRecv()
begin
    assert CanRecv(self[1], messages);
    \* TODO: is there a more elegant way to get the next value from a sequence while removing it?
    message := Recv(self[1], messages)[1] || messages := Recv(self[1], messages)[2];
end macro;

\* Follower Phase 1: Discovery
procedure FP1()
variable message
begin
    Notify:
        DoSend(candidate, CepochMessage(self[1], last_epoch));
    GetAckEpochMessage:
        await CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = NEWEPOCH /\ Head(messages[self[1]]).from = candidate;
        DoRecv();
    HandleAckEpochMessage:
        if last_epoch < message.epoch then
            last_epoch := message.epoch;
            DoSend(candidate, AckEpochMessage(self[1], last_leader, history));
        else
            \* TODO: under what conditions should we not check for the next message, e.g. restart leader election?
            goto GetAckEpochMessage;
        end if;
    End:
        return;
end procedure;

\* Leader Phase 1: Discovery
procedure LP1()
variables confirmed = {},
          message,
          i = 0;
begin
    GatherQuorum:
        while ~IsQuorum(Range(followers), Servers) do
            GetCepochMessage:
                await CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = CEPOCH;
                DoRecv();
            HandleCepochMessage:
                \* TODO: under what conditions should we not check for the next message, e.g. restart leader election?
                \* latest epoch seen by followers in quorum
                new_epoch := Max(new_epoch, message.last_epoch);
                if message.from \notin Range(followers) then
                    followers := Append(followers, message.from);
                end if;
        end while;

        assert IsQuorum(Range(followers), Servers);
        i := 1;
    NewEpoch:
        while i <= Len(followers) do
            DoSend(followers[i], NewEpochMessage(self[1], new_epoch));
            i := i+1;
        end while;
    HistorySelection:
        while confirmed /= Range(followers) do
            GetAck:
                await CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = ACK_E;
                DoRecv();
            HandleAck:
                confirmed := confirmed \union {message.from};

                if  \/ message.last_leader > selected_history.last_leader
                    \/  /\ message.last_leader = selected_history.last_leader
                        /\ ZxidGreaterThan(Last(message.history).zxid, Last(selected_history.history).zxid) then
                    selected_history := [last_leader |-> message.last_leader, history |-> message.history];
                end if;
        end while;

    End:
        return;
end procedure;

\* Follower Phase 2: Synchronization
procedure FP2()
begin
    GetNewLeaderMessage:
        await CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = NEWLEADER;
        DoRecv();
    HandleNewLeaderMessage:
        if last_epoch = message.epoch then
            last_leader := message.epoch;
            \* TODO: do we need to separately accept each value, zxid pair? Or can we just set the history
            history := message.inital_history;
            DoSend(candidate, AckLeaderMessage(self[1], message.epoch))
        else
            \* should start the protocol over again if the last acknowledged epoch proposal is different than the specified epoch
            \* TODO: how should we structure the spec to be able to jump back to the beginning of the process?
            restart := TRUE;
            goto End;
        end if;
    GetCommitMessage:
        await CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = COMMIT_LD;
        DoRecv();
    HandleCommitMessage:
        \* TODO: should delivered be a tuple since the transactions in a history should be delivered in-order?
        delivered := delivered \union {history};
    End:
        return;
end procedure;

\* Leader Phase 2: Synchronization
procedure LP2()
variables confirmed = {};   \* followers that have ack'd the new leader message
begin
    LP2Start:
        assert IsQuorum(Range(followers), Servers);
        i := 1;
    NewLeader:
        while i <= Len(followers) do
            DoSend(followers[i], NewLeaderMessage(self[1], new_epoch, selected_history));
            i := i+1;
        end while;
    AwaitCommit:
        while ~IsQuorum(confirmed, Servers) do
            GetAck:
                await CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = ACK_LD;
                DoRecv();
            HandleAck:
                confirmed := confirmed \union {message.from};
        end while;
        i := 1;
    SendCommit:
        while i <= Len(followers) do
            DoSend(followers[i], CommitLeaderMessage(self[1], new_epoch));
            i := i+1;
        end while;
    End:
        return;
end procedure;

\* Follower Phase 3: Broadcast
procedure FollowerBroadcastAccept()
begin
    GetProposalMessage:
        await   /\ CanRecv(self[1], messages)
                /\ Head(messages[self[1]]).type = PROPOSE
                /\ Head(messages[self[1]]).from = candidate;
        DoRecv();

    HandleProposal:
        \* TODO: should we do epoch and zxid checks before appending?
        history := Append(history, message.transaction);

        DoSend(candidate, AckProposalMessage(self[1], message.epoch, message.Transaction));

        return;
end procedure;

procedure FollowerBroadcastCommit()
begin
    GetCommitMessage:
        await   /\ CanRecv(self[1], messages)
                /\ Head(messages[self[1]]).type = COMMIT
                /\ Head(messages[self[1]]).from = candidate;
        DoRecv();

    HandleCommit:
        \* TODO: if all previous transactions have not been delivered yet, should we discard the COMMIT message or try to save it for later?
        \* Only deliver if all previous transactions in the history have been delivered as per zxid
        if \A trans \in history : ZxidGreaterThan(message.transaction.zxid, trans.zxid) => trans \in delivered then
            delivered := delivered \union {message.transaction};
        end if;

        return;
end procedure;

\* Leader Phase 3: Broadcast
procedure LeaderPropose(v)
begin
    LeaderProposeStart:
        assert IsQuorum(Range(followers), Servers);
        i := 1;
    SendProposal:
        while i <= Len(followers) do
            DoSend(followers[i], ProposalMessage(self[1], new_epoch, Transaction(v, Zxid(new_epoch, counter))));
            i := i+1;
        end while;
        proposed := Append(proposed, Transaction(v, Zxid(new_epoch, counter)));
        counter := counter + 1;

        return;
end procedure;

procedure LeaderCommit()
begin
    GetProposeAckMessage:
        await   /\ CanRecv(self[1], messages)
                /\ Head(messages[self[1]]).type = ACK_P;
        DoRecv();
    HandleProposalAck:
        proposal_acks[message.transaction, message.epoch] := proposal_acks[message.transaction, message.epoch] \union {message.from};
    CheckQuorumAckd:
        \* TODO: should probably only send commit message once
        if IsQuorum(proposal_acks[message.transaction, message.epoch], Servers) then
            i := 1;
            SendCommit:
                \* Send to all followers, not just those that have ackd
                while i <= Len(followers) do
                    DoSend(followers[i], ProposalMessage(self[1], new_epoch, Transaction(v, Zxid(new_epoch, counter))));
                    i := i+1;
                end while;
        end if;

    End:
        return;
end procedure;

procedure LeaderSetupNewFollower()
begin
    GetCepochMessage:
        await   /\ CanRecv(self[1], messages)
                /\ Head(messages[self[1]]).type = CEPOCH;
        DoRecv();
    HandleCepochMessage:
        if message.epoch < new_epoch then
            SendNewEpoch:
                DoSend(message.from, NewEpochMessage(self[1], new_epoch));
            SendNewLeader:
                DoSend(message.from, NewLeaderMessage(self[1], new_epoch, selected_history.history \o proposed));
        else
            \* TODO: what to do if the epoch in the CEPOCH message is greater than the current epoch? Restart the discovery process?
            skip;
        end if;

    End:
        return;
end procedure;

procedure LeaderAddFollowerToQuorum()
begin
    GetAckNewLeaderMessage:
        await   /\ CanRecv(self[1], messages)
                /\ Head(messages[self[1]]).type = ACK_LD;
        DoRecv();
    HandleAckLeader:
        if message.epoch = new_epoch then
            DoSend(message.from, CommitLeaderMessage(self[1], new_epoch));
            \* TODO: can we make followers a set?
            followers := Append(followers, message.from);
        end if;

    return;
end procedure;

\* Models follower thread for each process
process follower_tuple \in Servers \X {0}
variables last_epoch = 0,       \* Last new epoch proposol acknowledged
          last_leader = 0,      \* Last new leader proposal acknowledged
          history = <<>>,              \* In-order record of all the accepted value proposals
          \* TODO: do we really need to track zxid, or can we just use history?
          zxid = Zxid(0, 0),    \* Zookeeper transaction ID (zxid) of last accepted transaction in the history
          candidate,            \* Candidate selected by leader oracle
          delivered = {},       \* Tracks the transactions that have been delivered to the application by Zab
          \* TODO: how should we structure the spec to be able to jump back to the beginning of the process? Right now we use a flag
          restart = FALSE,
          \* TODO: should we instead store a history of when ready was called to ensure that it's only called at most once per epoch?
          ready = FALSE;        \* Tracks that ready was invoked by the follower (should only be done by one follower per epoch)
begin
    \* TODO: need to run multiple iterations, should include a loop
    GetCandidate:
        candidate := LeaderOracle(last_epoch + 1);

    FollowerDiscover:
        call FP1();

    FollowerSynchronize:
        call FP2();
    FollowerSynchronizeCheckRestart:
        if restart then
            goto End;
        end if;

    SetReady:
        if candidate = self[1] then
            ready := TRUE;
        end if;

    FollowerBroadcast:
        while TRUE do
            FollowerBroadcastStep:
                either
                    call FollowerBroadcastAccept();
                or
                    call FollowerBroadcastCommit();
                end either;
        end while;

    End:
        skip;
end process;

\* Models leader thread for each process
process leader_tuple \in Servers \X {1}
variables leader_candidate,            \* Candidate selected by leader oracle
          \* TODO: we use a sequence since we need to be able to run the macro DoSend() for each element in it, and I don't know how to do that using sets
          followers = <<>>,     \* tracks the followers committed to a leader
          selected_history = [last_leader |-> 0, history |-> <<>>],     \* tracks the selected initial history
          new_epoch = 0,
          counter = 0,          \* Incremented for each proposal, used to generate monotonically increasing zxid
          proposed = <<>>,        \* Tracks the transactions proposed by the leader for the current epoch
          proposal_acks = [t \in Transactions, e \in Epochs |-> {}];   \* Tracks acks for proposed transactions
begin
    \* TODO: need to run multiple iterations, should include a loop
    GetCandidate:
        leader_candidate := LeaderOracle(last_epoch + 1);

    if leader_candidate = self[1] then
        LeaderDiscover:
            call LP1();

        LeaderSynchronize:
            call LP2();

        LeaderBroadcast:
            while TRUE do
                LeaderBroadcastStep:
                    either
                        with val \in Values do
                            call LeaderPropose(val);
                        end with;
                    or
                        call LeaderCommit();
                    or
                        call LeaderSetupNewFollower();
                    or
                        call LeaderAddFollowerToQuorum();
                    end either
            end while;
    end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2e3fcefa" /\ chksum(tla) = "d5f9de7d")
\* Label End of procedure FP1 at line 149 col 9 changed to End_
\* Label GetCepochMessage of procedure LP1 at line 161 col 17 changed to GetCepochMessage_
\* Label HandleCepochMessage of procedure LP1 at line 166 col 17 changed to HandleCepochMessage_
\* Label GetAck of procedure LP1 at line 182 col 17 changed to GetAck_
\* Label HandleAck of procedure LP1 at line 185 col 17 changed to HandleAck_
\* Label End of procedure LP1 at line 195 col 9 changed to End_L
\* Label GetCommitMessage of procedure FP2 at line 217 col 9 changed to GetCommitMessage_
\* Label End of procedure FP2 at line 223 col 9 changed to End_F
\* Label SendCommit of procedure LP2 at line 248 col 9 changed to SendCommit_
\* Label End of procedure LP2 at line 253 col 9 changed to End_LP
\* Label End of procedure LeaderCommit at line 330 col 9 changed to End_Le
\* Label End of procedure LeaderSetupNewFollower at line 351 col 9 changed to End_Lea
\* Label GetCandidate of process follower_tuple at line 386 col 9 changed to GetCandidate_
\* Procedure variable message of procedure FP1 at line 133 col 10 changed to message_
\* Procedure variable confirmed of procedure LP1 at line 154 col 11 changed to confirmed_
CONSTANT defaultInitValue
VARIABLES messages, pc, stack

(* define statement *)
Zxid(epoch, counter) == [epoch |-> epoch, counter |-> counter]

ZxidGreaterThan(left, right) == \/ left.epoch > right.epoch
                                \/ /\ left.epoch = right.epoch
                                   /\ left.counter > right.counter

Transaction(value, zxid) == [value |-> value, zxid |-> zxid]


Epochs == 0..MAX_EPOCHS
Counters == 0..MAX_COUNTER
Zxids == {Zxid(epoch, counter) : epoch \in Epochs, counter \in Counters}
Transactions == {Transaction(value, zxid) : value \in Values, zxid \in Zxids}
Histories == [1..MAX_HISTORY_LENGTH -> Transactions]




Send(to, m, _messages) == [_messages EXCEPT ![to] = Append(_messages[to], m)]


Recv(server, _messages) == <<Head(_messages[server]), [_messages EXCEPT ![server] = Tail(_messages[server])]>>

CanRecv(server, _messages) == Len(_messages[server]) > 0


CepochMessage(from, last_epoch) == [from |-> from, type |-> CEPOCH, last_epoch |-> last_epoch]
NewEpochMessage(from, epoch) == [from |-> from, type |-> NEWEPOCH, epoch |-> epoch]
AckEpochMessage(from, last_leader, history) == [from |-> from, type |-> ACK_E, last_leader |-> last_leader, history |-> history]
NewLeaderMessage(from, epoch, initial_history) == [from |-> from, type |-> NEWLEADER, epoch |-> epoch, initial_history |-> initial_history]
AckLeaderMessage(from, epoch) == [from |-> from, type |-> ACK_LD, epoch |-> epoch]
CommitLeaderMessage(from, epoch) == [from |-> from, type |-> COMMIT_LD, epoch |-> epoch]
ProposalMessage(from, epoch, transaction) == [from |-> from, type |-> PROPOSE, epoch |-> epoch, transaction |-> transaction]
AckProposalMessage(from, epoch, transaction) == [from |-> from, type |-> ACK_P, epoch |-> epoch, transaction |-> transaction]
CommitProposalMessage(from, epoch, transaction) == [from |-> from, type |-> COMMIT, epoch |-> epoch, transaction |-> transaction]


CepochMessageType == [from : Servers, type : {CEPOCH}, last_epoch : Epochs]
NewEpochMessageType == [from : Servers, type : {NEWEPOCH}, epoch : Epochs]
AckEpochMessageType == [from : Servers, type : {ACK_E}, last_leader : Epochs, history : Histories]
NewLeaderMessageType == [from : Servers, type : {NEWLEADER}, epoch : Epochs, initial_history : Histories]
AckLeaderMessageType == [from : Servers, type : {ACK_LD}, epoch : Epochs]
CommitLeaderMessageType == [from : Servers, type : {COMMIT_LD}, epoch : Epochs]
ProposalMessageType == [from : Servers, type : {PROPOSE}, epoch : Epochs, transaction : Transactions]
AckProposalMessageType == [from : Servers, type : {ACK_P}, epoch : Epochs, transaction : Transactions]
CommitProposalMessageType == [from : Servers, type : {COMMIT}, epoch : Epochs, transaction : Transactions]

MessageType == UNION {
        CepochMessageType,
        NewEpochMessageType,
        AckEpochMessageType,
        NewLeaderMessageType,
        AckLeaderMessageType,
        CommitLeaderMessageType,
        ProposalMessageType,
        AckProposalMessageType,
        CommitProposalMessageType
}




IsQuorum(subset, set) == 2 * Cardinality(subset) > Cardinality(set)

Max(a, b) == IF b > a THEN b ELSE a

Range(seq) == {seq[i] : i \in DOMAIN seq}

Last(seq) == seq[Len(seq)]






LeaderOracle(epoch) == CHOOSE s \in Servers : TRUE



TypeOK == messages \in [Servers -> UNION {[1..m -> MessageType] : m \in 0..MAX_MESSAGES}]

VARIABLES message_, confirmed_, message, i, confirmed, v, last_epoch,
          last_leader, history, zxid, candidate, delivered, restart, ready,
          leader_candidate, followers, selected_history, new_epoch, counter,
          proposed, proposal_acks

vars == << messages, pc, stack, message_, confirmed_, message, i, confirmed,
           v, last_epoch, last_leader, history, zxid, candidate, delivered,
           restart, ready, leader_candidate, followers, selected_history,
           new_epoch, counter, proposed, proposal_acks >>

ProcSet == (Servers \X {0}) \cup (Servers \X {1})

Init == (* Global variables *)
        /\ messages = [s \in Servers |-> <<>>]
        (* Procedure FP1 *)
        /\ message_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure LP1 *)
        /\ confirmed_ = [ self \in ProcSet |-> {}]
        /\ message = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> 0]
        (* Procedure LP2 *)
        /\ confirmed = [ self \in ProcSet |-> {}]
        (* Procedure LeaderPropose *)
        /\ v = [ self \in ProcSet |-> defaultInitValue]
        (* Process follower_tuple *)
        /\ last_epoch = [self \in Servers \X {0} |-> 0]
        /\ last_leader = [self \in Servers \X {0} |-> 0]
        /\ history = [self \in Servers \X {0} |-> <<>>]
        /\ zxid = [self \in Servers \X {0} |-> Zxid(0, 0)]
        /\ candidate = [self \in Servers \X {0} |-> defaultInitValue]
        /\ delivered = [self \in Servers \X {0} |-> {}]
        /\ restart = [self \in Servers \X {0} |-> FALSE]
        /\ ready = [self \in Servers \X {0} |-> FALSE]
        (* Process leader_tuple *)
        /\ leader_candidate = [self \in Servers \X {1} |-> defaultInitValue]
        /\ followers = [self \in Servers \X {1} |-> <<>>]
        /\ selected_history = [self \in Servers \X {1} |-> [last_leader |-> 0, history |-> <<>>]]
        /\ new_epoch = [self \in Servers \X {1} |-> 0]
        /\ counter = [self \in Servers \X {1} |-> 0]
        /\ proposed = [self \in Servers \X {1} |-> <<>>]
        /\ proposal_acks = [self \in Servers \X {1} |-> [t \in Transactions, e \in Epochs |-> {}]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Servers \X {0} -> "GetCandidate_"
                                        [] self \in Servers \X {1} -> "GetCandidate"]

Notify(self) == /\ pc[self] = "Notify"
                /\ messages' = Send(candidate[self], (CepochMessage(self[1], last_epoch[self])), messages)
                /\ pc' = [pc EXCEPT ![self] = "GetAckEpochMessage"]
                /\ UNCHANGED << stack, message_, confirmed_, message, i,
                                confirmed, v, last_epoch, last_leader, history,
                                zxid, candidate, delivered, restart, ready,
                                leader_candidate, followers, selected_history,
                                new_epoch, counter, proposed, proposal_acks >>

GetAckEpochMessage(self) == /\ pc[self] = "GetAckEpochMessage"
                            /\ CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = NEWEPOCH /\ Head(messages[self[1]]).from = candidate[self]
                            /\ Assert(CanRecv(self[1], messages),
                                      "Failure of assertion at line 126, column 5 of macro called at line 139, column 9.")
                            /\ /\ message_' = [message_ EXCEPT ![self] = Recv(self[1], messages)[1]]
                               /\ messages' = Recv(self[1], messages)[2]
                            /\ pc' = [pc EXCEPT ![self] = "HandleAckEpochMessage"]
                            /\ UNCHANGED << stack, confirmed_, message, i,
                                            confirmed, v, last_epoch,
                                            last_leader, history, zxid,
                                            candidate, delivered, restart,
                                            ready, leader_candidate, followers,
                                            selected_history, new_epoch,
                                            counter, proposed, proposal_acks >>

HandleAckEpochMessage(self) == /\ pc[self] = "HandleAckEpochMessage"
                               /\ IF last_epoch[self] < message_[self].epoch
                                     THEN /\ last_epoch' = [last_epoch EXCEPT ![self] = message_[self].epoch]
                                          /\ messages' = Send(candidate[self], (AckEpochMessage(self[1], last_leader[self], history[self])), messages)
                                          /\ pc' = [pc EXCEPT ![self] = "End_"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "GetAckEpochMessage"]
                                          /\ UNCHANGED << messages, last_epoch >>
                               /\ UNCHANGED << stack, message_, confirmed_,
                                               message, i, confirmed, v,
                                               last_leader, history, zxid,
                                               candidate, delivered, restart,
                                               ready, leader_candidate,
                                               followers, selected_history,
                                               new_epoch, counter, proposed,
                                               proposal_acks >>

End_(self) == /\ pc[self] = "End_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ message_' = [message_ EXCEPT ![self] = Head(stack[self]).message_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << messages, confirmed_, message, i, confirmed, v,
                              last_epoch, last_leader, history, zxid,
                              candidate, delivered, restart, ready,
                              leader_candidate, followers, selected_history,
                              new_epoch, counter, proposed, proposal_acks >>

FP1(self) == Notify(self) \/ GetAckEpochMessage(self)
                \/ HandleAckEpochMessage(self) \/ End_(self)

GatherQuorum(self) == /\ pc[self] = "GatherQuorum"
                      /\ IF ~IsQuorum(Range(followers[self]), Servers)
                            THEN /\ pc' = [pc EXCEPT ![self] = "GetCepochMessage_"]
                                 /\ i' = i
                            ELSE /\ Assert(IsQuorum(Range(followers[self]), Servers),
                                           "Failure of assertion at line 172, column 9.")
                                 /\ i' = [i EXCEPT ![self] = 1]
                                 /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                      /\ UNCHANGED << messages, stack, message_, confirmed_,
                                      message, confirmed, v, last_epoch,
                                      last_leader, history, zxid, candidate,
                                      delivered, restart, ready,
                                      leader_candidate, followers,
                                      selected_history, new_epoch, counter,
                                      proposed, proposal_acks >>

GetCepochMessage_(self) == /\ pc[self] = "GetCepochMessage_"
                           /\ CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = CEPOCH
                           /\ Assert(CanRecv(self[1], messages),
                                     "Failure of assertion at line 126, column 5 of macro called at line 162, column 17.")
                           /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                              /\ messages' = Recv(self[1], messages)[2]
                           /\ pc' = [pc EXCEPT ![self] = "HandleCepochMessage_"]
                           /\ UNCHANGED << stack, message_, confirmed_, i,
                                           confirmed, v, last_epoch,
                                           last_leader, history, zxid,
                                           candidate, delivered, restart,
                                           ready, leader_candidate, followers,
                                           selected_history, new_epoch,
                                           counter, proposed, proposal_acks >>

HandleCepochMessage_(self) == /\ pc[self] = "HandleCepochMessage_"
                              /\ new_epoch' = [new_epoch EXCEPT ![self] = Max(new_epoch[self], message[self].last_epoch)]
                              /\ IF message[self].from \notin Range(followers[self])
                                    THEN /\ followers' = [followers EXCEPT ![self] = Append(followers[self], message[self].from)]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED followers
                              /\ pc' = [pc EXCEPT ![self] = "GatherQuorum"]
                              /\ UNCHANGED << messages, stack, message_,
                                              confirmed_, message, i,
                                              confirmed, v, last_epoch,
                                              last_leader, history, zxid,
                                              candidate, delivered, restart,
                                              ready, leader_candidate,
                                              selected_history, counter,
                                              proposed, proposal_acks >>

NewEpoch(self) == /\ pc[self] = "NewEpoch"
                  /\ IF i[self] <= Len(followers[self])
                        THEN /\ messages' = Send((followers[self][i[self]]), (NewEpochMessage(self[1], new_epoch[self])), messages)
                             /\ i' = [i EXCEPT ![self] = i[self]+1]
                             /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                             /\ UNCHANGED << messages, i >>
                  /\ UNCHANGED << stack, message_, confirmed_, message,
                                  confirmed, v, last_epoch, last_leader,
                                  history, zxid, candidate, delivered, restart,
                                  ready, leader_candidate, followers,
                                  selected_history, new_epoch, counter,
                                  proposed, proposal_acks >>

HistorySelection(self) == /\ pc[self] = "HistorySelection"
                          /\ IF confirmed_[self] /= Range(followers[self])
                                THEN /\ pc' = [pc EXCEPT ![self] = "GetAck_"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "End_L"]
                          /\ UNCHANGED << messages, stack, message_,
                                          confirmed_, message, i, confirmed, v,
                                          last_epoch, last_leader, history,
                                          zxid, candidate, delivered, restart,
                                          ready, leader_candidate, followers,
                                          selected_history, new_epoch, counter,
                                          proposed, proposal_acks >>

GetAck_(self) == /\ pc[self] = "GetAck_"
                 /\ CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = ACK_E
                 /\ Assert(CanRecv(self[1], messages),
                           "Failure of assertion at line 126, column 5 of macro called at line 183, column 17.")
                 /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                    /\ messages' = Recv(self[1], messages)[2]
                 /\ pc' = [pc EXCEPT ![self] = "HandleAck_"]
                 /\ UNCHANGED << stack, message_, confirmed_, i, confirmed, v,
                                 last_epoch, last_leader, history, zxid,
                                 candidate, delivered, restart, ready,
                                 leader_candidate, followers, selected_history,
                                 new_epoch, counter, proposed, proposal_acks >>

HandleAck_(self) == /\ pc[self] = "HandleAck_"
                    /\ confirmed_' = [confirmed_ EXCEPT ![self] = confirmed_[self] \union {message[self].from}]
                    /\ IF \/ message[self].last_leader > selected_history[self].last_leader
                          \/  /\ message[self].last_leader = selected_history[self].last_leader
                              /\ ZxidGreaterThan(Last(message[self].history).zxid, Last(selected_history[self].history).zxid)
                          THEN /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> message[self].last_leader, history |-> message[self].history]]
                          ELSE /\ TRUE
                               /\ UNCHANGED selected_history
                    /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                    /\ UNCHANGED << messages, stack, message_, message, i,
                                    confirmed, v, last_epoch, last_leader,
                                    history, zxid, candidate, delivered,
                                    restart, ready, leader_candidate,
                                    followers, new_epoch, counter, proposed,
                                    proposal_acks >>

End_L(self) == /\ pc[self] = "End_L"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ confirmed_' = [confirmed_ EXCEPT ![self] = Head(stack[self]).confirmed_]
               /\ message' = [message EXCEPT ![self] = Head(stack[self]).message]
               /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << messages, message_, confirmed, v, last_epoch,
                               last_leader, history, zxid, candidate,
                               delivered, restart, ready, leader_candidate,
                               followers, selected_history, new_epoch, counter,
                               proposed, proposal_acks >>

LP1(self) == GatherQuorum(self) \/ GetCepochMessage_(self)
                \/ HandleCepochMessage_(self) \/ NewEpoch(self)
                \/ HistorySelection(self) \/ GetAck_(self)
                \/ HandleAck_(self) \/ End_L(self)

GetNewLeaderMessage(self) == /\ pc[self] = "GetNewLeaderMessage"
                             /\ CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = NEWLEADER
                             /\ Assert(CanRecv(self[1], messages),
                                       "Failure of assertion at line 126, column 5 of macro called at line 203, column 9.")
                             /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                                /\ messages' = Recv(self[1], messages)[2]
                             /\ pc' = [pc EXCEPT ![self] = "HandleNewLeaderMessage"]
                             /\ UNCHANGED << stack, message_, confirmed_, i,
                                             confirmed, v, last_epoch,
                                             last_leader, history, zxid,
                                             candidate, delivered, restart,
                                             ready, leader_candidate,
                                             followers, selected_history,
                                             new_epoch, counter, proposed,
                                             proposal_acks >>

HandleNewLeaderMessage(self) == /\ pc[self] = "HandleNewLeaderMessage"
                                /\ IF last_epoch[self] = message[self].epoch
                                      THEN /\ last_leader' = [last_leader EXCEPT ![self] = message[self].epoch]
                                           /\ history' = [history EXCEPT ![self] = message[self].inital_history]
                                           /\ messages' = Send(candidate[self], (AckLeaderMessage(self[1], message[self].epoch)), messages)
                                           /\ pc' = [pc EXCEPT ![self] = "GetCommitMessage_"]
                                           /\ UNCHANGED restart
                                      ELSE /\ restart' = [restart EXCEPT ![self] = TRUE]
                                           /\ pc' = [pc EXCEPT ![self] = "End_F"]
                                           /\ UNCHANGED << messages,
                                                           last_leader,
                                                           history >>
                                /\ UNCHANGED << stack, message_, confirmed_,
                                                message, i, confirmed, v,
                                                last_epoch, zxid, candidate,
                                                delivered, ready,
                                                leader_candidate, followers,
                                                selected_history, new_epoch,
                                                counter, proposed,
                                                proposal_acks >>

GetCommitMessage_(self) == /\ pc[self] = "GetCommitMessage_"
                           /\ CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = COMMIT_LD
                           /\ Assert(CanRecv(self[1], messages),
                                     "Failure of assertion at line 126, column 5 of macro called at line 218, column 9.")
                           /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                              /\ messages' = Recv(self[1], messages)[2]
                           /\ pc' = [pc EXCEPT ![self] = "HandleCommitMessage"]
                           /\ UNCHANGED << stack, message_, confirmed_, i,
                                           confirmed, v, last_epoch,
                                           last_leader, history, zxid,
                                           candidate, delivered, restart,
                                           ready, leader_candidate, followers,
                                           selected_history, new_epoch,
                                           counter, proposed, proposal_acks >>

HandleCommitMessage(self) == /\ pc[self] = "HandleCommitMessage"
                             /\ delivered' = [delivered EXCEPT ![self] = delivered[self] \union {history[self]}]
                             /\ pc' = [pc EXCEPT ![self] = "End_F"]
                             /\ UNCHANGED << messages, stack, message_,
                                             confirmed_, message, i, confirmed,
                                             v, last_epoch, last_leader,
                                             history, zxid, candidate, restart,
                                             ready, leader_candidate,
                                             followers, selected_history,
                                             new_epoch, counter, proposed,
                                             proposal_acks >>

End_F(self) == /\ pc[self] = "End_F"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << messages, message_, confirmed_, message, i,
                               confirmed, v, last_epoch, last_leader, history,
                               zxid, candidate, delivered, restart, ready,
                               leader_candidate, followers, selected_history,
                               new_epoch, counter, proposed, proposal_acks >>

FP2(self) == GetNewLeaderMessage(self) \/ HandleNewLeaderMessage(self)
                \/ GetCommitMessage_(self) \/ HandleCommitMessage(self)
                \/ End_F(self)

LP2Start(self) == /\ pc[self] = "LP2Start"
                  /\ Assert(IsQuorum(Range(followers[self]), Servers),
                            "Failure of assertion at line 231, column 9.")
                  /\ i' = [i EXCEPT ![self] = 1]
                  /\ pc' = [pc EXCEPT ![self] = "NewLeader"]
                  /\ UNCHANGED << messages, stack, message_, confirmed_,
                                  message, confirmed, v, last_epoch,
                                  last_leader, history, zxid, candidate,
                                  delivered, restart, ready, leader_candidate,
                                  followers, selected_history, new_epoch,
                                  counter, proposed, proposal_acks >>

NewLeader(self) == /\ pc[self] = "NewLeader"
                   /\ IF i[self] <= Len(followers[self])
                         THEN /\ messages' = Send((followers[self][i[self]]), (NewLeaderMessage(self[1], new_epoch[self], selected_history[self])), messages)
                              /\ i' = [i EXCEPT ![self] = i[self]+1]
                              /\ pc' = [pc EXCEPT ![self] = "NewLeader"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "AwaitCommit"]
                              /\ UNCHANGED << messages, i >>
                   /\ UNCHANGED << stack, message_, confirmed_, message,
                                   confirmed, v, last_epoch, last_leader,
                                   history, zxid, candidate, delivered,
                                   restart, ready, leader_candidate, followers,
                                   selected_history, new_epoch, counter,
                                   proposed, proposal_acks >>

AwaitCommit(self) == /\ pc[self] = "AwaitCommit"
                     /\ IF ~IsQuorum(confirmed[self], Servers)
                           THEN /\ pc' = [pc EXCEPT ![self] = "GetAck"]
                                /\ i' = i
                           ELSE /\ i' = [i EXCEPT ![self] = 1]
                                /\ pc' = [pc EXCEPT ![self] = "SendCommit_"]
                     /\ UNCHANGED << messages, stack, message_, confirmed_,
                                     message, confirmed, v, last_epoch,
                                     last_leader, history, zxid, candidate,
                                     delivered, restart, ready,
                                     leader_candidate, followers,
                                     selected_history, new_epoch, counter,
                                     proposed, proposal_acks >>

GetAck(self) == /\ pc[self] = "GetAck"
                /\ CanRecv(self[1], messages) /\ Head(messages[self[1]]).type = ACK_LD
                /\ Assert(CanRecv(self[1], messages),
                          "Failure of assertion at line 126, column 5 of macro called at line 242, column 17.")
                /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                   /\ messages' = Recv(self[1], messages)[2]
                /\ pc' = [pc EXCEPT ![self] = "HandleAck"]
                /\ UNCHANGED << stack, message_, confirmed_, i, confirmed, v,
                                last_epoch, last_leader, history, zxid,
                                candidate, delivered, restart, ready,
                                leader_candidate, followers, selected_history,
                                new_epoch, counter, proposed, proposal_acks >>

HandleAck(self) == /\ pc[self] = "HandleAck"
                   /\ confirmed' = [confirmed EXCEPT ![self] = confirmed[self] \union {message[self].from}]
                   /\ pc' = [pc EXCEPT ![self] = "AwaitCommit"]
                   /\ UNCHANGED << messages, stack, message_, confirmed_,
                                   message, i, v, last_epoch, last_leader,
                                   history, zxid, candidate, delivered,
                                   restart, ready, leader_candidate, followers,
                                   selected_history, new_epoch, counter,
                                   proposed, proposal_acks >>

SendCommit_(self) == /\ pc[self] = "SendCommit_"
                     /\ IF i[self] <= Len(followers[self])
                           THEN /\ messages' = Send((followers[self][i[self]]), (CommitLeaderMessage(self[1], new_epoch[self])), messages)
                                /\ i' = [i EXCEPT ![self] = i[self]+1]
                                /\ pc' = [pc EXCEPT ![self] = "SendCommit_"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "End_LP"]
                                /\ UNCHANGED << messages, i >>
                     /\ UNCHANGED << stack, message_, confirmed_, message,
                                     confirmed, v, last_epoch, last_leader,
                                     history, zxid, candidate, delivered,
                                     restart, ready, leader_candidate,
                                     followers, selected_history, new_epoch,
                                     counter, proposed, proposal_acks >>

End_LP(self) == /\ pc[self] = "End_LP"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ confirmed' = [confirmed EXCEPT ![self] = Head(stack[self]).confirmed]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << messages, message_, confirmed_, message, i, v,
                                last_epoch, last_leader, history, zxid,
                                candidate, delivered, restart, ready,
                                leader_candidate, followers, selected_history,
                                new_epoch, counter, proposed, proposal_acks >>

LP2(self) == LP2Start(self) \/ NewLeader(self) \/ AwaitCommit(self)
                \/ GetAck(self) \/ HandleAck(self) \/ SendCommit_(self)
                \/ End_LP(self)

GetProposalMessage(self) == /\ pc[self] = "GetProposalMessage"
                            /\ /\ CanRecv(self[1], messages)
                               /\ Head(messages[self[1]]).type = PROPOSE
                               /\ Head(messages[self[1]]).from = candidate[self]
                            /\ Assert(CanRecv(self[1], messages),
                                      "Failure of assertion at line 126, column 5 of macro called at line 263, column 9.")
                            /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                               /\ messages' = Recv(self[1], messages)[2]
                            /\ pc' = [pc EXCEPT ![self] = "HandleProposal"]
                            /\ UNCHANGED << stack, message_, confirmed_, i,
                                            confirmed, v, last_epoch,
                                            last_leader, history, zxid,
                                            candidate, delivered, restart,
                                            ready, leader_candidate, followers,
                                            selected_history, new_epoch,
                                            counter, proposed, proposal_acks >>

HandleProposal(self) == /\ pc[self] = "HandleProposal"
                        /\ history' = [history EXCEPT ![self] = Append(history[self], message[self].transaction)]
                        /\ messages' = Send(candidate[self], (AckProposalMessage(self[1], message[self].epoch, message[self].Transaction)), messages)
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << message_, confirmed_, message, i,
                                        confirmed, v, last_epoch, last_leader,
                                        zxid, candidate, delivered, restart,
                                        ready, leader_candidate, followers,
                                        selected_history, new_epoch, counter,
                                        proposed, proposal_acks >>

FollowerBroadcastAccept(self) == GetProposalMessage(self)
                                    \/ HandleProposal(self)

GetCommitMessage(self) == /\ pc[self] = "GetCommitMessage"
                          /\ /\ CanRecv(self[1], messages)
                             /\ Head(messages[self[1]]).type = COMMIT
                             /\ Head(messages[self[1]]).from = candidate[self]
                          /\ Assert(CanRecv(self[1], messages),
                                    "Failure of assertion at line 126, column 5 of macro called at line 280, column 9.")
                          /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                             /\ messages' = Recv(self[1], messages)[2]
                          /\ pc' = [pc EXCEPT ![self] = "HandleCommit"]
                          /\ UNCHANGED << stack, message_, confirmed_, i,
                                          confirmed, v, last_epoch,
                                          last_leader, history, zxid,
                                          candidate, delivered, restart, ready,
                                          leader_candidate, followers,
                                          selected_history, new_epoch, counter,
                                          proposed, proposal_acks >>

HandleCommit(self) == /\ pc[self] = "HandleCommit"
                      /\ IF \A trans \in history[self] : ZxidGreaterThan(message[self].transaction.zxid, trans.zxid) => trans \in delivered[self]
                            THEN /\ delivered' = [delivered EXCEPT ![self] = delivered[self] \union {message[self].transaction}]
                            ELSE /\ TRUE
                                 /\ UNCHANGED delivered
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << messages, message_, confirmed_, message,
                                      i, confirmed, v, last_epoch, last_leader,
                                      history, zxid, candidate, restart, ready,
                                      leader_candidate, followers,
                                      selected_history, new_epoch, counter,
                                      proposed, proposal_acks >>

FollowerBroadcastCommit(self) == GetCommitMessage(self)
                                    \/ HandleCommit(self)

LeaderProposeStart(self) == /\ pc[self] = "LeaderProposeStart"
                            /\ Assert(IsQuorum(Range(followers[self]), Servers),
                                      "Failure of assertion at line 296, column 9.")
                            /\ i' = [i EXCEPT ![self] = 1]
                            /\ pc' = [pc EXCEPT ![self] = "SendProposal"]
                            /\ UNCHANGED << messages, stack, message_,
                                            confirmed_, message, confirmed, v,
                                            last_epoch, last_leader, history,
                                            zxid, candidate, delivered,
                                            restart, ready, leader_candidate,
                                            followers, selected_history,
                                            new_epoch, counter, proposed,
                                            proposal_acks >>

SendProposal(self) == /\ pc[self] = "SendProposal"
                      /\ IF i[self] <= Len(followers[self])
                            THEN /\ messages' = Send((followers[self][i[self]]), (ProposalMessage(self[1], new_epoch[self], Transaction(v[self], Zxid(new_epoch[self], counter[self])))), messages)
                                 /\ i' = [i EXCEPT ![self] = i[self]+1]
                                 /\ pc' = [pc EXCEPT ![self] = "SendProposal"]
                                 /\ UNCHANGED << stack, v, counter, proposed >>
                            ELSE /\ proposed' = [proposed EXCEPT ![self] = Append(proposed[self], Transaction(v[self], Zxid(new_epoch[self], counter[self])))]
                                 /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ v' = [v EXCEPT ![self] = Head(stack[self]).v]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << messages, i >>
                      /\ UNCHANGED << message_, confirmed_, message, confirmed,
                                      last_epoch, last_leader, history, zxid,
                                      candidate, delivered, restart, ready,
                                      leader_candidate, followers,
                                      selected_history, new_epoch,
                                      proposal_acks >>

LeaderPropose(self) == LeaderProposeStart(self) \/ SendProposal(self)

GetProposeAckMessage(self) == /\ pc[self] = "GetProposeAckMessage"
                              /\ /\ CanRecv(self[1], messages)
                                 /\ Head(messages[self[1]]).type = ACK_P
                              /\ Assert(CanRecv(self[1], messages),
                                        "Failure of assertion at line 126, column 5 of macro called at line 314, column 9.")
                              /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                                 /\ messages' = Recv(self[1], messages)[2]
                              /\ pc' = [pc EXCEPT ![self] = "HandleProposalAck"]
                              /\ UNCHANGED << stack, message_, confirmed_, i,
                                              confirmed, v, last_epoch,
                                              last_leader, history, zxid,
                                              candidate, delivered, restart,
                                              ready, leader_candidate,
                                              followers, selected_history,
                                              new_epoch, counter, proposed,
                                              proposal_acks >>

HandleProposalAck(self) == /\ pc[self] = "HandleProposalAck"
                           /\ proposal_acks' = [proposal_acks EXCEPT ![self][message[self].transaction, message[self].epoch] = proposal_acks[self][message[self].transaction, message[self].epoch] \union {message[self].from}]
                           /\ pc' = [pc EXCEPT ![self] = "CheckQuorumAckd"]
                           /\ UNCHANGED << messages, stack, message_,
                                           confirmed_, message, i, confirmed,
                                           v, last_epoch, last_leader, history,
                                           zxid, candidate, delivered, restart,
                                           ready, leader_candidate, followers,
                                           selected_history, new_epoch,
                                           counter, proposed >>

CheckQuorumAckd(self) == /\ pc[self] = "CheckQuorumAckd"
                         /\ IF IsQuorum(proposal_acks[self][message[self].transaction, message[self].epoch], Servers)
                               THEN /\ i' = [i EXCEPT ![self] = 1]
                                    /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "End_Le"]
                                    /\ i' = i
                         /\ UNCHANGED << messages, stack, message_, confirmed_,
                                         message, confirmed, v, last_epoch,
                                         last_leader, history, zxid, candidate,
                                         delivered, restart, ready,
                                         leader_candidate, followers,
                                         selected_history, new_epoch, counter,
                                         proposed, proposal_acks >>

SendCommit(self) == /\ pc[self] = "SendCommit"
                    /\ IF i[self] <= Len(followers[self])
                          THEN /\ messages' = Send((followers[self][i[self]]), (ProposalMessage(self[1], new_epoch[self], Transaction(v[self], Zxid(new_epoch[self], counter[self])))), messages)
                               /\ i' = [i EXCEPT ![self] = i[self]+1]
                               /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "End_Le"]
                               /\ UNCHANGED << messages, i >>
                    /\ UNCHANGED << stack, message_, confirmed_, message,
                                    confirmed, v, last_epoch, last_leader,
                                    history, zxid, candidate, delivered,
                                    restart, ready, leader_candidate,
                                    followers, selected_history, new_epoch,
                                    counter, proposed, proposal_acks >>

End_Le(self) == /\ pc[self] = "End_Le"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << messages, message_, confirmed_, message, i,
                                confirmed, v, last_epoch, last_leader, history,
                                zxid, candidate, delivered, restart, ready,
                                leader_candidate, followers, selected_history,
                                new_epoch, counter, proposed, proposal_acks >>

LeaderCommit(self) == GetProposeAckMessage(self) \/ HandleProposalAck(self)
                         \/ CheckQuorumAckd(self) \/ SendCommit(self)
                         \/ End_Le(self)

GetCepochMessage(self) == /\ pc[self] = "GetCepochMessage"
                          /\ /\ CanRecv(self[1], messages)
                             /\ Head(messages[self[1]]).type = CEPOCH
                          /\ Assert(CanRecv(self[1], messages),
                                    "Failure of assertion at line 126, column 5 of macro called at line 338, column 9.")
                          /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                             /\ messages' = Recv(self[1], messages)[2]
                          /\ pc' = [pc EXCEPT ![self] = "HandleCepochMessage"]
                          /\ UNCHANGED << stack, message_, confirmed_, i,
                                          confirmed, v, last_epoch,
                                          last_leader, history, zxid,
                                          candidate, delivered, restart, ready,
                                          leader_candidate, followers,
                                          selected_history, new_epoch, counter,
                                          proposed, proposal_acks >>

HandleCepochMessage(self) == /\ pc[self] = "HandleCepochMessage"
                             /\ IF message[self].epoch < new_epoch[self]
                                   THEN /\ pc' = [pc EXCEPT ![self] = "SendNewEpoch"]
                                   ELSE /\ TRUE
                                        /\ pc' = [pc EXCEPT ![self] = "End_Lea"]
                             /\ UNCHANGED << messages, stack, message_,
                                             confirmed_, message, i, confirmed,
                                             v, last_epoch, last_leader,
                                             history, zxid, candidate,
                                             delivered, restart, ready,
                                             leader_candidate, followers,
                                             selected_history, new_epoch,
                                             counter, proposed, proposal_acks >>

SendNewEpoch(self) == /\ pc[self] = "SendNewEpoch"
                      /\ messages' = Send((message[self].from), (NewEpochMessage(self[1], new_epoch[self])), messages)
                      /\ pc' = [pc EXCEPT ![self] = "SendNewLeader"]
                      /\ UNCHANGED << stack, message_, confirmed_, message, i,
                                      confirmed, v, last_epoch, last_leader,
                                      history, zxid, candidate, delivered,
                                      restart, ready, leader_candidate,
                                      followers, selected_history, new_epoch,
                                      counter, proposed, proposal_acks >>

SendNewLeader(self) == /\ pc[self] = "SendNewLeader"
                       /\ messages' = Send((message[self].from), (NewLeaderMessage(self[1], new_epoch[self], selected_history[self].history \o proposed[self])), messages)
                       /\ pc' = [pc EXCEPT ![self] = "End_Lea"]
                       /\ UNCHANGED << stack, message_, confirmed_, message, i,
                                       confirmed, v, last_epoch, last_leader,
                                       history, zxid, candidate, delivered,
                                       restart, ready, leader_candidate,
                                       followers, selected_history, new_epoch,
                                       counter, proposed, proposal_acks >>

End_Lea(self) == /\ pc[self] = "End_Lea"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << messages, message_, confirmed_, message, i,
                                 confirmed, v, last_epoch, last_leader,
                                 history, zxid, candidate, delivered, restart,
                                 ready, leader_candidate, followers,
                                 selected_history, new_epoch, counter,
                                 proposed, proposal_acks >>

LeaderSetupNewFollower(self) == GetCepochMessage(self)
                                   \/ HandleCepochMessage(self)
                                   \/ SendNewEpoch(self)
                                   \/ SendNewLeader(self) \/ End_Lea(self)

GetAckNewLeaderMessage(self) == /\ pc[self] = "GetAckNewLeaderMessage"
                                /\ /\ CanRecv(self[1], messages)
                                   /\ Head(messages[self[1]]).type = ACK_LD
                                /\ Assert(CanRecv(self[1], messages),
                                          "Failure of assertion at line 126, column 5 of macro called at line 359, column 9.")
                                /\ /\ message' = [message EXCEPT ![self] = Recv(self[1], messages)[1]]
                                   /\ messages' = Recv(self[1], messages)[2]
                                /\ pc' = [pc EXCEPT ![self] = "HandleAckLeader"]
                                /\ UNCHANGED << stack, message_, confirmed_, i,
                                                confirmed, v, last_epoch,
                                                last_leader, history, zxid,
                                                candidate, delivered, restart,
                                                ready, leader_candidate,
                                                followers, selected_history,
                                                new_epoch, counter, proposed,
                                                proposal_acks >>

HandleAckLeader(self) == /\ pc[self] = "HandleAckLeader"
                         /\ IF message[self].epoch = new_epoch[self]
                               THEN /\ messages' = Send((message[self].from), (CommitLeaderMessage(self[1], new_epoch[self])), messages)
                                    /\ followers' = [followers EXCEPT ![self] = Append(followers[self], message[self].from)]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << messages, followers >>
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << message_, confirmed_, message, i,
                                         confirmed, v, last_epoch, last_leader,
                                         history, zxid, candidate, delivered,
                                         restart, ready, leader_candidate,
                                         selected_history, new_epoch, counter,
                                         proposed, proposal_acks >>

LeaderAddFollowerToQuorum(self) == GetAckNewLeaderMessage(self)
                                      \/ HandleAckLeader(self)

GetCandidate_(self) == /\ pc[self] = "GetCandidate_"
                       /\ candidate' = [candidate EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                       /\ pc' = [pc EXCEPT ![self] = "FollowerDiscover"]
                       /\ UNCHANGED << messages, stack, message_, confirmed_,
                                       message, i, confirmed, v, last_epoch,
                                       last_leader, history, zxid, delivered,
                                       restart, ready, leader_candidate,
                                       followers, selected_history, new_epoch,
                                       counter, proposed, proposal_acks >>

FollowerDiscover(self) == /\ pc[self] = "FollowerDiscover"
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP1",
                                                                   pc        |->  "FollowerSynchronize",
                                                                   message_  |->  message_[self] ] >>
                                                               \o stack[self]]
                          /\ message_' = [message_ EXCEPT ![self] = defaultInitValue]
                          /\ pc' = [pc EXCEPT ![self] = "Notify"]
                          /\ UNCHANGED << messages, confirmed_, message, i,
                                          confirmed, v, last_epoch,
                                          last_leader, history, zxid,
                                          candidate, delivered, restart, ready,
                                          leader_candidate, followers,
                                          selected_history, new_epoch, counter,
                                          proposed, proposal_acks >>

FollowerSynchronize(self) == /\ pc[self] = "FollowerSynchronize"
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP2",
                                                                      pc        |->  "FollowerSynchronizeCheckRestart" ] >>
                                                                  \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "GetNewLeaderMessage"]
                             /\ UNCHANGED << messages, message_, confirmed_,
                                             message, i, confirmed, v,
                                             last_epoch, last_leader, history,
                                             zxid, candidate, delivered,
                                             restart, ready, leader_candidate,
                                             followers, selected_history,
                                             new_epoch, counter, proposed,
                                             proposal_acks >>

FollowerSynchronizeCheckRestart(self) == /\ pc[self] = "FollowerSynchronizeCheckRestart"
                                         /\ IF restart[self]
                                               THEN /\ pc' = [pc EXCEPT ![self] = "End"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "SetReady"]
                                         /\ UNCHANGED << messages, stack,
                                                         message_, confirmed_,
                                                         message, i, confirmed,
                                                         v, last_epoch,
                                                         last_leader, history,
                                                         zxid, candidate,
                                                         delivered, restart,
                                                         ready,
                                                         leader_candidate,
                                                         followers,
                                                         selected_history,
                                                         new_epoch, counter,
                                                         proposed,
                                                         proposal_acks >>

SetReady(self) == /\ pc[self] = "SetReady"
                  /\ IF candidate[self] = self[1]
                        THEN /\ ready' = [ready EXCEPT ![self] = TRUE]
                        ELSE /\ TRUE
                             /\ ready' = ready
                  /\ pc' = [pc EXCEPT ![self] = "FollowerBroadcast"]
                  /\ UNCHANGED << messages, stack, message_, confirmed_,
                                  message, i, confirmed, v, last_epoch,
                                  last_leader, history, zxid, candidate,
                                  delivered, restart, leader_candidate,
                                  followers, selected_history, new_epoch,
                                  counter, proposed, proposal_acks >>

FollowerBroadcast(self) == /\ pc[self] = "FollowerBroadcast"
                           /\ pc' = [pc EXCEPT ![self] = "FollowerBroadcastStep"]
                           /\ UNCHANGED << messages, stack, message_,
                                           confirmed_, message, i, confirmed,
                                           v, last_epoch, last_leader, history,
                                           zxid, candidate, delivered, restart,
                                           ready, leader_candidate, followers,
                                           selected_history, new_epoch,
                                           counter, proposed, proposal_acks >>

FollowerBroadcastStep(self) == /\ pc[self] = "FollowerBroadcastStep"
                               /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FollowerBroadcastAccept",
                                                                              pc        |->  "FollowerBroadcast" ] >>
                                                                          \o stack[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "GetProposalMessage"]
                                  \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FollowerBroadcastCommit",
                                                                              pc        |->  "FollowerBroadcast" ] >>
                                                                          \o stack[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "GetCommitMessage"]
                               /\ UNCHANGED << messages, message_, confirmed_,
                                               message, i, confirmed, v,
                                               last_epoch, last_leader,
                                               history, zxid, candidate,
                                               delivered, restart, ready,
                                               leader_candidate, followers,
                                               selected_history, new_epoch,
                                               counter, proposed,
                                               proposal_acks >>

End(self) == /\ pc[self] = "End"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << messages, stack, message_, confirmed_, message, i,
                             confirmed, v, last_epoch, last_leader, history,
                             zxid, candidate, delivered, restart, ready,
                             leader_candidate, followers, selected_history,
                             new_epoch, counter, proposed, proposal_acks >>

follower_tuple(self) == GetCandidate_(self) \/ FollowerDiscover(self)
                           \/ FollowerSynchronize(self)
                           \/ FollowerSynchronizeCheckRestart(self)
                           \/ SetReady(self) \/ FollowerBroadcast(self)
                           \/ FollowerBroadcastStep(self) \/ End(self)

GetCandidate(self) == /\ pc[self] = "GetCandidate"
                      /\ leader_candidate' = [leader_candidate EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                      /\ IF leader_candidate'[self] = self[1]
                            THEN /\ pc' = [pc EXCEPT ![self] = "LeaderDiscover"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << messages, stack, message_, confirmed_,
                                      message, i, confirmed, v, last_epoch,
                                      last_leader, history, zxid, candidate,
                                      delivered, restart, ready, followers,
                                      selected_history, new_epoch, counter,
                                      proposed, proposal_acks >>

LeaderDiscover(self) == /\ pc[self] = "LeaderDiscover"
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP1",
                                                                 pc        |->  "LeaderSynchronize",
                                                                 confirmed_ |->  confirmed_[self],
                                                                 message   |->  message[self],
                                                                 i         |->  i[self] ] >>
                                                             \o stack[self]]
                        /\ confirmed_' = [confirmed_ EXCEPT ![self] = {}]
                        /\ message' = [message EXCEPT ![self] = defaultInitValue]
                        /\ i' = [i EXCEPT ![self] = 0]
                        /\ pc' = [pc EXCEPT ![self] = "GatherQuorum"]
                        /\ UNCHANGED << messages, message_, confirmed, v,
                                        last_epoch, last_leader, history, zxid,
                                        candidate, delivered, restart, ready,
                                        leader_candidate, followers,
                                        selected_history, new_epoch, counter,
                                        proposed, proposal_acks >>

LeaderSynchronize(self) == /\ pc[self] = "LeaderSynchronize"
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP2",
                                                                    pc        |->  "LeaderBroadcast",
                                                                    confirmed |->  confirmed[self] ] >>
                                                                \o stack[self]]
                           /\ confirmed' = [confirmed EXCEPT ![self] = {}]
                           /\ pc' = [pc EXCEPT ![self] = "LP2Start"]
                           /\ UNCHANGED << messages, message_, confirmed_,
                                           message, i, v, last_epoch,
                                           last_leader, history, zxid,
                                           candidate, delivered, restart,
                                           ready, leader_candidate, followers,
                                           selected_history, new_epoch,
                                           counter, proposed, proposal_acks >>

LeaderBroadcast(self) == /\ pc[self] = "LeaderBroadcast"
                         /\ pc' = [pc EXCEPT ![self] = "LeaderBroadcastStep"]
                         /\ UNCHANGED << messages, stack, message_, confirmed_,
                                         message, i, confirmed, v, last_epoch,
                                         last_leader, history, zxid, candidate,
                                         delivered, restart, ready,
                                         leader_candidate, followers,
                                         selected_history, new_epoch, counter,
                                         proposed, proposal_acks >>

LeaderBroadcastStep(self) == /\ pc[self] = "LeaderBroadcastStep"
                             /\ \/ /\ \E val \in Values:
                                        /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderPropose",
                                                                                    pc        |->  "LeaderBroadcast",
                                                                                    v         |->  v[self] ] >>
                                                                                \o stack[self]]
                                           /\ v' = [v EXCEPT ![self] = val]
                                        /\ pc' = [pc EXCEPT ![self] = "LeaderProposeStart"]
                                \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderCommit",
                                                                            pc        |->  "LeaderBroadcast" ] >>
                                                                        \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "GetProposeAckMessage"]
                                   /\ v' = v
                                \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderSetupNewFollower",
                                                                            pc        |->  "LeaderBroadcast" ] >>
                                                                        \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "GetCepochMessage"]
                                   /\ v' = v
                                \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LeaderAddFollowerToQuorum",
                                                                            pc        |->  "LeaderBroadcast" ] >>
                                                                        \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "GetAckNewLeaderMessage"]
                                   /\ v' = v
                             /\ UNCHANGED << messages, message_, confirmed_,
                                             message, i, confirmed, last_epoch,
                                             last_leader, history, zxid,
                                             candidate, delivered, restart,
                                             ready, leader_candidate,
                                             followers, selected_history,
                                             new_epoch, counter, proposed,
                                             proposal_acks >>

leader_tuple(self) == GetCandidate(self) \/ LeaderDiscover(self)
                         \/ LeaderSynchronize(self)
                         \/ LeaderBroadcast(self)
                         \/ LeaderBroadcastStep(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ FP1(self) \/ LP1(self) \/ FP2(self)
                               \/ LP2(self) \/ FollowerBroadcastAccept(self)
                               \/ FollowerBroadcastCommit(self)
                               \/ LeaderPropose(self) \/ LeaderCommit(self)
                               \/ LeaderSetupNewFollower(self)
                               \/ LeaderAddFollowerToQuorum(self))
           \/ (\E self \in Servers \X {0}: follower_tuple(self))
           \/ (\E self \in Servers \X {1}: leader_tuple(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
