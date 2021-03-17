---- MODULE zab_pluscal ----

EXTENDS Sequences, Integers, TLC, FiniteSets


\* Set of server IDs
CONSTANTS Servers

\* Server states
CONSTANTS Follower, Candidate, Leader

\* Message types, correspond to those in the "Dissecting Zab" tech report
CONSTANTS CEPOCH, NEWEPOCH, ACK_E,
          NEWLEADER, ACK_LD, COMMIT_LD,
          PROPOSE, ACK_P, COMMIT


(* --algorithm zab_algo

\* Represents messages sent from one server to another
\* Maps from the destination server to the message in the format <<from, type, contents>>
variable messages = [s \in Servers |-> <<>>]

define
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
    ProposalMessage(from, epoch, transaction) == [from |-> from, epoch |-> epoch, transaction |-> transaction]
    AckProposalMessage(from, epoch, transaction) == [from |-> from, epoch |-> epoch, transaction |-> transaction]
    CommitProposalMessage(from, epoch, transaction) == [from |-> from, epoch |-> epoch, transaction |-> transaction]
    \* TODO: do we need a generic Message type? The paxos TLA spec uses Messages to represent the set of all possible messages, and then
    \*  introduces a TypeOK variant to check that every message is one of those types:
    \*  https://github.com/tlaplus/Examples/blob/master/specifications/PaxosHowToWinATuringAward/Paxos.tla#L67
    \* Message == CepochMessage(from, last_epoch)
    \*     \union NewEpochMessage(from, epoch)
    \*     \union AckEpochMessage(from, last_leader, history)


    \*** Other Helpers

    Zxid(epoch, counter) == [epoch |-> epoch, counter |-> counter]

    ZxidGreaterThan(left, right) == \/ left.epoch > right.epoch
                                    \/ /\ left.epoch = right.epoch
                                       /\ left.counter > right.counter

    Transaction(value, zxid) == [value |-> value, zxid |-> zxid]

    IsQuorum(subset, set) == 2 * Cardinality(subset) > Cardinality(set)

    Max(a, b) == IF b > a THEN b ELSE a

    Range(seq) == {seq[i] : i \in DOMAIN seq}

    Last(seq) == seq[Len(seq)]


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

\* Wraps the Recv() operator to set the message variable to the next message and update the messages structure
macro DoRecv()
begin
    assert CanRecv(self, messages);
    \* TODO: is there a more elegant way to get the next value from a sequence while removing it?
    message := Recv(self, messages)[1] || messages := Recv(self, messages)[2];
end macro;

\* Follower Phase 1: Discovery
procedure FP1()
variable message
begin
    Notify:
        DoSend(candidate, CepochMessage(self, last_epoch));
    GetMessage:
        await CanRecv(self, messages);
        DoRecv();
    HandleMessage:
        if message.type = NEWEPOCH /\ message.from = candidate then
            if last_epoch < message.epoch then
                last_epoch := message.epoch;
                DoSend(candidate, AckEpochMessage(self, last_leader, history));
            end if;
        else
            \* TODO: under what conditions should we not check for the next message, e.g. restart leader election?
            goto GetMessage;
        end if;
    End:
        return;
end procedure;

\* Leader Phase 1: Discovery
procedure LP1()
variables confirmed = {},
          message,
          i;
begin
    GatherQuorum:
        while ~IsQuorum(followers, Servers) do
            GetMessage:
                await CanRecv(self, messages);
                DoRecv();
            HandleMessage:
                \* TODO: under what conditions should we not check for the next message, e.g. restart leader election?
                if message.type = CEPOCH then
                    \* latest epoch seen by followers in quorum
                    new_epoch := Max(new_epoch, message.last_epoch);
                    if message.from \notin Range(followers) then
                        followers := Append(followers, message.from);
                    end if;
                end if;
        end while;

        assert IsQuorum(followers, Servers);
        i := 1;
    NewEpoch:
        while i <= DOMAIN followers do
            DoSend(followers[i], NewEpochMessage(self, new_epoch));
            i := i+1;
        end while;
    HistorySelection:
        while confirmed /= Range(followers) do
            GetAck:
                await CanRecv(self, messages);
                DoRecv();
            HandleAck:
                if message.type = ACK_E then
                    confirmed := confirmed \union {message.from};

                    if  \/ message.last_leader > selected_history.last_leader
                        \/  /\ message.last_leader = selected_history.last_leader
                            /\ ZxidGreaterThan(Last(message.history).zxid, Last(selected_history.history).zxid) then
                        selected_history := [last_leader |-> message.last_leader, history |-> message.history];
                    end if;
                end if;
        end while;

    End:
        return;
end procedure;

\* Follower Phase 2: Synchronization
procedure FP2()
begin
    GetNewLeaderMessage:
        await CanRecv(self, messages);
        DoRecv();
    HandleNewLeaderMessage:
        if message.type = NEWLEADER then
            if last_epoch = message.epoch then
                last_leader := message.epoch;
                \* TODO: do we need to separately accept each value, zxid pair? Or can we just set the history
                history := message.inital_history;
                DoSend(candidate, AckLeaderMessage(self, message.epoch))
            else
                \* should start the protocol over again if the last acknowledged epoch proposal is different than the specified epoch
                \* TODO: how should we structure the spec to be able to jump back to the beginning of the process?
                restart := TRUE;
                goto End;
            end if;
        else
            \* TODO: under what conditions should we not check for the next message? Timeout?
            goto GetNewLeaderMessage;
        end if;
    GetCommitMessage:
        await CanRecv(self, messages);
        DoRecv();
    HandleCommitMessage:
        if message.type = COMMIT_LD then
            \* TODO: should delivered be a tuple since the transactions in a history should be delivered in-order?
            delivered := delivered \union {history}
        else
            \* TODO: under what conditions should we not check for the next message? Timeout?
            goto GetCommitMessage;
        end if;
    End:
        return;
end procedure;

\* Leader Phase 2: Synchronization
procedure LP2()
variables confirmed = {};   \* followers that have ack'd the new leader message
begin
    LP2Start:
        assert IsQuorum(followers, Servers);
        i := 1;
    NewLeader:
        while i <= DOMAIN followers do
            DoSend(followers[i], NewLeaderMessage(self, new_epoch, selected_history));
            i := i+1;
        end while;
    AwaitCommit:
        while ~IsQuorum(confirmed, Servers) do
            GetAck:
                await CanRecv(self, messages);
                DoRecv();
            HandleAck:
                if message.type = ACK_LD then
                    confirmed := confirmed \union {message.from};
                end if;
        end while;
        i := 1;
    SendCommit:
        while i <= DOMAIN followers do
            DoSend(followers[i], CommitLeaderMessage(self, new_epoch));
            i := i+1;
        end while;
    End:
        return;
end procedure;

procedure DoFollower(candidate)
\* TODO: how should we structure the spec to be able to jump back to the beginning of the process? Right now we use a flag
variables restart = FALSE;
begin
    FollowerDiscover:
        call FP1();
    FollowerDiscoverCheckRestart:
        if restart then
            goto End;
        end if;

    FollowerSynchronize:
        call FP2();
    FollowerSynchronizeCheckRestart:
        if restart then
            goto End;
        end if;

    End:
        return;
end procedure;

procedure DoLeader()
\* TODO: we use a sequence since we need to be able to run the macro DoSend() for each element in it, and I don't know how to do that using sets
variables followers = <<>>,     \* tracks the followers committed to a leader
          selected_history = [last_leader |-> 0, history |-> <<>>],     \* tracks the selected initial history
          new_epoch = last_epoch,
          \* TODO: how should we structure the spec to be able to jump back to the beginning of the process? Right now we use a flag
          restart = FALSE;
begin
    LeaderDiscover:
        call LP1();
    LeaderDiscoverCheckRestart:
        if restart then
            goto End;
        end if;

    LeaderSynchronize:
        call FP2();
    LeaderSynchronizeCheckRestart:
        if restart then
            goto End;
        end if;

    End:
        return;
end procedure;

process server \in Servers
variables state = Follower,     \* Current state of the server
          last_epoch = 0,       \* Last new epoch proposol acknowledged
          last_leader = 0,      \* Last new leader proposal acknowledged
          history,              \* In-order record of all the accepted value proposals
          \* TODO: do we really need to track zxid, or can we just use history?
          zxid = Zxid(0, 0),    \* Zookeeper transaction ID (zxid) of last accepted transaction in the history
          candidate,            \* Candidate selected by leader oracle
          delivered = {};       \* Tracks the transactions that have been delivered to the application by Zab
begin
    \* TODO: need to run multiple iterations, should include a loop
    GetCandidate:
        candidate := LeaderOracle(last_epoch + 1);
    RunRole:
        \* TODO: a leader also runs the follower steps
        if candidate = self then
            call DoLeader();
        else
            call DoFollower(candidate);
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4473c17e" /\ chksum(tla) = "9a352225")
\* Label GetMessage of procedure FP1 at line 100 col 9 changed to GetMessage_
\* Label HandleMessage of procedure FP1 at line 103 col 9 changed to HandleMessage_
\* Label End of procedure FP1 at line 113 col 9 changed to End_
\* Label GetAck of procedure LP1 at line 148 col 17 changed to GetAck_
\* Label HandleAck of procedure LP1 at line 151 col 17 changed to HandleAck_
\* Label End of procedure LP1 at line 163 col 9 changed to End_L
\* Label End of procedure FP2 at line 201 col 9 changed to End_F
\* Label End of procedure LP2 at line 233 col 9 changed to End_LP
\* Label End of procedure DoFollower at line 255 col 9 changed to End_D
\* Process variable candidate of process server at line 291 col 11 changed to candidate_
\* Procedure variable message of procedure FP1 at line 95 col 10 changed to message_
\* Procedure variable confirmed of procedure LP1 at line 118 col 11 changed to confirmed_
\* Procedure variable restart of procedure DoFollower at line 238 col 11 changed to restart_
CONSTANT defaultInitValue
VARIABLES messages, pc, stack

(* define statement *)
Send(to, m, _messages) == [_messages EXCEPT ![to] = Append(_messages[to], m)]


Recv(server, _messages) == <<Head(_messages[server]), [_messages EXCEPT ![server] = Tail(_messages[server])]>>

CanRecv(server, _messages) == Len(_messages[server]) > 0


CepochMessage(from, last_epoch) == [from |-> from, type |-> CEPOCH, last_epoch |-> last_epoch]
NewEpochMessage(from, epoch) == [from |-> from, type |-> NEWEPOCH, epoch |-> epoch]
AckEpochMessage(from, last_leader, history) == [from |-> from, type |-> ACK_E, last_leader |-> last_leader, history |-> history]
NewLeaderMessage(from, epoch, initial_history) == [from |-> from, type |-> NEWLEADER, epoch |-> epoch, initial_history |-> initial_history]
AckLeaderMessage(from, epoch) == [from |-> from, type |-> ACK_LD, epoch |-> epoch]
CommitLeaderMessage(from, epoch) == [from |-> from, type |-> COMMIT_LD, epoch |-> epoch]
ProposalMessage(from, epoch, transaction) == [from |-> from, epoch |-> epoch, transaction |-> transaction]
AckProposalMessage(from, epoch, transaction) == [from |-> from, epoch |-> epoch, transaction |-> transaction]
CommitProposalMessage(from, epoch, transaction) == [from |-> from, epoch |-> epoch, transaction |-> transaction]










Zxid(epoch, counter) == [epoch |-> epoch, counter |-> counter]

ZxidGreaterThan(left, right) == \/ left.epoch > right.epoch
                                \/ /\ left.epoch = right.epoch
                                   /\ left.counter > right.counter

Transaction(value, zxid) == [value |-> value, zxid |-> zxid]

IsQuorum(subset, set) == 2 * Cardinality(subset) > Cardinality(set)

Max(a, b) == IF b > a THEN b ELSE a

Range(seq) == {seq[i] : i \in DOMAIN seq}

Last(seq) == seq[Len(seq)]






LeaderOracle(epoch) == CHOOSE s \in Servers : TRUE

VARIABLES message_, confirmed_, message, i, confirmed, candidate, restart_,
          followers, selected_history, new_epoch, restart, state, last_epoch,
          last_leader, history, zxid, candidate_, delivered

vars == << messages, pc, stack, message_, confirmed_, message, i, confirmed,
           candidate, restart_, followers, selected_history, new_epoch,
           restart, state, last_epoch, last_leader, history, zxid, candidate_,
           delivered >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ messages = [s \in Servers |-> <<>>]
        (* Procedure FP1 *)
        /\ message_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure LP1 *)
        /\ confirmed_ = [ self \in ProcSet |-> {}]
        /\ message = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure LP2 *)
        /\ confirmed = [ self \in ProcSet |-> {}]
        (* Procedure DoFollower *)
        /\ candidate = [ self \in ProcSet |-> defaultInitValue]
        /\ restart_ = [ self \in ProcSet |-> FALSE]
        (* Procedure DoLeader *)
        /\ followers = [ self \in ProcSet |-> <<>>]
        /\ selected_history = [ self \in ProcSet |-> [last_leader |-> 0, history |-> <<>>]]
        /\ new_epoch = [ self \in ProcSet |-> last_epoch[self]]
        /\ restart = [ self \in ProcSet |-> FALSE]
        (* Process server *)
        /\ state = [self \in Servers |-> Follower]
        /\ last_epoch = [self \in Servers |-> 0]
        /\ last_leader = [self \in Servers |-> 0]
        /\ history = [self \in Servers |-> defaultInitValue]
        /\ zxid = [self \in Servers |-> Zxid(0, 0)]
        /\ candidate_ = [self \in Servers |-> defaultInitValue]
        /\ delivered = [self \in Servers |-> {}]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "GetCandidate"]

Notify(self) == /\ pc[self] = "Notify"
                /\ messages' = Send(candidate[self], (CepochMessage(self, last_epoch[self])), messages)
                /\ pc' = [pc EXCEPT ![self] = "GetMessage_"]
                /\ UNCHANGED << stack, message_, confirmed_, message, i,
                                confirmed, candidate, restart_, followers,
                                selected_history, new_epoch, restart, state,
                                last_epoch, last_leader, history, zxid,
                                candidate_, delivered >>

GetMessage_(self) == /\ pc[self] = "GetMessage_"
                     /\ CanRecv(self, messages)
                     /\ Assert(CanRecv(self, messages),
                               "Failure of assertion at line 88, column 5 of macro called at line 101, column 9.")
                     /\ /\ message_' = [message_ EXCEPT ![self] = Recv(self, messages)[1]]
                        /\ messages' = Recv(self, messages)[2]
                     /\ pc' = [pc EXCEPT ![self] = "HandleMessage_"]
                     /\ UNCHANGED << stack, confirmed_, message, i, confirmed,
                                     candidate, restart_, followers,
                                     selected_history, new_epoch, restart,
                                     state, last_epoch, last_leader, history,
                                     zxid, candidate_, delivered >>

HandleMessage_(self) == /\ pc[self] = "HandleMessage_"
                        /\ IF message_[self].type = NEWEPOCH /\ message_[self].from = candidate[self]
                              THEN /\ IF last_epoch[self] < message_[self].epoch
                                         THEN /\ last_epoch' = [last_epoch EXCEPT ![self] = message_[self].epoch]
                                              /\ messages' = Send(candidate[self], (AckEpochMessage(self, last_leader[self], history[self])), messages)
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << messages,
                                                              last_epoch >>
                                   /\ pc' = [pc EXCEPT ![self] = "End_"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "GetMessage_"]
                                   /\ UNCHANGED << messages, last_epoch >>
                        /\ UNCHANGED << stack, message_, confirmed_, message,
                                        i, confirmed, candidate, restart_,
                                        followers, selected_history, new_epoch,
                                        restart, state, last_leader, history,
                                        zxid, candidate_, delivered >>

End_(self) == /\ pc[self] = "End_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ message_' = [message_ EXCEPT ![self] = Head(stack[self]).message_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << messages, confirmed_, message, i, confirmed,
                              candidate, restart_, followers, selected_history,
                              new_epoch, restart, state, last_epoch,
                              last_leader, history, zxid, candidate_,
                              delivered >>

FP1(self) == Notify(self) \/ GetMessage_(self) \/ HandleMessage_(self)
                \/ End_(self)

GatherQuorum(self) == /\ pc[self] = "GatherQuorum"
                      /\ IF ~IsQuorum(followers[self], Servers)
                            THEN /\ pc' = [pc EXCEPT ![self] = "GetMessage"]
                                 /\ i' = i
                            ELSE /\ Assert(IsQuorum(followers[self], Servers),
                                           "Failure of assertion at line 138, column 9.")
                                 /\ i' = [i EXCEPT ![self] = 1]
                                 /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                      /\ UNCHANGED << messages, stack, message_, confirmed_,
                                      message, confirmed, candidate, restart_,
                                      followers, selected_history, new_epoch,
                                      restart, state, last_epoch, last_leader,
                                      history, zxid, candidate_, delivered >>

GetMessage(self) == /\ pc[self] = "GetMessage"
                    /\ CanRecv(self, messages)
                    /\ Assert(CanRecv(self, messages),
                              "Failure of assertion at line 88, column 5 of macro called at line 126, column 17.")
                    /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                       /\ messages' = Recv(self, messages)[2]
                    /\ pc' = [pc EXCEPT ![self] = "HandleMessage"]
                    /\ UNCHANGED << stack, message_, confirmed_, i, confirmed,
                                    candidate, restart_, followers,
                                    selected_history, new_epoch, restart,
                                    state, last_epoch, last_leader, history,
                                    zxid, candidate_, delivered >>

HandleMessage(self) == /\ pc[self] = "HandleMessage"
                       /\ IF message[self].type = CEPOCH
                             THEN /\ new_epoch' = [new_epoch EXCEPT ![self] = Max(new_epoch[self], message[self].last_epoch)]
                                  /\ IF message[self].from \notin Range(followers[self])
                                        THEN /\ followers' = [followers EXCEPT ![self] = Append(followers[self], message[self].from)]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED followers
                             ELSE /\ TRUE
                                  /\ UNCHANGED << followers, new_epoch >>
                       /\ pc' = [pc EXCEPT ![self] = "GatherQuorum"]
                       /\ UNCHANGED << messages, stack, message_, confirmed_,
                                       message, i, confirmed, candidate,
                                       restart_, selected_history, restart,
                                       state, last_epoch, last_leader, history,
                                       zxid, candidate_, delivered >>

NewEpoch(self) == /\ pc[self] = "NewEpoch"
                  /\ IF i[self] <= DOMAIN followers[self]
                        THEN /\ messages' = Send((followers[self][i[self]]), (NewEpochMessage(self, new_epoch[self])), messages)
                             /\ i' = [i EXCEPT ![self] = i[self]+1]
                             /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                             /\ UNCHANGED << messages, i >>
                  /\ UNCHANGED << stack, message_, confirmed_, message,
                                  confirmed, candidate, restart_, followers,
                                  selected_history, new_epoch, restart, state,
                                  last_epoch, last_leader, history, zxid,
                                  candidate_, delivered >>

HistorySelection(self) == /\ pc[self] = "HistorySelection"
                          /\ IF confirmed_[self] /= Range(followers[self])
                                THEN /\ pc' = [pc EXCEPT ![self] = "GetAck_"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "End_L"]
                          /\ UNCHANGED << messages, stack, message_,
                                          confirmed_, message, i, confirmed,
                                          candidate, restart_, followers,
                                          selected_history, new_epoch, restart,
                                          state, last_epoch, last_leader,
                                          history, zxid, candidate_, delivered >>

GetAck_(self) == /\ pc[self] = "GetAck_"
                 /\ CanRecv(self, messages)
                 /\ Assert(CanRecv(self, messages),
                           "Failure of assertion at line 88, column 5 of macro called at line 149, column 17.")
                 /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                    /\ messages' = Recv(self, messages)[2]
                 /\ pc' = [pc EXCEPT ![self] = "HandleAck_"]
                 /\ UNCHANGED << stack, message_, confirmed_, i, confirmed,
                                 candidate, restart_, followers,
                                 selected_history, new_epoch, restart, state,
                                 last_epoch, last_leader, history, zxid,
                                 candidate_, delivered >>

HandleAck_(self) == /\ pc[self] = "HandleAck_"
                    /\ IF message[self].type = ACK_E
                          THEN /\ confirmed_' = [confirmed_ EXCEPT ![self] = confirmed_[self] \union {message[self].from}]
                               /\ IF \/ message[self].last_leader > selected_history[self].last_leader
                                     \/  /\ message[self].last_leader = selected_history[self].last_leader
                                         /\ ZxidGreaterThan(Last(message[self].history).zxid, Last(selected_history[self].history).zxid)
                                     THEN /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> message[self].last_leader, history |-> message[self].history]]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED selected_history
                          ELSE /\ TRUE
                               /\ UNCHANGED << confirmed_, selected_history >>
                    /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                    /\ UNCHANGED << messages, stack, message_, message, i,
                                    confirmed, candidate, restart_, followers,
                                    new_epoch, restart, state, last_epoch,
                                    last_leader, history, zxid, candidate_,
                                    delivered >>

End_L(self) == /\ pc[self] = "End_L"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ confirmed_' = [confirmed_ EXCEPT ![self] = Head(stack[self]).confirmed_]
               /\ message' = [message EXCEPT ![self] = Head(stack[self]).message]
               /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << messages, message_, confirmed, candidate,
                               restart_, followers, selected_history,
                               new_epoch, restart, state, last_epoch,
                               last_leader, history, zxid, candidate_,
                               delivered >>

LP1(self) == GatherQuorum(self) \/ GetMessage(self) \/ HandleMessage(self)
                \/ NewEpoch(self) \/ HistorySelection(self)
                \/ GetAck_(self) \/ HandleAck_(self) \/ End_L(self)

GetNewLeaderMessage(self) == /\ pc[self] = "GetNewLeaderMessage"
                             /\ CanRecv(self, messages)
                             /\ Assert(CanRecv(self, messages),
                                       "Failure of assertion at line 88, column 5 of macro called at line 171, column 9.")
                             /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                                /\ messages' = Recv(self, messages)[2]
                             /\ pc' = [pc EXCEPT ![self] = "HandleNewLeaderMessage"]
                             /\ UNCHANGED << stack, message_, confirmed_, i,
                                             confirmed, candidate, restart_,
                                             followers, selected_history,
                                             new_epoch, restart, state,
                                             last_epoch, last_leader, history,
                                             zxid, candidate_, delivered >>

HandleNewLeaderMessage(self) == /\ pc[self] = "HandleNewLeaderMessage"
                                /\ IF message[self].type = NEWLEADER
                                      THEN /\ IF last_epoch[self] = message[self].epoch
                                                 THEN /\ last_leader' = [last_leader EXCEPT ![self] = message[self].epoch]
                                                      /\ history' = [history EXCEPT ![self] = message[self].inital_history]
                                                      /\ messages' = Send(candidate[self], (AckLeaderMessage(self, message[self].epoch)), messages)
                                                      /\ pc' = [pc EXCEPT ![self] = "GetCommitMessage"]
                                                      /\ UNCHANGED restart
                                                 ELSE /\ restart' = [restart EXCEPT ![self] = TRUE]
                                                      /\ pc' = [pc EXCEPT ![self] = "End_F"]
                                                      /\ UNCHANGED << messages,
                                                                      last_leader,
                                                                      history >>
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "GetNewLeaderMessage"]
                                           /\ UNCHANGED << messages, restart,
                                                           last_leader,
                                                           history >>
                                /\ UNCHANGED << stack, message_, confirmed_,
                                                message, i, confirmed,
                                                candidate, restart_, followers,
                                                selected_history, new_epoch,
                                                state, last_epoch, zxid,
                                                candidate_, delivered >>

GetCommitMessage(self) == /\ pc[self] = "GetCommitMessage"
                          /\ CanRecv(self, messages)
                          /\ Assert(CanRecv(self, messages),
                                    "Failure of assertion at line 88, column 5 of macro called at line 191, column 9.")
                          /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                             /\ messages' = Recv(self, messages)[2]
                          /\ pc' = [pc EXCEPT ![self] = "HandleCommitMessage"]
                          /\ UNCHANGED << stack, message_, confirmed_, i,
                                          confirmed, candidate, restart_,
                                          followers, selected_history,
                                          new_epoch, restart, state,
                                          last_epoch, last_leader, history,
                                          zxid, candidate_, delivered >>

HandleCommitMessage(self) == /\ pc[self] = "HandleCommitMessage"
                             /\ IF message[self].type = COMMIT_LD
                                   THEN /\ delivered' = [delivered EXCEPT ![self] = delivered[self] \union {history[self]}]
                                        /\ pc' = [pc EXCEPT ![self] = "End_F"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "GetCommitMessage"]
                                        /\ UNCHANGED delivered
                             /\ UNCHANGED << messages, stack, message_,
                                             confirmed_, message, i, confirmed,
                                             candidate, restart_, followers,
                                             selected_history, new_epoch,
                                             restart, state, last_epoch,
                                             last_leader, history, zxid,
                                             candidate_ >>

End_F(self) == /\ pc[self] = "End_F"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << messages, message_, confirmed_, message, i,
                               confirmed, candidate, restart_, followers,
                               selected_history, new_epoch, restart, state,
                               last_epoch, last_leader, history, zxid,
                               candidate_, delivered >>

FP2(self) == GetNewLeaderMessage(self) \/ HandleNewLeaderMessage(self)
                \/ GetCommitMessage(self) \/ HandleCommitMessage(self)
                \/ End_F(self)

LP2Start(self) == /\ pc[self] = "LP2Start"
                  /\ Assert(IsQuorum(followers[self], Servers),
                            "Failure of assertion at line 209, column 9.")
                  /\ i' = [i EXCEPT ![self] = 1]
                  /\ pc' = [pc EXCEPT ![self] = "NewLeader"]
                  /\ UNCHANGED << messages, stack, message_, confirmed_,
                                  message, confirmed, candidate, restart_,
                                  followers, selected_history, new_epoch,
                                  restart, state, last_epoch, last_leader,
                                  history, zxid, candidate_, delivered >>

NewLeader(self) == /\ pc[self] = "NewLeader"
                   /\ IF i[self] <= DOMAIN followers[self]
                         THEN /\ messages' = Send((followers[self][i[self]]), (NewLeaderMessage(self, new_epoch[self], selected_history[self])), messages)
                              /\ i' = [i EXCEPT ![self] = i[self]+1]
                              /\ pc' = [pc EXCEPT ![self] = "NewLeader"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "AwaitCommit"]
                              /\ UNCHANGED << messages, i >>
                   /\ UNCHANGED << stack, message_, confirmed_, message,
                                   confirmed, candidate, restart_, followers,
                                   selected_history, new_epoch, restart, state,
                                   last_epoch, last_leader, history, zxid,
                                   candidate_, delivered >>

AwaitCommit(self) == /\ pc[self] = "AwaitCommit"
                     /\ IF ~IsQuorum(confirmed[self], Servers)
                           THEN /\ pc' = [pc EXCEPT ![self] = "GetAck"]
                                /\ i' = i
                           ELSE /\ i' = [i EXCEPT ![self] = 1]
                                /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                     /\ UNCHANGED << messages, stack, message_, confirmed_,
                                     message, confirmed, candidate, restart_,
                                     followers, selected_history, new_epoch,
                                     restart, state, last_epoch, last_leader,
                                     history, zxid, candidate_, delivered >>

GetAck(self) == /\ pc[self] = "GetAck"
                /\ CanRecv(self, messages)
                /\ Assert(CanRecv(self, messages),
                          "Failure of assertion at line 88, column 5 of macro called at line 220, column 17.")
                /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                   /\ messages' = Recv(self, messages)[2]
                /\ pc' = [pc EXCEPT ![self] = "HandleAck"]
                /\ UNCHANGED << stack, message_, confirmed_, i, confirmed,
                                candidate, restart_, followers,
                                selected_history, new_epoch, restart, state,
                                last_epoch, last_leader, history, zxid,
                                candidate_, delivered >>

HandleAck(self) == /\ pc[self] = "HandleAck"
                   /\ IF message[self].type = ACK_LD
                         THEN /\ confirmed' = [confirmed EXCEPT ![self] = confirmed[self] \union {message[self].from}]
                         ELSE /\ TRUE
                              /\ UNCHANGED confirmed
                   /\ pc' = [pc EXCEPT ![self] = "AwaitCommit"]
                   /\ UNCHANGED << messages, stack, message_, confirmed_,
                                   message, i, candidate, restart_, followers,
                                   selected_history, new_epoch, restart, state,
                                   last_epoch, last_leader, history, zxid,
                                   candidate_, delivered >>

SendCommit(self) == /\ pc[self] = "SendCommit"
                    /\ IF i[self] <= DOMAIN followers[self]
                          THEN /\ messages' = Send((followers[self][i[self]]), (CommitLeaderMessage(self, new_epoch[self])), messages)
                               /\ i' = [i EXCEPT ![self] = i[self]+1]
                               /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "End_LP"]
                               /\ UNCHANGED << messages, i >>
                    /\ UNCHANGED << stack, message_, confirmed_, message,
                                    confirmed, candidate, restart_, followers,
                                    selected_history, new_epoch, restart,
                                    state, last_epoch, last_leader, history,
                                    zxid, candidate_, delivered >>

End_LP(self) == /\ pc[self] = "End_LP"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ confirmed' = [confirmed EXCEPT ![self] = Head(stack[self]).confirmed]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << messages, message_, confirmed_, message, i,
                                candidate, restart_, followers,
                                selected_history, new_epoch, restart, state,
                                last_epoch, last_leader, history, zxid,
                                candidate_, delivered >>

LP2(self) == LP2Start(self) \/ NewLeader(self) \/ AwaitCommit(self)
                \/ GetAck(self) \/ HandleAck(self) \/ SendCommit(self)
                \/ End_LP(self)

FollowerDiscover(self) == /\ pc[self] = "FollowerDiscover"
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP1",
                                                                   pc        |->  "FollowerDiscoverCheckRestart",
                                                                   message_  |->  message_[self] ] >>
                                                               \o stack[self]]
                          /\ message_' = [message_ EXCEPT ![self] = defaultInitValue]
                          /\ pc' = [pc EXCEPT ![self] = "Notify"]
                          /\ UNCHANGED << messages, confirmed_, message, i,
                                          confirmed, candidate, restart_,
                                          followers, selected_history,
                                          new_epoch, restart, state,
                                          last_epoch, last_leader, history,
                                          zxid, candidate_, delivered >>

FollowerDiscoverCheckRestart(self) == /\ pc[self] = "FollowerDiscoverCheckRestart"
                                      /\ IF restart_[self]
                                            THEN /\ pc' = [pc EXCEPT ![self] = "End_D"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "FollowerSynchronize"]
                                      /\ UNCHANGED << messages, stack,
                                                      message_, confirmed_,
                                                      message, i, confirmed,
                                                      candidate, restart_,
                                                      followers,
                                                      selected_history,
                                                      new_epoch, restart,
                                                      state, last_epoch,
                                                      last_leader, history,
                                                      zxid, candidate_,
                                                      delivered >>

FollowerSynchronize(self) == /\ pc[self] = "FollowerSynchronize"
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP2",
                                                                      pc        |->  "FollowerSynchronizeCheckRestart" ] >>
                                                                  \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "GetNewLeaderMessage"]
                             /\ UNCHANGED << messages, message_, confirmed_,
                                             message, i, confirmed, candidate,
                                             restart_, followers,
                                             selected_history, new_epoch,
                                             restart, state, last_epoch,
                                             last_leader, history, zxid,
                                             candidate_, delivered >>

FollowerSynchronizeCheckRestart(self) == /\ pc[self] = "FollowerSynchronizeCheckRestart"
                                         /\ IF restart_[self]
                                               THEN /\ pc' = [pc EXCEPT ![self] = "End_D"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "End_D"]
                                         /\ UNCHANGED << messages, stack,
                                                         message_, confirmed_,
                                                         message, i, confirmed,
                                                         candidate, restart_,
                                                         followers,
                                                         selected_history,
                                                         new_epoch, restart,
                                                         state, last_epoch,
                                                         last_leader, history,
                                                         zxid, candidate_,
                                                         delivered >>

End_D(self) == /\ pc[self] = "End_D"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ restart_' = [restart_ EXCEPT ![self] = Head(stack[self]).restart_]
               /\ candidate' = [candidate EXCEPT ![self] = Head(stack[self]).candidate]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << messages, message_, confirmed_, message, i,
                               confirmed, followers, selected_history,
                               new_epoch, restart, state, last_epoch,
                               last_leader, history, zxid, candidate_,
                               delivered >>

DoFollower(self) == FollowerDiscover(self)
                       \/ FollowerDiscoverCheckRestart(self)
                       \/ FollowerSynchronize(self)
                       \/ FollowerSynchronizeCheckRestart(self)
                       \/ End_D(self)

LeaderDiscover(self) == /\ pc[self] = "LeaderDiscover"
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP1",
                                                                 pc        |->  "LeaderDiscoverCheckRestart",
                                                                 confirmed_ |->  confirmed_[self],
                                                                 message   |->  message[self],
                                                                 i         |->  i[self] ] >>
                                                             \o stack[self]]
                        /\ confirmed_' = [confirmed_ EXCEPT ![self] = {}]
                        /\ message' = [message EXCEPT ![self] = defaultInitValue]
                        /\ i' = [i EXCEPT ![self] = defaultInitValue]
                        /\ pc' = [pc EXCEPT ![self] = "GatherQuorum"]
                        /\ UNCHANGED << messages, message_, confirmed,
                                        candidate, restart_, followers,
                                        selected_history, new_epoch, restart,
                                        state, last_epoch, last_leader,
                                        history, zxid, candidate_, delivered >>

LeaderDiscoverCheckRestart(self) == /\ pc[self] = "LeaderDiscoverCheckRestart"
                                    /\ IF restart[self]
                                          THEN /\ pc' = [pc EXCEPT ![self] = "End"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "LeaderSynchronize"]
                                    /\ UNCHANGED << messages, stack, message_,
                                                    confirmed_, message, i,
                                                    confirmed, candidate,
                                                    restart_, followers,
                                                    selected_history,
                                                    new_epoch, restart, state,
                                                    last_epoch, last_leader,
                                                    history, zxid, candidate_,
                                                    delivered >>

LeaderSynchronize(self) == /\ pc[self] = "LeaderSynchronize"
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP2",
                                                                    pc        |->  "LeaderSynchronizeCheckRestart" ] >>
                                                                \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "GetNewLeaderMessage"]
                           /\ UNCHANGED << messages, message_, confirmed_,
                                           message, i, confirmed, candidate,
                                           restart_, followers,
                                           selected_history, new_epoch,
                                           restart, state, last_epoch,
                                           last_leader, history, zxid,
                                           candidate_, delivered >>

LeaderSynchronizeCheckRestart(self) == /\ pc[self] = "LeaderSynchronizeCheckRestart"
                                       /\ IF restart[self]
                                             THEN /\ pc' = [pc EXCEPT ![self] = "End"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "End"]
                                       /\ UNCHANGED << messages, stack,
                                                       message_, confirmed_,
                                                       message, i, confirmed,
                                                       candidate, restart_,
                                                       followers,
                                                       selected_history,
                                                       new_epoch, restart,
                                                       state, last_epoch,
                                                       last_leader, history,
                                                       zxid, candidate_,
                                                       delivered >>

End(self) == /\ pc[self] = "End"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ followers' = [followers EXCEPT ![self] = Head(stack[self]).followers]
             /\ selected_history' = [selected_history EXCEPT ![self] = Head(stack[self]).selected_history]
             /\ new_epoch' = [new_epoch EXCEPT ![self] = Head(stack[self]).new_epoch]
             /\ restart' = [restart EXCEPT ![self] = Head(stack[self]).restart]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << messages, message_, confirmed_, message, i,
                             confirmed, candidate, restart_, state, last_epoch,
                             last_leader, history, zxid, candidate_, delivered >>

DoLeader(self) == LeaderDiscover(self) \/ LeaderDiscoverCheckRestart(self)
                     \/ LeaderSynchronize(self)
                     \/ LeaderSynchronizeCheckRestart(self) \/ End(self)

GetCandidate(self) == /\ pc[self] = "GetCandidate"
                      /\ candidate_' = [candidate_ EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                      /\ pc' = [pc EXCEPT ![self] = "RunRole"]
                      /\ UNCHANGED << messages, stack, message_, confirmed_,
                                      message, i, confirmed, candidate,
                                      restart_, followers, selected_history,
                                      new_epoch, restart, state, last_epoch,
                                      last_leader, history, zxid, delivered >>

RunRole(self) == /\ pc[self] = "RunRole"
                 /\ IF candidate_[self] = self
                       THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "DoLeader",
                                                                     pc        |->  "Done",
                                                                     followers |->  followers[self],
                                                                     selected_history |->  selected_history[self],
                                                                     new_epoch |->  new_epoch[self],
                                                                     restart   |->  restart[self] ] >>
                                                                 \o stack[self]]
                            /\ followers' = [followers EXCEPT ![self] = <<>>]
                            /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> 0, history |-> <<>>]]
                            /\ new_epoch' = [new_epoch EXCEPT ![self] = last_epoch[self]]
                            /\ restart' = [restart EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "LeaderDiscover"]
                            /\ UNCHANGED << candidate, restart_ >>
                       ELSE /\ /\ candidate' = [candidate EXCEPT ![self] = candidate_[self]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "DoFollower",
                                                                        pc        |->  "Done",
                                                                        restart_  |->  restart_[self],
                                                                        candidate |->  candidate[self] ] >>
                                                                    \o stack[self]]
                            /\ restart_' = [restart_ EXCEPT ![self] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "FollowerDiscover"]
                            /\ UNCHANGED << followers, selected_history,
                                            new_epoch, restart >>
                 /\ UNCHANGED << messages, message_, confirmed_, message, i,
                                 confirmed, state, last_epoch, last_leader,
                                 history, zxid, candidate_, delivered >>

server(self) == GetCandidate(self) \/ RunRole(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ FP1(self) \/ LP1(self) \/ FP2(self)
                               \/ LP2(self) \/ DoFollower(self)
                               \/ DoLeader(self))
           \/ (\E self \in Servers: server(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
