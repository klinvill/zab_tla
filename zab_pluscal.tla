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
    \* TODO: do we need a generic Message type? The paxos TLA spec uses Messages to represent the set of all possible messages, and then
    \*  introduces a TypeOK variant to check that every message is one of those types:
    \*  https://github.com/tlaplus/Examples/blob/master/specifications/PaxosHowToWinATuringAward/Paxos.tla#L67
    \* Message == CepochMessage(from, last_epoch)
    \*     \union NewEpochMessage(from, epoch)
    \*     \union AckEpochMessage(from, last_leader, history)


    \*** Other Helpers

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
procedure FP1(candidate)
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
variables followers = <<>>, \* TODO: we use a sequence since we need to be able to run the macro DoSend() for each element in it, and I don't know how to do that using sets
          confirmed = {},
          message,
          latest_epoch = last_epoch,
          selected_history = [last_leader |-> 0, history |-> <<>>],
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
                    latest_epoch := Max(latest_epoch, message.last_epoch);
                    if message.from \notin Range(followers) then
                        followers := Append(followers, message.from);
                    end if;
                end if;
        end while;

        assert IsQuorum(followers, Servers);
        i := 1;
    NewEpoch:
        while i <= DOMAIN followers do
            DoSend(followers[i], NewEpochMessage(self, latest_epoch));
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
                            /\ Last(message.history).zxid > Last(selected_history.history).zxid then
                        selected_history := [last_leader |-> message.last_leader, history |-> message.history];
                    end if;
                end if;
        end while;

    \* TODO: need to make sure that selected_history is persisted back to the process/used for phase 2
    End:
        return;
end procedure;

\* Follower Phase 2: Synchronization
procedure FP2(candidate)
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

process server \in Servers
variables state = Follower,     \* Current state of the server
          last_epoch = 0,       \* Last new epoch proposol acknowledged
          last_leader = 0,      \* Last new leader proposal acknowledged
          history,              \* In-order record of all the accepted value proposals
          \* TODO: do we really need to track zxid, or can we just use history?
          zxid = 0,             \* Zookeeper transaction ID (zxid) of last accepted transaction in the history
          candidate,            \* Candidate selected by leader oracle
          delivered = {},       \* Tracks the transactions that have been delivered to the application by Zab
          \* TODO: how should we structure the spec to be able to jump back to the beginning of the process? Right now we use a flag
          restart = FALSE;
begin
    Loop:
        restart := FALSE;
    GetCandidate:
        candidate := LeaderOracle(last_epoch + 1);
    Discover:
        if candidate = self then
            call LP1();
        else
            call FP1(Candidate);
        end if;

    DiscoverCheckRestart:
        if restart then
            goto Loop;
        end if;

    Synchronize:
        if candidate = self then
            skip;
        else
            call FP2(Candidate);
        end if;

    SynchronizeCheckRestart:
        if restart then
            goto Loop;
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e861b7be" /\ chksum(tla) = "c7d2cc96")
\* Label GetMessage of procedure FP1 at line 89 col 9 changed to GetMessage_
\* Label HandleMessage of procedure FP1 at line 92 col 9 changed to HandleMessage_
\* Label End of procedure FP1 at line 102 col 9 changed to End_
\* Label End of procedure LP1 at line 156 col 9 changed to End_L
\* Process variable candidate of process server at line 204 col 11 changed to candidate_
\* Procedure variable message of procedure FP1 at line 84 col 10 changed to message_
\* Parameter candidate of procedure FP1 at line 83 col 15 changed to candidate_F
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










IsQuorum(subset, set) == 2 * Cardinality(subset) > Cardinality(set)

Max(a, b) == IF b > a THEN b ELSE a

Range(seq) == {seq[i] : i \in DOMAIN seq}

Last(seq) == seq[Len(seq)]






LeaderOracle(epoch) == CHOOSE s \in Servers : TRUE

VARIABLES candidate_F, message_, followers, confirmed, message, latest_epoch,
          selected_history, i, candidate, state, last_epoch, last_leader,
          history, zxid, candidate_, delivered, restart

vars == << messages, pc, stack, candidate_F, message_, followers, confirmed,
           message, latest_epoch, selected_history, i, candidate, state,
           last_epoch, last_leader, history, zxid, candidate_, delivered,
           restart >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ messages = [s \in Servers |-> <<>>]
        (* Procedure FP1 *)
        /\ candidate_F = [ self \in ProcSet |-> defaultInitValue]
        /\ message_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure LP1 *)
        /\ followers = [ self \in ProcSet |-> <<>>]
        /\ confirmed = [ self \in ProcSet |-> {}]
        /\ message = [ self \in ProcSet |-> defaultInitValue]
        /\ latest_epoch = [ self \in ProcSet |-> last_epoch[self]]
        /\ selected_history = [ self \in ProcSet |-> [last_leader |-> 0, history |-> <<>>]]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure FP2 *)
        /\ candidate = [ self \in ProcSet |-> defaultInitValue]
        (* Process server *)
        /\ state = [self \in Servers |-> Follower]
        /\ last_epoch = [self \in Servers |-> 0]
        /\ last_leader = [self \in Servers |-> 0]
        /\ history = [self \in Servers |-> defaultInitValue]
        /\ zxid = [self \in Servers |-> 0]
        /\ candidate_ = [self \in Servers |-> defaultInitValue]
        /\ delivered = [self \in Servers |-> {}]
        /\ restart = [self \in Servers |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Loop"]

Notify(self) == /\ pc[self] = "Notify"
                /\ messages' = Send(candidate_F[self], (CepochMessage(self, last_epoch[self])), messages)
                /\ pc' = [pc EXCEPT ![self] = "GetMessage_"]
                /\ UNCHANGED << stack, candidate_F, message_, followers,
                                confirmed, message, latest_epoch,
                                selected_history, i, candidate, state,
                                last_epoch, last_leader, history, zxid,
                                candidate_, delivered, restart >>

GetMessage_(self) == /\ pc[self] = "GetMessage_"
                     /\ CanRecv(self, messages)
                     /\ Assert(CanRecv(self, messages),
                               "Failure of assertion at line 77, column 5 of macro called at line 90, column 9.")
                     /\ /\ message_' = [message_ EXCEPT ![self] = Recv(self, messages)[1]]
                        /\ messages' = Recv(self, messages)[2]
                     /\ pc' = [pc EXCEPT ![self] = "HandleMessage_"]
                     /\ UNCHANGED << stack, candidate_F, followers, confirmed,
                                     message, latest_epoch, selected_history,
                                     i, candidate, state, last_epoch,
                                     last_leader, history, zxid, candidate_,
                                     delivered, restart >>

HandleMessage_(self) == /\ pc[self] = "HandleMessage_"
                        /\ IF message_[self].type = NEWEPOCH /\ message_[self].from = candidate_F[self]
                              THEN /\ IF last_epoch[self] < message_[self].epoch
                                         THEN /\ last_epoch' = [last_epoch EXCEPT ![self] = message_[self].epoch]
                                              /\ messages' = Send(candidate_F[self], (AckEpochMessage(self, last_leader[self], history[self])), messages)
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << messages,
                                                              last_epoch >>
                                   /\ pc' = [pc EXCEPT ![self] = "End_"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "GetMessage_"]
                                   /\ UNCHANGED << messages, last_epoch >>
                        /\ UNCHANGED << stack, candidate_F, message_,
                                        followers, confirmed, message,
                                        latest_epoch, selected_history, i,
                                        candidate, state, last_leader, history,
                                        zxid, candidate_, delivered, restart >>

End_(self) == /\ pc[self] = "End_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ message_' = [message_ EXCEPT ![self] = Head(stack[self]).message_]
              /\ candidate_F' = [candidate_F EXCEPT ![self] = Head(stack[self]).candidate_F]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << messages, followers, confirmed, message,
                              latest_epoch, selected_history, i, candidate,
                              state, last_epoch, last_leader, history, zxid,
                              candidate_, delivered, restart >>

FP1(self) == Notify(self) \/ GetMessage_(self) \/ HandleMessage_(self)
                \/ End_(self)

GatherQuorum(self) == /\ pc[self] = "GatherQuorum"
                      /\ IF ~IsQuorum(followers[self], Servers)
                            THEN /\ pc' = [pc EXCEPT ![self] = "GetMessage"]
                                 /\ i' = i
                            ELSE /\ Assert(IsQuorum(followers[self], Servers),
                                           "Failure of assertion at line 130, column 9.")
                                 /\ i' = [i EXCEPT ![self] = 1]
                                 /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                      /\ UNCHANGED << messages, stack, candidate_F, message_,
                                      followers, confirmed, message,
                                      latest_epoch, selected_history,
                                      candidate, state, last_epoch,
                                      last_leader, history, zxid, candidate_,
                                      delivered, restart >>

GetMessage(self) == /\ pc[self] = "GetMessage"
                    /\ CanRecv(self, messages)
                    /\ Assert(CanRecv(self, messages),
                              "Failure of assertion at line 77, column 5 of macro called at line 118, column 17.")
                    /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                       /\ messages' = Recv(self, messages)[2]
                    /\ pc' = [pc EXCEPT ![self] = "HandleMessage"]
                    /\ UNCHANGED << stack, candidate_F, message_, followers,
                                    confirmed, latest_epoch, selected_history,
                                    i, candidate, state, last_epoch,
                                    last_leader, history, zxid, candidate_,
                                    delivered, restart >>

HandleMessage(self) == /\ pc[self] = "HandleMessage"
                       /\ IF message[self].type = CEPOCH
                             THEN /\ latest_epoch' = [latest_epoch EXCEPT ![self] = Max(latest_epoch[self], message[self].last_epoch)]
                                  /\ IF message[self].from \notin Range(followers[self])
                                        THEN /\ followers' = [followers EXCEPT ![self] = Append(followers[self], message[self].from)]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED followers
                             ELSE /\ TRUE
                                  /\ UNCHANGED << followers, latest_epoch >>
                       /\ pc' = [pc EXCEPT ![self] = "GatherQuorum"]
                       /\ UNCHANGED << messages, stack, candidate_F, message_,
                                       confirmed, message, selected_history, i,
                                       candidate, state, last_epoch,
                                       last_leader, history, zxid, candidate_,
                                       delivered, restart >>

NewEpoch(self) == /\ pc[self] = "NewEpoch"
                  /\ IF i[self] <= DOMAIN followers[self]
                        THEN /\ messages' = Send((followers[self][i[self]]), (NewEpochMessage(self, latest_epoch[self])), messages)
                             /\ i' = [i EXCEPT ![self] = i[self]+1]
                             /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                             /\ UNCHANGED << messages, i >>
                  /\ UNCHANGED << stack, candidate_F, message_, followers,
                                  confirmed, message, latest_epoch,
                                  selected_history, candidate, state,
                                  last_epoch, last_leader, history, zxid,
                                  candidate_, delivered, restart >>

HistorySelection(self) == /\ pc[self] = "HistorySelection"
                          /\ IF confirmed[self] /= Range(followers[self])
                                THEN /\ pc' = [pc EXCEPT ![self] = "GetAck"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "End_L"]
                          /\ UNCHANGED << messages, stack, candidate_F,
                                          message_, followers, confirmed,
                                          message, latest_epoch,
                                          selected_history, i, candidate,
                                          state, last_epoch, last_leader,
                                          history, zxid, candidate_, delivered,
                                          restart >>

GetAck(self) == /\ pc[self] = "GetAck"
                /\ CanRecv(self, messages)
                /\ Assert(CanRecv(self, messages),
                          "Failure of assertion at line 77, column 5 of macro called at line 141, column 17.")
                /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                   /\ messages' = Recv(self, messages)[2]
                /\ pc' = [pc EXCEPT ![self] = "HandleAck"]
                /\ UNCHANGED << stack, candidate_F, message_, followers,
                                confirmed, latest_epoch, selected_history, i,
                                candidate, state, last_epoch, last_leader,
                                history, zxid, candidate_, delivered, restart >>

HandleAck(self) == /\ pc[self] = "HandleAck"
                   /\ IF message[self].type = ACK_E
                         THEN /\ confirmed' = [confirmed EXCEPT ![self] = confirmed[self] \union {message[self].from}]
                              /\ IF \/ message[self].last_leader > selected_history[self].last_leader
                                    \/  /\ message[self].last_leader = selected_history[self].last_leader
                                        /\ Last(message[self].history).zxid > Last(selected_history[self].history).zxid
                                    THEN /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> message[self].last_leader, history |-> message[self].history]]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED selected_history
                         ELSE /\ TRUE
                              /\ UNCHANGED << confirmed, selected_history >>
                   /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                   /\ UNCHANGED << messages, stack, candidate_F, message_,
                                   followers, message, latest_epoch, i,
                                   candidate, state, last_epoch, last_leader,
                                   history, zxid, candidate_, delivered,
                                   restart >>

End_L(self) == /\ pc[self] = "End_L"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ followers' = [followers EXCEPT ![self] = Head(stack[self]).followers]
               /\ confirmed' = [confirmed EXCEPT ![self] = Head(stack[self]).confirmed]
               /\ message' = [message EXCEPT ![self] = Head(stack[self]).message]
               /\ latest_epoch' = [latest_epoch EXCEPT ![self] = Head(stack[self]).latest_epoch]
               /\ selected_history' = [selected_history EXCEPT ![self] = Head(stack[self]).selected_history]
               /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << messages, candidate_F, message_, candidate,
                               state, last_epoch, last_leader, history, zxid,
                               candidate_, delivered, restart >>

LP1(self) == GatherQuorum(self) \/ GetMessage(self) \/ HandleMessage(self)
                \/ NewEpoch(self) \/ HistorySelection(self) \/ GetAck(self)
                \/ HandleAck(self) \/ End_L(self)

GetNewLeaderMessage(self) == /\ pc[self] = "GetNewLeaderMessage"
                             /\ CanRecv(self, messages)
                             /\ Assert(CanRecv(self, messages),
                                       "Failure of assertion at line 77, column 5 of macro called at line 164, column 9.")
                             /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                                /\ messages' = Recv(self, messages)[2]
                             /\ pc' = [pc EXCEPT ![self] = "HandleNewLeaderMessage"]
                             /\ UNCHANGED << stack, candidate_F, message_,
                                             followers, confirmed,
                                             latest_epoch, selected_history, i,
                                             candidate, state, last_epoch,
                                             last_leader, history, zxid,
                                             candidate_, delivered, restart >>

HandleNewLeaderMessage(self) == /\ pc[self] = "HandleNewLeaderMessage"
                                /\ IF message[self].type = NEWLEADER
                                      THEN /\ IF last_epoch[self] = message[self].epoch
                                                 THEN /\ last_leader' = [last_leader EXCEPT ![self] = message[self].epoch]
                                                      /\ history' = [history EXCEPT ![self] = message[self].inital_history]
                                                      /\ messages' = Send(candidate[self], (AckLeaderMessage(self, message[self].epoch)), messages)
                                                      /\ pc' = [pc EXCEPT ![self] = "GetCommitMessage"]
                                                      /\ UNCHANGED restart
                                                 ELSE /\ restart' = [restart EXCEPT ![self] = TRUE]
                                                      /\ pc' = [pc EXCEPT ![self] = "End"]
                                                      /\ UNCHANGED << messages,
                                                                      last_leader,
                                                                      history >>
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "GetNewLeaderMessage"]
                                           /\ UNCHANGED << messages,
                                                           last_leader,
                                                           history, restart >>
                                /\ UNCHANGED << stack, candidate_F, message_,
                                                followers, confirmed, message,
                                                latest_epoch, selected_history,
                                                i, candidate, state,
                                                last_epoch, zxid, candidate_,
                                                delivered >>

GetCommitMessage(self) == /\ pc[self] = "GetCommitMessage"
                          /\ CanRecv(self, messages)
                          /\ Assert(CanRecv(self, messages),
                                    "Failure of assertion at line 77, column 5 of macro called at line 184, column 9.")
                          /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                             /\ messages' = Recv(self, messages)[2]
                          /\ pc' = [pc EXCEPT ![self] = "HandleCommitMessage"]
                          /\ UNCHANGED << stack, candidate_F, message_,
                                          followers, confirmed, latest_epoch,
                                          selected_history, i, candidate,
                                          state, last_epoch, last_leader,
                                          history, zxid, candidate_, delivered,
                                          restart >>

HandleCommitMessage(self) == /\ pc[self] = "HandleCommitMessage"
                             /\ IF message[self].type = COMMIT_LD
                                   THEN /\ delivered' = [delivered EXCEPT ![self] = delivered[self] \union {history[self]}]
                                        /\ pc' = [pc EXCEPT ![self] = "End"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "GetCommitMessage"]
                                        /\ UNCHANGED delivered
                             /\ UNCHANGED << messages, stack, candidate_F,
                                             message_, followers, confirmed,
                                             message, latest_epoch,
                                             selected_history, i, candidate,
                                             state, last_epoch, last_leader,
                                             history, zxid, candidate_,
                                             restart >>

End(self) == /\ pc[self] = "End"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ candidate' = [candidate EXCEPT ![self] = Head(stack[self]).candidate]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << messages, candidate_F, message_, followers,
                             confirmed, message, latest_epoch,
                             selected_history, i, state, last_epoch,
                             last_leader, history, zxid, candidate_, delivered,
                             restart >>

FP2(self) == GetNewLeaderMessage(self) \/ HandleNewLeaderMessage(self)
                \/ GetCommitMessage(self) \/ HandleCommitMessage(self)
                \/ End(self)

Loop(self) == /\ pc[self] = "Loop"
              /\ restart' = [restart EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "GetCandidate"]
              /\ UNCHANGED << messages, stack, candidate_F, message_,
                              followers, confirmed, message, latest_epoch,
                              selected_history, i, candidate, state,
                              last_epoch, last_leader, history, zxid,
                              candidate_, delivered >>

GetCandidate(self) == /\ pc[self] = "GetCandidate"
                      /\ candidate_' = [candidate_ EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                      /\ pc' = [pc EXCEPT ![self] = "Discover"]
                      /\ UNCHANGED << messages, stack, candidate_F, message_,
                                      followers, confirmed, message,
                                      latest_epoch, selected_history, i,
                                      candidate, state, last_epoch,
                                      last_leader, history, zxid, delivered,
                                      restart >>

Discover(self) == /\ pc[self] = "Discover"
                  /\ IF candidate_[self] = self
                        THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP1",
                                                                      pc        |->  "DiscoverCheckRestart",
                                                                      followers |->  followers[self],
                                                                      confirmed |->  confirmed[self],
                                                                      message   |->  message[self],
                                                                      latest_epoch |->  latest_epoch[self],
                                                                      selected_history |->  selected_history[self],
                                                                      i         |->  i[self] ] >>
                                                                  \o stack[self]]
                             /\ followers' = [followers EXCEPT ![self] = <<>>]
                             /\ confirmed' = [confirmed EXCEPT ![self] = {}]
                             /\ message' = [message EXCEPT ![self] = defaultInitValue]
                             /\ latest_epoch' = [latest_epoch EXCEPT ![self] = last_epoch[self]]
                             /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> 0, history |-> <<>>]]
                             /\ i' = [i EXCEPT ![self] = defaultInitValue]
                             /\ pc' = [pc EXCEPT ![self] = "GatherQuorum"]
                             /\ UNCHANGED << candidate_F, message_ >>
                        ELSE /\ /\ candidate_F' = [candidate_F EXCEPT ![self] = Candidate]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP1",
                                                                         pc        |->  "DiscoverCheckRestart",
                                                                         message_  |->  message_[self],
                                                                         candidate_F |->  candidate_F[self] ] >>
                                                                     \o stack[self]]
                             /\ message_' = [message_ EXCEPT ![self] = defaultInitValue]
                             /\ pc' = [pc EXCEPT ![self] = "Notify"]
                             /\ UNCHANGED << followers, confirmed, message,
                                             latest_epoch, selected_history, i >>
                  /\ UNCHANGED << messages, candidate, state, last_epoch,
                                  last_leader, history, zxid, candidate_,
                                  delivered, restart >>

DiscoverCheckRestart(self) == /\ pc[self] = "DiscoverCheckRestart"
                              /\ IF restart[self]
                                    THEN /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "Synchronize"]
                              /\ UNCHANGED << messages, stack, candidate_F,
                                              message_, followers, confirmed,
                                              message, latest_epoch,
                                              selected_history, i, candidate,
                                              state, last_epoch, last_leader,
                                              history, zxid, candidate_,
                                              delivered, restart >>

Synchronize(self) == /\ pc[self] = "Synchronize"
                     /\ IF candidate_[self] = self
                           THEN /\ TRUE
                                /\ pc' = [pc EXCEPT ![self] = "SynchronizeCheckRestart"]
                                /\ UNCHANGED << stack, candidate >>
                           ELSE /\ /\ candidate' = [candidate EXCEPT ![self] = Candidate]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP2",
                                                                            pc        |->  "SynchronizeCheckRestart",
                                                                            candidate |->  candidate[self] ] >>
                                                                        \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "GetNewLeaderMessage"]
                     /\ UNCHANGED << messages, candidate_F, message_,
                                     followers, confirmed, message,
                                     latest_epoch, selected_history, i, state,
                                     last_epoch, last_leader, history, zxid,
                                     candidate_, delivered, restart >>

SynchronizeCheckRestart(self) == /\ pc[self] = "SynchronizeCheckRestart"
                                 /\ IF restart[self]
                                       THEN /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED << messages, stack, candidate_F,
                                                 message_, followers,
                                                 confirmed, message,
                                                 latest_epoch,
                                                 selected_history, i,
                                                 candidate, state, last_epoch,
                                                 last_leader, history, zxid,
                                                 candidate_, delivered,
                                                 restart >>

server(self) == Loop(self) \/ GetCandidate(self) \/ Discover(self)
                   \/ DiscoverCheckRestart(self) \/ Synchronize(self)
                   \/ SynchronizeCheckRestart(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: FP1(self) \/ LP1(self) \/ FP2(self))
           \/ (\E self \in Servers: server(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
