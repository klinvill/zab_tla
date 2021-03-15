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
            DoSend(followers[i], NewEpochMessage(self, epoch));
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

process server \in Servers
variables state = Follower,    \* Current state of the server
          last_epoch = 0,      \* Last new epoch proposol acknowledged
          last_leader = 0,     \* Last new leader proposal acknowledged
          history,              \* In-order record of all the accepted value proposals
          \* TODO: do we really need to track zxid, or can we just use history?
          zxid = 0,            \* Zookeeper transaction ID (zxid) of last accepted transaction in the history
          candidate;            \* Candidate selected by leader oracle
begin
    GetCandidate:
        candidate := LeaderOracle(last_epoch + 1);
    Discover:
        if candidate /= self then
            call FP1(Candidate);
        else
            call LP1();
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e714bf92" /\ chksum(tla) = "38cf4122")
\* Label GetMessage of procedure FP1 at line 86 col 9 changed to GetMessage_
\* Label HandleMessage of procedure FP1 at line 89 col 9 changed to HandleMessage_
\* Label End of procedure FP1 at line 99 col 9 changed to End_
\* Process variable candidate of process server at line 163 col 11 changed to candidate_
\* Procedure variable message of procedure FP1 at line 81 col 10 changed to message_
CONSTANT defaultInitValue
VARIABLES messages, pc, stack

(* define statement *)
Send(to, m, _messages) == [_messages EXCEPT ![to] = Append(_messages[to], m)]


Recv(server, _messages) == <<Head(_messages[server]), [_messages EXCEPT ![server] = Tail(_messages[server])]>>

CanRecv(server, _messages) == Len(_messages[server]) > 0


CepochMessage(from, last_epoch) == [from |-> from, type |-> CEPOCH, last_epoch |-> last_epoch]
NewEpochMessage(from, epoch) == [from |-> from, type |-> NEWEPOCH, epoch |-> epoch]
AckEpochMessage(from, last_leader, history) == [from |-> from, type |-> ACK_E, last_leader |-> last_leader, history |-> history]










IsQuorum(subset, set) == 2 * Cardinality(subset) > Cardinality(set)

Max(a, b) == IF b > a THEN b ELSE a

Range(seq) == {seq[i] : i \in DOMAIN seq}

Last(seq) == seq[Len(seq)]






LeaderOracle(epoch) == CHOOSE s \in Servers : TRUE

VARIABLES candidate, message_, followers, confirmed, message, latest_epoch,
          selected_history, i, state, last_epoch, last_leader, history, zxid,
          candidate_

vars == << messages, pc, stack, candidate, message_, followers, confirmed,
           message, latest_epoch, selected_history, i, state, last_epoch,
           last_leader, history, zxid, candidate_ >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ messages = [s \in Servers |-> <<>>]
        (* Procedure FP1 *)
        /\ candidate = [ self \in ProcSet |-> defaultInitValue]
        /\ message_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure LP1 *)
        /\ followers = [ self \in ProcSet |-> <<>>]
        /\ confirmed = [ self \in ProcSet |-> {}]
        /\ message = [ self \in ProcSet |-> defaultInitValue]
        /\ latest_epoch = [ self \in ProcSet |-> last_epoch[self]]
        /\ selected_history = [ self \in ProcSet |-> [last_leader |-> 0, history |-> <<>>]]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        (* Process server *)
        /\ state = [self \in Servers |-> Follower]
        /\ last_epoch = [self \in Servers |-> 0]
        /\ last_leader = [self \in Servers |-> 0]
        /\ history = [self \in Servers |-> defaultInitValue]
        /\ zxid = [self \in Servers |-> 0]
        /\ candidate_ = [self \in Servers |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "GetCandidate"]

Notify(self) == /\ pc[self] = "Notify"
                /\ messages' = Send(candidate[self], (CepochMessage(self, last_epoch[self])), messages)
                /\ pc' = [pc EXCEPT ![self] = "GetMessage_"]
                /\ UNCHANGED << stack, candidate, message_, followers,
                                confirmed, message, latest_epoch,
                                selected_history, i, state, last_epoch,
                                last_leader, history, zxid, candidate_ >>

GetMessage_(self) == /\ pc[self] = "GetMessage_"
                     /\ CanRecv(self, messages)
                     /\ Assert(CanRecv(self, messages),
                               "Failure of assertion at line 74, column 5 of macro called at line 87, column 9.")
                     /\ /\ message_' = [message_ EXCEPT ![self] = Recv(self, messages)[1]]
                        /\ messages' = Recv(self, messages)[2]
                     /\ pc' = [pc EXCEPT ![self] = "HandleMessage_"]
                     /\ UNCHANGED << stack, candidate, followers, confirmed,
                                     message, latest_epoch, selected_history,
                                     i, state, last_epoch, last_leader,
                                     history, zxid, candidate_ >>

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
                        /\ UNCHANGED << stack, candidate, message_, followers,
                                        confirmed, message, latest_epoch,
                                        selected_history, i, state,
                                        last_leader, history, zxid, candidate_ >>

End_(self) == /\ pc[self] = "End_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ message_' = [message_ EXCEPT ![self] = Head(stack[self]).message_]
              /\ candidate' = [candidate EXCEPT ![self] = Head(stack[self]).candidate]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << messages, followers, confirmed, message,
                              latest_epoch, selected_history, i, state,
                              last_epoch, last_leader, history, zxid,
                              candidate_ >>

FP1(self) == Notify(self) \/ GetMessage_(self) \/ HandleMessage_(self)
                \/ End_(self)

GatherQuorum(self) == /\ pc[self] = "GatherQuorum"
                      /\ IF ~IsQuorum(followers[self], Servers)
                            THEN /\ pc' = [pc EXCEPT ![self] = "GetMessage"]
                                 /\ i' = i
                            ELSE /\ Assert(IsQuorum(followers[self], Servers),
                                           "Failure of assertion at line 127, column 9.")
                                 /\ i' = [i EXCEPT ![self] = 1]
                                 /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                      /\ UNCHANGED << messages, stack, candidate, message_,
                                      followers, confirmed, message,
                                      latest_epoch, selected_history, state,
                                      last_epoch, last_leader, history, zxid,
                                      candidate_ >>

GetMessage(self) == /\ pc[self] = "GetMessage"
                    /\ CanRecv(self, messages)
                    /\ Assert(CanRecv(self, messages),
                              "Failure of assertion at line 74, column 5 of macro called at line 115, column 17.")
                    /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                       /\ messages' = Recv(self, messages)[2]
                    /\ pc' = [pc EXCEPT ![self] = "HandleMessage"]
                    /\ UNCHANGED << stack, candidate, message_, followers,
                                    confirmed, latest_epoch, selected_history,
                                    i, state, last_epoch, last_leader, history,
                                    zxid, candidate_ >>

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
                       /\ UNCHANGED << messages, stack, candidate, message_,
                                       confirmed, message, selected_history, i,
                                       state, last_epoch, last_leader, history,
                                       zxid, candidate_ >>

NewEpoch(self) == /\ pc[self] = "NewEpoch"
                  /\ IF i[self] <= DOMAIN followers[self]
                        THEN /\ messages' = Send((followers[self][i[self]]), (NewEpochMessage(self, epoch)), messages)
                             /\ i' = [i EXCEPT ![self] = i[self]+1]
                             /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                             /\ UNCHANGED << messages, i >>
                  /\ UNCHANGED << stack, candidate, message_, followers,
                                  confirmed, message, latest_epoch,
                                  selected_history, state, last_epoch,
                                  last_leader, history, zxid, candidate_ >>

HistorySelection(self) == /\ pc[self] = "HistorySelection"
                          /\ IF confirmed[self] /= Range(followers[self])
                                THEN /\ pc' = [pc EXCEPT ![self] = "GetAck"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "End"]
                          /\ UNCHANGED << messages, stack, candidate, message_,
                                          followers, confirmed, message,
                                          latest_epoch, selected_history, i,
                                          state, last_epoch, last_leader,
                                          history, zxid, candidate_ >>

GetAck(self) == /\ pc[self] = "GetAck"
                /\ CanRecv(self, messages)
                /\ Assert(CanRecv(self, messages),
                          "Failure of assertion at line 74, column 5 of macro called at line 138, column 17.")
                /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                   /\ messages' = Recv(self, messages)[2]
                /\ pc' = [pc EXCEPT ![self] = "HandleAck"]
                /\ UNCHANGED << stack, candidate, message_, followers,
                                confirmed, latest_epoch, selected_history, i,
                                state, last_epoch, last_leader, history, zxid,
                                candidate_ >>

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
                   /\ UNCHANGED << messages, stack, candidate, message_,
                                   followers, message, latest_epoch, i, state,
                                   last_epoch, last_leader, history, zxid,
                                   candidate_ >>

End(self) == /\ pc[self] = "End"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ followers' = [followers EXCEPT ![self] = Head(stack[self]).followers]
             /\ confirmed' = [confirmed EXCEPT ![self] = Head(stack[self]).confirmed]
             /\ message' = [message EXCEPT ![self] = Head(stack[self]).message]
             /\ latest_epoch' = [latest_epoch EXCEPT ![self] = Head(stack[self]).latest_epoch]
             /\ selected_history' = [selected_history EXCEPT ![self] = Head(stack[self]).selected_history]
             /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << messages, candidate, message_, state, last_epoch,
                             last_leader, history, zxid, candidate_ >>

LP1(self) == GatherQuorum(self) \/ GetMessage(self) \/ HandleMessage(self)
                \/ NewEpoch(self) \/ HistorySelection(self) \/ GetAck(self)
                \/ HandleAck(self) \/ End(self)

GetCandidate(self) == /\ pc[self] = "GetCandidate"
                      /\ candidate_' = [candidate_ EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                      /\ pc' = [pc EXCEPT ![self] = "Discover"]
                      /\ UNCHANGED << messages, stack, candidate, message_,
                                      followers, confirmed, message,
                                      latest_epoch, selected_history, i, state,
                                      last_epoch, last_leader, history, zxid >>

Discover(self) == /\ pc[self] = "Discover"
                  /\ IF candidate_[self] /= self
                        THEN /\ /\ candidate' = [candidate EXCEPT ![self] = Candidate]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP1",
                                                                         pc        |->  "Done",
                                                                         message_  |->  message_[self],
                                                                         candidate |->  candidate[self] ] >>
                                                                     \o stack[self]]
                             /\ message_' = [message_ EXCEPT ![self] = defaultInitValue]
                             /\ pc' = [pc EXCEPT ![self] = "Notify"]
                             /\ UNCHANGED << followers, confirmed, message,
                                             latest_epoch, selected_history, i >>
                        ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP1",
                                                                      pc        |->  "Done",
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
                             /\ UNCHANGED << candidate, message_ >>
                  /\ UNCHANGED << messages, state, last_epoch, last_leader,
                                  history, zxid, candidate_ >>

server(self) == GetCandidate(self) \/ Discover(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: FP1(self) \/ LP1(self))
           \/ (\E self \in Servers: server(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
