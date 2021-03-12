---- MODULE zab_pluscal ----

EXTENDS Sequences, Integers, TLC


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

    Message(from, type, contents) == [from |-> from, type |-> type, contents |-> contents]


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
        DoSend(candidate, Message(self, CEPOCH, [last_epoch |-> last_epoch]));
    GetMessage:
        await CanRecv(self, messages);
        DoRecv();
    HandleMessage:
        if message.type = NEWEPOCH /\ message.from = candidate then
            if last_epoch < message.epoch then
                last_epoch := message.epoch;
                DoSend(candidate, Message(self, ACK_E, [last_leader |-> last_leader, history |-> history]));
            end if;
        else
            \* TODO: under what conditions should we not check for the next message, e.g. restart leader election?
            goto GetMessage;
        end if;
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
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "694bda9e" /\ chksum(tla) = "b4a242a")
\* Process variable candidate of process server at line 89 col 11 changed to candidate_
CONSTANT defaultInitValue
VARIABLES messages, pc, stack

(* define statement *)
Send(to, m, _messages) == [_messages EXCEPT ![to] = Append(_messages[to], m)]


Recv(server, _messages) == <<Head(_messages[server]), [_messages EXCEPT ![server] = Tail(_messages[server])]>>

CanRecv(server, _messages) == Len(_messages[server]) > 0

Message(from, type, contents) == [from |-> from, type |-> type, contents |-> contents]






LeaderOracle(epoch) == CHOOSE s \in Servers : TRUE

VARIABLES candidate, message, state, last_epoch, last_leader, history, zxid,
          candidate_

vars == << messages, pc, stack, candidate, message, state, last_epoch,
           last_leader, history, zxid, candidate_ >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ messages = [s \in Servers |-> <<>>]
        (* Procedure FP1 *)
        /\ candidate = [ self \in ProcSet |-> defaultInitValue]
        /\ message = [ self \in ProcSet |-> defaultInitValue]
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
                /\ messages' = Send(candidate[self], (Message(self, CEPOCH, [last_epoch |-> last_epoch[self]])), messages)
                /\ pc' = [pc EXCEPT ![self] = "GetMessage"]
                /\ UNCHANGED << stack, candidate, message, state, last_epoch,
                                last_leader, history, zxid, candidate_ >>

GetMessage(self) == /\ pc[self] = "GetMessage"
                    /\ CanRecv(self, messages)
                    /\ Assert(CanRecv(self, messages),
                              "Failure of assertion at line 54, column 5 of macro called at line 67, column 9.")
                    /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                       /\ messages' = Recv(self, messages)[2]
                    /\ pc' = [pc EXCEPT ![self] = "HandleMessage"]
                    /\ UNCHANGED << stack, candidate, state, last_epoch,
                                    last_leader, history, zxid, candidate_ >>

HandleMessage(self) == /\ pc[self] = "HandleMessage"
                       /\ IF message[self].type = NEWEPOCH /\ message[self].from = candidate[self]
                             THEN /\ IF last_epoch[self] < message[self].epoch
                                        THEN /\ last_epoch' = [last_epoch EXCEPT ![self] = message[self].epoch]
                                             /\ messages' = Send(candidate[self], (Message(self, ACK_E, [last_leader |-> last_leader[self], history |-> history[self]])), messages)
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << messages,
                                                             last_epoch >>
                                  /\ pc' = [pc EXCEPT ![self] = "End"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "GetMessage"]
                                  /\ UNCHANGED << messages, last_epoch >>
                       /\ UNCHANGED << stack, candidate, message, state,
                                       last_leader, history, zxid, candidate_ >>

End(self) == /\ pc[self] = "End"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ message' = [message EXCEPT ![self] = Head(stack[self]).message]
             /\ candidate' = [candidate EXCEPT ![self] = Head(stack[self]).candidate]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << messages, state, last_epoch, last_leader, history,
                             zxid, candidate_ >>

FP1(self) == Notify(self) \/ GetMessage(self) \/ HandleMessage(self)
                \/ End(self)

GetCandidate(self) == /\ pc[self] = "GetCandidate"
                      /\ candidate_' = [candidate_ EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                      /\ pc' = [pc EXCEPT ![self] = "Discover"]
                      /\ UNCHANGED << messages, stack, candidate, message,
                                      state, last_epoch, last_leader, history,
                                      zxid >>

Discover(self) == /\ pc[self] = "Discover"
                  /\ IF candidate_[self] /= self
                        THEN /\ /\ candidate' = [candidate EXCEPT ![self] = Candidate]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP1",
                                                                         pc        |->  "Done",
                                                                         message   |->  message[self],
                                                                         candidate |->  candidate[self] ] >>
                                                                     \o stack[self]]
                             /\ message' = [message EXCEPT ![self] = defaultInitValue]
                             /\ pc' = [pc EXCEPT ![self] = "Notify"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << stack, candidate, message >>
                  /\ UNCHANGED << messages, state, last_epoch, last_leader,
                                  history, zxid, candidate_ >>

server(self) == GetCandidate(self) \/ Discover(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: FP1(self))
           \/ (\E self \in Servers: server(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
