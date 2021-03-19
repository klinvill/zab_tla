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

\* Leader steps, correspond to those in "Dissecting Zab"
\* Phase 1: Discovery
CONSTANTS LS_1_1
CONSTANTS LS_1_2
\* Phase 2: Synchronization
CONSTANTS LS_2_1
CONSTANTS LS_2_2
\* Phase 3: Broadcast
CONSTANTS LS_3_1
CONSTANTS LS_3_2
CONSTANTS LS_3_3
CONSTANTS LS_3_4

\* Follower steps, correspond to those in "Dissecting Zab"
\* Phase 1: Discovery
CONSTANTS FS_1_1
CONSTANTS FS_1_2
\* Phase 2: Synchronization
CONSTANTS FS_2_1
CONSTANTS FS_2_2
\* Phase 3: Broadcast
CONSTANTS FS_3_1
CONSTANTS FS_3_2
CONSTANTS FS_3_3


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
\* Follower Phase 1 Step 1
procedure FP1_1()
begin
    Notify:
        DoSend(candidate, CepochMessage(self, last_epoch));
        \* completed, move to next step
        follower_step := FS_1_2;
        return;
end procedure;

\* Follower Phase 1 Step 2
procedure FP1_2()
variable message;
begin
    GetMessage:
        DoRecv();
        assert message.type = NEWEPOCH /\ message.from = candidate;
    HandleMessage:
        if last_epoch < message.epoch then
            last_epoch := message.epoch;
            DoSend(candidate, AckEpochMessage(self, last_leader, history));
            \* completed, move to next step
            follower_step := FS_2_1;
        end if;
        return;
end procedure;

\* Leader Phase 1: Discovery
\* Leader Phase 1 Step 1
procedure LP1_1()
variables message,
          i;
begin
    GetMessage:
        DoRecv();
        assert message.type = CEPOCH;
    HandleMessage:
        \* latest epoch seen by followers in quorum
        new_epoch := Max(new_epoch, message.last_epoch);
        if message.from \notin Range(followers) then
            followers := Append(followers, message.from);
        end if;

        if IsQuorum(followers, Servers) then
            i := 1;
            NewEpoch:
                while i <= DOMAIN followers do
                    DoSend(followers[i], NewEpochMessage(self, new_epoch));
                    i := i+1;
                end while;
                leader_step := LS_1_2;
        end if;
    EndLP1_1:
        return;
end procedure;

\* Leader Phase 1 Step 2
procedure LP1_2()
variables message,
          i;
begin
    GetMessage:
        DoRecv();
        assert message.type = ACK_E /\ message.epoch = new_epoch;
    HistorySelection:
        ackd_e := ackd_e \union {message.from};

        if  \/ message.last_leader > selected_history.last_leader
            \/  /\ message.last_leader = selected_history.last_leader
                /\ ZxidGreaterThan(Last(message.history).zxid, Last(selected_history.history).zxid) then
            selected_history := [last_leader |-> message.last_leader, history |-> message.history];
        end if;

    CheckAllAckd:
        if ackd_e = Range(followers) then
            leader_step := LS_2_1;
        end if;
    return;
end procedure;

\* Follower Phase 2: Synchronization
\* Follower Phase 2 Step 1
procedure FP2_1()
variables message;
begin
    GetNewLeaderMessage:
        DoRecv();
        assert message.type = NEWLEADER /\ message.from = candidate;
    HandleNewLeaderMessage:
        if last_epoch = message.epoch then
            last_leader := message.epoch;
            \* TODO: do we need to separately accept each value, zxid pair? Or can we just set the history
            history := message.inital_history;
            DoSend(candidate, AckLeaderMessage(self, message.epoch));
            follower_step := FS_2_2;
        else
            \* should start the protocol over again if the last acknowledged epoch proposal is different than the specified epoch
            restart := TRUE;
        end if;
    return;
end procedure;

\* Follower Phase 2 Step 2
procedure FP2_2()
variables message;
begin
    GetCommitMessage:
        DoRecv();
        assert message.type = COMMIT_LD /\ message.from = candidate;
    HandleCommitMessage:
        \* TODO: should delivered be a tuple since the transactions in a history should be delivered in-order?
        delivered := delivered \union {history};
        follower_step := FS_3_1;
    return;
end procedure;

\* Leader Phase 2: Synchronization
\* Leader Phase 2 Step 1
procedure LP2_1()
variables i;
begin
    LP2Start:
        assert IsQuorum(followers, Servers);
        i := 1;
    NewLeader:
        while i <= DOMAIN followers do
            DoSend(followers[i], NewLeaderMessage(self, new_epoch, selected_history));
            i := i+1;
        end while;
        leader_step := LS_2_2;
    return;
end procedure;

\* Leader Phase 2 Step 2
procedure LP2_2()
variables message,
          i;
begin
    GetAckMessage:
        DoRecv();
        assert message.type = ACK_LD /\ message.epoch = new_epoch;
    HandleAck:
        ackd_ld := ackd_ld \union {message.from};
        if IsQuorum(ackd_ld, Servers) then
            i := 1;
            SendCommit:
                while i <= DOMAIN followers do
                    DoSend(followers[i], CommitLeaderMessage(self, new_epoch));
                    i := i+1;
                end while;
                leader_step := LS_3_1;
        end if;
    EndLP2_2:
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
          \* TODO: the "Dissecting Zab" report calls this set "txns", should we match that convention?
          delivered = {},       \* Tracks the transactions that have been delivered to the application by Zab
          follower_step = FS_1_1,

          \** Leader Variables
          followers = <<>>,     \* tracks the followers committed to a leader
          selected_history = [last_leader |-> 0, history |-> <<>>],     \* tracks the selected initial history
          new_epoch = last_epoch,
          ackd_e = {},          \* tracks the followers that have sent acks for a CEPOCH message
          ackd_ld = {},         \* tracks the followers that have sent acks for a NEWLEADER message
          leader_step = LS_1_1,

          \** Other Variables
          restart = FALSE;      \* used to detect when a new iteration should be started
begin
    GetCandidate:
        \* TODO: there can be a leader change by the oracle at any given time. Should maybe model the oracle as another process, and have an either step that checks to see if it's changed?
        candidate := LeaderOracle(last_epoch + 1);
    RunStep:
        while TRUE do
            \*** Phase 1: Discovery
            either
                await follower_step = FS_1_1;
                call FP1_1();
            or
                \* Note: it looks like pluscal needs the await in the either statement in order to decide whether or not to enable that action. It cannot be in the procedure.
                await   /\ follower_step = FS_1_2
                        /\ CanRecv(self, messages)
                        /\ Head(messages[self]).type = NEWEPOCH
                        /\ Head(messages[self]).from = candidate;
                call FP1_2();
            or
                await   /\ candidate = self
                        /\ leader_step = LS_1_1
                        /\ CanRecv(self, messages)
                        /\ Head(messages[self]).type = CEPOCH;

                \* Reset variables used by leader
                followers := <<>>;
                selected_history := [last_leader |-> 0, history |-> <<>>];
                new_epoch := last_epoch;
                ackd_e := {};
                ackd_ld := {};

                call LP1_1();
            or
                await   /\ candidate = self
                        /\ leader_step = LS_1_2
                        /\ CanRecv(self, messages)
                        /\ Head(messages[self]).type = ACK_E
                        /\ Head(messages[self]).epoch = new_epoch;
                call LP1_2();

            \*** Phase 2: Synchronization
            or
                await   /\ follower_step = FS_2_1
                        /\ CanRecv(self, messages)
                        /\ Head(messages[self]).type = NEWLEADER
                        /\ Head(messages[self]).from = candidate;
                call FP2_1();
                CheckRestart:
                    if restart then
                        follower_step := FS_1_1;
                    end if;
            or
                await   /\ follower_step = FS_2_1
                        /\ CanRecv(self, messages)
                        /\ Head(messages[self]).type = COMMIT_LD
                        /\ Head(messages[self]).from = candidate;
                call FP2_2();
            or
                await   /\ candidate = self
                        /\ leader_step = LS_2_1;

                call LP2_1();
            or
                await   /\ candidate = self
                        /\ leader_step = LS_2_2
                        /\ CanRecv(self, messages)
                        /\ Head(messages[self]).type = ACK_LD
                        /\ Head(messages[self]).epoch = new_epoch;
                call LP2_2();
            end either;
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1e21f588" /\ chksum(tla) = "91ce9325")
\* Label GetMessage of procedure FP1_2 at line 113 col 5 changed to GetMessage_
\* Label HandleMessage of procedure FP1_2 at line 137 col 9 changed to HandleMessage_
\* Label GetMessage of procedure LP1_1 at line 113 col 5 changed to GetMessage_L
\* Procedure variable message of procedure FP1_2 at line 131 col 10 changed to message_
\* Procedure variable message of procedure LP1_1 at line 149 col 11 changed to message_L
\* Procedure variable i of procedure LP1_1 at line 150 col 11 changed to i_
\* Procedure variable message of procedure LP1_2 at line 177 col 11 changed to message_LP
\* Procedure variable i of procedure LP1_2 at line 178 col 11 changed to i_L
\* Procedure variable message of procedure FP2_1 at line 202 col 11 changed to message_F
\* Procedure variable message of procedure FP2_2 at line 223 col 11 changed to message_FP
\* Procedure variable i of procedure LP2_1 at line 238 col 11 changed to i_LP
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

VARIABLES message_, message_L, i_, message_LP, i_L, message_F, message_FP,
          i_LP, message, i, state, last_epoch, last_leader, history, zxid,
          candidate, delivered, follower_step, followers, selected_history,
          new_epoch, ackd_e, ackd_ld, leader_step, restart

vars == << messages, pc, stack, message_, message_L, i_, message_LP, i_L,
           message_F, message_FP, i_LP, message, i, state, last_epoch,
           last_leader, history, zxid, candidate, delivered, follower_step,
           followers, selected_history, new_epoch, ackd_e, ackd_ld,
           leader_step, restart >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ messages = [s \in Servers |-> <<>>]
        (* Procedure FP1_2 *)
        /\ message_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure LP1_1 *)
        /\ message_L = [ self \in ProcSet |-> defaultInitValue]
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure LP1_2 *)
        /\ message_LP = [ self \in ProcSet |-> defaultInitValue]
        /\ i_L = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure FP2_1 *)
        /\ message_F = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure FP2_2 *)
        /\ message_FP = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure LP2_1 *)
        /\ i_LP = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure LP2_2 *)
        /\ message = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        (* Process server *)
        /\ state = [self \in Servers |-> Follower]
        /\ last_epoch = [self \in Servers |-> 0]
        /\ last_leader = [self \in Servers |-> 0]
        /\ history = [self \in Servers |-> defaultInitValue]
        /\ zxid = [self \in Servers |-> Zxid(0, 0)]
        /\ candidate = [self \in Servers |-> defaultInitValue]
        /\ delivered = [self \in Servers |-> {}]
        /\ follower_step = [self \in Servers |-> FS_1_1]
        /\ followers = [self \in Servers |-> <<>>]
        /\ selected_history = [self \in Servers |-> [last_leader |-> 0, history |-> <<>>]]
        /\ new_epoch = [self \in Servers |-> last_epoch[self]]
        /\ ackd_e = [self \in Servers |-> {}]
        /\ ackd_ld = [self \in Servers |-> {}]
        /\ leader_step = [self \in Servers |-> LS_1_1]
        /\ restart = [self \in Servers |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "GetCandidate"]

Notify(self) == /\ pc[self] = "Notify"
                /\ messages' = Send(candidate[self], (CepochMessage(self, last_epoch[self])), messages)
                /\ follower_step' = [follower_step EXCEPT ![self] = FS_1_2]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << message_, message_L, i_, message_LP, i_L,
                                message_F, message_FP, i_LP, message, i, state,
                                last_epoch, last_leader, history, zxid,
                                candidate, delivered, followers,
                                selected_history, new_epoch, ackd_e, ackd_ld,
                                leader_step, restart >>

FP1_1(self) == Notify(self)

GetMessage_(self) == /\ pc[self] = "GetMessage_"
                     /\ Assert(CanRecv(self, messages),
                               "Failure of assertion at line 113, column 5 of macro called at line 134, column 9.")
                     /\ /\ message_' = [message_ EXCEPT ![self] = Recv(self, messages)[1]]
                        /\ messages' = Recv(self, messages)[2]
                     /\ Assert(message_'[self].type = NEWEPOCH /\ message_'[self].from = candidate[self],
                               "Failure of assertion at line 135, column 9.")
                     /\ pc' = [pc EXCEPT ![self] = "HandleMessage_"]
                     /\ UNCHANGED << stack, message_L, i_, message_LP, i_L,
                                     message_F, message_FP, i_LP, message, i,
                                     state, last_epoch, last_leader, history,
                                     zxid, candidate, delivered, follower_step,
                                     followers, selected_history, new_epoch,
                                     ackd_e, ackd_ld, leader_step, restart >>

HandleMessage_(self) == /\ pc[self] = "HandleMessage_"
                        /\ IF last_epoch[self] < message_[self].epoch
                              THEN /\ last_epoch' = [last_epoch EXCEPT ![self] = message_[self].epoch]
                                   /\ messages' = Send(candidate[self], (AckEpochMessage(self, last_leader[self], history[self])), messages)
                                   /\ follower_step' = [follower_step EXCEPT ![self] = FS_2_1]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << messages, last_epoch,
                                                   follower_step >>
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ message_' = [message_ EXCEPT ![self] = Head(stack[self]).message_]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << message_L, i_, message_LP, i_L,
                                        message_F, message_FP, i_LP, message,
                                        i, state, last_leader, history, zxid,
                                        candidate, delivered, followers,
                                        selected_history, new_epoch, ackd_e,
                                        ackd_ld, leader_step, restart >>

FP1_2(self) == GetMessage_(self) \/ HandleMessage_(self)

GetMessage_L(self) == /\ pc[self] = "GetMessage_L"
                      /\ Assert(CanRecv(self, messages),
                                "Failure of assertion at line 113, column 5 of macro called at line 153, column 9.")
                      /\ /\ message_L' = [message_L EXCEPT ![self] = Recv(self, messages)[1]]
                         /\ messages' = Recv(self, messages)[2]
                      /\ Assert(message_L'[self].type = CEPOCH,
                                "Failure of assertion at line 154, column 9.")
                      /\ pc' = [pc EXCEPT ![self] = "HandleMessage"]
                      /\ UNCHANGED << stack, message_, i_, message_LP, i_L,
                                      message_F, message_FP, i_LP, message, i,
                                      state, last_epoch, last_leader, history,
                                      zxid, candidate, delivered,
                                      follower_step, followers,
                                      selected_history, new_epoch, ackd_e,
                                      ackd_ld, leader_step, restart >>

HandleMessage(self) == /\ pc[self] = "HandleMessage"
                       /\ new_epoch' = [new_epoch EXCEPT ![self] = Max(new_epoch[self], message_L[self].last_epoch)]
                       /\ IF message_L[self].from \notin Range(followers[self])
                             THEN /\ followers' = [followers EXCEPT ![self] = Append(followers[self], message_L[self].from)]
                             ELSE /\ TRUE
                                  /\ UNCHANGED followers
                       /\ IF IsQuorum(followers'[self], Servers)
                             THEN /\ i_' = [i_ EXCEPT ![self] = 1]
                                  /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "EndLP1_1"]
                                  /\ i_' = i_
                       /\ UNCHANGED << messages, stack, message_, message_L,
                                       message_LP, i_L, message_F, message_FP,
                                       i_LP, message, i, state, last_epoch,
                                       last_leader, history, zxid, candidate,
                                       delivered, follower_step,
                                       selected_history, ackd_e, ackd_ld,
                                       leader_step, restart >>

NewEpoch(self) == /\ pc[self] = "NewEpoch"
                  /\ IF i_[self] <= DOMAIN followers[self]
                        THEN /\ messages' = Send((followers[self][i_[self]]), (NewEpochMessage(self, new_epoch[self])), messages)
                             /\ i_' = [i_ EXCEPT ![self] = i_[self]+1]
                             /\ pc' = [pc EXCEPT ![self] = "NewEpoch"]
                             /\ UNCHANGED leader_step
                        ELSE /\ leader_step' = [leader_step EXCEPT ![self] = LS_1_2]
                             /\ pc' = [pc EXCEPT ![self] = "EndLP1_1"]
                             /\ UNCHANGED << messages, i_ >>
                  /\ UNCHANGED << stack, message_, message_L, message_LP, i_L,
                                  message_F, message_FP, i_LP, message, i,
                                  state, last_epoch, last_leader, history,
                                  zxid, candidate, delivered, follower_step,
                                  followers, selected_history, new_epoch,
                                  ackd_e, ackd_ld, restart >>

EndLP1_1(self) == /\ pc[self] = "EndLP1_1"
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ message_L' = [message_L EXCEPT ![self] = Head(stack[self]).message_L]
                  /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << messages, message_, message_LP, i_L,
                                  message_F, message_FP, i_LP, message, i,
                                  state, last_epoch, last_leader, history,
                                  zxid, candidate, delivered, follower_step,
                                  followers, selected_history, new_epoch,
                                  ackd_e, ackd_ld, leader_step, restart >>

LP1_1(self) == GetMessage_L(self) \/ HandleMessage(self) \/ NewEpoch(self)
                  \/ EndLP1_1(self)

GetMessage(self) == /\ pc[self] = "GetMessage"
                    /\ Assert(CanRecv(self, messages),
                              "Failure of assertion at line 113, column 5 of macro called at line 181, column 9.")
                    /\ /\ message_LP' = [message_LP EXCEPT ![self] = Recv(self, messages)[1]]
                       /\ messages' = Recv(self, messages)[2]
                    /\ Assert(message_LP'[self].type = ACK_E /\ message_LP'[self].epoch = new_epoch[self],
                              "Failure of assertion at line 182, column 9.")
                    /\ pc' = [pc EXCEPT ![self] = "HistorySelection"]
                    /\ UNCHANGED << stack, message_, message_L, i_, i_L,
                                    message_F, message_FP, i_LP, message, i,
                                    state, last_epoch, last_leader, history,
                                    zxid, candidate, delivered, follower_step,
                                    followers, selected_history, new_epoch,
                                    ackd_e, ackd_ld, leader_step, restart >>

HistorySelection(self) == /\ pc[self] = "HistorySelection"
                          /\ ackd_e' = [ackd_e EXCEPT ![self] = ackd_e[self] \union {message_LP[self].from}]
                          /\ IF \/ message_LP[self].last_leader > selected_history[self].last_leader
                                \/  /\ message_LP[self].last_leader = selected_history[self].last_leader
                                    /\ ZxidGreaterThan(Last(message_LP[self].history).zxid, Last(selected_history[self].history).zxid)
                                THEN /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> message_LP[self].last_leader, history |-> message_LP[self].history]]
                                ELSE /\ TRUE
                                     /\ UNCHANGED selected_history
                          /\ pc' = [pc EXCEPT ![self] = "CheckAllAckd"]
                          /\ UNCHANGED << messages, stack, message_, message_L,
                                          i_, message_LP, i_L, message_F,
                                          message_FP, i_LP, message, i, state,
                                          last_epoch, last_leader, history,
                                          zxid, candidate, delivered,
                                          follower_step, followers, new_epoch,
                                          ackd_ld, leader_step, restart >>

CheckAllAckd(self) == /\ pc[self] = "CheckAllAckd"
                      /\ IF ackd_e[self] = Range(followers[self])
                            THEN /\ leader_step' = [leader_step EXCEPT ![self] = LS_2_1]
                            ELSE /\ TRUE
                                 /\ UNCHANGED leader_step
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ message_LP' = [message_LP EXCEPT ![self] = Head(stack[self]).message_LP]
                      /\ i_L' = [i_L EXCEPT ![self] = Head(stack[self]).i_L]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << messages, message_, message_L, i_,
                                      message_F, message_FP, i_LP, message, i,
                                      state, last_epoch, last_leader, history,
                                      zxid, candidate, delivered,
                                      follower_step, followers,
                                      selected_history, new_epoch, ackd_e,
                                      ackd_ld, restart >>

LP1_2(self) == GetMessage(self) \/ HistorySelection(self)
                  \/ CheckAllAckd(self)

GetNewLeaderMessage(self) == /\ pc[self] = "GetNewLeaderMessage"
                             /\ Assert(CanRecv(self, messages),
                                       "Failure of assertion at line 113, column 5 of macro called at line 205, column 9.")
                             /\ /\ message_F' = [message_F EXCEPT ![self] = Recv(self, messages)[1]]
                                /\ messages' = Recv(self, messages)[2]
                             /\ Assert(message_F'[self].type = NEWLEADER /\ message_F'[self].from = candidate[self],
                                       "Failure of assertion at line 206, column 9.")
                             /\ pc' = [pc EXCEPT ![self] = "HandleNewLeaderMessage"]
                             /\ UNCHANGED << stack, message_, message_L, i_,
                                             message_LP, i_L, message_FP, i_LP,
                                             message, i, state, last_epoch,
                                             last_leader, history, zxid,
                                             candidate, delivered,
                                             follower_step, followers,
                                             selected_history, new_epoch,
                                             ackd_e, ackd_ld, leader_step,
                                             restart >>

HandleNewLeaderMessage(self) == /\ pc[self] = "HandleNewLeaderMessage"
                                /\ IF last_epoch[self] = message_F[self].epoch
                                      THEN /\ last_leader' = [last_leader EXCEPT ![self] = message_F[self].epoch]
                                           /\ history' = [history EXCEPT ![self] = message_F[self].inital_history]
                                           /\ messages' = Send(candidate[self], (AckLeaderMessage(self, message_F[self].epoch)), messages)
                                           /\ follower_step' = [follower_step EXCEPT ![self] = FS_2_2]
                                           /\ UNCHANGED restart
                                      ELSE /\ restart' = [restart EXCEPT ![self] = TRUE]
                                           /\ UNCHANGED << messages,
                                                           last_leader,
                                                           history,
                                                           follower_step >>
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ message_F' = [message_F EXCEPT ![self] = Head(stack[self]).message_F]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << message_, message_L, i_,
                                                message_LP, i_L, message_FP,
                                                i_LP, message, i, state,
                                                last_epoch, zxid, candidate,
                                                delivered, followers,
                                                selected_history, new_epoch,
                                                ackd_e, ackd_ld, leader_step >>

FP2_1(self) == GetNewLeaderMessage(self) \/ HandleNewLeaderMessage(self)

GetCommitMessage(self) == /\ pc[self] = "GetCommitMessage"
                          /\ Assert(CanRecv(self, messages),
                                    "Failure of assertion at line 113, column 5 of macro called at line 226, column 9.")
                          /\ /\ message_FP' = [message_FP EXCEPT ![self] = Recv(self, messages)[1]]
                             /\ messages' = Recv(self, messages)[2]
                          /\ Assert(message_FP'[self].type = COMMIT_LD /\ message_FP'[self].from = candidate[self],
                                    "Failure of assertion at line 227, column 9.")
                          /\ pc' = [pc EXCEPT ![self] = "HandleCommitMessage"]
                          /\ UNCHANGED << stack, message_, message_L, i_,
                                          message_LP, i_L, message_F, i_LP,
                                          message, i, state, last_epoch,
                                          last_leader, history, zxid,
                                          candidate, delivered, follower_step,
                                          followers, selected_history,
                                          new_epoch, ackd_e, ackd_ld,
                                          leader_step, restart >>

HandleCommitMessage(self) == /\ pc[self] = "HandleCommitMessage"
                             /\ delivered' = [delivered EXCEPT ![self] = delivered[self] \union {history[self]}]
                             /\ follower_step' = [follower_step EXCEPT ![self] = FS_3_1]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ message_FP' = [message_FP EXCEPT ![self] = Head(stack[self]).message_FP]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << messages, message_, message_L, i_,
                                             message_LP, i_L, message_F, i_LP,
                                             message, i, state, last_epoch,
                                             last_leader, history, zxid,
                                             candidate, followers,
                                             selected_history, new_epoch,
                                             ackd_e, ackd_ld, leader_step,
                                             restart >>

FP2_2(self) == GetCommitMessage(self) \/ HandleCommitMessage(self)

LP2Start(self) == /\ pc[self] = "LP2Start"
                  /\ Assert(IsQuorum(followers[self], Servers),
                            "Failure of assertion at line 241, column 9.")
                  /\ i_LP' = [i_LP EXCEPT ![self] = 1]
                  /\ pc' = [pc EXCEPT ![self] = "NewLeader"]
                  /\ UNCHANGED << messages, stack, message_, message_L, i_,
                                  message_LP, i_L, message_F, message_FP,
                                  message, i, state, last_epoch, last_leader,
                                  history, zxid, candidate, delivered,
                                  follower_step, followers, selected_history,
                                  new_epoch, ackd_e, ackd_ld, leader_step,
                                  restart >>

NewLeader(self) == /\ pc[self] = "NewLeader"
                   /\ IF i_LP[self] <= DOMAIN followers[self]
                         THEN /\ messages' = Send((followers[self][i_LP[self]]), (NewLeaderMessage(self, new_epoch[self], selected_history[self])), messages)
                              /\ i_LP' = [i_LP EXCEPT ![self] = i_LP[self]+1]
                              /\ pc' = [pc EXCEPT ![self] = "NewLeader"]
                              /\ UNCHANGED << stack, leader_step >>
                         ELSE /\ leader_step' = [leader_step EXCEPT ![self] = LS_2_2]
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ i_LP' = [i_LP EXCEPT ![self] = Head(stack[self]).i_LP]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED messages
                   /\ UNCHANGED << message_, message_L, i_, message_LP, i_L,
                                   message_F, message_FP, message, i, state,
                                   last_epoch, last_leader, history, zxid,
                                   candidate, delivered, follower_step,
                                   followers, selected_history, new_epoch,
                                   ackd_e, ackd_ld, restart >>

LP2_1(self) == LP2Start(self) \/ NewLeader(self)

GetAckMessage(self) == /\ pc[self] = "GetAckMessage"
                       /\ Assert(CanRecv(self, messages),
                                 "Failure of assertion at line 113, column 5 of macro called at line 258, column 9.")
                       /\ /\ message' = [message EXCEPT ![self] = Recv(self, messages)[1]]
                          /\ messages' = Recv(self, messages)[2]
                       /\ Assert(message'[self].type = ACK_LD /\ message'[self].epoch = new_epoch[self],
                                 "Failure of assertion at line 259, column 9.")
                       /\ pc' = [pc EXCEPT ![self] = "HandleAck"]
                       /\ UNCHANGED << stack, message_, message_L, i_,
                                       message_LP, i_L, message_F, message_FP,
                                       i_LP, i, state, last_epoch, last_leader,
                                       history, zxid, candidate, delivered,
                                       follower_step, followers,
                                       selected_history, new_epoch, ackd_e,
                                       ackd_ld, leader_step, restart >>

HandleAck(self) == /\ pc[self] = "HandleAck"
                   /\ ackd_ld' = [ackd_ld EXCEPT ![self] = ackd_ld[self] \union {message[self].from}]
                   /\ IF IsQuorum(ackd_ld'[self], Servers)
                         THEN /\ i' = [i EXCEPT ![self] = 1]
                              /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "EndLP2_2"]
                              /\ i' = i
                   /\ UNCHANGED << messages, stack, message_, message_L, i_,
                                   message_LP, i_L, message_F, message_FP,
                                   i_LP, message, state, last_epoch,
                                   last_leader, history, zxid, candidate,
                                   delivered, follower_step, followers,
                                   selected_history, new_epoch, ackd_e,
                                   leader_step, restart >>

SendCommit(self) == /\ pc[self] = "SendCommit"
                    /\ IF i[self] <= DOMAIN followers[self]
                          THEN /\ messages' = Send((followers[self][i[self]]), (CommitLeaderMessage(self, new_epoch[self])), messages)
                               /\ i' = [i EXCEPT ![self] = i[self]+1]
                               /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                               /\ UNCHANGED leader_step
                          ELSE /\ leader_step' = [leader_step EXCEPT ![self] = LS_3_1]
                               /\ pc' = [pc EXCEPT ![self] = "EndLP2_2"]
                               /\ UNCHANGED << messages, i >>
                    /\ UNCHANGED << stack, message_, message_L, i_, message_LP,
                                    i_L, message_F, message_FP, i_LP, message,
                                    state, last_epoch, last_leader, history,
                                    zxid, candidate, delivered, follower_step,
                                    followers, selected_history, new_epoch,
                                    ackd_e, ackd_ld, restart >>

EndLP2_2(self) == /\ pc[self] = "EndLP2_2"
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ message' = [message EXCEPT ![self] = Head(stack[self]).message]
                  /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << messages, message_, message_L, i_,
                                  message_LP, i_L, message_F, message_FP, i_LP,
                                  state, last_epoch, last_leader, history,
                                  zxid, candidate, delivered, follower_step,
                                  followers, selected_history, new_epoch,
                                  ackd_e, ackd_ld, leader_step, restart >>

LP2_2(self) == GetAckMessage(self) \/ HandleAck(self) \/ SendCommit(self)
                  \/ EndLP2_2(self)

GetCandidate(self) == /\ pc[self] = "GetCandidate"
                      /\ candidate' = [candidate EXCEPT ![self] = LeaderOracle(last_epoch[self] + 1)]
                      /\ pc' = [pc EXCEPT ![self] = "RunStep"]
                      /\ UNCHANGED << messages, stack, message_, message_L, i_,
                                      message_LP, i_L, message_F, message_FP,
                                      i_LP, message, i, state, last_epoch,
                                      last_leader, history, zxid, delivered,
                                      follower_step, followers,
                                      selected_history, new_epoch, ackd_e,
                                      ackd_ld, leader_step, restart >>

RunStep(self) == /\ pc[self] = "RunStep"
                 /\ \/ /\ follower_step[self] = FS_1_1
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP1_1",
                                                                pc        |->  "RunStep" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "Notify"]
                       /\ UNCHANGED <<message_, message_L, i_, message_LP, i_L, message_F, message_FP, i_LP, message, i, followers, selected_history, new_epoch, ackd_e, ackd_ld>>
                    \/ /\ /\ follower_step[self] = FS_1_2
                          /\ CanRecv(self, messages)
                          /\ Head(messages[self]).type = NEWEPOCH
                          /\ Head(messages[self]).from = candidate[self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP1_2",
                                                                pc        |->  "RunStep",
                                                                message_  |->  message_[self] ] >>
                                                            \o stack[self]]
                       /\ message_' = [message_ EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "GetMessage_"]
                       /\ UNCHANGED <<message_L, i_, message_LP, i_L, message_F, message_FP, i_LP, message, i, followers, selected_history, new_epoch, ackd_e, ackd_ld>>
                    \/ /\ /\ candidate[self] = self
                          /\ leader_step[self] = LS_1_1
                          /\ CanRecv(self, messages)
                          /\ Head(messages[self]).type = CEPOCH
                       /\ followers' = [followers EXCEPT ![self] = <<>>]
                       /\ selected_history' = [selected_history EXCEPT ![self] = [last_leader |-> 0, history |-> <<>>]]
                       /\ new_epoch' = [new_epoch EXCEPT ![self] = last_epoch[self]]
                       /\ ackd_e' = [ackd_e EXCEPT ![self] = {}]
                       /\ ackd_ld' = [ackd_ld EXCEPT ![self] = {}]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP1_1",
                                                                pc        |->  "RunStep",
                                                                message_L |->  message_L[self],
                                                                i_        |->  i_[self] ] >>
                                                            \o stack[self]]
                       /\ message_L' = [message_L EXCEPT ![self] = defaultInitValue]
                       /\ i_' = [i_ EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "GetMessage_L"]
                       /\ UNCHANGED <<message_, message_LP, i_L, message_F, message_FP, i_LP, message, i>>
                    \/ /\ /\ candidate[self] = self
                          /\ leader_step[self] = LS_1_2
                          /\ CanRecv(self, messages)
                          /\ Head(messages[self]).type = ACK_E
                          /\ Head(messages[self]).epoch = new_epoch[self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP1_2",
                                                                pc        |->  "RunStep",
                                                                message_LP |->  message_LP[self],
                                                                i_L       |->  i_L[self] ] >>
                                                            \o stack[self]]
                       /\ message_LP' = [message_LP EXCEPT ![self] = defaultInitValue]
                       /\ i_L' = [i_L EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "GetMessage"]
                       /\ UNCHANGED <<message_, message_L, i_, message_F, message_FP, i_LP, message, i, followers, selected_history, new_epoch, ackd_e, ackd_ld>>
                    \/ /\ /\ follower_step[self] = FS_2_1
                          /\ CanRecv(self, messages)
                          /\ Head(messages[self]).type = NEWLEADER
                          /\ Head(messages[self]).from = candidate[self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP2_1",
                                                                pc        |->  "CheckRestart",
                                                                message_F |->  message_F[self] ] >>
                                                            \o stack[self]]
                       /\ message_F' = [message_F EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "GetNewLeaderMessage"]
                       /\ UNCHANGED <<message_, message_L, i_, message_LP, i_L, message_FP, i_LP, message, i, followers, selected_history, new_epoch, ackd_e, ackd_ld>>
                    \/ /\ /\ follower_step[self] = FS_2_1
                          /\ CanRecv(self, messages)
                          /\ Head(messages[self]).type = COMMIT_LD
                          /\ Head(messages[self]).from = candidate[self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FP2_2",
                                                                pc        |->  "RunStep",
                                                                message_FP |->  message_FP[self] ] >>
                                                            \o stack[self]]
                       /\ message_FP' = [message_FP EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "GetCommitMessage"]
                       /\ UNCHANGED <<message_, message_L, i_, message_LP, i_L, message_F, i_LP, message, i, followers, selected_history, new_epoch, ackd_e, ackd_ld>>
                    \/ /\ /\ candidate[self] = self
                          /\ leader_step[self] = LS_2_1
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP2_1",
                                                                pc        |->  "RunStep",
                                                                i_LP      |->  i_LP[self] ] >>
                                                            \o stack[self]]
                       /\ i_LP' = [i_LP EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "LP2Start"]
                       /\ UNCHANGED <<message_, message_L, i_, message_LP, i_L, message_F, message_FP, message, i, followers, selected_history, new_epoch, ackd_e, ackd_ld>>
                    \/ /\ /\ candidate[self] = self
                          /\ leader_step[self] = LS_2_2
                          /\ CanRecv(self, messages)
                          /\ Head(messages[self]).type = ACK_LD
                          /\ Head(messages[self]).epoch = new_epoch[self]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LP2_2",
                                                                pc        |->  "RunStep",
                                                                message   |->  message[self],
                                                                i         |->  i[self] ] >>
                                                            \o stack[self]]
                       /\ message' = [message EXCEPT ![self] = defaultInitValue]
                       /\ i' = [i EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "GetAckMessage"]
                       /\ UNCHANGED <<message_, message_L, i_, message_LP, i_L, message_F, message_FP, i_LP, followers, selected_history, new_epoch, ackd_e, ackd_ld>>
                 /\ UNCHANGED << messages, state, last_epoch, last_leader,
                                 history, zxid, candidate, delivered,
                                 follower_step, leader_step, restart >>

CheckRestart(self) == /\ pc[self] = "CheckRestart"
                      /\ IF restart[self]
                            THEN /\ follower_step' = [follower_step EXCEPT ![self] = FS_1_1]
                            ELSE /\ TRUE
                                 /\ UNCHANGED follower_step
                      /\ pc' = [pc EXCEPT ![self] = "RunStep"]
                      /\ UNCHANGED << messages, stack, message_, message_L, i_,
                                      message_LP, i_L, message_F, message_FP,
                                      i_LP, message, i, state, last_epoch,
                                      last_leader, history, zxid, candidate,
                                      delivered, followers, selected_history,
                                      new_epoch, ackd_e, ackd_ld, leader_step,
                                      restart >>

server(self) == GetCandidate(self) \/ RunStep(self) \/ CheckRestart(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ FP1_1(self) \/ FP1_2(self) \/ LP1_1(self)
                               \/ LP1_2(self) \/ FP2_1(self) \/ FP2_2(self)
                               \/ LP2_1(self) \/ LP2_2(self))
           \/ (\E self \in Servers: server(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
