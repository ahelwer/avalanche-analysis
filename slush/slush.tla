----------------------------- MODULE SlushPCal -----------------------------

EXTENDS
    Naturals,
    FiniteSets

CONSTANTS
    Node,
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold

----------------------------------------------------------------------------

Red == "Red"

Blue == "Blue"

Color == {Red, Blue}

NoColor == CHOOSE c : c \notin Color

QueryMessageType == "QueryMessageType"

QueryReplyMessageType == "QueryReplyMessageType"

Message ==
    [type   : {QueryMessageType, QueryReplyMessageType},
    src     : Node,
    dst     : Node,
    color   : Color]

(*--algorithm Slush
variables
    pick = [node \in Node |-> NoColor];
    
    message = {}

define
    TypeInvariant ==
        /\ pick \in [Node -> Color \cup {NoColor}]
        /\ message \subseteq Message    

    QueryMessage(node) ==
        {m \in message :
            /\ m.type = QueryMessageType 
            /\ m.dst = node}

    QueryReplyMessage(node) ==
        {m \in message :
            /\ m.type = QueryReplyMessageType 
            /\ m.dst = node}

end define

procedure OnQuery(self)
variables
    queryMessage
begin
    RequireQueryMessage:
        await QueryMessage(self) /= {};

    GetMessage:
        with msg \in QueryMessage(self) do
            queryMessage := msg;
        end with;

    AssignColorIfBlank:
        if pick[self] = NoColor then
            pick[self] := queryMessage.color;
        end if;

    RespondToQuery:
        message := message \cup
            {[type  |-> QueryReplyMessageType,
            src     |-> self,
            dst     |-> queryMessage.src,
            color   |-> pick[self]]};

    MarkQueryMessageAsProcessed:
        message := message \ {queryMessage}
    
end procedure;

procedure SlushLoop(self)
variables
    sampleSet,
    loopVariant = 0
begin
    RequireColorAssignment: 
        await pick[self] /= NoColor;

    ExecuteSlushLoop: while loopVariant < SlushIterationCount do

        PickSampleSet:
            with possibleSampleSet \in {set \in SUBSET (Node \ {self}) : Cardinality(set) = SampleSetSize} do
                sampleSet := possibleSampleSet;
            end with;

        QuerySampleSet:
            message := message \cup
                {[type  |-> QueryMessageType,
                src     |-> self,
                dst     |-> node,
                color   |-> pick[self]] :
                    node \in sampleSet};

        WaitForQueryReplies:
            await
                /\ \A node \in sampleSet :
                    /\ \E msg \in Message :
                        /\ msg.type = QueryReplyMessageType
                        /\ msg.dst = self
                        /\ msg.src = node;

        TallyRedQueryReplies:
            with
                redTally = Cardinality(
                    {msg \in Message :
                        /\ msg.type = QueryReplyMessageType
                        /\ msg.src \in sampleSet
                        /\ msg.dst = self
                        /\ msg.color = Red}),
                blueTally = Cardinality(
                    {msg \in Message :
                        /\ msg.type = QueryReplyMessageType
                        /\ msg.src \in sampleSet
                        /\ msg.dst = self
                        /\ msg.color = Blue})
            do
                if redTally >= PickFlipThreshold then
                    pick[self] := Red;
                elsif blueTally >= PickFlipThreshold then
                    pick[self] := Blue;
                end if;
            end with;

        MarkQueryReplyMessagesAsProcessed:
            message := message \
                {msg \in message :
                    /\ msg.type = QueryReplyMessageType
                    /\ msg.src \in sampleSet
                    /\ msg.dst = self};

        IncrementLoopVariant:
            loopVariant := loopVariant + 1;

    end while;

end procedure;

process ClientRequest = "ClientRequest"
begin
    AssignColorToNode:
        with node \in Node, color \in Color do
            if pick[node] = NoColor then
                pick[node] := color;
            end if;
        end with;
end process;

process SlushNode \in Node
begin
    Run:
        either call OnQuery(self)
        or call SlushLoop(self)
        end either;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
\* Parameter self of procedure OnQuery at line 56 col 19 changed to self_
CONSTANT defaultInitValue
VARIABLES pick, message, pc, stack

(* define statement *)
TypeInvariant ==
    /\ pick \in [Node -> Color \cup {NoColor}]
    /\ message \subseteq Message

QueryMessage(node) ==
    {m \in message :
        /\ m.type = QueryMessageType
        /\ m.dst = node}

QueryReplyMessage(node) ==
    {m \in message :
        /\ m.type = QueryReplyMessageType
        /\ m.dst = node}

VARIABLES self_, queryMessage, self, sampleSet, loopVariant

vars == << pick, message, pc, stack, self_, queryMessage, self, sampleSet, 
           loopVariant >>

ProcSet == {"ClientRequest"} \cup (Node)

Init == (* Global variables *)
        /\ pick = [node \in Node |-> NoColor]
        /\ message = {}
        (* Procedure OnQuery *)
        /\ self_ = [ self \in ProcSet |-> defaultInitValue]
        /\ queryMessage = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure SlushLoop *)
        /\ self = [ self \in ProcSet |-> defaultInitValue]
        /\ sampleSet = [ self \in ProcSet |-> defaultInitValue]
        /\ loopVariant = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "ClientRequest" -> "AssignColorToNode"
                                        [] self \in Node -> "Run"]

RequireQueryMessage(self) == /\ pc[self] = "RequireQueryMessage"
                             /\ QueryMessage(self_[self]) /= {}
                             /\ pc' = [pc EXCEPT ![self] = "GetMessage"]
                             /\ UNCHANGED << pick, message, stack, self_, 
                                             queryMessage, self, sampleSet, 
                                             loopVariant >>

GetMessage(self) == /\ pc[self] = "GetMessage"
                    /\ \E msg \in QueryMessage(self_[self]):
                         queryMessage' = [queryMessage EXCEPT ![self] = msg]
                    /\ pc' = [pc EXCEPT ![self] = "AssignColorIfBlank"]
                    /\ UNCHANGED << pick, message, stack, self_, self, 
                                    sampleSet, loopVariant >>

AssignColorIfBlank(self) == /\ pc[self] = "AssignColorIfBlank"
                            /\ IF pick[self_[self]] = NoColor
                                  THEN /\ pick' = [pick EXCEPT ![self_[self]] = queryMessage[self].color]
                                  ELSE /\ TRUE
                                       /\ pick' = pick
                            /\ pc' = [pc EXCEPT ![self] = "RespondToQuery"]
                            /\ UNCHANGED << message, stack, self_, 
                                            queryMessage, self, sampleSet, 
                                            loopVariant >>

RespondToQuery(self) == /\ pc[self] = "RespondToQuery"
                        /\ message' = (       message \cup
                                       {[type  |-> QueryReplyMessageType,
                                       src     |-> self_[self],
                                       dst     |-> queryMessage[self].src,
                                       color   |-> pick[self_[self]]]})
                        /\ pc' = [pc EXCEPT ![self] = "MarkQueryMessageAsProcessed"]
                        /\ UNCHANGED << pick, stack, self_, queryMessage, self, 
                                        sampleSet, loopVariant >>

MarkQueryMessageAsProcessed(self) == /\ pc[self] = "MarkQueryMessageAsProcessed"
                                     /\ message' = message \ {queryMessage[self]}
                                     /\ pc' = [pc EXCEPT ![self] = "Error"]
                                     /\ UNCHANGED << pick, stack, self_, 
                                                     queryMessage, self, 
                                                     sampleSet, loopVariant >>

OnQuery(self) == RequireQueryMessage(self) \/ GetMessage(self)
                    \/ AssignColorIfBlank(self) \/ RespondToQuery(self)
                    \/ MarkQueryMessageAsProcessed(self)

RequireColorAssignment(self) == /\ pc[self] = "RequireColorAssignment"
                                /\ pick[self[self]] /= NoColor
                                /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
                                /\ UNCHANGED << pick, message, stack, self_, 
                                                queryMessage, self, sampleSet, 
                                                loopVariant >>

ExecuteSlushLoop(self) == /\ pc[self] = "ExecuteSlushLoop"
                          /\ IF loopVariant[self] < SlushIterationCount
                                THEN /\ pc' = [pc EXCEPT ![self] = "PickSampleSet"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                          /\ UNCHANGED << pick, message, stack, self_, 
                                          queryMessage, self, sampleSet, 
                                          loopVariant >>

PickSampleSet(self) == /\ pc[self] = "PickSampleSet"
                       /\ \E possibleSampleSet \in {set \in SUBSET (Node \ {self[self]}) : Cardinality(set) = SampleSetSize}:
                            sampleSet' = [sampleSet EXCEPT ![self] = possibleSampleSet]
                       /\ pc' = [pc EXCEPT ![self] = "QuerySampleSet"]
                       /\ UNCHANGED << pick, message, stack, self_, 
                                       queryMessage, self, loopVariant >>

QuerySampleSet(self) == /\ pc[self] = "QuerySampleSet"
                        /\ message' = (       message \cup
                                       {[type  |-> QueryMessageType,
                                       src     |-> self[self],
                                       dst     |-> node,
                                       color   |-> pick[self[self]]] :
                                           node \in sampleSet[self]})
                        /\ pc' = [pc EXCEPT ![self] = "WaitForQueryReplies"]
                        /\ UNCHANGED << pick, stack, self_, queryMessage, self, 
                                        sampleSet, loopVariant >>

WaitForQueryReplies(self) == /\ pc[self] = "WaitForQueryReplies"
                             /\ /\ \A node \in sampleSet[self] :
                                    /\ \E msg \in Message :
                                        /\ msg.type = QueryReplyMessageType
                                        /\ msg.dst = self[self]
                                        /\ msg.src = node
                             /\ pc' = [pc EXCEPT ![self] = "TallyRedQueryReplies"]
                             /\ UNCHANGED << pick, message, stack, self_, 
                                             queryMessage, self, sampleSet, 
                                             loopVariant >>

TallyRedQueryReplies(self) == /\ pc[self] = "TallyRedQueryReplies"
                              /\ LET redTally ==        Cardinality(
                                                 {msg \in Message :
                                                     /\ msg.type = QueryReplyMessageType
                                                     /\ msg.src \in sampleSet[self]
                                                     /\ msg.dst = self[self]
                                                     /\ msg.color = Red}) IN
                                   LET blueTally ==         Cardinality(
                                                    {msg \in Message :
                                                        /\ msg.type = QueryReplyMessageType
                                                        /\ msg.src \in sampleSet[self]
                                                        /\ msg.dst = self[self]
                                                        /\ msg.color = Blue}) IN
                                     IF redTally >= PickFlipThreshold
                                        THEN /\ pick' = [pick EXCEPT ![self[self]] = Red]
                                        ELSE /\ IF blueTally >= PickFlipThreshold
                                                   THEN /\ pick' = [pick EXCEPT ![self[self]] = Blue]
                                                   ELSE /\ TRUE
                                                        /\ pick' = pick
                              /\ pc' = [pc EXCEPT ![self] = "MarkQueryReplyMessagesAsProcessed"]
                              /\ UNCHANGED << message, stack, self_, 
                                              queryMessage, self, sampleSet, 
                                              loopVariant >>

MarkQueryReplyMessagesAsProcessed(self) == /\ pc[self] = "MarkQueryReplyMessagesAsProcessed"
                                           /\ message' =        message \
                                                         {msg \in message :
                                                             /\ msg.type = QueryReplyMessageType
                                                             /\ msg.src \in sampleSet[self]
                                                             /\ msg.dst = self[self]}
                                           /\ pc' = [pc EXCEPT ![self] = "IncrementLoopVariant"]
                                           /\ UNCHANGED << pick, stack, self_, 
                                                           queryMessage, self, 
                                                           sampleSet, 
                                                           loopVariant >>

IncrementLoopVariant(self) == /\ pc[self] = "IncrementLoopVariant"
                              /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
                              /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
                              /\ UNCHANGED << pick, message, stack, self_, 
                                              queryMessage, self, sampleSet >>

SlushLoop(self) == RequireColorAssignment(self) \/ ExecuteSlushLoop(self)
                      \/ PickSampleSet(self) \/ QuerySampleSet(self)
                      \/ WaitForQueryReplies(self)
                      \/ TallyRedQueryReplies(self)
                      \/ MarkQueryReplyMessagesAsProcessed(self)
                      \/ IncrementLoopVariant(self)

AssignColorToNode == /\ pc["ClientRequest"] = "AssignColorToNode"
                     /\ \E node \in Node:
                          \E color \in Color:
                            IF pick[node] = NoColor
                               THEN /\ pick' = [pick EXCEPT ![node] = color]
                               ELSE /\ TRUE
                                    /\ pick' = pick
                     /\ pc' = [pc EXCEPT !["ClientRequest"] = "Done"]
                     /\ UNCHANGED << message, stack, self_, queryMessage, self, 
                                     sampleSet, loopVariant >>

ClientRequest == AssignColorToNode

Run(self) == /\ pc[self] = "Run"
             /\ \/ /\ /\ self_' = [self_ EXCEPT ![self] = self[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "OnQuery",
                                                               pc        |->  "Done",
                                                               queryMessage |->  queryMessage[self],
                                                               self_     |->  self_[self] ] >>
                                                           \o stack[self]]
                   /\ queryMessage' = [queryMessage EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "RequireQueryMessage"]
                   /\ UNCHANGED <<self, sampleSet, loopVariant>>
                \/ /\ /\ self' = [self EXCEPT ![self] = self[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SlushLoop",
                                                               pc        |->  "Done",
                                                               sampleSet |->  sampleSet[self],
                                                               loopVariant |->  loopVariant[self],
                                                               self      |->  self[self] ] >>
                                                           \o stack[self]]
                   /\ sampleSet' = [sampleSet EXCEPT ![self] = defaultInitValue]
                   /\ loopVariant' = [loopVariant EXCEPT ![self] = 0]
                   /\ pc' = [pc EXCEPT ![self] = "RequireColorAssignment"]
                   /\ UNCHANGED <<self_, queryMessage>>
             /\ UNCHANGED << pick, message >>

SlushNode(self) == Run(self)

Next == ClientRequest
           \/ (\E self \in ProcSet: OnQuery(self) \/ SlushLoop(self))
           \/ (\E self \in Node: SlushNode(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
