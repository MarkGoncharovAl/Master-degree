-------------------------------- MODULE hotel --------------------------------

EXTENDS Integers
CONSTANT NGuest
CONSTANT NRooms
CONSTANT NRoomsKeys

(*--algorithm hotel
variables
 \* Мапим гостей на комнаты. 0 = ещё не заселен
 Guest = [i \in 1..NGuest |-> 0],
 \* Мапим комнаты на гостей. 0 = ещё не заселена
 Occupant = [i \in 1..NRooms |-> 0],
 
 \* В этот момент уже у нас сделан init предикат
  
define
\* проверяем первую комнату на соответствие с гостем
check == (Guest[1] /= 0) => Occupant[Guest[1]] = 1
end define;
 
 
fair process CheckinPar \in 1..NGuest
    variable tmpRoom = 1;
begin
Checkin11:
while (TRUE) do
    \* берём информацию о госте через self
    
    \*если уже заселён, то пропускаем такт 
    if (Guest[self] /= 0) then
        skip;
    end if;
    
    \* ищем свободную комнату и в том же такте заселяем
    b: while (Occupant[tmpRoom] /= 0) do
        if (tmpRoom = NRooms) then
            skip;
        else
            tmpRoom := tmpRoom + 1
        end if;
    end while;
    \* заселяем 
    Guest[self] := tmpRoom;
    Occupant[tmpRoom] := self;
end while;
end process;

fair process CheckoutPar \in NGuest+1..NGuest+NGuest
    variable tmpRoom = 1;
begin
Checkout11:
while (TRUE) do
    Occupant[Guest[self - NGuest]] := 0;
    Guest[self - NGuest] := 0;
end while;
end process; 
 
end algorithm; *)
\* BEGIN TRANSLATION
\* Process variable tmpRoom of process CheckinPar at line 24 col 14 changed to tmpRoom_
VARIABLES Guest, Occupant, pc

(* define statement *)
check == (Guest[1] /= 0) => Occupant[Guest[1]] = 1

VARIABLES tmpRoom_, tmpRoom

vars == << Guest, Occupant, pc, tmpRoom_, tmpRoom >>

ProcSet == (1..NGuest) \cup (NGuest+1..NGuest+NGuest)

Init == (* Global variables *)
        /\ Guest = [i \in 1..NGuest |-> 0]
        /\ Occupant = [i \in 1..NRooms |-> 0]
        (* Process CheckinPar *)
        /\ tmpRoom_ = [self \in 1..NGuest |-> 1]
        (* Process CheckoutPar *)
        /\ tmpRoom = [self \in NGuest+1..NGuest+NGuest |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..NGuest -> "Checkin11"
                                        [] self \in NGuest+1..NGuest+NGuest -> "Checkout11"]

Checkin11(self) == /\ pc[self] = "Checkin11"
                   /\ IF (Guest[self] /= 0)
                         THEN /\ TRUE
                         ELSE /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "b"]
                   /\ UNCHANGED << Guest, Occupant, tmpRoom_, tmpRoom >>

b(self) == /\ pc[self] = "b"
           /\ IF (Occupant[tmpRoom_[self]] /= 0)
                 THEN /\ IF (tmpRoom_[self] = NRooms)
                            THEN /\ TRUE
                                 /\ UNCHANGED tmpRoom_
                            ELSE /\ tmpRoom_' = [tmpRoom_ EXCEPT ![self] = tmpRoom_[self] + 1]
                      /\ pc' = [pc EXCEPT ![self] = "b"]
                      /\ UNCHANGED << Guest, Occupant >>
                 ELSE /\ Guest' = [Guest EXCEPT ![self] = tmpRoom_[self]]
                      /\ Occupant' = [Occupant EXCEPT ![tmpRoom_[self]] = self]
                      /\ pc' = [pc EXCEPT ![self] = "Checkin11"]
                      /\ UNCHANGED tmpRoom_
           /\ UNCHANGED tmpRoom

CheckinPar(self) == Checkin11(self) \/ b(self)

Checkout11(self) == /\ pc[self] = "Checkout11"
                    /\ Occupant' = [Occupant EXCEPT ![Guest[self - NGuest]] = 0]
                    /\ Guest' = [Guest EXCEPT ![self - NGuest] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "Checkout11"]
                    /\ UNCHANGED << tmpRoom_, tmpRoom >>

CheckoutPar(self) == Checkout11(self)

Next == (\E self \in 1..NGuest: CheckinPar(self))
           \/ (\E self \in NGuest+1..NGuest+NGuest: CheckoutPar(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NGuest : WF_vars(CheckinPar(self))
        /\ \A self \in NGuest+1..NGuest+NGuest : WF_vars(CheckoutPar(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
