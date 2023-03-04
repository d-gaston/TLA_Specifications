 -------------------------- MODULE SharedMenu --------------------------

(***************************************************************************
A certain restaurant has only one menu that is shared between all its 
tables. The owner implemented a system where each table has a count that
represents the number of tables that have seen the menu since that table's
last possession. Once a table gets a menu, it orders its next course and 
hands the menu to the next table (either directly or via a waiter). Which
table is next is decided by whoever has waited the longest for the menu,
with preference given to patrons who have arrived earlier (for example 
by subtracting their course number from the time since they've last seen
the menu).

Note: After implementing this idea, it's a lot less interesting than 
I thought it'd be. It's completely deterministic (judging by the 
model output), so some modification would have to be made to this
idea to get some non-determinism in the system.

 ***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS numTables, numCourses
VARIABLE tables



(***************************************************************************
Create a set of structs with the number of elements specified by numTables.
 ***************************************************************************)

MakeTable(id) == [
                    id            |-> id,
                    hasMenu       |-> FALSE,
                    lastSeenCount |-> 0,
                    course        |-> 0 
                 ]
                 
Init == tables = {MakeTable(i): i \in 1..numTables }  


(***************************************************************************
The actions that can be taken for a table.
 ***************************************************************************)
GiveMenu(table) == [ table EXCEPT !.hasMenu = TRUE ]

IncrementLastSeen(table) == [ table EXCEPT !.lastSeenCount = 1 + @ ]

TakeMenuFrom(table) == [ table EXCEPT   
                         !.hasMenu = FALSE,
                         !.lastSeenCount = 0,
                         !.course = 1 + @   
                       ]
SeatNewPatrons(table) ==  [ table EXCEPT
                            !.hasMenu = FALSE,
                            !.lastSeenCount = 0,
                            !.course = 0
                          ] 
(***************************************************************************
Returns a table with the highest lastSeenCount after the course number
has been subtracted.
 ***************************************************************************)
ChooseTable == CHOOSE t \in tables:
                      \A u \in tables: 
                         /\ (t.lastSeenCount - t.course) >= 
                            (u.lastSeenCount - u.course) 

 
    


TypeOK == Cardinality(tables) = numTables   


(***************************************************************************
I couldn't figure out how to specify that only one given element of the
tables set has a new value in the next state. I was thinking of something 
like
\A t \in tables:
    /\ t.hasMenu
    /\ t' = TakeMenu(t)
but it wasn't quite working
 ***************************************************************************)   
Next == /\ tables' = { CASE t.hasMenu = TRUE    -> TakeMenuFrom(t)
                       [] t.course = numCourses -> SeatNewPatrons(t)
                       [] t = ChooseTable       -> GiveMenu(t)
                       [] t.hasMenu = FALSE     -> IncrementLastSeen(t)
                       [] OTHER                 -> t
                       : 
                       t \in tables
                     }


AtMostOneTableHasMenu == 
        Cardinality({t \in tables: t.hasMenu = TRUE}) <= 1
        
Spec == Init /\ [][Next]_tables /\ WF_tables(Next)
        
                

========================================================================
