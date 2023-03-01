--------------------------- MODULE Nim --------------------------
 
EXTENDS Naturals, Sequences


(***************************************************************************)
(* This is a model for the game Nim.  A description can be found here:     *)
(* https://plus.maths.org/content/play-win-nim                             *)
(***************************************************************************)
VARIABLES playerTurn, heaps, gameOver, winner
vars == <<playerTurn, heaps, gameOver, winner>>




(***************************************************************************)
(* from: https://learntla.com/core/advanced-operators.html                 *)
(***************************************************************************)
RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN 0 ELSE
  Head(s) + SumSeq(Tail(s))

  
(***************************************************************************)
(* Due to state explosion, it's a good idea to keep the heap relatively    *)
(* small.                                                                  *)
(*                                                                         *)
(* The playerTurn variable assumes the value "START" only in the first     *)
(* state and thenceforth can have the states "P1" and "P2"                 *)
(*                                                                         *)
(* The gameOver variable becomes true when there is only one item total    *)
(* left in the heaps.                                                      *)
(***************************************************************************)
   
Init == /\ heaps = <<1,1,1>>
        /\ playerTurn = "START"
        /\ gameOver = FALSE
        /\ winner = "NONE"
        
TypeOK == /\ playerTurn \in {"P1", "P2", "START"}
          /\ winner \in {"P1", "P2", "NONE"}
          /\ Len(heaps) = 3
          /\ gameOver \in {TRUE, FALSE}


(***************************************************************************)
(* We can take from a heap when it is not empty.  At least one must be     *)
(* taken, up to the full amount of the heap such that the total sizes of   *)
(* the heaps is greater than zero.  For example, given a heap <<0,0,5>> a  *)
(* playerTurn can from 1 to 4 from it, since that playerTurn wants to      *)
(* leave one item for the other playerTurn to take (i.e.  a playerTurn     *)
(* won't lose on purpose).                                                 *)
(***************************************************************************)

TakeFromHeap(heapNum) == /\ heaps[heapNum] # 0
                         /\ \E amount \in 1..heaps[heapNum]:
                            /\ amount < SumSeq(heaps)
                            /\ heaps' = [ 
                                heaps EXCEPT 
                                  ![heapNum] = heaps[heapNum] - amount
                               ]


(***************************************************************************)
(* The playerTurn whose turn it is can attempt to take from one of the     *)
(* three heaps.                                                            *)
(***************************************************************************)
Move == \/ TakeFromHeap(1)
        \/ TakeFromHeap(2)
        \/ TakeFromHeap(3)

   
Next == /\ gameOver = FALSE
        /\ Move
        /\ playerTurn' = IF playerTurn = "P2" \/ playerTurn = "START" 
                     THEN "P1" 
                     ELSE "P2"
        /\ gameOver' = IF SumSeq(heaps') = 1 
                       THEN TRUE 
                       ELSE FALSE
        /\ winner' = IF gameOver' = TRUE
                     THEN playerTurn'
                     ELSE "NONE"
(***************************************************************************)
(* These are my attempts at writing temporal formulas to specify that both *)
(* playerTurns can win.  They don't work because they say either that      *)
(* eventually playerTurn = "P1" AND playerTurn = "P2" must be true         *)
(* simultaneously or that either playerTurn = "P1" OR playerTurn = "P2"    *)
(* must be true.                                                           *)
(*                                                                         *)
(* But what Iwant to specify is that there exist at least one state where  *)
(* playerTurn = "P1" and at least one state where playerTurn = "P2"        *)
(*                                                                         *)
(* P1EventuallyLoses == <>(gameOver /\ playerTurn = "P1")                  *)
(* P2EventuallyLoses == <>(gameOver /\ playerTurn = "P2")                  *)
(* BothplayerTurnsCanWin == \/ <>(gameOver /\ playerTurn = "P1")           *)
(*                      \/ <>(gameOver /\ playerTurn = "P2")               *)
(***************************************************************************)        
 

(***************************************************************************)
(* A sanity check invariant, it should be trivially true based on the Next *)
(* predicate.                                                              *)
(***************************************************************************)
GameOverAtOneLeft == IF SumSeq(heaps) = 1 
                     THEN gameOver = TRUE 
                     ELSE gameOver = FALSE   
    
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)




=================================================================
