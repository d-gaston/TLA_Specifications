 -------------------------- MODULE MatchingPennies --------------------------

(***************************************************************************)
(* This is a model for the Matching Pennies game. An explanation of the    *)
(* game can be found here:                                                 *)
(* https://www.gametheory.net/dictionary/Games/MatchingPennies.html        *)
(***************************************************************************)
EXTENDS Naturals

(***************************************************************************)
(* Matcher: The player who wins when the pennies match                     *)
(*                                                                         *)
(* Mismatcher: The player who wins when the pennies don't match            *)
(*                                                                         *)
(* Winner: The player who won, either "Matcher" or "Mismatcher             *)
(*                                                                         *)
(* GameOver: A boolean flag to prevent the model from exploring states     *)
(* after a winner has been decided                                         *)
(***************************************************************************)
VARIABLES Matcher, Mismatcher, Winner, GameOver
vars == <<Matcher, Mismatcher, Winner, GameOver>> 




Init == /\ Matcher = "" 
        /\ Mismatcher  = "" 
        /\ Winner  = "" 
        /\ GameOver = FALSE
        
(***************************************************************************)
(* The Next state is guarded by the GameOver boolean; the model only       *)
(* advances to the next state if the game is NOT over.  The rest of the    *)
(* predicate enumerates the states each player can take, and the states    *)
(* that winner can take based on the next states of the players.  The next *)
(* state of GameOver is always TRUE, since this game only has one round    *)
(***************************************************************************)
Next == /\ GameOver = FALSE
        /\ \/ Matcher' = "Heads"
           \/ Matcher' = "Tails"
        /\ \/ Mismatcher' = "Heads"
           \/ Mismatcher' = "Tails"
        /\ Winner' = IF Matcher' = Mismatcher' 
                     THEN "Matcher" 
                     ELSE "Mismatcher"
        /\ GameOver' = TRUE                


(***************************************************************************)
(* Weak Fairness is included to prevent infinite stutter steps. Although   *)
(* it's overkill to specify these temporal properties for such a small     *)
(* system (visual inspection is sufficient), it's a good exercise. Here we *)
(* are saying that eventually GameOver will be TRUE and from that point on *)
(* it will always be TRUE. Winner will eventually reach either the state   *)
(* "Matcher" or "Mismatcher"                                               *)
(*                                                                         *)
(* Note that this model will deadlock, so deadlock detection should        *)
(* be turned off                                                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Properties == /\ <>[](GameOver = TRUE) 
              /\ <>(Winner = "Matcher" \/ Winner = "Mismatcher")
=============================================================================