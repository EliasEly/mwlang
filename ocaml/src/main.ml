(*Auteur : Elias El Yandouzi & Amad Salmon*)
open Config;;
open While;;
open Printf;;

(** Exercice 4 :
L'instruction If nécessite l'évaluation d'une expression bexp qui permet de déterminer la suite du programme à exécuter.
Les règles de transition de If sont donc :
  eval(bexp) = true
    E, ((if bexp) then P else Q) -> E, P
  eval(bexp) = false
    E, ((if bexp) then P else Q) -> E, Q
**)

let t2 = list_of_string "a:=1;b:=1;w(a){b:=1}";;
let _ = p_S t2;;

let t3 = list_of_string " a:=1;b:=1;i(1){b:=1}{c:=0}";;
let _ = p_S t3;;

let t4 = list_of_string "a:=1;b:=1;a:=#;i(1){b:=1}{c:=0}";;
let _ = p_S t4;;

let t5 = list_of_string
"
a:=1;
c:=1;
i(0)
  {b:=1}
  {c:=0}";; 
                          
let instr = let (i, _) = p_S t5 in i;; 

let _ = faire_un_pas instr (init 4);;
let _ = executer instr (init 4);;
let _ = executer_interactif instr (init 4);;