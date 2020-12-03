(*Auteur : Elias El Yandouzi & Amad Salmon*)
open Config;;
open While;;
open Printf;;

let t2 = list_of_string "a:=1;b:=1;w(a){b:=1}";;
let _ = p_S t2;;

let t3 = list_of_string "  a:=1;b:=1;i(1){b:=1}{c:=0}";;
let _ = p_S t3;;

let t4 = list_of_string "  a:=1;b:=1;a:=#;i(1){b:=1}{c:=0}";;
let _ = p_S t4;;

let t3 = list_of_string
"a:=1;
c:=1;
i(0)
  {b:=1}
  {c:=0}";; 
                          
let instr = let (i, _) = p_S t3 in i;; 

let _ = faire_un_pas instr (init 4);;
let _ = executer instr (init 4);;
let _ = executer_interactif instr (init 4);;