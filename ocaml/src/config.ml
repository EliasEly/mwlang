(*Auteur : Elias El Yandouzi & Amad Salmon*)
open Printf;;
open While;;

type state = int list;;

type config =
  | Inter of winstr * state
  | Final of state;;

let init n  =
  let rec aux n s =
  match n with
  | 0 -> s
  | n -> aux (n-1) (0::s) in
  aux n [];;

let rec get x s = 
  match x with
  | 0 -> (match s with
          | [] -> 0
          | v::_ -> v)
  | x -> (match s with
          | [] -> 0
          | _::l -> get (x-1) l);;

let rec update s v n =
  match v with
  | 0 -> (match s with
        | [] -> [n]
        | _::l -> n::l)
  | v ->
    (match s with
      | [] -> 0::(update [] (v-1) n)
      | a::l -> a::(update l (v-1) n));;    

  
let index_var = fun e ->
  match e with
  | V A -> 0
  | V B -> 1
  | V C -> 2
  | V D -> 3
  | _ -> raise Erreur;;

let value_exp(e: exp) (s: state) : int =
  match e with
  | Cst Opposite -> (-1)
  | Cst Zero -> 0
  | Cst Un -> 1
  | _ -> get (index_var e) s;;

let eval(e: exp) (s: state) : bool =
  match e with
  | Cst Zero -> false
  | Cst Un -> true
  | Cst Opposite -> raise Erreur 
  | _ -> let v = get (index_var e) s in if v = 1 then true else false;;


let rec faire_un_pas = fun instr s -> 
  match instr with
| Vide -> Final(s)
| Assign(x, v) -> Final(update s (index_var (V x)) (let v = (value_exp v s) in if v = (-1) then ((-1) * (get (index_var (V x)) s) + 1) else v))
| Seq(e1, e2) -> (match (faire_un_pas e1 s) with
                  | Inter(e1_bis, s_bis) -> Inter(Seq(e1_bis, e2), s_bis)
                  | Final(s_bis) -> Inter(e2, s_bis))
| If(cond, e1, e2) -> (match (eval cond s) with
                      | true -> Inter(e1, s)
                      | false -> Inter(e2, s))
| While(cond, e) -> (match (eval cond s) with
                      | true -> Inter(Seq(e, While(cond, e)), s)
                      | false -> Inter(Vide, s));;

let rec executer = fun instr s ->
  match (faire_un_pas instr s) with
  | Final(s) -> true
  | Inter(i1, s1) -> executer i1 s1;;


let nombre_de_pas = fun instr ->
  let rec __nombre_de_pas = fun instr s acc ->
    match (faire_un_pas instr s) with
    | Final(s) -> acc
    | Inter(i1, s1) -> __nombre_de_pas i1 s1 (acc+1)
  in __nombre_de_pas instr (init 4) 0;;

let print_state = fun s ->
  let rec __print_state (s: state) = 
    match s with
    | x::l -> printf " %d" x; if l != [] then printf " ;" else printf " " ; __print_state l
    | [] -> ()
    in printf "["; __print_state s; printf "]";;

let rec executer_interactif = fun instr s ->
  printf "> ";
  let input = read_line() in match input with
                            | "n" | "next"  -> (match (faire_un_pas instr s) with
                                              | Final(s) -> true
                                              | Inter(i1, s1) -> executer_interactif i1 s1)
                            | "q" | "quit"  -> false
                            | "p" | "print" -> printf "L'état vaut : "; print_state s; printf "\n" ;executer_interactif instr s
                            | "c" | "continue" -> executer instr s
                            | _ -> executer_interactif instr s;;
