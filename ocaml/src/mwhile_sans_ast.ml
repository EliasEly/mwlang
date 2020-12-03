exception Erreur

type mwhile = char list -> char list

let list_of_string s =
  let rec boucle s i n =
    if i = n then [] else s.[i] :: boucle s (i+1) n
in boucle s 0 (String.length s)


let terminal c : mwhile = fun l ->
  match l with
  | x::l when x = c -> l
  | _ -> raise Erreur

(* a suivi de b *)  
let (+>) (a: mwhile) (b: mwhile) : mwhile =
  fun l -> b (a l)

(* a ou b *)
let (+|) (a: mwhile) (b : mwhile) : mwhile =
  fun l -> try a l with Erreur -> b l


(**Terminal fin de ligne ; *)
let term_eol : mwhile = terminal ';';;

(**Terminal pour les variables allant de a à d *)
let term_a : mwhile = terminal 'a';;
let term_b : mwhile = terminal 'b';;
let term_c : mwhile = terminal 'c';;
let term_d : mwhile = terminal 'd';;

(**Terminal pour les variables allant de 0 à 1 *)
let term_0 : mwhile = terminal '0';;
let term_1 : mwhile = terminal '1';;

(**Terminal pour la négation d'une variable *)
let term_neg : mwhile = terminal '#';;

(**Terminal pour le while et le if *)
let term_w : mwhile = terminal 'w';;
let term_if : mwhile = terminal 'i';;

(**Terminal pour les paranthèses et les acccolades *)
let term_pg : mwhile = terminal '(';;
let term_pd : mwhile = terminal ')';;
let term_ag : mwhile = terminal '{';;
let term_ad : mwhile = terminal '}';;

let epsilon =  fun l -> l;;

let rec p_Blanc : mwhile = 
  fun l -> (
      ((terminal ' ') +| (terminal '\n') +| (terminal '\t') +> (p_Blanc))
      +|
      (epsilon)
  ) l;;

let p_Var : mwhile = 
  fun l -> (
    (term_a +| term_b +| term_c +| term_d)
  ) l;;

let p_Cst : mwhile = 
  fun l -> (
    (term_0 +| term_1)
  ) l;;

let p_Affectation : mwhile =
  fun l -> (
      (p_Blanc)
    +>
      (p_Var)
    +>
      (p_Blanc)
    +>
      (terminal ':')
    +>
      (p_Blanc)
    +> 
      (terminal '=')
    +>
      (p_Blanc)
    +>
      (term_0 +| term_1 +| term_a +| term_b +| term_c +| term_d +| term_neg)
    +>
      (p_Blanc)  
  ) l;;

 
let rec p_S : mwhile = 
  let p_L l = ((term_eol +> p_Blanc +> p_S) +| epsilon) l
  and p_I l =  (p_Affectation 
               +| (term_w +> p_Blanc
                  +> term_pg +> p_Blanc +> (p_Var +| p_Cst) +> p_Blanc +> term_pd +> p_Blanc
                  +> term_ag +> p_Blanc +> p_S +> p_Blanc +> term_ad) 
               +| (term_if +> p_Blanc
                  +> 
                  term_pg +> p_Blanc +> (p_Var +| p_Cst) +> p_Blanc +> term_pd +> p_Blanc 
                  +> 
                  term_ag +> p_Blanc +> p_S +> term_ad +> p_Blanc 
                  +> 
                  term_ag +> p_Blanc +> p_S +> term_ad) 
               +| epsilon) l
  in fun l -> ((p_I +> p_L)+| epsilon) l
  
  
let t1 = list_of_string "a:=1;";;
let _ = p_S t1;;

let t2 = list_of_string "a:=1;b:=1;w(a){b:=1}";;
let _ = p_S t2;;

let t3 = list_of_string "  a:=1;b:=1;i(1){b:=1}{c:=0}";;
let res = p_S t3;;

let t4 = list_of_string "i(1){b:=a}{c:=0}";;
let res = p_S t4;;

let isWhileLanguage = fun l -> let l = p_S l in
  match l with
  | [] -> true
  | _ -> false;;

isWhileLanguage t1;;
isWhileLanguage t2;;
isWhileLanguage t3;;
isWhileLanguage t4;;