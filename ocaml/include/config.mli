module Config:
sig
  type state

  type config

  val init : state 

  val aux : state

  val get : int 

  val update : state   

  val index_var : int

  val value_exp : exp -> state -> int

  val eval : exp -> state -> bool

  val faire_un_pas : winstr

  val executer : bool

  val nombre_de_pas : int

  val __nombre_de_pas : int

  val print_state : state 

  val __print_state : state

  val executer_interactif : bool

end;;

