
(* ---- STAIC ANALYSIS ----
How to analyze types: symbolic execution of program where the only values are types (statically) => define a controller for our language 
*)

(* Which types I have in the language *)
type ttype =
  | Tint
  | Tbool
  | Tfun of ttype * ttype;; (* element's type and result's type  *)

type expr =
  | Eint of int
  | Ebool of bool
  | Var of string
  | LetIn of string * expr * expr
  | Prim of string * expr * expr
  | If of expr * expr * expr
  | Fun of string * ttype * expr (* param (string), annotates the param with the type of argument (not indicates result's type because it is calculates) *)  
  | Call of expr * expr;;
  
(* in our language this list contains the runtime values, now it contains the type annotation binded to the variables *)
type 'v env = (string * 'v) list;;

let rec lookup env x =
    match env with
    | []        -> failwith (x ^ " not found")
    | (y, v)::r -> if x=y then v else lookup r x;;

(* basic types for primitive operations *)
let basicTypes = [
  "+", Tfun(Tint, Tfun(Tint, Tint)); (* take an Integer and "it says that it calculates a sum between Integer and return an Integer" *)
  "-", Tfun(Tint, Tfun(Tint, Tint));
  "*", Tfun(Tint, Tfun(Tint, Tint));
  "<", Tfun(Tint, Tfun(Tint, Tbool));
  "and", Tfun(Tbool, Tfun(Tbool, Tbool));
  "or", Tfun(Tbool, Tfun(Tbool, Tbool))
];;

exception Type_error of string;;

let rec type_of gamma e = (* symbols table (gamma) (env), 
e is the program to check type *)
  match e with
  | Eint(_) -> Tint
  | Ebool(_) -> Tbool
  | Var(x)  -> lookup gamma x
  | LetIn(x, e1, e2) ->
    let t1 = type_of gamma e1 in
    type_of ((x,t1)::gamma) e2 (* vado a vedere qual è il tipo di 'e2' (
      corpo let) nell'ambiente di tipo esteso con il legame tra il nome della
      variabile 'x' introdotta nel let e il tipo 't1', che è il tipo della
      espressione 'e1'. Se questo mi da un certo tipo,
      allora sarà il tipo associato al let. 
      Quindi quando definisco un let, il tipo del let sarà il tipo del corpo
      'e2' ma valutato in una tabella dei simboli che oltre a tutte le info 
      che aveva prima contiene anche il legame tra la variabile che ho
      introdotto nel let e il tipo dell expr 'e1' che una volta valutata sarà 
      il valore di base del let! *)
  | If(e1, e2, e3) ->
    if (type_of gamma e1) = Tbool then
      let t2 = type_of gamma e2 in
      let t3 = type_of gamma e3 in
      if t2 = t3 then t2 else raise (Type_error "if branches have different types") (* they must have the same type to enforce "composizionalità"*)
    else
      raise (Type_error "if with no a boolean guard")
  | Fun(x, tx, e) -> Tfun(tx, type_of ((x, tx) :: gamma) e) (*
      tipo primo elemento (var), poi vede qual è il tipo della espressione 
      (corpo della funzione) in un ambiente esteso con 
      il legame tra il nome del parametro formale e il suo tipo, 
      e da il tipo del risultato *)
  | Prim("=", e1, e2) ->
    let t1 = type_of gamma e1 in
    let t2 = type_of gamma e2 in
    begin
      match t1, t2 with
      | Tint, Tint
      | Tbool, Tbool -> Tbool
      | Tfun(_,_), Tfun(_,_) ->
        raise (Type_error "Error comparing functional values for equality")
      | _, _ -> raise (Type_error "error in the arguments of =")
    end
  | Prim(op, e1, e2) ->
    let t1 = type_of gamma e1 in
    let t2 = type_of gamma e2 in
    let top = lookup gamma op in
    begin
      match top with
      | Tfun(t1', Tfun(t2', tr')) ->
        if (t1' = t1 && t2' = t2) then
          tr'
        else
          raise (Type_error ("error in the arguments of " ^ op))
      | _ -> failwith "Inconsistent state"
    end
  | Call(e1, e2) ->
    let t1 = type_of gamma e1 in
    let t2 = type_of gamma e2 in
    begin
      match t1 with
      | Tfun(tx, tr) -> (* prende argomento e da risultato,
       deve anche controllare che quando passso i parametri deve esserci 
       un match tra il tipo dell argomento (attuale) e il tipo aspettato
      (formale) *)
        if tx = t2 then (* t2 è il tipo attuale, tx è l'aspettato*)
          tr (* restituisco il tipo del risultato *)
        else
          raise (Type_error "fuctional application: argument type mismatch")
      | _ -> raise (Type_error "application to a non functional value")
end ;;

let type_check e = type_of basicTypes e;;


