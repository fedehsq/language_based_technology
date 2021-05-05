(* ---- DECLARATION OF TYPES ---- *)
(* ----------- DFA --------------*)

(*
DFA
• A deterministic ﬁnite automaton M is a 5tuple, (Q, Σ, δ, q0, F), consisting of
– a ﬁnite set of states (Q)
– a ﬁnite set of input symbols called the alphabet (Σ)
– a transition function (δ : Q × Σ → Q)
– a start state (q0 ∈ Q)
– a set of accepti ng states (F ⊆ Q)
*)

(* Respresents states of dfa as int *)
type state = int;;

(* Represents symbols (alphabet) as a char *)
type symbol = char;;

(* transaction function delta *)
type transition = state * symbol * state;;

(* description of dfa *)
type dfa = 
{
  states : state list;
  sigma : symbol list;
  start : state;
  transitions : transition list;
  accepting : state list;
  error : string;
};;

(*
explode takes a string `s`, and turns it into its individual
characters. This way we can run the DFA on the string "101"
without explicitly writing ['1';'0';'1']
*)
let explode s =
  let rec expl i l =
    if i < 0 
      then l 
      (* s.[i] returns the ith element of s as a char *)
    else expl (i - 1) (s.[i] :: l) in 
   (* String.length s returns the length of s *)
      expl (String.length s - 1) [];;

(* 
another helper function that checks whether a list contains an
element *)
let rec contains e l =
  match l with
  | [] -> false
  | hd::tl -> if hd = e then true else contains e tl;;

(*
Checking DFA Acceptance
• Attempt 1: we might keep a (mutable) 
variable that keeps track of what state the
DFA is currently at, and then updates the state depending on that.
*)
let check_accepts str dfa =
  (* Get the list of symbols. *)
  let symbols = explode str in
    (* If I'm at state {state}, where do I go on {symbol}? *)
    let transition state symbol =
      let rec find_state l =
        match l with
        | (s1, sym, s2)::tl ->
          if (s1 = state && symbol = sym) then s2 else find_state tl
        | _ -> failwith "no next state" 
      in find_state dfa.transitions      
    in let final_state = 
      let rec h symbol_list =
        match symbol_list with
        | [hd] -> (transition dfa.start hd)
        | hd::tl -> (transition (h tl) hd)
        | _ -> failwith "empty list of symbols"
      in h (List.rev symbols) in
        if (contains final_state dfa.accepting) then 
          true 
        else false;;

(* --------------- Language ----------------*)
(* Critical resource *)
type resource =
  | Database
  | File
  | Socket
  | Net;;

(* expressions of language *)
type exp = 
  | Enone (* termination of List / tuple*)
  | Eint of int
  | Echar of char
  | Ebool of bool
  | Estring of string
  | Elist of exp (* Eitem or None*)
  | Eitem of exp * exp (* element and something other or Enone *)
  | Epolicy of exp (* Programmer can define policies => Elist(Eitem(Edfa...)) *)
  | Read of resource (* Sensible operation: access event α *)
  | Write of resource (* Sensible operation: access event α *)
  | Download of resource (* Sensible operation: access event α *)
  | Connect of resource (* Sensible operation: access event α *)
  | Check of exp * exp (* Block where to check if policy is satisfied, second exp must be a Epolicy *)
  | Var of string
  | Plus of exp * exp (* + of Int * Int *)
  | Minus of exp * exp (* - of Int * Int *)
  | Mul of exp * exp (* * of Int * Int *)
  | Div of exp * exp (* / of Int * Int *)
  | Greater of exp * exp (* e1 > e2 *)
  | Minor of exp * exp (* e1 < e2 *)
  | Equals of exp * exp (* e1 == e2 *)
  | Concat of exp * exp (* s1 ^ s2 *)
  | IfThenElse of exp * exp * exp (* "guardia", then, else *)
  (* The following builder permits to give a name to an exp *)
  | LetIn of string * exp * exp  (* ide, value to associate to ide, body of let 
  i.e y (ide) = 5 (exp) in y + x (exp)  *)
  (* Lambda is anonymous => it hasn't a name! 'ide' is the formal parameter!
  i.e f(x) = x + 1  => x is the formal parameter, x + 1 is the body *)
  | Lambda of string * exp (* formal parameter with function body *)
  | LambdaRec of string * exp (* function name, exp must be Lambda *)
  | Apply of exp * exp (* Lambda with acutal parameter *)
  | Edfa of
      exp * (* Elist(Eitem(Eint 0, Eitem(Eint 1, Enone)) *)
      exp * (* Elist(Eitem(Echar 'w', Eitem(Echar 'r', Enone)) *)
      exp * (* Eint 0 *)
      exp * (* Elist(Eitem(Eint 0, Eitem(Echar 'r', Eitem(Eint 1, Enone))) *)
      exp * (* Elist(Eitem(Eint 0, Eitem(Eint 1, Enone)) *)
      exp   (* Estring "error" *)
  ;;

(* environment is a couple list of ide with their value *)
type 'v env = (string * 'v)list;; 

(* language values *)
type value =
  | None (* List termination *)
  | Int of int
  | Char of char
  | Bool of bool
  | String of string
  | Policy of value (* local policies => List(Item(Dfa(...), Item(Dfa(...), None)) *)
  | Closure of string * exp * value env (* formal param, body, env *)
  | RecClosure of string * string * exp * value env (* Lambda name, formal param, body, env *)
  | List of value (* List(Item(Int 5, Item(Int 6, None))) *)
  | Item of value * value (* Item(Int 5, Item(Int 6, None)) *)
  | Dfa of
      value * (* List(Item(Int 0, Item(Int 1, None)) *)
      value * (* List(Item(Char 'w', Item(Char 'r', None)) *)
      value * (* Int 0 *)
      value * (* List(Item(Int 0, Item(Char 'r', Item(Int 1, None))) *)
      value * (* List(Item(Int 0, Item(Int 1, None)) *)
      value   (* String "error" *)
  ;;

(* ---- DECLARATION OF FUNCTIONS ---- *)

(* associate var with value to env *)
let bind (var: string) (value: value) (env: 'v env) =
  (var, value)::env;;

(* It checks if var has a associated value in the environment env  *)
let rec lookup (env: 'v env) (var: string) : value = 
  match env with
  | [] -> failwith(var ^ " not found")
  | (ide, value)::envs -> if (ide = var) then value else lookup envs var;;

(* basic operations *)
let calculator (op: string) (x: value) (y: value): value =
    begin match (op, x, y) with
    | ("+", Int x, Int y) -> Int (x + y)
    | ("-", Int x, Int y) -> Int (x - y)
    | ("*", Int x, Int y) -> Int (x * y)
    | ("/", Int x, Int y) -> Int (x / y)
    | (">", Int x, Int y) -> Bool (x > y)
    | ("<", Int x, Int y) -> Bool (x < y)
    | ("==", Int x, Int y) -> Bool (x = y)
    | ("==", Bool x, Bool y) -> Bool (x = y)
    | ("==", String x, String y) -> Bool (x = y)
    | ("^", String x, String y) -> String (x ^ y)
    | (_, _, _) -> failwith("Not yet implemented")
    end;;

(* It takes the dfa, history, and actual op to check.
return the val (1 if success),  and the updated history *)
let rec ieval (policies: dfa list) (history: string)
  : (value * exp * string) =
  (* check if some policy is here *)
  match policies with
  | [] -> (Int 1, Elist(Enone), history)
  | hd::tl -> (* check the current policy *)
    (* Check if the op can be done checking policy *)
    if check_accepts history hd then 
      (* call on previous policy (extern) *)
      ieval tl history
    else 
      (* op cannot be respect policy => abort *)
      failwith(hd.error)
    ;; 

(* Helper functions to convert an exp into a primitive oCaml values (for dfa) *)

(* Verifies if a particular exp is a correct policy definition *)
  let rec verify_edfa_list(dfa_list : exp) : bool =
    match dfa_list with
    | Enone -> true
    | Eitem(x, y) -> 
      begin match x with
      | Edfa _ -> verify_edfa_list y
      | _ -> false
      end
    | _ -> false 

(* Convert Eitem(Eint x, ...)) in int list *)
let rec parse_int_item(item: exp) : int list =
  match item with
  | Enone -> []
  | Eitem(x, y) -> 
    begin match x with
    | (Eint x) -> x::parse_int_item y
    | _ ->  failwith ("type parse int item error")
  end
  | _ -> failwith ("type parse int item error");;

(* Convert Elist(Eitem(Eint x, ...)) in int list *)
let parse_int_list(list : exp) : int list =
  match list with
  | Enone -> []
  | Elist l -> 
    begin match l with
    | Eitem(x, y) -> parse_int_item (Eitem(x, y))
    | _ -> failwith ("type int list error")
  end
  | _ -> failwith("type int list error")
;;

(* Convert (Eitem(Echar x, ...)) in char list *)
let rec parse_char_item(item: exp) : char list =
  match item with
  | Enone -> []
  | Eitem(x, y) -> 
    begin match x with
    | (Echar x) -> x::parse_char_item y
    | _ ->  failwith ("type char item error")
  end
  | _ -> failwith ("type char item error");;

(* Convert Elist(Eitem(Echar x, ...)) in char list *)
let parse_char_list(list : exp) : char list =
  match list with
  | Enone -> []
  | Elist l -> 
    begin match l with
    | Eitem(x, y) -> parse_char_item (Eitem(x, y))
    | _ -> failwith ("type char list error")
  end
  | _ -> failwith("type char list error")
;;
  
(* Build the triple representing the dfa transitions starting from exp *)
let rec parse_transition_item(item: exp) : (int * char * int) list =
  match item with
  | Enone -> []
  | Eitem(x, y) -> 
    begin match x, y with
    (* Represents the triple of transition *)
    | (Eint z, Eitem(Echar c, Eitem(Eint i, Enone))) -> [(z, c, i)]
    | (Eint z, Eitem(Echar c, Eitem(Eint i, Eitem(e, t)))) -> (z, c, i)::parse_transition_item (Eitem(e, t))
    | _ ->  failwith ("type item error")
  end
  | _ -> failwith ("type i error");;

(* Convert Elist(Eitem(Eint x, Echar(c, Eitem(Eint y, Enone)...)) in (int * char * int) list *)
let parse_transition_list(list : exp) : (int * char * int) list =
  match list with
  | Enone -> []
  | Elist l -> 
    begin match l with
    | Eitem(x, y) -> parse_transition_item (Eitem(x, y))
    | _ -> failwith ("type list error")
  end
  | _ -> failwith("type lt error")
;;

(* Convert Estring to string *)
let parse_string(estring : exp) : string =
  match estring with
  | Estring s -> s
  | _ -> failwith "type parse string error";;

(* Convert Eint to int *)
let parse_int(eint : exp) : int =
  match eint with
  | Eint i -> i
  | _ -> failwith "type parse int error";;


(* Takes an exp and check that it is of Edfa type, 
   then convert this Edfa to basic dfa, with oCaml primiteves values *)
let rec to_ocaml_dfa(dfa: exp) : dfa =
match dfa with
| Edfa(states, sigma, start, transition, accepting, error) -> 
    {
    states = parse_int_list states; (* convert Elist(Eitem(Eint x, ...)) in int list *)
    sigma = parse_char_list sigma; (* convert Elist(Eitem(Echar x, ...)) in char list *)
    start = parse_int start; (* convert Eint x in int x *)
    transitions = parse_transition_list transition; (* convert Elist(Eitem(Eint x, Echar(c, Eitem(Eint y, Enone)...)) in (int * char * int) list *)
    accepting = parse_int_list accepting; (* convert Elist(Eitem(Eint x, ...)) in int list *)
    error = parse_string error; (* convert Estring s in string s *)
  }
| _ -> failwith("Dfa error");;

(* Convert Eitem(Edfa d, ...) in dfa list *)
let rec parse_dfa_item(item: exp) : dfa list =
  match item with
  | Enone -> []
  | Eitem(x, y) -> to_ocaml_dfa x::parse_dfa_item y
  | _ -> failwith ("type parse dfa item error");;

(* Convert Elist(Eitem(Edfa d, ...)) in dfa list *)
let parse_dfa_list(list : exp) : dfa list =
  match list with
  | Enone -> []
  | Elist l -> 
    begin match l with
    | Enone -> []
    | Eitem(x, y) -> parse_dfa_item (Eitem(x, y))
    | _ -> failwith ("type parse dfa list internal error")
  end
  | _ -> failwith("type parse dfa list external error")
;;

(* Head pushing Eitem l1 to Eitem l2 *)
let rec cons l1 l2 : exp =
  match l1 with
  | Enone -> l2
  | Eitem(x, y) -> Eitem(x, cons y l2)
  | _ -> failwith("append error")

(* Interpreter: return a triple => value, dfa, and string (op) *)
let eval (exp: exp) (env: 'v env): (value) = 

  (* list of dfa *)
  let rec rec_eval (exp: exp) (env: 'v env) (dfa: exp) (op : string): 
  (value * exp * string) =
  match exp with
  | Enone -> (None, dfa, op)
  | Eint x -> (Int x, dfa, op)
  | Echar c -> (Char c, dfa, op)
  | Ebool b -> (Bool b, dfa, op)
  | Estring s -> (String s, dfa, op)
  | Elist l ->
    begin match rec_eval l env dfa op with
    | (Item(x, y), _, _) -> (List(Item(x, y)), dfa, op)
    | (None, _, _) -> (List(None), dfa, op)
    | _ -> failwith("Wrong List declaration")
    end
  | Eitem(x, y) -> 
    let (x, _, _) = rec_eval x env dfa op in 
    let (y, _, _) = rec_eval y env dfa op in 
    (* Check if y is a termination element ora another Eitem *)
      begin match y with
      | None -> (Item(x, y), dfa, op)
      | Item(_ ,_) -> (Item(x, y), dfa, op)
      | _ -> failwith("Wrong item declaration")
    end
  (* Local policies as language primiteves => must be Elist(Eitem(Edfa...)) *)
  | Epolicy p -> 
    begin match p with
    | Elist l -> 
      (* Verify that all Eitem in Elist are Edfa *)
      if verify_edfa_list l then
        let (p, _ ,_) = rec_eval p env dfa op in ((Policy p), dfa, op)
      else 
        failwith("Wrong policies declaration")
    | _ -> failwith("Wrong policies declaration")
      end
  | Read r -> 
    (* Check if policy is a list of automata; the head of p is the current policy *)
    begin match dfa with
    | Epolicy p -> ieval (parse_dfa_list p) (op ^ "r")
    | _ -> failwith ("type error")
    end
  | Write w -> 
    (* Check if policy is a list of automata; the head of p is the current policy *)
      begin match dfa with
    | Epolicy p -> ieval (parse_dfa_list p) (op ^ "w")
    | _ -> failwith ("type error")
    end
  | Download d -> 
    (* Check if policy is a list of automata; the head of p is the current policy *)
      begin match dfa with
    | Epolicy p -> ieval (parse_dfa_list p) (op ^ "d")
    | _ -> failwith ("type error")
    end
  | Connect c -> 
    (* Check if policy is a list of automata; the head of p is the current policy *)
    begin match dfa with
    | Epolicy p -> 
      ieval (parse_dfa_list p) (op ^ "c")
    | _ -> failwith ("type error")
  end
  (* Head pushing the current policy *)
  | Check(block, policy) -> 
    begin match (dfa, policy) with
    | (Epolicy prev, Epolicy curr) ->
      (* check correct policy declarations *)
      begin match prev, curr with
      | Elist l1, Elist l2 -> 
        if verify_edfa_list l1 && verify_edfa_list l2 then
          begin match l2, l1 with
          | Eitem(_, _), Enone -> 
            (* Cons new policy to other ones *)
            rec_eval block env (Epolicy(Elist(cons l2 l1))) op
            | Eitem(_, _), Eitem (_, _) ->  
             rec_eval block env (Epolicy(Elist(cons l2 l1))) op
          | _ -> failwith("")
          end
        else
          failwith("Wrong policy if declaration")
      | _ -> failwith("Wrong policy if declaration")
      end
    | _ -> failwith("Wrong policy declaration")
    end
  | Var(x) -> (lookup env x, dfa, op)
  | IfThenElse(guardia, t, e) -> 
      begin match rec_eval guardia env dfa op with
      | (Bool b, _, _) -> if b then rec_eval t env dfa op else rec_eval e env dfa op
      | _ -> failwith("not a valid statement")
      end 
  | Plus(x, y) -> 
    let (x, _, _) = (rec_eval x env dfa op) in 
    let (y, _, _) = (rec_eval y env dfa op) in
    (calculator "+" x y, dfa, op)
  | Minus(x, y) -> 
    let (x, _, _) = (rec_eval x env dfa op) in 
    let (y, _, _) = (rec_eval y env dfa op) in
    (calculator "-" x y, dfa, op)
  | Mul(x, y) -> 
    let (x, _, _) = (rec_eval x env dfa op) in 
    let (y, _, _) = (rec_eval y env dfa op) in
    (calculator "*" x y, dfa, op)
  | Div(x, y) -> 
    let (x, _, _) = (rec_eval x env dfa op) in 
    let (y, _, _) = (rec_eval y env dfa op) in
    (calculator "/" x y, dfa, op)
  | Greater(x, y) -> 
    let (x, _, _) = (rec_eval x env dfa op) in 
    let (y, _, _) = (rec_eval y env dfa op) in
    (calculator ">" x y, dfa, op)
  | Minor(x, y) -> 
    let (x, _, _) = (rec_eval x env dfa op) in 
    let (y, _, _) = (rec_eval y env dfa op) in
    (calculator "<" x y, dfa, op)
  | Equals(x, y) -> 
    let (x, _, _) = (rec_eval x env dfa op) in 
    let (y, _, _) = (rec_eval y env dfa op) in
    (calculator "==" x y, dfa, op)
  | Concat(x, y) -> 
    let (x, _, _) = (rec_eval x env dfa op) in 
    let (y, _, _) = (rec_eval y env dfa op) in
    (calculator "^" x y, dfa, op)
  | LetIn(ide, value, body) ->
      (* "calculate" value AND UPDATE STRING OP!! HISTORY!!... *)
      let (v, _, history) = rec_eval value env dfa op in 
      (* ... and bind this value to the ide for creating new env 
      (new value on the stack).. *)
      let new_env = bind ide v env in
      (* ... and use it in the body WITH UPDATED HISTORY!! *)
      rec_eval body new_env dfa history
  (* define functions*)
  (* ---- WARNING ----
      var isn't the name of function! It is the argument, 
      the formal parameter of function!
      i.e f (x) = x + 1   =>  var is x! Not the name of function! 
      For naming a function we must use the builder LetIn! 
      *)
  | Lambda(param, body) -> (Closure(param, body, env), dfa, op)

  (* in this case the function is not anonymous anymore, it has a name *)
  | LambdaRec(f_name, f_def) -> 
    (* check if f_def is a Func *)
      begin match f_def with
      | Lambda(param, body) ->
        (* build new env with rec function *)
       RecClosure(f_name, param, body, env), dfa, op
      | _ -> failwith("non functional def")  
    end
  
  (* Apply an anonymous lambda or a named lambda *)
  | Apply(f, actual_param) -> 
      let (func, _, _) = rec_eval f env dfa op in
      begin match func with
      | Closure(formal_param, body, decl_env) -> 
        (* rec_evaluate the ACTUAL param in the current environment and update history *)
        let (a_p, _, history) = rec_eval actual_param env dfa op in
        (* BIND THE FORMAL PARAMETER TO THE ACTUAL ONE AND ADD THEM TO DECL ENV! *)
        let new_env = bind formal_param a_p decl_env in
        (* calculate the functions with the extened env and extended history! *)
        rec_eval body new_env dfa history
      
      | RecClosure(f_name, formal_param, f_body, decl_env) -> 
        (* rec_evaluate the ACTUAL param in the current environment and update history *)
        let (a_p, _, history) = rec_eval actual_param env dfa op in
        (* bind func value to func name *)
        let r_env = bind f_name func decl_env in
        (* BIND THE FORMAL PARAMETER TO THE ACTUAL ONE AND ADD THEM TO DECL ENV! *)
        let new_env = bind formal_param a_p r_env in
        (* calculate the functions with the extened env! *)
        rec_eval f_body new_env dfa history 
      | _ -> failwith("not a function")
      (* empty policy at the beginning of program *)
      end
  (* Dfa *)
  | Edfa(states, sigma, start, transition, accepting, error) -> 
    let (states, _, _) = rec_eval states env dfa op in
    let (sigma, _, _) = rec_eval sigma env dfa op in
    let (start, _, _) = rec_eval start env dfa op in
    let (transitions, _, _) = rec_eval transition env dfa op in
    let (accepting, _, _) = rec_eval accepting env dfa op in
    let (error, _, _) = rec_eval error env dfa op in
    begin match (states, sigma, start, transitions, accepting, error) with
    (* ---- ASSUMING CORRECT LIST TYPE HERE, CHECK WILL BE DONE LATER ----- *)
    | (List _, List _, Int _, List _, List _, String _) -> 
      Dfa(
        states,
        sigma,
        start,
        transitions,
        accepting,
        error)
        , dfa, op
    | _ -> failwith("Wrong dfa definition")
    end
  (* Empty policies list to start of program *)
  in let (r, _, _) = rec_eval exp env (Epolicy(Elist(Enone))) "" in r;;

(* -----
no_r_w: no write after read
no_w_r: no read after write
no_r: no read
no_w_ no write
------ 
*)
let no_r = Edfa(
  Elist(Eitem(Eint 0, Eitem(Eint 1, Enone))), (* states *)
  Elist(Eitem(Echar 'r', Eitem(Echar 'w', Eitem(Echar 'c', Eitem(Echar 'd', Enone))))), (* sigma *)
  Eint 0, (* start *)
  Elist(Eitem(Eint 0, Eitem(Echar 'w', Eitem(Eint 0,
        Eitem(Eint 0, Eitem(Echar 'r', Eitem(Eint 1,
        Eitem(Eint 0, Eitem(Echar 'd', Eitem(Eint 0,
        Eitem(Eint 0, Eitem(Echar 'c', Eitem(Eint 0,
        Eitem(Eint 1, Eitem(Echar 'r', Eitem(Eint 1,
        Eitem(Eint 1, Eitem(Echar 'w', Eitem(Eint 1, 
        Eitem(Eint 1, Eitem(Echar 'd', Eitem(Eint 1,
        Eitem(Eint 1, Eitem(Echar 'c', Eitem(Eint 1, 
        Enone))))))))))))))))))))))))), (* transitions *)
  Elist(Eitem(Eint 0, Enone)), (* accepting *)
  Estring("Read detected") (* failure message *)
);;

let no_w = Edfa(
  Elist(Eitem(Eint 0, Eitem(Eint 1, Enone))), (* states *)
  Elist(Eitem(Echar 'r', Eitem(Echar 'w', Eitem(Echar 'c', Eitem(Echar 'd', Enone))))), (* sigma *)
  Eint 0, (* start *)
  Elist(Eitem(Eint 0, Eitem(Echar 'w', Eitem(Eint 1,
        Eitem(Eint 0, Eitem(Echar 'r', Eitem(Eint 0,
        Eitem(Eint 0, Eitem(Echar 'd', Eitem(Eint 0,
        Eitem(Eint 0, Eitem(Echar 'c', Eitem(Eint 0,
        Eitem(Eint 1, Eitem(Echar 'r', Eitem(Eint 1,
        Eitem(Eint 1, Eitem(Echar 'w', Eitem(Eint 1, 
        Eitem(Eint 1, Eitem(Echar 'd', Eitem(Eint 1,
        Eitem(Eint 1, Eitem(Echar 'c', Eitem(Eint 1, 
        Enone))))))))))))))))))))))))), (* transitions *)
  Elist(Eitem(Eint 0, Enone)), (* accepting *)
  Estring("Write detected") (* failure message *)
);;

let no_r_w = Edfa(
  Elist(Eitem(Eint 0, Eitem(Eint 1, Eitem(Eint 2, Enone)))), (* states *)
  Elist(Eitem(Echar 'r', Eitem(Echar 'w', Eitem(Echar 'c', Eitem(Echar 'd', Enone))))), (* sigma *)
  Eint 0, (* start *)
  Elist(Eitem(Eint 0, Eitem(Echar 'r', Eitem(Eint 1,
        Eitem(Eint 0, Eitem(Echar 'w', Eitem(Eint 0,
        Eitem(Eint 0, Eitem(Echar 'd', Eitem(Eint 0,
        Eitem(Eint 0, Eitem(Echar 'c', Eitem(Eint 0,
        Eitem(Eint 1, Eitem(Echar 'w', Eitem(Eint 2,
        Eitem(Eint 1, Eitem(Echar 'r', Eitem(Eint 1, 
        Eitem(Eint 1, Eitem(Echar 'd', Eitem(Eint 1,
        Eitem(Eint 1, Eitem(Echar 'c', Eitem(Eint 1, 
        Eitem(Eint 2, Eitem(Echar 'w', Eitem(Eint 2,
        Eitem(Eint 2, Eitem(Echar 'r', Eitem(Eint 2, 
        Eitem(Eint 2, Eitem(Echar 'd', Eitem(Eint 2,
        Eitem(Eint 2, Eitem(Echar 'c', Eitem(Eint 2, 
        Enone))))))))))))))))))))))))))))))))))))), (* transitions *)
  Elist(Eitem(Eint 0, Eitem(Eint 1, Enone))), (* accepting *)
  Estring("Write after read detected") (* failure message *)
);;

let no_w_r = Edfa(
  Elist(Eitem(Eint 0, Eitem(Eint 1, Eitem(Eint 2, Enone)))), (* states *)
  Elist(Eitem(Echar 'r', Eitem(Echar 'w', Eitem(Echar 'c', Eitem(Echar 'd', Enone))))), (* sigma *)
  Eint 0, (* start *)
  Elist(Eitem(Eint 0, Eitem(Echar 'w', Eitem(Eint 1,
        Eitem(Eint 0, Eitem(Echar 'r', Eitem(Eint 0,
        Eitem(Eint 0, Eitem(Echar 'd', Eitem(Eint 0,
        Eitem(Eint 0, Eitem(Echar 'c', Eitem(Eint 0,
        Eitem(Eint 1, Eitem(Echar 'r', Eitem(Eint 2,
        Eitem(Eint 1, Eitem(Echar 'w', Eitem(Eint 1, 
        Eitem(Eint 1, Eitem(Echar 'd', Eitem(Eint 1,
        Eitem(Eint 1, Eitem(Echar 'c', Eitem(Eint 1, 
        Eitem(Eint 2, Eitem(Echar 'w', Eitem(Eint 2,
        Eitem(Eint 2, Eitem(Echar 'r', Eitem(Eint 2, 
        Eitem(Eint 2, Eitem(Echar 'd', Eitem(Eint 2,
        Eitem(Eint 2, Eitem(Echar 'c', Eitem(Eint 2, 
        Enone))))))))))))))))))))))))))))))))))))), (* transitions *)
  Elist(Eitem(Eint 0, Eitem(Eint 1, Enone))), (* accepting *)
  Estring("Read after read detected") (* failure message *)
);;

(* How λ works: if I want to execute e1;e2 => the following
  abbreviation is standard: e1; e2 = (λ.e2)e1 is a
function without params that it has e2 as body, 
it is applied with e1. eval e1 then pass the params. 
But the function hasn't params so it execs the body of function e2 
without passsing params.
THE EFFECT IS EXECUTING IN SEQUENCES e1; e2; AND THE RESULT IS THE TYPE OF e2 *)

let env = [];;

(* dfa *)
eval no_r env;;

(* policy *)
eval (Epolicy(Elist(Eitem(no_r_w, Enone)))) env;;

(* read; φ[write]   φ = no write after read *)
eval(Apply(Lambda("x", Check(Write(File), 
  Epolicy(Elist(Eitem(no_r_w, Enone))))), Read(Socket))) env;;
(* Exception: Failure "Write after read detected". *)

(* write; φ[read] ok   φ = no write after read  *)
eval(Apply(Lambda("x", Check(Read(File), 
  Epolicy(Elist(Eitem(no_r_w, Enone))))), Write(Socket))) env;;
(* value = Int 1*)

(* φ[read; write]    φ = no write after read *)
eval(Check(Apply(Lambda("x", Write(File)), Read(Socket)),
  Epolicy(Elist(Eitem(no_r_w, Enone))))) env;;
(* Exception: Failure "Write after read detected". *)

(* φ[φ'[read]; write]    φ = no read, φ' = no read after write *)
eval (Check(Apply(Lambda("x", Write(File)), 
  Check(Read(Socket), Epolicy(Elist(Eitem(no_w_r, Enone))))), 
    Epolicy(Elist(Eitem(no_r, Enone))))) env;;
(* Exception: Failure "Read detected". *)

(* φ[read; φ'[write]]    φ = no write after read, φ' = no read after write *)
eval (Check(Apply(Lambda("x", 
  Check(Write(Socket), Epolicy(Elist(Eitem(no_w_r, Enone))))), 
  Read(Socket)),
  Epolicy(Elist(Eitem(no_r_w, Enone))))) env;;
(* Exception: Failure "Write after read detected". *)

(* φ'[φ[φ'[read]; φ'[write]; φ'[connect]]; φ'[download]; φ'[read]] => (φ[φ'[read]; φ'[write]; φ'[connect]] broken) 
  φ = no write after read, φ' = no read after write
*)
eval (Check(
        Apply(
          Lambda("x", 
            Check(
              Read(Socket), 
              Epolicy(Elist(Eitem(no_w_r, Enone)))
            )
          ), 
          Apply(
            Lambda("x", 
              Check(
                Download(Socket), 
                Epolicy(Elist(Eitem(no_w_r, Enone)))
              )
            ), 
            Check( (* ... φ[φ'[read]; φ'[write], φ'[connect]] ... *)
              Apply(
                Lambda("x", 
                  Check(
                    Connect(Socket), 
                    Epolicy(Elist(Eitem(no_w_r, Enone)))
                  )
                ), 
                Apply(
                  Lambda("x", 
                    Check(
                      Write(Socket),
                      Epolicy(Elist(Eitem(no_w_r, Enone)))
                    )
                  ), 
                  Check(
                    Read(Socket), 
                    Epolicy(Elist(Eitem(no_w_r, Enone)))
                  )
                )
              ), 
            Epolicy(Elist(Eitem(no_r_w, Enone)))
          )
        )
      ),
      Epolicy(Elist(Eitem(no_w_r, Enone))
    )
  )
) env;;
(* Exception: Failure "Write after read detected". *)

(* φ'[φ[φ'[read]; φ'[read], φ'[connect]], φ'[download], φ'[write]] (ok) 
  φ = no write after read, φ' = no read after write
*)
eval (Check(
        Apply(
          Lambda("x", 
            Check(
              Write(Socket), 
              Epolicy(Elist(Eitem(no_w_r, Enone)))
            )
          ), 
          Apply(
            Lambda("x", 
              Check(
                Download(Socket), 
                Epolicy(Elist(Eitem(no_w_r, Enone)))
              )
            ), 
            Check( (* ... φ[φ'[read]; φ'[read], φ'[connect]] ... *)
              Apply(
                Lambda("x", 
                  Check(
                    Connect(Socket), 
                    Epolicy(Elist(Eitem(no_w_r, Enone)))
                  )
                ), 
                Apply(
                  Lambda("x", 
                    Check(
                      Read(Socket),
                      Epolicy(Elist(Eitem(no_w_r, Enone)))
                    )
                  ), 
                  Check(
                    Read(Socket), 
                    Epolicy(Elist(Eitem(no_w_r, Enone)))
                  )
                )
              ), 
              Epolicy(Elist(Eitem(no_r_w, Enone)))
            )
          )
        ),
      Epolicy(Elist(Eitem(no_w_r, Enone))
    )
  )
) env;;
(* value = Int 1*)

(* φ'[φ[φ'[write]; φ'[write]; φ'[connect]]; φ'[download]; φ'[read]] => (last φ' broken )
  φ = no write after read, φ' = no read after write
*)
eval (Check(
        Apply(
          Lambda("x", 
            Check(
              Read(Socket), 
              Epolicy(Elist(Eitem(no_w_r, Enone)))
            )
          ), 
          Apply(
            Lambda("x", 
              Check(
                Download(Socket), 
                Epolicy(Elist(Eitem(no_w_r, Enone)))
              )
            ), 
            Check( (* ... φ[φ'[read]; φ'[read], φ'[connect]] ... *)
              Apply(
                Lambda("x", 
                  Check(
                    Connect(Socket), 
                    Epolicy(Elist(Eitem(no_w_r, Enone)))
                  )
                ), 
                Apply(
                  Lambda("x", 
                    Check(
                      Write(Socket),
                      Epolicy(Elist(Eitem(no_w_r, Enone)))
                    )
                  ), 
                  Check(
                    Write(Socket), 
                    Epolicy(Elist(Eitem(no_w_r, Enone)))
                  )
                )
              ), 
              Epolicy(Elist(Eitem(no_r_w, Enone)))
            )
          )
        ),
      Epolicy(Elist(Eitem(no_w_r, Enone))
    )
  )
) env;;
(* Exception: Failure "Read after write detected". *)

(* let rec fact x = if x <= 1 then 1 else x * fact(x - 1); fact(5) *)
eval
  (* call *)
  (Apply(
    (* rec fun name, formal param *)
    (LambdaRec("fact", (Lambda("x", 
      (* if x < 1*)
      IfThenElse(Minor(Var "x", Eint 1), 
      (* then*)
        Eint 1,
      (* else *)
        Mul(Var "x", (Apply(Var "fact", Minus(Var "x", Eint 1)))) 
      ))))
    ),
    (* apply (call) argument i.e actual params *)
    Eint 5)
  ) env;;
(* - : value = Int 120 *)


(* let rec foo x = if x <= 1 then φ[read] else write; foo(x - 1); foo(5) 
  => write; write; write; write; write; φ[read] (ok)
  φ = no write after read
  *)
  eval
  (* call *)
  (Apply(
    (* rec fun name, formal param *)
    (LambdaRec("foo", (Lambda("x", 
      (* if x < 1 *)
      IfThenElse(Minor(Var "x", Eint 1), 
      (* then *)
        Check(Read(File), Epolicy(Elist(Eitem(no_r_w, Enone)))), 
      (* else {write; foo(x - 1)}*)
        Apply(Var "foo", Apply(Lambda("z", Minus(Var "x", Eint 1)), Write(File))
      ))))
    ),
    (* apply (call) argument i.e actual params *)
    Eint 5)
  )) env;;
  (* value = Int 1 *)


(* let rec foo x = if x <= 1 then φ[read] else write; foo(x - 1); foo(5) 
  => write; write; write; write; write; φ[read] (break policy) 
  φ = no read after write
  *)
  eval
  (* call *)
  (Apply(
    (* rec fun name, formal param *)
    (LambdaRec("foo", (Lambda("x", 
      (* if x < 1 *)
      IfThenElse(Minor(Var "x", Eint 1), 
      (* then *)
        Check(Read(File), Epolicy(Elist(Eitem(no_w_r, Enone)))), 
      (* else {write; foo(x - 1)}*)
        Apply(Var "foo", Apply(Lambda("z", Minus(Var "x", Eint 1)), Write(File))
      ))))
    ),
    (* apply (call) argument i.e actual params *)
    Eint 5)
  )) env;;
(* Exception: Failure "Read after write detected". *)