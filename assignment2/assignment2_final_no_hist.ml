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
type dfa = {
  states : state list;
  sigma : symbol list;
  start : state;
  transitions : transition list;
  accepting : state list;
  error : string;
};;

type n_dfa =
  | Dfa of dfa
  | None

(* Auxiliary Functions *)
(* To dereference a record, use the dot notation *)
let states (dfa : dfa) = dfa.states;;
let alphabet (dfa : dfa) = dfa.sigma;;
let start (dfa : dfa) = dfa.start;;
let transitions (dfa : dfa) = dfa.transitions;;
let acceptings (dfa : dfa) = dfa.accepting;;

(* This is a function that takes in a DFA as input, and adds a transition.
*)

(* "with" evaluates to a new record of the same type as X, and whose 
fields are initialized to the same as those in X, except the ones
which are listed after the "with", which are initialized to those
given values.
*)
let addTransition t dfa = { 
  dfa with transitions = t::dfa.transitions 
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
  | Eint of int
  | Ebool of bool
  | Estring of string
  | Read of resource
  | Write of resource
  | Download of resource
  | Connect of resource
  | Check of exp * n_dfa (* Block where check if policy is satisfied*)
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
  (* Fun is anonymous => it hasn't a name! 'ide' is the formal parameter!
  i.e f(x) = x + 1  => x is the formal parameter, x + 1 is the body *)
  (* formal parameter with function body *)
  | Fun of string * exp
  (* name, formal parameter with function, let body *)
  | LetRec of string * exp * exp 
  | Call of exp * exp;; (* Fun with acutal parameter *)

(* environment is a couple list of ide with their value *)
type 'v env = (string * 'v)list;; 

(* language values *)
type value =
  | Int of int
  | Bool of bool
  | String of string
  | Closure of string * exp * value env (* formal param, body, env *)
  | RecClosure of string * string * exp * value env;; (* fun name, formal param, body, env *)

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
return the val (1 if success), the same dfa and the updated history *)
let ieval (d: n_dfa) (history: string) (op: char) 
  : (value * n_dfa * string) =
  (* check if some policy is here *)
  match d with
  | Dfa dfa -> 
    (* Check if 'op' is in the alphabet.. *)
    if contains op (dfa.sigma) then
      (* .. if yes, check if the op can be done checking policy *)
      if check_accepts (history ^ Char.escaped op) dfa then
        (* update history of automata *)
        (Int 1, d , history ^ Char.escaped op)
      else 
        (* op cannot be respect policy => abort *)
        failwith(dfa.error)
    else (* op isn't in policy, by default is granted *)
        (Int 1, d, history)
  (* not to check *)
  | _ -> (Int 1, d, history)
    

(* interpreter: return a triple => value, dfa, and string (op) *)
let eval (exp: exp) (env: 'v env): (value) = 

  let rec rec_eval (exp: exp) (env: 'v env) (dfa: n_dfa) (op : string): 
  (value * n_dfa * string) =
  match exp with 
  | Eint x -> (Int x, dfa, op)
  | Ebool b -> (Bool b, dfa, op)
  | Estring s -> (String s, dfa, op)

  (* Here there are operations on critical resource, 
    so check if in local policy fi there is the op in the alphabet, 
    if not, the sensible operation will be executed over
    critical resource by default *)
  | Read r -> ieval dfa op 'r'
  | Write w -> ieval dfa op 'w'
  | Download d -> ieval dfa op 'd'
  | Connect c -> ieval dfa op 'c'
  | Check(block, policy) -> rec_eval block env policy ""

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
  | Fun(param, body) -> (Closure(param, body, env), dfa, op)

  (* in this case the function is not anonymous anymore, it has a name *)
  | LetRec(f_name, f_def, let_body) -> 
    (* check if f_def is a Func *)
      begin match f_def with
      | Fun(param, body) ->
        (* build new env with rec function *)
        let new_env = bind f_name (RecClosure(f_name, param, body, env)) env
        (* rec_eval rec function body in new env *)
        in rec_eval let_body new_env dfa op 
      | _ -> failwith("non functional def")  
    end
  
  (* Call a function f with p actual parameter i.e f(x) = x + 1 => f(5) = 6 *)
  | Call(f, actual_param) -> 
      let (func, _, _) = rec_eval f env dfa op in
      begin match func with
      | (Closure(formal_param, body, decl_env)) -> 
        (* rec_evaluate the ACTUAL param in the current environment *)
        let (a_p, _, _) = rec_eval actual_param env dfa op in
        (* BIND THE FORMAL PARAMETER TO THE ACTUAL ONE AND ADD THEM TO DECL ENV! *)
        let new_env = bind formal_param a_p decl_env in
        (* calculate the functions with the extened env! *)
        rec_eval body new_env dfa op
      
      | (RecClosure(f_name, formal_param, f_body, decl_env)) -> 
        (* rec_evaluate the ACTUAL param in the current environment *)
        let (a_p, _, _) = rec_eval actual_param env dfa op in
        (* bind func value to func name *)
        let r_env = bind f_name func decl_env in
        (* BIND THE FORMAL PARAMETER TO THE ACTUAL ONE AND ADD THEM TO DECL ENV! *)
        let new_env = bind formal_param a_p r_env in
        (* calculate the functions with the extened env! *)
        rec_eval f_body new_env dfa op 
      | _ -> failwith("not a function")
      end in let (r, _, _) = rec_eval exp env None "" in r;;

(* Example: no write after read *)
let dfa : dfa = { 
  states = [0; 1; 2];
  sigma = ['r';'w'];
  start = 0;
  transitions =
    [(0, 'r', 1);
    (0, 'w', 0);
    (1, 'w', 2);
    (1, 'r', 1);
    (2, 'r', 2);
    (2, 'w', 2)];
  accepting = [0; 1];
  error = "Write after read detected"
};;

let env = [("z", Int 10); ("y", Int 20)];;

eval(Check(LetIn("x", Read(File), Write(Net)), Dfa(dfa))) env;;
eval(LetIn("y", (Check(LetIn("x", Read(File), Read(Net)), Dfa(dfa))), Write(Socket))) env;;
eval(LetIn("y", Write(Socket), (Check(LetIn("x", Read(File), Read(Net)), Dfa(dfa))))) env;;

