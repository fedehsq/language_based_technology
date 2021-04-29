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

type n_dfa =
  | Dfa of dfa
  | None;;

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
  | Epolicy of n_dfa (* programmer can define policy *)
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
  (* formal parameter with function body *)
  | Lambda of string * exp
  (* name, formal parameter with function, let body *)
  | LetRec of string * exp * exp 
  | Apply of exp * exp;; (* Lambda with acutal parameter *)

(* environment is a couple list of ide with their value *)
type 'v env = (string * 'v)list;; 

(* language values *)
type value =
  | Int of int
  | Bool of bool
  | String of string
  | Policy of n_dfa 
  | Closure of string * exp * value env (* formal param, body, env *)
  | RecClosure of string * string * exp * value env;; (* Lambda name, formal param, body, env *)

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
let ieval (d: n_dfa) (history: string)
  : (value * exp * string) =
  print_string(history);

  (* check if some policy is here *)
  match d with
  | Dfa dfa -> 
      (* Check if the op can be done checking policy *)
      if check_accepts (history) dfa then
        (* update history of automata *)
        (Int 1, Epolicy(d) , history)
      else 
        (* op cannot be respect policy => abort *)
        failwith(dfa.error)
  (* not to check, only update history *)
  | _ -> (Int 1, Epolicy(d), history)
    
(* interpreter: return a triple => value, dfa, and string (op) *)
let eval (exp: exp) (env: 'v env): (value) = 

  let rec rec_eval (exp: exp) (env: 'v env) (dfa: exp) (op : string): 
  (value * exp * string) =
  match exp with 
  | Eint x -> (Int x, dfa, op)
  | Ebool b -> (Bool b, dfa, op)
  | Estring s -> (String s, dfa, op)
  | Epolicy p -> (Policy p, dfa, op)


  (* Here there are operations on critical resource, 
    so check if in local policy fi there is the op in the alphabet, 
    if not, the sensible operation will be executed over
    critical resource by default *)
  | Read r -> 
    (* Check if policy is an automata! *)
    let (policy, _, _) = rec_eval dfa env dfa op in
      begin match policy with
      | Policy p -> ieval p (op ^ "r")
      | _ -> failwith("Wrong policy declaration")
      end
  | Write w -> (* Check if policy is an automata! *)
    let (policy, _, _) = rec_eval dfa env dfa op in
      begin match policy with
      | Policy p -> ieval p (op ^ "w")
      | _ -> failwith("Wrong policy declaration")
      end
  | Download d -> (* Check if policy is an automata! *)
    let (policy, _, _) = rec_eval dfa env dfa op in
      begin match policy with
      | Policy p -> ieval p (op ^ "d")
      | _ -> failwith("Wrong policy declaration")
      end
  | Connect c -> (* Check if policy is an automata! *)
    let (policy, _, _) = rec_eval dfa env dfa op in
      begin match policy with
      | Policy p -> ieval p (op ^ "c")
      | _ -> failwith("Wrong policy declaration")
      end
  | Check(block, policy) -> rec_eval block env policy op
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
  | LetRec(f_name, f_def, let_body) -> 
    (* check if f_def is a Func *)
      begin match f_def with
      | Lambda(param, body) ->
        (* build new env with rec function *)
        let new_env = bind f_name (RecClosure(f_name, param, body, env)) env
        (* rec_eval rec function body in new env *)
        in rec_eval let_body new_env dfa op 
      | _ -> failwith("non functional def")  
    end
  
  (* Apply a function f with p actual parameter i.e f(x) = x + 1 => f(5) = 6 *)
  | Apply(f, actual_param) -> 
      let (func, _, _) = rec_eval f env dfa op in
      begin match func with
      | Closure(formal_param, body, decl_env) -> 
        (* rec_evaluate the ACTUAL param in the current environment and update history *)
        let (a_p, d, history) = rec_eval actual_param env dfa op in
        (* BIND THE FORMAL PARAMETER TO THE ACTUAL ONE AND ADD THEM TO DECL ENV! *)
        let new_env = bind formal_param a_p decl_env in
        (* calculate the functions with the extened env and extended history! *)
        rec_eval body new_env dfa (* d *) history
      
      | RecClosure(f_name, formal_param, f_body, decl_env) -> 
        (* rec_evaluate the ACTUAL param in the current environment *)
        let (a_p, _, _) = rec_eval actual_param env dfa op in
        (* bind func value to func name *)
        let r_env = bind f_name func decl_env in
        (* BIND THE FORMAL PARAMETER TO THE ACTUAL ONE AND ADD THEM TO DECL ENV! *)
        let new_env = bind formal_param a_p r_env in
        (* calculate the functions with the extened env! *)
        rec_eval f_body new_env dfa op 
      | _ -> failwith("not a function")

      (* empty policy at the beginning of program *)
      end in let (r, _, _) = rec_eval exp env (Epolicy(None)) "" in r;;

(* Example: no write after read *)
let dfa : dfa = { 
  states = [0; 1; 2];
  (* Read | Write | Connect | Download *)
  sigma = ['r'; 'w'; 'c'; 'd'];
  start = 0;
  transitions =
    [(0, 'r', 1);
    (0, 'w', 0);
    (0, 'd', 0);
    (0, 'c', 0);
    (1, 'w', 2);
    (1, 'r', 1);
    (1, 'd', 1);
    (1, 'c', 1);
    (2, 'r', 2);
    (2, 'd', 2);
    (2, 'c', 2);
    (2, 'w', 2)];
  accepting = [0; 1];
  error = "Write after read detected"
};;


(* Example: no read after write *)
let dfa1 : dfa = { 
  states = [0; 1; 2];
  (* Read | Write | Connect | Download *)
  sigma = ['r'; 'w'; 'c'; 'd'];
  start = 0;
  transitions =
    [(0, 'w', 1);
    (0, 'r', 0);
    (0, 'd', 0);
    (0, 'c', 0);
    (1, 'r', 2);
    (1, 'w', 1);
    (1, 'd', 1);
    (1, 'c', 1);
    (2, 'w', 2);
    (2, 'd', 2);
    (2, 'c', 2);
    (2, 'r', 2)];
  accepting = [0; 1];
  error = "Read after write detected"
};;

let env = [("z", Int 10); ("y", Int 20)];;

(* ------ ONE POLICY: no write after read ------ *)
(* φ[let x = read in write] *)
eval(Check(LetIn("x", Read(File), Write(Net)), Epolicy(Dfa(dfa)))) env;;
(* Exception: Failure "Write after read detected".*)

(* let x = read in φ[write] *)
eval(LetIn("x", Read(Socket), Check(Write(Net), Epolicy(Dfa(dfa))))) env;;
(* Exception: Failure "Write after read detected".*)

(* let x = φ[read] in write *)
eval(LetIn("x", (Check(Read(Net), Epolicy(Dfa(dfa)))), Write(Socket))) env;;
(* - : value = Int 1 (Ok because out of scope of local policy) *)

(* let y = read in φ[let x = write in download] *)
eval(LetIn("y", Read(Socket), (Check(LetIn("x", Write(File), Download(Net)), Epolicy(Dfa(dfa)))))) env;;
(* Exception: Failure "Write after read detected".*)

Lambda("x", Check(Read(File), Epolicy(Dfa(dfa))));;
Lambda("y", Write(File));;

eval (Apply(Lambda("y", Write(File)), Lambda("x", Check(Read(File), Epolicy(Dfa(dfa)))))) env;;

(* ----- NESTED POLICY
dfa : no write after read
dfa1: no read after write
------ 
(* φ[let x = read in φ'[let y = write in read]] *) 
eval(Check(LetIn("x", Read(File), (Check(LetIn("y", Write(File), Read(Net)), Epolicy(Dfa(dfa1))))), Epolicy(Dfa(dfa)))) env;;
(* Failure "Read after write detected" (Ok beacuse LIFO) *)

(* let x = φ[write] in φ'[read] *) 
eval(LetIn("x", Check(Write(File), Epolicy(Dfa(dfa))), (Check(Read(File), Epolicy(Dfa(dfa1)))))) env;;
(* Failure "Read after write detected" *)

(* φ[let x = read in φ'[write]] *) 
eval(Check(LetIn("x", Read(File), (Check(Write(File), Epolicy(Dfa(dfa1))))), Epolicy(Dfa(dfa)))) env;;
*)

eval (Apply(Lambda("y", Write(File)), Lambda("x", Check(Read(File), Epolicy(Dfa(dfa)))))) env;;

(* How λ works: if I want to execute e1;e2 => the following
  abbreviation is standard: e1; e2 = (λ.e2)e1 is a
function without params that it has e2 as body, 
it is applied with e1. eval e1 then pass the params. 
But the function hasn't params so it execs the body of function e2 
without passsing params.
THE EFFECT IS EXECUTING IN SEQUENCES e1; e2; AND THE RESULT IS THE TYPE OF e2 *)

(* read; φ[write] *)
eval(Apply(Lambda("x", Check(Write(File), Epolicy(Dfa(dfa)))), Read(Socket))) env;;
(* Exception: Failure "Write after read detected". *)

(* φ[read; write] *)
eval(Check(Apply(Lambda("x", Write(File)), Read(Socket)), Epolicy(Dfa(dfa)))) env;;
(* Exception: Failure "Write after read detected". *)

(* φ[read; download; write] *)
eval (Check(Apply(Lambda("x", Write(File)), Apply(Lambda("x", Download(File)), Read(Socket))), Epolicy(Dfa(dfa)))) env;;
(* Exception: Failure "Write after read detected". *)

(* read; φ[download]; write *)
eval (Apply(Lambda("x", Write(File)), Apply(Lambda("x", Check(Download(File), Epolicy(Dfa(dfa)))), Read(Socket)))) env;;

(* φ[φ'[read]; write] *) 
eval (Check(Apply(Lambda("x", Write(File)), Check(Read(Socket), Epolicy(Dfa(dfa1)))), Epolicy(Dfa(dfa)))) env;;
(* Exception: Failure "Write after read detected".*)

(* φ[read; φ'[write]] *)
(* da il risultato perche quando valuto 'write' ho la politica locale che mi sostituisce quella più esterna ! *)
(* idea: nella ieval controllo quella attuale, poi quella un po' piu fuori e cosi via => 
lista di automi che controllo in ordine LIFO!
quindi quando parte il programma ho una lista di politiche, aggiungo man mano in testa nella Check e nella ieval parto a controllare dalla testa => LIFO

quando il blocco da controllare si chiude devo ELIMINARE LA POLICY da questa lista! 
come posso fare la rimozione?

quindi nella Apply mi salvo il risultato della prima eval e rimuovo quel particolare automa dalla lista, e returno la lista aggiornata senza questa policy! *)
eval (Check(Apply(Lambda("x", Check(Write(Socket), Epolicy(Dfa(dfa1)))), Read(Socket)), Epolicy(Dfa(dfa)))) env;;