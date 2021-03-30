
(* In this homework, we will extend the interpreter of the simple functional 
language into an interpreter of a functional language which includes a dynamic
mechanism for enforcing access control checks,
along the line of the so-called stack inspection algorithm.

In this homework you will build an interpreter of a simple functional language
equipped with  security permissions. Each function definition is equipped with
a set of permissions (e.g. {read, write}, {}) over a set of security relevant 
actions. We also assume that the language is  equipped with a primitive construct to check
a permission. 
The interpreter executes if  permissions are enabled; otherwise, execution fails 
  
Simulare stack inspection in ocaml (interprete)
Abbiamo un linguaggio funzionale con (funzioni) primitive definite da programma,
non esamineremo in questo momento le op privilegiate, e poi un altro insieme di funzioni
che sono potenzialmente untrusted e dobbiamo simulare l'algoritmo di stack inspection 
(quindi avere un interprete del linguaggio con un security manager che simula il controllo
dello stack per l'esecuzione delle funzioni che non sono trusted)

(* ---- IDEAS ---- *)
new type named permission containing Read|Write
when i call eval, pass also a specific permission, and match this permission with
the ones associated to op
es: la lookup "legge" viene eseguita sse alla eval in quella esecuzione ho abilitato la read!
la LetIn che scrive sse ho abiloitato la write in quella eval!

IDEA 1:
extend the exp with a type permission for each declaration

IDEA 2:
extend only the Fun of exp with permission*)

(* ---- DECLARATION OF TYPES ---- *)

(* security permission that "exp" can execute *)
type permission = 
  | None
  | Read
  | Write
  | Permission of permission * permission (* list of permission *)


(* languages value *)
type exp = 
  (* ------ THESE EXP ARE PRIMITEVES, DON'T NEED ANY PERMISSION ------ *)
  | Enone
  | Eint of int
  | Ebool of bool
  | Estring of string
  | Elist of exp (* Eitem or None*)
  | Eitem of exp * exp (* element and something other or None *)
  (* ------ VAR NEED TO READ THE VALUE OF A VAR ------ *)
  | Var of string * permission
  (* ------ ASSUME THAT EVERY BASIC OP READ EXP AND WRITE OR READ THE RESULT ------ *)
  | Plus of exp * exp * permission (* + of Int * Int * Write *)
  | Minus of exp * exp * permission (* - of Int * Int * Write *)
  | Mul of exp * exp * permission (* * of Int * Int * Write *)
  | Div of exp * exp * permission (* / of Int * Int * Write *)
  | Greater of exp * exp * permission (* e1 > e2 * Read *)
  | Minor of exp * exp * permission (* e1 < e2 * Read *)
  | Equals of exp * exp * permission (* e1 == e2 * Read *)
  | Concat of exp * exp * permission (* s1 ^ s2 * Write *)
  | Cons of exp * exp * permission (* x::xs * Write*)
  | IfThenElse of exp * exp * exp (* "guardia", then, else *)
  (* The following builder permits to give a name to an exp *)
  (* ------ LET IN NEEDS READ EXP AND WRITE THE RESULT ------ *)
  | LetIn of string * exp * exp * permission (* ide, value to associate to ide, body of let 
  i.e y (ide) = 5 (exp) in y + x (exp)  *)
  (* Fun is anonymous => it hasn't a name! 'ide' is the formal parameter!
  i.e f(x) = x + 1  => x is the formal parameter, x + 1 is the bodyn*)
  (* ------ FUN NEED TO READ THE VALUE OF EXP ------ *)
  | Fun of string * exp  (* formal parameter with function body *)
  (* ------ ASSUME THAT EVERY BASIC OP READ EXP AND WRITE OR READ THE RESULT ------ *)
  | Call of exp * exp * permission;; (* Fun with acutal parameter *)

(* environment is a couple list of ide with their value *)
type 'v env = (string * 'v)list;; 

type value =
  | None
  | Int of int
  | Bool of bool
  | String of string
  | List of value (* List(Item(Eint 5, None)) *)
  | Item of value * value (* Item(Eint 5, None)) => List item or tuple!*)
  | Func of string * exp * value env;; (* formal param, body, env *)

(* ---- DECLARATION OF FUNCTIONS ---- *)

(* associate val with value to env *)
let bind (var: string) (value: value) (env: 'v env) =
  (var, value)::env;;

(* security manager compare ONE op requested with the granted ops *)
let rec check_one_permission (cp: permission) (gp: permission) : bool =
  match gp with
  | None -> false (* no op granted  *)
  | Read -> if cp = Read then true else false
  | Write -> if cp = Write then true else false
  | Permission(p, pgs) ->
     if p = cp then 
      true 
    else check_one_permission cp pgs
    
(* security manager compare ONE op requested with the granted ops *)
let rec check_all_permission (cp: permission) (gp: permission) : bool =
  match cp with
  | None -> false (* no op granted  *)
  | Read -> check_one_permission Read gp
  | Write -> check_one_permission Write gp
  | Permission(cp, pcs) -> 
    if check_one_permission cp gp then 
      check_all_permission pcs gp 
    else 
      false

let rec print_error (cp: permission) (gp: permission)= 
  match cp with
  | Read -> 
    if not(check_one_permission Read gp) then
      failwith("Read can't be executed")
    else 
      failwith("--- Abort ---")
  | Write -> 
      if not(check_one_permission Write gp) then
        failwith("Write can't be executed")
      else 
        failwith("--- Abort ---")
  | Permission(p, ps) ->
    begin match p with
    | Read ->
      if not(check_one_permission Read gp) then
        print_string("Read can't be executed\n");
      print_error ps gp
    | Write ->
      if not(check_one_permission Write gp) then
        print_string("Write can't be executed\n");
      print_error ps gp
    | _ ->  print_error ps gp
  end
  | _ -> failwith("Why are you try to fucking me?")

(* Firstly security manager check if it is possible to do the Read op. 
  If yes, it checks if var has a associated value in the environment env  *)
let lookup(env: 'v env) (var: string) (cp: permission) 
(gp: permission): value = 
  (* the only perm to check is Read *)
  if check_all_permission cp gp then
    let rec lookup (env: 'v env) (var: string) : value = 
    match env with
    | [] -> failwith(var ^ " not found")
    | (ide, value)::envs -> 
      print_string(ide ^ "\n");
      if (ide = var) then
        value
      else
        lookup envs var
      in lookup env var
  else 
    print_error cp gp;;

(* ---- THE INTERPRETER ---- *)
let calculator (op: string) (x: value) (y: value) 
(cp: permission) (gp: permission): value =
  (* this operation must have the permission of read and write to operate *)
  if check_all_permission cp gp then
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
    | ("::", _x, Item(y, z)) -> (* check if x will be inserted as head *)
      begin match x with
      | Item _ -> failwith("Not a :: operation!")
      | None -> failwith("Not a :: operation!")
      | _x -> Item(x, Item (y, z))
    end
    | (_, _, _) -> failwith("Not yet implemented")
  end
else 
  print_error cp gp;;


(* evaluate my language: interpreter *)
let rec eval (exp: exp) (env: 'v env) (gp: permission): value = match exp with
  | Enone -> None
  | Eint x -> Int x
  | Ebool b -> Bool b
  | Estring s -> String s
  | Elist l ->
    begin match eval l env gp with
    | Item(x, y) -> List(Item(x, y))
    | None -> List(None)
    | _ -> failwith("Wrong List declaration")
    end
  | Eitem(x, y) -> (* check if 2nd elem is Item or Enone!*)
    begin match y with 
    | Enone -> Item(eval x env gp, eval y env gp)
    | Eitem(_, _) -> Item(eval x env gp, eval y env gp)
    | _ -> failwith("Wrong Item declarations")
    end
  | Var(x, cp) -> 
    begin match cp with
    | Read -> lookup env x cp gp
    | _ -> failwith("Given a wrong permission")
    end
  | IfThenElse(guardia, t, e) -> 
      begin match eval guardia env gp with
      | Bool b -> if b then eval t env gp else eval e env gp
      | _ -> failwith("not a valid statement")
      end 
  | Plus(x, y, cp) -> calculator "+" (eval x env gp) (eval y env gp) cp gp
  | Minus(x, y, cp) -> calculator "-" (eval x env gp) (eval y env gp) cp gp 
  | Mul(x, y, cp) -> calculator "*" (eval x env gp) (eval y env gp) cp gp 
  | Div(x, y, cp) -> calculator "/" (eval x env gp) (eval y env gp) cp gp 
  | Greater(x, y, cp) -> calculator ">" (eval x env gp) (eval y env gp) cp gp 
  | Minor(x, y, cp) -> calculator "<" (eval x env gp) (eval y env gp) cp gp 
  | Equals(x, y, cp) -> calculator "==" (eval x env gp) (eval y env gp) cp gp 
  | Concat(x, y, cp) -> calculator "^" (eval x env gp) (eval y env gp) cp gp 
  | Cons(x, xs, cp) -> calculator "::" (eval x env gp) (eval xs env gp) cp gp
  | LetIn(ide, value, body, cp) ->
    (* check for op *)
    if check_all_permission cp gp then
    (* "calculate" value ... *)
      let v = eval value env gp in 
      (* ... and bind this value to the ide for creating new env 
      (new value on the stack).. *)
      let new_env = bind ide v env in
      (* check if v is a function that compare in the policies *)
        begin match v with 
        | Func(_, _, _) -> eval body new_env gp
        | _ ->  eval body new_env gp  (* ... and use it in the body *)
      end
    else
      print_error cp gp
  (* define functions*)
  (* ---- WARNING ----
      var isn't the name of function! It is the argument, 
      the formal parameter of function!
      i.e f (x) = x + 1   =>  var is x! Not the name of function! 
      For naming a function we must use the builder LetIn! 
      *)
  | Fun(var, exp) -> Func(var, exp, env)  

  (* Call a function f with p actual parameter 
  i.e f(x) = x + 1 => f(5) = 6 *)
  | Call(f, actual_param, cp) -> 
    if check_all_permission cp gp then
      let func = eval f env gp in
      begin match func with
      | Func(formal_param, body, decl_env) -> 
        (* evaluate the ACTUAL param in the current environment *)
        let a_p = eval actual_param env gp in
        (* BIND THE FORMAL PARAMETER TO THE ACTUAL ONE AND ADD THEM TO DECL ENV! *)
        let new_env = bind formal_param a_p decl_env in
        (* calculate the fucking functions with the extened env! *)
        eval body new_env gp
      | _ -> failwith("not a function")
      end
    else
      print_error cp gp;;
      (* ----- WARNING ------
    in this implementations I don't extend the fun environment!
    I don't consider it! 
      begin match f with
        | Fun(var, exp) -> 
          (* evaluate the ACTUAL parameter in the calling env *)
          let a_p = eval param env  in
          (* bind the value of actual parameter to the formal parameter! *)
          let new_env = bind var a_p env in
          (* call the fucking function *)
          eval exp new_env 
        | _ -> failwith("Not a function!")
      end
      *)

    
(* ---- "MAIN" ---- *)
let permissions : permission = None;;
(* val permissions : permission = None *)

let env = bind "x" (Int 10) [];;
(* val env : (string * value) list = [("x", Int 10)] *)

eval (Var("x", Read)) env permissions;; 
(* Exception: Failure "Read can't be executed". *)

let permissions = Permission(Read, permissions);;
(* val permissions : permission = Permission(Read, None) *)

eval (Var("x", Read)) env permissions;;
(* value = Int 10 *) 

eval (Plus(Eint 10, Eint 5, Permission(Write, Read))) env (Permission(Read, None));;