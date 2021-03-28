(*MICROFUN language*)

(* 
  represent the environment as a list of couple: (ide, 'val)
  map ide in 'val
*)
type 'v env = (string * 'v)list

(*
  ---- STATIC SCOPE ----
  lookup return the 'v associated to var in the enviroment env
*)
let rec lookup (env: 'v env) x = match env with
  | [] -> failwith("value not found")
  | (ide, value)::envs -> 
    if (x = ide) then
      value
    else
      lookup envs x 

type expr =
  | Mbool of bool (* "base" value => costant *)
  | MInt of int (* "base" value => costant *)
  | MString of string (* "base" value => string *)
  | Var of string (* i.e "x" (string) *)
  | Let of (string * expr * expr) (* i.e "let" (string) "x" (string) = (Bool (expr) | Int (expr) | String (expr)) in (expr)) *)
  | Prim of (string * expr * expr) (* standard op i.e: "+", Eint(5), Eint(10) *)

type value = (* this type is need to 'return' basic values in eval *)
  | Empty of int (* represent the empty env*)
  | Int of int
  | Bool of bool
  | String of string

(* take the operator as string and 2 value type of Int and return a Int*)
let eval_math_operation (op: string) (x: int) (y: int): value =
if (op == "+") then 
  Int(x + y) 
else if (op == "-") then
  Int(x - y)
else if (op == "*") then
  Int(x*y)
else if (op == "/") then
  Int(x/y) 
else
  failwith("operation not exists")


let rec eval (e: expr) (env: 'v env): value = match e with 
  | Mbool b -> Bool b
  | MInt x -> Int x
  | MString s -> String s
  | Var x -> lookup env x
  | Prim(op, x, y) -> 
      (* evaluate i2 & i2 in their declaring env and then check if they are int *)
      let i1 = eval x env in
      let i2 = eval y env in
      begin
        match (i1, i2) with 
          | (Int z, Int y) ->
            (* check for integer overflow! *)
              if (Int.abs(z) > Int.max_int || Int.abs(y) > Int.max_int) then
                failwith("You can't hack me")
              else if (op == "+") then 
                Int(z + y)
              else if (op == "-") then
                Int(z - y)
              else if (op == "*") then
                Int(z*y)
              else if (op == "/") then
                Int(z/y) 
              else
                failwith("operation not exists")
          | ( _ , _) -> failwith("type error")
      end
  | (_) -> failwith("not yet implemented")
  ;;

  (* declare environment*)
  eval (Var "y") ["y", Int 5];;

(*
let b = Mbool true;;
MInt 5;;
Var("y");;
Let("x", MInt(5), MInt 5);; (* no sensa *)

let x = 3 in true;;
*)


