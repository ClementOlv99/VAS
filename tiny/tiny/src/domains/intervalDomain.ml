(* Template to write your own non relational abstract domain. *)

(* To implement your own non relational abstract domain,
 * first give the type of its elements, *)
type t = Bot | Itv of int option * int option

(* a printing function (useful for debuging), *)
let fprint ff x = match x with
  |Itv (None, None) -> Format.fprintf ff "]-inf, +inf ["
  |Itv (None, (Some n)) -> Format.fprintf ff "]-inf, %d[" n
  |Itv ((Some n), None) -> Format.fprintf ff "]%d, inf[" n
  |Itv ((Some n1), (Some n2)) -> Format.fprintf ff "]%d, %d[" n1 n2
  |Bot -> Format.fprintf ff "BOT"

   (* Extension de <= `a Z U {-oo}. *)
let leq_minf x y = match x, y with
| None, _ -> true (* -oo <= y *)
| _, None -> false (* x > -oo (x != -oo) *)
| Some x, Some y -> x <= y
(* Extension de <= `a Z U {+oo}. *)
let leq_pinf x y = match x, y with
| _, None -> true (* x <= +oo *)
| None, _ -> false (* +oo > y (y != +oo) *)
| Some x, Some y -> x <= y

(* the order of the lattice. *)
let order x y = match x, y with
  | Bot, _  -> true
  | _, Bot -> false
  |Itv(n1, n2), Itv(n3, n4) -> (leq_minf n3 n1) && (leq_pinf n2 n4)

(* and infimums of the lattice. *)
let top = Itv(None, None)
let bottom = Bot

(* All the functions below are safe overapproximations.
 * You can keep them as this in a first implementation,
 * then refine them only when you need it to improve
 * the precision of your analyses. *)



let min_minf x y = if leq_minf x y then x else y 

let max_pinf x y = if leq_pinf x y then y else x

let join x y = match x, y with
  |Bot, i | i, Bot -> i 
  | Itv(n1,n2), Itv(n3, n4) -> Itv(min_minf n1 n3, max_pinf n2 n4)

let meet x y = match x, y with
  |Bot, i | i, Bot -> Bot
  | Itv(n1, n2), Itv(n3, n4) -> Itv(max_pinf n1 n3, min_minf n2 n4) (*TODO FINIR*)

let widening x y = 
  match x,y with 
  |Bot, a |a, Bot -> a 
  |Itv(a, b), Itv(c, d) when (leq_minf a c) && (leq_pinf d b) -> Itv(a,b)
  |Itv(a, b), Itv(c, d) when (leq_minf a c) && (leq_pinf b d) -> Itv(a, None)
  |Itv(a, b), Itv(c, d) when (leq_minf c a) && (leq_pinf d b) -> Itv(None, b)
  |Itv(a, b), Itv(c, d) when (leq_minf c a) && (leq_pinf b d) ->  Itv(None, None)
  |_ -> failwith "tg"
  

                                  



let sem_itv n1 n2 = 
  if n1 > n2 then Bot else Itv(Some(n1),Some(n2))


let plusinf x y = 
  match x, y with 
  |None, _ | _, None -> None
  |Some(a), Some(b) -> Some(a+b) 

let sem_plus x y = 
  match x, y with
  |Bot, _ | _, Bot -> Bot
  |Itv(n1, n2), Itv(n3, n4) -> Itv(plusinf n1 n3, plusinf n2 n4)


let moinsinf x y = 
  match x, y with 
  |None, _ | _, None -> None
  |Some(a), Some(b) -> Some(a-b) 

let sem_minus x y = 
  match x, y with
  |Bot, _ | _, Bot -> Bot
  |Itv(n1, n2), Itv(n3, n4) -> Itv(moinsinf n1 n3, moinsinf n2 n4)


type bmul = PlusInf | MoinsInf | Int of int
type tmul = Bot | It of bmul * bmul

let rec mulb x y = 
  match x,y with
  |PlusInf, MoinsInf -> MoinsInf
  |PlusInf, PlusInf | MoinsInf, MoinsInf -> PlusInf
  |Int(a), PlusInf -> PlusInf
  |Int(a), MoinsInf -> MoinsInf
  |Int(a), Int(b) -> Int(a*b)
  |_, _-> (mulb y x)






let sem_times x y = top
  

let sem_div x y = top

let sem_guard x = (meet (x) (Itv(Some(1), None)))

let backsem_plus x y r = x, y
let backsem_minus x y r = x, y
let backsem_times x y r = x, y
let backsem_div x y r = x, y
