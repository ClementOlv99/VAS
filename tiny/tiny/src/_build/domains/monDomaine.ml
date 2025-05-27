(* Template to write your own non relational abstract domain. *)

(* To implement your own non relational abstract domain,
 * first give the type of its elements, *)
type t = Integer of int | Top | Bottom

(* a printing function (useful for debuging), *)
let fprint ff = function
  | Integer(a) -> Format.fprintf ff "%d" a
  | Top -> Format.fprintf ff "Top"
  | Bottom -> Format.fprintf ff "Bottom"

(* the order of the lattice. *)
let order x y = match x, y with
  | Top, _ | _, Bottom -> false
  | Bottom, _ | _, Top -> true
  | Integer(a), Integer(b) when a = b -> true 
  | Integer(a), Integer(b) -> false


(* and infimums of the lattice. *)
let top = Top
let bottom = Bottom

(* All the functions below are safe overapproximations.
 * You can keep them as this in a first implementation,
 * then refine them only when you need it to improve
 * the precision of your analyses. *)

let join x y = match x, y with
  | Integer(a), Integer(b) when a = b -> Integer(a)
  | Integer(a), Integer(b) -> Top
  | Bottom, e | e, Bottom -> e
  | _, Top | Top, _ -> Top


let meet x y = match x, y with
  | Integer(a), Integer(b) when a = b -> Integer(a)
  | Integer(a), Integer(b) -> Bottom
  | Top, e | e, Top -> e
  | _, Bottom | Bottom, _ -> Bottom

let widening = join  (* Ok, maybe you'll need to implement this one if your
                      * lattice has infinite ascending chains and you want
                      * your analyses to terminate. *)

let sem_itv n1 n2 = 
  if n1 = n2 then Integer(n2) else Top

let sem_plus x y = 
  match x,y with 
  | Bottom, _ |  _ , Bottom -> Bottom
  | Top, _ | _, Top -> Top
  | Integer(a), Integer(b) -> Integer(a + b)
  
let sem_minus x y = 
  match x,y with 
  | Bottom, _ |  _ , Bottom -> Bottom
  | Top, _ | _, Top -> Top
  | Integer(a), Integer(b) -> Integer(a - b)

let sem_times x y = 
  match x,y with 
  | Bottom, _ |  _ , Bottom -> Bottom
  | Top, Integer(0) | Integer(0), Top -> Integer(0)
  | Top, _ | _, Top -> Top
  | Integer(a), Integer(b) -> Integer(a * b)

let sem_div x y = 
  match x,y with 
  | Bottom, _ |  _ , Bottom -> Bottom
  | _ , Integer(0) | Integer(0), _ -> Bottom
  | Top, _ | _, Top -> Top
  | Integer(a), Integer(b) -> Integer(a / b)

let sem_guard = function
  | t -> t

let backsem_plus x y r = x,y
let backsem_minus x y r = x, y
let backsem_times x y r = x, y
let backsem_div x y r = x, y
