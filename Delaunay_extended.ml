(* Modules *)


#load "graphics.cma";;
#load "unix.cma";;
open Graphics;;
open Unix;;
open Random;;

(* Graph *)

close_graph();;
open_graph " 1280x720";;
set_color black;;

let max_x = 1280;;
let max_y = 720;;

(* types and their functions *)

type point = {x: float; y: float};;

let make_point a b = {x=a ; y=b};;

type triangle = {p1: point; p2: point; p3:point};;

let make_triangle a b c = {p1=a; p2=b; p3=c};;

type point_set = point list;;

let empty_point () = ([]:point_set);;
let cons_point (p:point) (l:point_set) = (p::l:point_set);;

type triangle_set = triangle list;;

let empty_triangle () = ([]:triangle_set);;
let cons_triangle (t:triangle) (l:triangle_set) = (t::l:triangle_set);;


(* basic functions *)

let random_point max_x max_y = (* make a random point *)
  let a = float_of_int (Random.int max_x) and b = float_of_int (Random.int max_y) in {x=a; y=b};;

let det a b c d e f g h i = (* det of | a b c |
			              | d e f |
                                      | g h i | *)
a*.e*.i +. d*.h*.c +. g*.b*.f -. c*.e*.g -. f*.h*.a -. i*.b*.d;;



let search_point p points =
  let rec aux_search_point p points k =
  match points with
  | [] -> k false
  | t::q -> if t=p then k true else aux_search_point p q k
  in
  aux_search_point p points (function b -> b);;


let search_edge (x,y) l = (* return true if (x,y) or (y,x) is in the list l, else false *)
  let rec aux_search_edge (x,y) l k =
  match l with
  | [] -> k false
  | t::q -> if t=(x,y) || t=(y,x) then k true else aux_search_edge (x,y) q k
  in
  aux_search_edge (x,y) l (function b -> b);;


let make_edge_list triangles = (* change the triangle list in the list of their edges *)
  let rec aux_make_edge_list triangles k =
  match triangles with
  | [] -> k []
  | t::q -> let k' r = k ((t.p1,t.p2)::(t.p2,t.p3)::(t.p1,t.p3)::r) in (aux_make_edge_list q k')
  in
  aux_make_edge_list triangles (function l -> l);;




(* functions *)

let rec random nb max_x max_y = (* return a point_set with nb random point with x<max_x and y<max_y *)
match nb with
|0 -> empty_point ()
|n -> cons_point (random_point max_x max_y) (random (nb-1) max_x max_y);;


let ccw a b c = ((b.x -. a.x)*.(c.y -. a.y) -. (b.y -. a.y)*.(c.x -. a.x))>=0.0;; (* return true if the triangle abc is direct, else false *)

let in_circle t p = (* return true if the point p is in the circle of the triangle t *)
  let a = t.p1 and b = t.p2 and c = t.p3
in
  let ax = a.x and ay = a.y and bx = b.x and by = b.y and cx = c.x and cy = c.y and dx = p.x and dy = p.y
in
  let a2 = ax**2. +. ay**2. and b2 = bx**2. +. by**2.
  and c2 = cx**2. +. cy**2. and d2 = dx**2. +. dy**2.
in
  let  det1 = det bx by b2 cx cy c2 dx dy d2 and det2 = det ax ay a2 cx cy c2 dx dy d2
  and det3 = det ax ay a2 bx by b2 dx dy d2 and det4 = det ax ay a2 bx by b2 cx cy c2
in
(-.det1 +. det2 -. det3 +. det4 > 0. && ccw a b c) || (-.det1 +. det2 -. det3 +. det4 < 0. && ccw b a c);;


let separate triangles p = (* make the set of triangles with p in circle and the set with others *)
  let rec aux_separate triangles p k =
  match triangles with
  | [] -> k ([],[])
  | t::q -> if in_circle t p then let k1 (a,b) = k (t::a,b) in aux_separate q p k1
                           else let k2 (a,b) = k (a,t::b) in aux_separate q p k2
  in aux_separate triangles p (function c -> c);;


let border (triangles:triangle_set) = (* make the edge list of convexe enveloppe of triangles *)
  let edge_list = make_edge_list triangles in
  let rec aux in_border no_in_border k =
match in_border with
| [] -> k []
| t::q -> if search_edge t q || search_edge t no_in_border
          then aux q (t::no_in_border) k
          else aux q no_in_border (function r -> k (t::r))
  in aux edge_list [] (function r -> r);;


let add_point triangles point = (* modification of triangles with the add of point *)
  let edges = border triangles in
  let rec aux edges k =
match edges with
| [] -> k ([]:triangle_set)
| t::q -> aux q (function r -> k ({p1 = fst t; p2 = snd t; p3 = point}::r))
  in aux edges (function l -> l);;

let change triangles point = (* make the set with triangles after the add of point *)
  let (ex_triangles,other_triangles) = separate triangles point in
  let new_triangles = add_point ex_triangles point in
  let rec aux list k =
match list with
| [] -> k new_triangles
| t::q -> aux q (function r -> t::(k r))
  in
  aux other_triangles (function l -> l);;


let delaunay (points:point_set) max_x max_y = (* make the Delaunay triangulation *)
  let p1 = make_point 0. 0. and p2 = make_point (float_of_int max_x) 0. and p3 = make_point 0. (float_of_int max_y) and
   p4 = make_point (float_of_int max_x) (float_of_int max_y) in
  let t1 = make_triangle p1 p2 p3 and t2 = make_triangle p2 p3 p4 in
  let triangles = cons_triangle t1 (cons_triangle t2 (empty_triangle ())) in
  let rec aux triangles points =
match points with
| [] -> triangles
| t::q -> aux (change triangles t) q
  in aux triangles points;;

(* draws *)

let rec draw_points (points:point_set) = (* draw the points *)
match points with
| [] -> sleep 1
| t::q -> plot (int_of_float t.x) (int_of_float t.y); draw_points q;;


let rec draw_triangles (triangles:triangle_set) = (* draw the triangles *)
match triangles with
| [] -> ()
| t::q -> let a = (int_of_float t.p1.x,int_of_float t.p1.y) and b = (int_of_float t.p2.x,int_of_float t.p2.y)
          and c = (int_of_float t.p3.x,int_of_float t.p3.y) 
	  in
          draw_poly [|a;b;c|]; draw_triangles q;;


let draw t = clear_graph ();draw_triangles t;sleep 1;; (* draw the triangles after a clear of graph *)


let delaunay_step_by_step (points:point_set) max_x max_y = (* the triangulation of Delaunay with a graphic affichage *)
  let p1 = make_point 0. 0. and p2 = make_point (float_of_int max_x) 0. and p3 = make_point 0. (float_of_int max_y) and
   p4 = make_point (float_of_int max_x) (float_of_int max_y) in
  let t1 = make_triangle p1 p2 p3 and t2 = make_triangle p2 p3 p4 in
  let triangles = cons_triangle t1 (cons_triangle t2 (empty_triangle ())) in
  let rec aux triangles points =
match points with
| [] -> ()
| t::q -> let new_triangles = change triangles t in draw new_triangles; aux new_triangles q
  in draw triangles; aux triangles points;;


(* extension *)


let hd list =
match list with
| [] -> failwith "hd"
| t::q -> t;;

let tl list =
match list with
| [] -> failwith "tl"
| t::q -> q;;

let concat l1 l2 =
  let rec aux l1 l2 k =
match l1 with
| [] -> k l2
| t::q -> aux q l2 (function r -> t::(k r))
  in aux l1 l2 (function r -> r);;


let abs_min points = (* return the point with the minimal abscise *)
  let rec aux min points =
match points with
| [] -> min
| t::q -> if t.x < min.x then aux t q else aux min q
  in aux (hd points) (tl points);;



let rec del p points = (* return points without all p occurences *)
match points with
| [] -> []
| t::q -> if t=p then del p q else t::(del p q);;


let choose_next p points = (* choose the next point in Jarvis alogrithm *)
  let without_min = del p points in
    let rec aux min points =
match points with
| [] -> min
| t::q -> if ccw p min t then aux min q else aux t q
  in aux (hd without_min) without_min;;


let jarvis points = (* return the convexe enveloppe of points *)
  let a_min = abs_min points in
  let rec aux points wrap p =
match p with
| x when x = a_min -> concat wrap [a_min]
| _ -> aux points (p::wrap) (choose_next p points)
  in aux points [a_min] (choose_next a_min points);;


let rec draw_points_bis p = (* to a better view of points *)
match p with
| [] -> sleep 1
| t::q -> draw_circle (int_of_float t.x) (int_of_float t.y) 4; draw_points_bis q;;

let jarvis_affich points = (* draw the points and their wrap *)
  let j = jarvis points in
  let rec aux points =
match points with
| [] -> failwith "affich1"
| [x] -> failwith "affich2"
| a::[b] -> draw_poly [| (int_of_float a.x, int_of_float a.y) ; (int_of_float b.x,int_of_float b.y) |]
| t::t2::q -> draw_poly [| (int_of_float t.x, int_of_float t.y) ; (int_of_float t2.x,int_of_float t2.y) |]; aux (t2::q)
  in
  clear_graph();draw_points_bis points; aux j;sleep 5;;



let change_jarvis points = (* return the list of points out of the convexe enveloppe *)
  let wrap = jarvis points in
  let rec aux l =
match l with
| [] -> []
| t::q -> if search_point t wrap then aux q else t::(aux q)
  in aux points;;



let border_points points = (* make the edge list of convexe enveloppe *)
  let j = jarvis points in
  let rec aux l =
match l with
| [] -> failwith "border_points"
| [x] -> failwith "border_points"
| a::[b] -> [(a,b)]
| t::t2::q -> (t,t2)::(aux (t2::q))
  in aux j;;


let make_base points = (* make the basic triangulation with convexe enveloppe*)
  let edges = border_points points in
  let point = hd (change_jarvis points) in
  let rec aux edges k =
match edges with
| [] -> k ([]:triangle_set)
| t::q -> aux q (function r -> k ({p1 = fst t; p2 = snd t; p3 = point}::r))
  in aux edges (function l -> l);;



let delaunay_step_by_step_extended (points:point_set) = (* the triangulation of Delaunay with a graphic affichage without extremal points *)
  let triangles = make_base points in
  let other_points = change_jarvis points in
  let rec aux triangles points =
match points with
| [] -> ()
| t::q -> let new_triangles = change triangles t in draw new_triangles; aux new_triangles q
  in draw triangles; aux triangles other_points;;



let test = random 50 max_x max_y;;
delaunay_step_by_step_extended test;;

