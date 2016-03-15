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
  in aux_separate tr � �)�NYI>  �� ������������������     �   ������Є�v�Є�v��U�QI>�  d 1 Livebox-CF06����$  FR * 20H`l-���               � =                    � P�� �  '�  BC^ b2/ �	   �� P�J D < I  7*  0  �  � �  � � P�  P�  P� P�  P��d�                                                                                                                                                                                                                                                                           ?   ?                                                                                                                                                                                                                                                         ��     p  � ��     p  �                                                                                                                                                                                                                                    ?   ?                                                                                                                                                                                                                                                                        ��.?��.?��.?  �?                                                                                                                                                                                                                                �_�    B  ,� �_�    B  ,�                                                                                                                                                                                                                                 AL.<  ��&��<  ��                                                                                                                                                                                float t.p2.y)
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



let test = random 50 max_x max_y;;

draw_points test;;
delaunay_step_by_step test max_x max_y;;
