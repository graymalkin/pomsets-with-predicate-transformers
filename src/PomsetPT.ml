open AST
open Relation
open Util

type value = int
type register = string [@@deriving show]

type location = string [@@deriving show]
              
type scope = CTA | GPU | SYS
type amode = WK | RLX | RA | SC
type fmode = REL | ACQ | FSC
                                 
type event = int
type action =
  Write of amode * scope * location * value
| Read  of amode * scope * location * value
| Fence of fmode * scope

type symbol =
  Write_sym
| Downgrade of location
[@@deriving show]
         
type formula =
  Eq_expr of expr * expr
| Eq_var  of location * expr
| Eq_reg  of register * expr (* TODO: James does not have this. *)
| Symbol of symbol
| Not of formula
| And of formula * formula
| Or of formula * formula
[@@deriving show]


      
let rec sub_reg e r = function
  | Eq_reg (r',e') when r = r' -> Eq_expr (e,e')
  | Not f -> Not (sub_reg e r f)
  | And (f,f') -> And (sub_reg e r f, sub_reg e r f')
  | Or  (f,f') -> Or  (sub_reg e r f, sub_reg e r f')
  | f -> f

let rec sub_loc e l = function
  | Eq_var (l',e') when l = l' -> Eq_expr (e,e')
  | Not f -> Not (sub_loc e l f)
  | And (f,f') -> And (sub_loc e l f, sub_loc e l f')
  | Or  (f,f') -> Or  (sub_loc e l f, sub_loc e l f')
  | f -> f

let rec sub_sym phi s = function
  | Symbol s' when s = s' -> phi
  | Not f -> Not (sub_sym phi s f)
  | And (f,f') -> And (sub_sym phi s f, sub_sym phi s f')
  | Or  (f,f') -> Or  (sub_sym phi s f, sub_sym phi s f')
  | f -> f


      
let rec evalf = function
    Eq_expr (e,e') -> eval_expr empty_env e = eval_expr empty_env e'
  | Not f -> not (evalf f)
  | And (f,f') -> (evalf f) && (evalf f')
  | Or (f,f') -> (evalf f) || (evalf f')
  | _ -> false


let rec negate = function
    And (f1,f2) -> Or (negate f1, negate f2)
  | Or (f1,f2) -> And (negate f1, negate f2)
  | Not f -> f
  | f -> Not f

       
let rec convert_cnf = function (* TODO: this is not right! *)
  | And (f1,f2) -> And (convert_cnf f1, convert_cnf f2)
  | Or (f1,f2) -> And (convert_cnf (negate f1), convert_cnf (negate f2))
  | Not f -> negate f
  | f -> f

let rec convert_dnf = function (* TODO: this is not right! *)
  | And (f1,f2) -> Or (convert_dnf (negate f1), convert_dnf (negate f2))
  | Or (f1,f2) -> Or (convert_dnf f1, convert_dnf f2)
  | Not f -> negate f
  | f -> f


let data1 = And (Or (Symbol Write_sym, Symbol Write_sym), Or (Symbol Write_sym, Symbol Write_sym))

let data2 = convert_dnf data1

let test () = pp_formula Format.std_formatter data2              


                
(*                 
let rec entails f f' =
match f with
  Or (f1,f2) -> (entails f1 f') && (entails f2 f')
| Not f1 -> entails (negate f1) f'
| And (f1,f2) -> )
 *)
