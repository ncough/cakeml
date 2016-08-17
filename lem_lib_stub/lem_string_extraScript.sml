(*Generated by Lem from string_extra.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_numTheory lem_listTheory lem_basic_classesTheory lem_stringTheory lem_list_extraTheory ASCIInumbersTheory stringLib;

val _ = numLib.prefer_num();



val _ = new_theory "lem_string_extra"

(******************************************************************************)
(* String functions                                                           *)
(******************************************************************************)

(*open import Basic_classes*)
(*open import Num*)
(*open import List*)
(*open import String*)
(*open import List_extra*)
(*open import {hol} `stringLib`*)
(*open import {hol} `ASCIInumbersTheory`*)


(******************************************************************************)
(* Character's to numbers                                                     *)
(******************************************************************************)

(*val ord : char -> nat*)

(*val chr : nat -> char*)

(******************************************************************************)
(* Converting to strings                                                      *)
(******************************************************************************)

(*val stringFromNatHelper : nat -> list char -> list char*)
 val stringFromNatHelper_defn = Hol_defn "stringFromNatHelper" `
 (stringFromNatHelper n acc=  
 (if n =( 0 : num) then
    acc
  else
    stringFromNatHelper (n DIV( 10 : num)) (CHR ((n MOD( 10 : num)) +( 48 : num)) :: acc)))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn stringFromNatHelper_defn;

(*val stringFromNat : nat -> string*)

(*val stringFromNaturalHelper : natural -> list char -> list char*)
 val stringFromNaturalHelper_defn = Hol_defn "stringFromNaturalHelper" `
 (stringFromNaturalHelper n acc=  
 (if n =( 0:num) then
    acc
  else
    stringFromNaturalHelper (n DIV( 10:num)) (CHR ((((n MOD( 10:num)) +( 48:num)):num)) :: acc)))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn stringFromNaturalHelper_defn;

(*val stringFromNatural : natural -> string*)

(*val stringFromInt : int -> string*)
val _ = Define `
 (stringFromInt i=  
  (if i <( 0 : int) then 
     STRCAT"-" (num_to_dec_string (Num (ABS i)))
  else
    num_to_dec_string (Num (ABS i))))`;


(*val stringFromInteger : integer -> string*)
val _ = Define `
 (stringFromInteger i=  
  (if i <( 0 : int) then 
     STRCAT"-" (num_to_dec_string (Num (ABS i)))
  else
    num_to_dec_string (Num (ABS i))))`;



(******************************************************************************)
(* List-like operations                                                       *)
(******************************************************************************)

(*val nth : string -> nat -> char*)
(*let nth s n=  List_extra.nth (toCharList s) n*)

(*val stringConcat : list string -> string*)
(*let stringConcat s= 
  List.foldr (^) "" s*)

(******************************************************************************)
(* String comparison                                                          *)
(******************************************************************************)

(*val stringCompare : string -> string -> ordering*)

val _ = Define `
 (stringLess x y=  (orderingIsLess (EQ)))`;

val _ = Define `
 (stringLessEq x y=  (~ (orderingIsGreater (EQ))))`;

val _ = Define `
 (stringGreater x y=  (stringLess y x))`;

val _ = Define `
 (stringGreaterEq x y=  (stringLessEq y x))`;


val _ = Define `
(instance_Basic_classes_Ord_string_dict= (<|

  compare_method := (\ x y. EQ);

  isLess_method := stringLess;

  isLessEqual_method := stringLessEq;

  isGreater_method := stringGreater;

  isGreaterEqual_method := stringGreaterEq|>))`;

 
val _ = export_theory()

