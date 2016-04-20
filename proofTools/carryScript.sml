(* ========================================================================= *)
(* FILE          : carryScript.sml                                           *)
(* DESCRIPTION   : Supporting theorems for carry operations.                 *)
(* AUTHOR        : KTH - Royal Institute of Technology                       *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

(* HOL_Interactive.toggle_quietdec(); *)
open HolKernel boolLib bossLib Parse;
open arithTheory;
open wordsLib;
(* HOL_Interactive.toggle_quietdec(); *)


val _ = new_theory "carry";

(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*  Theorems - Supporting theorems for carry operations                      *)
(* ------------------------------------------------------------------------- *)

val FROM_NUM_TO_PLUS = (REWRITE_RULE [arithmeticTheory.ADD1]);

(* ------------------------------------------------------------------------- *)
(* ARITH to ARITH THM                                                        *)
(* ------------------------------------------------------------------------- *)

val plus1mod2_thm =
let
  val j_var = ``j:num``
  val simpThm = ((SPECL [j_var, ``1:num``]) o (SIMP_RULE (arith_ss) []) o (SPEC ``2:num``)) arithmeticTheory.MOD_PLUS
  val simpThm1 = (SIMP_RULE (arith_ss) []) simpThm
in
  (GSYM o (GEN j_var)) simpThm1
end;
val plus1mod2_thm = save_thm("plus1mod2_thm", plus1mod2_thm);


val mult2plus1div2_thm =
let
  val simpThm = SPEC ``2:num`` arithmeticTheory.ADD_DIV_ADD_DIV
  val simpAssum = prove(``0 < 2:num``, FULL_SIMP_TAC (arith_ss) [])
in
  ((SIMP_RULE (arith_ss) []) o (GEN ``x:num``) o (SPECL [``x:num``, ``1:num``]) o (MP simpThm))  simpAssum
end;
val mult2plus1div2_thm = save_thm("mult2plus1div2_thm", mult2plus1div2_thm);


val mult2plus2div2_thm = store_thm(
    "mult2plus2div2_thm", 
    ``(2 * (m:num) + 2) DIV 2 = m + 1``,
  (ASSUME_TAC (((SPECL [``m:num``, ``2:num``]) o (SIMP_RULE (arith_ss) []) o (SPEC ``2:num``)) arithmeticTheory.ADD_DIV_ADD_DIV))
  THEN (FULL_SIMP_TAC (arith_ss) [])
);


val mult2plus2mod2_thm = store_thm(
   "mult2plus2mod2_thm",
   ``(2 * m + 2) MOD 2 = 0``,
  (ASSUME_TAC (((SPECL [``2*m:num``, ``2:num``]) o (SIMP_RULE (arith_ss) []) o (SPEC ``2:num``) o GSYM) arithmeticTheory.MOD_PLUS))
  THEN (FULL_SIMP_TAC (arith_ss) [])
  THEN (`EVEN (2*m)` by (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EVEN_DOUBLE]))
  THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
);

val mult2plus1mod2_thm = store_thm(
   "mult2plus1mod2_thm",
   ``(2 * m + 1) MOD 2 = 1``,
  (ASSUME_TAC (((SPECL [``2*m:num``, ``1:num``]) o (SIMP_RULE (arith_ss) []) o (SPEC ``2:num``) o GSYM) arithmeticTheory.MOD_PLUS))
  THEN (FULL_SIMP_TAC (arith_ss) [])
  THEN (`EVEN (2*m)` by (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EVEN_DOUBLE]))
  THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
);

val goal = ``
!n x y.
  ((x + (y + 1)) < (2 ** (SUC n)))
  =
  ((x DIV 2 + y DIV 2 + (x MOD 2 + y MOD 2 - x MOD 2 * y MOD 2)) < (2 ** n))
``;
val carry_1_thm = store_thm(
   "carry_1_thm",
   ``^goal``,
	(REPEAT GEN_TAC)
	THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ADD1])
	THEN (Q.ABBREV_TAC `z = y + 1`)
	THEN (FULL_SIMP_TAC (srw_ss()) [FROM_NUM_TO_PLUS SUM_2EXP_EQ])
	THEN (FULL_SIMP_TAC (srw_ss()) [Abbr `z`])
	THEN (Cases_on `EVEN y`)
	THENL [
          (ASSUME_TAC (((SPEC ``y:num``) o (REWRITE_RULE [Once EQ_IMP_THM]) o FROM_NUM_TO_PLUS) EVEN_DIV_EQ_SUC))
	  THEN (REV_FULL_SIMP_TAC (srw_ss()) [])
	  THEN (FULL_SIMP_TAC (pure_ss) [Once plus1mod2_thm])
	  THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
	  ,
	  ALL_TAC
	]
	THEN (FULL_SIMP_TAC (pure_ss) [GSYM arithmeticTheory.ODD_EVEN])
        THEN (ASSUME_TAC (((SPEC ``y:num``) o (REWRITE_RULE [Once EQ_IMP_THM]) o FROM_NUM_TO_PLUS) arithmeticTheory.ODD_EXISTS))
  	THEN (REV_FULL_SIMP_TAC (srw_ss()) [])
	THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ADD1])
	THEN (FULL_SIMP_TAC (arith_ss) [mult2plus1div2_thm, mult2plus2mod2_thm, mult2plus1mod2_thm, mult2plus2div2_thm])
);

(* ------------------------------------------------------------------------- *)
(* END OF ARITH to ARITH THM                                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* ARITH to WORD THM                                                         *)
(* ------------------------------------------------------------------------- *)
val mod2either0or1_thm = store_thm(
   "mod2either0or1_thm",
   ``!x. (x MOD 2 = 0) \/ (x MOD 2 = 1)``,
  (STRIP_TAC)
  THEN (Cases_on `EVEN x`)
  THENL [
    (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
    ,
    (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_ODD])
    THEN (ASSUME_TAC ((SPEC ``x:num``) (FROM_NUM_TO_PLUS arithmeticTheory.EVEN_ODD_EXISTS)))
    THEN (REV_FULL_SIMP_TAC (arith_ss) [])
    THEN (FULL_SIMP_TAC (arith_ss) [mult2plus1mod2_thm])
  ]
);

val mod2bormod2either0or1_thm = store_thm(
   "mod2bormod2either0or1_thm",  
  ``(BITWISE 64 $\/ (w2n (x:word64) MOD 2) (w2n (y:word64) MOD 2) = 1) \/
    (BITWISE 64 $\/ (w2n x MOD 2) (w2n y MOD 2) = 0)
  ``,
      (ASSUME_TAC ((SPEC ``w2n (x:word64)``) mod2either0or1_thm))
      THEN (ASSUME_TAC ((SPEC ``w2n (y:word64)``) mod2either0or1_thm))
      THEN (RW_TAC (bool_ss) [])
      THEN (FULL_SIMP_TAC (arith_ss) [])
      THEN (EVAL_TAC)
);

val mod2boreq_thm = store_thm(
   "mod2boreq_thm",
   ``BITWISE 64 $\/ (w2n (x:word64) MOD 2) (w2n (y:word64) MOD 2) = (w2n x MOD 2 + w2n y MOD 2 − w2n x MOD 2 * w2n y MOD 2)``,
  (ASSUME_TAC ((SPEC ``w2n (x:word64)``) mod2either0or1_thm))
  THEN (ASSUME_TAC ((SPEC ``w2n (y:word64)``) mod2either0or1_thm))
  THEN (RW_TAC (bool_ss) [])
  THEN (FULL_SIMP_TAC (arith_ss) [])
  THEN (EVAL_TAC)
);


val plus_plus1_lt_2exp64_thm = store_thm(
   "plus_plus1_lt_2exp64_thm",  
    ``∀ x y . 
      (w2n x DIV 2 + w2n y DIV 2 + (w2n x MOD 2 + w2n y MOD 2 − w2n x MOD 2 * w2n y MOD 2) < 9223372036854775808) =
      (((x // 2w) + (y // 2w) + ((word_mod x 2w) || (word_mod y 2w))) <+ (9223372036854775808w:word64))
    ``,
	(REPEAT STRIP_TAC)
	THEN (EVAL_TAC)
	THEN (FULL_SIMP_TAC (arith_ss) [bitTheory.MOD_PLUS_LEFT])
	THEN (`(w2n x DIV 2 + (w2n y DIV 2 + BITWISE 64 $\/ (w2n x MOD 2) (w2n y MOD 2))) < 18446744073709551616` by ALL_TAC)
	THENL [
	      (ASSUME_TAC (SPECL [``63:num``, ``w2n (x:word64)``, ``w2n (y:word64)``] RIGHT_SHIFT_SUM_LT_2EXP))
	      THEN (FULL_SIMP_TAC (srw_ss()) [])
	      THEN (ASSUME_TAC (ISPEC ``x:word64`` wordsTheory.w2n_lt))
	      THEN (ASSUME_TAC (ISPEC ``y:word64`` wordsTheory.w2n_lt))
	      THEN (FULL_SIMP_TAC (srw_ss()) [])
	      THEN (ASSUME_TAC mod2bormod2either0or1_thm)
	      THEN (FULL_SIMP_TAC (arith_ss) []),
	      ALL_TAC]
	 THEN (FULL_SIMP_TAC (arith_ss) [])
	 THEN (ASSUME_TAC mod2boreq_thm)
	 THEN (FULL_SIMP_TAC (arith_ss) [])
);

(* ------------------------------------------------------------------------- *)
(* END OF ARITH to WORD THM                                                  *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
val _ = export_theory();
