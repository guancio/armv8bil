HOL_Interactive.toggle_quietdec();
open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
open state_transformerTheory updateTheory arm8Theory;
open stateTheory;
open lcsymtacs arm8_stepTheory;
open state_transformerSyntax;
open arm8_stepLib;
open proofTools arithTheory;
open bilTheory arm8bilTheory;
open arm8bilLib;
HOL_Interactive.toggle_quietdec();


(*
tc_exp_arm8 ``T``;
tc_exp_arm8 ``s.REG 1w``;
tc_exp_arm8 ``(s.REG 1w) + 2w``;
tc_exp_arm8 ``(s.REG 1w) + (s.REG 2w)``;
tc_exp_arm8 ``(s.REG 1w) + (s.REG 1w)``;
tc_exp_arm8 ``mem_dword s.MEM 0w``;
tc_exp_arm8 ``mem_dword s.MEM ((s.REG 1w) + 2w)``;

tc_one_instruction2 `MOV X0, #1`;
tc_one_instruction2_by_bin "b9003bff";
*)

arm8_step_code `MOV X0, #1`;
arm8_step_code `ADD X0, X1, X2`;
tc_exp_arm8 ``s.REG 1w + s.REG 2w``;
tc_exp_arm8 ``s.REG 1w + s.REG 2w + 1w -37w + (s.REG 12w * 13w)``;

tc_exp_arm8 ``s.REG 1w >>~ 2w + s.REG 2w >>~ 2w``;



arm8_step_code `ADDS X0, X1, X2`;
tc_exp_arm8 ``(s.REG 1w + s.REG 2w) = 0w``;

val exp = ``((if
                  w2n (s.REG 1w) + w2n (s.REG 2w) < 18446744073709551616
                then
                  w2n (s.REG 1w) + w2n (s.REG 2w)
                else
                  (w2n (s.REG 1w) + w2n (s.REG 2w)) MOD
                  18446744073709551616) ≠
               w2n (s.REG 1w) + w2n (s.REG 2w))``;
val exp1 = (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [carry_thm])) exp;

val plus_lt_2exp64_tm = GSYM (tryprove(
    ``∀ x y . 
      (((x // 2w) + (y // 2w) + (word_mod x 2w) * (word_mod y 2w)) <+
       (9223372036854775808w:word64)) =
      (w2n x + w2n y < 18446744073709551616)
    ``,
	(REPEAT STRIP_TAC)
	THEN (EVAL_TAC)
	THEN ((FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_PLUS, DIV_PRODMOD_LT_2EXP]))
	THEN  (FULL_SIMP_TAC (pure_ss) [prove(``(18446744073709551616:num) = 2 ** SUC 63``, EVAL_TAC), SPECL [``63:num``, ``w2n(x:word64)``, ``w2n(y:word64)``] SUM_2EXP_EQ])
	THEN (ASSUME_TAC (SPECL [``63:num``, ``w2n(x:word64)``, ``w2n(y:word64)``] DIV_PRODMOD_LT_2EXP))
	THEN (ASSUME_TAC (ISPEC ``x:word64`` wordsTheory.w2n_lt))
	THEN (ASSUME_TAC (ISPEC ``y:word64`` wordsTheory.w2n_lt))
	THEN (FULL_SIMP_TAC (srw_ss()) [wordsTheory.dimword_64])
	THEN ((FULL_SIMP_TAC (arith_ss) []))
));






















val goal = ``
!n x y.
  ((x + (y + 1)) < (2 ** (SUC n)))
  =
  ((x DIV 2 + y DIV 2 + (x MOD 2 + y MOD 2 - x MOD 2 * y MOD 2)) < (2 ** n))
``;


val plus1mod2_thm =
let
  val j_var = ``j:num``
  val simpThm = ((SPECL [j_var, ``1:num``]) o (SIMP_RULE (arith_ss) []) o (SPEC ``2:num``)) arithmeticTheory.MOD_PLUS
  val simpThm1 = (SIMP_RULE (arith_ss) []) simpThm
in
  (GSYM o (GEN j_var)) simpThm1
end;

val mult2plus1div2_thm =
let
  val simpThm = SPEC ``2:num`` arithmeticTheory.ADD_DIV_ADD_DIV
  val simpAssum = prove(``0 < 2:num``, FULL_SIMP_TAC (arith_ss) [])
in
  ((SIMP_RULE (arith_ss) []) o (GEN ``x:num``) o (SPECL [``x:num``, ``1:num``]) o (MP simpThm))  simpAssum
end;


val mult2plus2div2 = prove(``(2 * (m:num) + 2) DIV 2 = m + 1``,
  (ASSUME_TAC (((SPECL [``m:num``, ``2:num``]) o (SIMP_RULE (arith_ss) []) o (SPEC ``2:num``)) arithmeticTheory.ADD_DIV_ADD_DIV))
  THEN (FULL_SIMP_TAC (arith_ss) [])
);

val mult2plus2mod2 = prove(``(2 * m + 2) MOD 2 = 0``,
  (ASSUME_TAC (((SPECL [``2*m:num``, ``2:num``]) o (SIMP_RULE (arith_ss) []) o (SPEC ``2:num``) o GSYM) arithmeticTheory.MOD_PLUS))
  THEN (FULL_SIMP_TAC (arith_ss) [])
  THEN (`EVEN (2*m)` by (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EVEN_DOUBLE]))
  THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
);

val mult2plus1mod2 = prove(``(2 * m + 1) MOD 2 = 1``,
  (ASSUME_TAC (((SPECL [``2*m:num``, ``1:num``]) o (SIMP_RULE (arith_ss) []) o (SPEC ``2:num``) o GSYM) arithmeticTheory.MOD_PLUS))
  THEN (FULL_SIMP_TAC (arith_ss) [])
  THEN (`EVEN (2*m)` by (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EVEN_DOUBLE]))
  THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
);

val FROM_NUM_TO_PLUS = (REWRITE_RULE [arithmeticTheory.ADD1]);

val thm_carry_1 = prove(``^goal``,
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
	THEN (FULL_SIMP_TAC (arith_ss) [mult2plus1div2_thm, mult2plus2mod2, mult2plus1mod2, mult2plus2div2])
);

val mod2either0or1 = prove(``!x. (x MOD 2 = 0) \/ (x MOD 2 = 1)``,
  (STRIP_TAC)
  THEN (Cases_on `EVEN x`)
  THENL [
    (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
    ,
    (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_ODD])
    THEN (ASSUME_TAC ((SPEC ``x:num``) (FROM_NUM_TO_PLUS arithmeticTheory.EVEN_ODD_EXISTS)))
    THEN (REV_FULL_SIMP_TAC (arith_ss) [])
    THEN (FULL_SIMP_TAC (arith_ss) [mult2plus1mod2])
  ]
);

val mod2bormod2either0or1 = prove(
  ``(BITWISE 64 $\/ (w2n (x:word64) MOD 2) (w2n (y:word64) MOD 2) = 1) \/
    (BITWISE 64 $\/ (w2n x MOD 2) (w2n y MOD 2) = 0)
  ``,
      (ASSUME_TAC ((SPEC ``w2n (x:word64)``) mod2either0or1))
      THEN (ASSUME_TAC ((SPEC ``w2n (y:word64)``) mod2either0or1))
      THEN (RW_TAC (bool_ss) [])
      THEN (FULL_SIMP_TAC (arith_ss) [])
      THEN (EVAL_TAC)
);

val mod2boreq = prove(``BITWISE 64 $\/ (w2n (x:word64) MOD 2) (w2n (y:word64) MOD 2) = (w2n x MOD 2 + w2n y MOD 2 − w2n x MOD 2 * w2n y MOD 2)``,
  (ASSUME_TAC ((SPEC ``w2n (x:word64)``) mod2either0or1))
  THEN (ASSUME_TAC ((SPEC ``w2n (y:word64)``) mod2either0or1))
  THEN (RW_TAC (bool_ss) [])
  THEN (FULL_SIMP_TAC (arith_ss) [])
  THEN (EVAL_TAC)
);


val plus_plus1_lt_2exp64_tm = GSYM (tryprove(
    ``∀ x y . 
      (((x // 2w) + (y // 2w) + ((word_mod x 2w) || (word_mod y 2w))) <+ (9223372036854775808w:word64)) =
      (w2n x DIV 2 + w2n y DIV 2 + (w2n x MOD 2 + w2n y MOD 2 − w2n x MOD 2 * w2n y MOD 2) < 9223372036854775808)
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
	      THEN (ASSUME_TAC mod2bormod2either0or1)


	      THEN (FULL_SIMP_TAC (arith_ss) []),
	      ALL_TAC]
	 THEN (FULL_SIMP_TAC (arith_ss) [])
	 THEN (ASSUME_TAC mod2boreq)
	 THEN (FULL_SIMP_TAC (arith_ss) [])
));














(w2n x DIV 2 +
 (w2n y DIV 2 + BITWISE 64 $\/ (w2n x MOD 2) (w2n y MOD 2))) MOD
18446744073709551616 < 9223372036854775808 ⇔
w2n x DIV 2 + w2n y DIV 2 +
(w2n x MOD 2 + w2n y MOD 2 − w2n x MOD 2 * w2n y MOD 2) <
9223372036854775808

if we prove that (w2n x DIV 2 +
 (w2n y DIV 2 + BITWISE 64 $\/ (w2n x MOD 2) (w2n y MOD 2))) < 18446744073709551616

then 
(w2n x DIV 2 +
 (w2n y DIV 2 + BITWISE 64 $\/ (w2n x MOD 2) (w2n y MOD 2))) MOD
18446744073709551616 =
(w2n x DIV 2 +
 (w2n y DIV 2 + BITWISE 64 $\/ (w2n x MOD 2) (w2n y MOD 2)))

then we have

(w2n x DIV 2 +
 (w2n y DIV 2 + BITWISE 64 $\/ (w2n x MOD 2) (w2n y MOD 2)))
 < 9223372036854775808 ⇔
w2n x DIV 2 + w2n y DIV 2 +
(w2n x MOD 2 + w2n y MOD 2 − w2n x MOD 2 * w2n y MOD 2) <
9223372036854775808




));

((a MOD n) + b)) MOD n mod n


blastLib.BBLAST_PROVE ``((word_mod (x:word64) 2w) + (word_mod (y:word64) (2w:word64))) =  (((word_mod x 2w) + (word_mod y 2w)) - (((word_mod x 2w) * (word_mod y 2w))))``;


val tmp1 = blastLib.BBLAST_PROVE ``((1w && x) = 1w) \/ ((1w && x) = 0w:word64)``;
val tmp2 = blastLib.BBLAST_PROVE ``((1w && y) = 1w) \/ ((1w && y) = 0w:word64)``;
prove(``((0x1w && (x:word64)) || (0x1w && (y:word64))) =
	 ((0x1w && (x:word64)) + (0x1w && (y:word64)) - ((0x1w && (x:word64)) * (0x1w && (y:word64))))``.
	 (ASSUME_TAC tmp1)
	 THEN (ASSUME_TAC tmp2)
	 THEN (RW_TAC (srw_ss()) [])
	 THEN (FULL_SIMP_TAC (srw_ss()) [])
);

blastLib.BBLAST_PROVE ``
 ((0x1w && (x:word64)) || (0x1w && (x:word64))) =
 ((0x1w && (x:word64)) * (0x1w && (x:word64)))
``;

val tmp3 = blastLib.BBLAST_PROVE ``((1w:word64) && y) = (word_mod y 2w)``;



 ((0x1w && (x:word64)) + (0x1w && (x:word64)) + ((0x1w && (x:word64)) * (0x1w && (x:word64))))
= 0x1w``;


GSYM (tryprove(
    ``∀ x y . 
      (((x // 2w) + (y // 2w) + ((word_mod x 2w) * (word_mod y 2w) )) <+ (9223372036854775808w:word64)) =
      (w2n x + w2n y < 18446744073709551616)
    ``,
	(REPEAT STRIP_TAC)
	THEN (EVAL_TAC)
	THEN ((FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_PLUS]))
	THEN ((FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_PLUS, DIV_PRODMOD_LT_2EXP]))
	THEN  (FULL_SIMP_TAC (pure_ss) [prove(``(18446744073709551616:num) = 2 ** SUC 63``, EVAL_TAC), SPECL [``63:num``, ``w2n(x:word64)``, ``w2n(y:word64)``] SUM_2EXP_EQ])
	THEN (ASSUME_TAC (SPECL [``63:num``, ``w2n(x:word64)``, ``w2n(y:word64)``] DIV_PRODMOD_LT_2EXP))
	THEN (ASSUME_TAC (ISPEC ``x:word64`` wordsTheory.w2n_lt))
	THEN (ASSUME_TAC (ISPEC ``y:word64`` wordsTheory.w2n_lt))
	THEN (FULL_SIMP_TAC (srw_ss()) [wordsTheory.dimword_64])
	THEN ((FULL_SIMP_TAC (arith_ss) []))
));




val DIV_PRODMOD_LT_2EXP = store_thm("DIV_PRODMOD_LT_2EXP"
  , ``∀ (n:num) (j:num) (k:num). (j < 2**(SUC n)) ∧ (k < 2**(SUC n)) ==> (j DIV 2 + k DIV 2 + (j MOD 2) * (k MOD 2) < 2**(SUC n))``
  ,       (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC (SPEC_ALL MULT_MOD2_01))
    THEN  (RW_TAC (pure_ss) [])
    THEN  (
            (RW_TAC (arith_ss) [])
      THEN  (RW_TAC (pure_ss) [arithmeticTheory.ADD_ASSOC])
      THEN  (FULL_SIMP_TAC (arith_ss) [RIGHT_SHIFT_SUM_LT_2EXP])
    )
);





arm8_step_code `SUBS X0, X1, X2`;
``((if
                  w2n (s.REG 1w) + w2n (¬s.REG 2w) + 1 <
                  18446744073709551616
                then
                  w2n (s.REG 1w) + w2n (¬s.REG 2w) + 1
                else
                  (w2n (s.REG 1w) + w2n (¬s.REG 2w) + 1) MOD
                  18446744073709551616) ≠
               w2n (s.REG 1w) + w2n (¬s.REG 2w) + 1)``;

``(if a < n then a else a MOD n) <> a``

``a<n``

val exp1 =  ``w2n (s.REG 1w) + w2n (¬s.REG 2w) + 1 < 18446744073709551616``;
val t1 = ((SIMP_RULE (arith_ss) []) o (SPEC ``63:num``)) thm_carry_1;
val t2 = SIMP_CONV (arith_ss) [t1] exp1;
(snd o dest_eq o concl) t2;


``w2n (¬s.REG 2w) DIV 2 + w2n (s.REG 1w) DIV 2 +
  (w2n (¬s.REG 2w) MOD 2 + w2n (s.REG 1w) MOD 2 −
   w2n (¬s.REG 2w) MOD 2 * w2n (s.REG 1w) MOD 2) < 9223372036854775808``
   =
tc_exp_arm8 
``¬s.REG 2w >>~ 1w + s.REG 1w >>~ 1w +
  (¬s.REG 2w && 1w + s.REG 1w && 1w −
   ¬s.REG 2w && 1w * s.REG 1w && 1w)``

tc_exp_arm8 ``9223372036854775808w:word64``;


tc_exp_arm8 `` (s.REG 2w) // 2w + (s.REG 2w) // 2w + (word_mod (s.REG 2w) 2w ‖ word_mod (s.REG 2w) 2w) <+ 9223372036854775808w``;


``¬s.REG 2w >>~ 1w + s.REG 1w >>~ 1w +
  (¬s.REG 2w && 1w + s.REG 1w && 1w −
   ¬s.REG 2w && 1w * s.REG 1w && 1w) = 9223372036854775808w:word64``;
   



2**63-1
2**63-1

2**64-2

val mult

PROVE_TAC [arithmeticTheory.RIGHT_ADD_DISTRIB]

EVAL_TAC

METIS_TAC [arithmeticTheory.RIGHT_ADD_DISTRIB]
RW_TAC (arith_ss) [arithmeticTheory.RIGHT_ADD_DISTRIB]
RW_TAC (arith_ss) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB]
FULL_SIMP_TAC (arith_ss) []

if x then (2=3) else (4=5)

(SIMP_CONV (srw_ss())  [arithmeticTheory.RIGHT_ADD_DISTRIB]) ``((m:num) + 1) * 2`` 




(*
	  THEN (FULL_SIMP_TAC (pure_ss) [Once (GSYM (specialize_thm_n_2 arithmeticTheory.MOD_PLUS)), arithmeticTheory.EVEN_DOUBLE, arithmeticTheory.EVEN_MOD2])

	  THEN ()
*)
(*	THEN (Cases_on `?y'. y = 2 * y'`)  *)

	THEN (FULL_SIMP_TAC (arith_ss) [EVEN_DIV_EQ_SUC])
	


	THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_ODD])


(FULL_SIMP_TAC (srw_ss()) [plus_lt_2exp64_tmb])

	THEN (RW_TAC (srw_ss()) [ASSUME ``y + 1 = z``])


REWRITE_TAC (srw_ss()) [ASSUME ``z = y + 1``])







print (String.concatWith "\n" (map (fn (x,y) => x) (axioms "min")));
print (String.concatWith "\n" (map PolyML.makestring (axioms "bool")));

T_DEF
F_DEF


print (String.concatWith "\n" (map (fn (x,y) => x) (theorems "min")));
print (String.concatWith "\n" (map (fn (x,y) => x) (types "min")));
print (String.concatWith "\n" (map (PolyML.makestring) (constants "min")));

PolyML.makestring

(SPEC (Term `j`) (SPEC (Term `2:num`) arithmeticTheory.MOD_PLUS))


 arithmeticTheory.NOT_ODD_EQ_EVEN










EVAL ``20w :word64 // 3w``;
EVAL ``4 MOD 2``;

open arithmeticTheory;













val SUM_1_2EXP_EQ = store_thm("SUM_1_2EXP_EQ"
  , ``∀ (j:num) (k:num). (j + (k + 1) < 2**(SUC 64)) = ((j DIV 2) + (k DIV 2) + (j MOD 2) * (k MOD 2) + 1 < 2**64)``


,       (REPEAT STRIP_TAC)
    THEN (Induct_on `j`)
    THENL [
    	  (FULL_SIMP_TAC (srw_ss()) [])
	  THEN (Induct_on `k`)
	  THENL [
	  	FULL_SIMP_TAC (srw_ss()) [],
		
	  ]
    ]


    THEN  (Cases_on `EVEN j`)
    THENL [
              (Cases_on `EVEN k`)
        THENL [
            (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2, EVENS_DIV2_ADD, arithmeticTheory.EXP2_LT])
          , (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2, ODD_MOD2, EVEN_ODD_MIX_DIV2_ADD, EVEN_ODD_MIX_DIV2, arithmeticTheory.EXP2_LT])
        ]
      ,       (Cases_on `EVEN k`)
        THENL [
            (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2, ODD_MOD2, EVEN_ODD_MIX_DIV2_ADD, EVEN_ODD_MIX_DIV2, arithmeticTheory.EXP2_LT])
          ,       (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
            THEN  (ASSUME_TAC ((UNDISCH_ALL o SPEC_ALL) ODD_SUM_GT1))
            THEN  (ASSUME_TAC ((UNDISCH_ALL o (SPEC ``(j:num) + k``)) GT1_DIV2_GT0))
            THEN  (FULL_SIMP_TAC (arith_ss) [ODD_MOD2, ODDS_DIV2_ADD, SUB2_DIV2_DIV2_SUB1, arithmeticTheory.EXP2_LT])
        ]
    ]
);


val minus_lt_2exp64_tm = GSYM (tryprove(
    ``∀ x y . 
      (((x // 2w) + (y // 2w) + (word_mod x 2w) * (word_mod y 2w)) + 1w <+
       (9223372036854775808w:word64)) =
      (w2n x + w2n y + 1 < 18446744073709551616)
    ``,
    (REPEAT STRIP_TAC)
    THEN (EVAL_TAC)
    THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_PLUS])
    THEN (REWRITE_TAC [Once (prove (``1 = 1 MOD 18446744073709551616``, FULL_SIMP_TAC (srw_ss()) []))])
    THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_PLUS])

    THEN (FULL_SIMP_TAC (pure_ss) [
    	 prove(``(18446744073709551616:num) = 2 ** SUC 63``, EVAL_TAC),
    	 SPECL [``63:num``, ``w2n(x:word64)``, ``w2n(y:word64)``] SUM_2EXP_EQ
	 ])
));
