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
!x y n.
  ((x + (y + 1)) < (2 ** (SUC n)))
  =
  ((x DIV 2 + y DIV 2 + (x MOD 2 + y MOD 2 - x MOD 2 * y MOD 2)) < (2 ** n))
``;

val plus1mod2_thm =
let
  val j_var = ``j:num``
  val simpThm = (GEN j_var (SPEC ``1:num`` (SPEC j_var (UNDISCH (SPEC (Term `2:num`) arithmeticTheory.MOD_PLUS)))))
  val simpAssum = GSYM (SIMP_CONV (arith_ss) [] ``0 < 2:num``)
  val simpThm2 = (REWRITE_RULE [EQ_IMP_THM] simpAssum)
  (* (REWRITE_RULE [AND1_THM] (SIMP_RULE (pure_ss) [EQ_IMP_THM] simpAssum)) *)
in
  GSYM (MP (DISCH (concl simpThm2) simpThm) simpThm2)
end;

val mult2plus1div2_thm =
let
  val x_var = ``x:num``
  val simpThm = SPEC ``2:num`` arithmeticTheory.ADD_DIV_ADD_DIV
  val simpAssum = prove(``0 < 2:num``, FULL_SIMP_TAC (arith_ss) [])
in
  SIMP_RULE (arith_ss) [] (GEN x_var (SPEC ``1:num`` (SPEC x_var (MP simpThm simpAssum))))
end;

(* TODO: experiment with simple solve spec arith conclusion function *)
fun specialize_thm_n_2 t =
  let
    val specThm = SPEC ``2:num`` t
    val simpAssum = prove(``0 < 2:num``, FULL_SIMP_TAC (arith_ss) [])
  in 
    MP specThm simpAssum
  end
;

val mult2plus2div2 = prove(``(2 * (m:num) + 2) DIV 2 = m + 1``,
  (RW_TAC (pure_ss) [(prove (``2 * (m:num) + 2 = (m + 1) * 2 + 0``, (RW_TAC (arith_ss) [])))])
  THEN (FULL_SIMP_TAC (arith_ss) [specialize_thm_n_2 arithmeticTheory.ADD_DIV_ADD_DIV])
);

val mult2plus2mod2 = prove(``(2 * m + 2) MOD 2 = 0``,
  (FULL_SIMP_TAC (arith_ss) [Once (GSYM (specialize_thm_n_2 arithmeticTheory.MOD_PLUS)), arithmeticTheory.EVEN_MOD2])
  THEN (Q.ABBREV_TAC `n = 2 * m`)
  THEN (`EVEN n` by ALL_TAC)
  THENL [
    (FULL_SIMP_TAC (srw_ss()) [Abbr `n`, arithmeticTheory.EVEN_DOUBLE])
    ,
    ALL_TAC
  ]
  THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
);

val mult2plus1mod2 = prove(``(2 * m + 1) MOD 2 = 1``,
  (FULL_SIMP_TAC (arith_ss) [Once (GSYM (specialize_thm_n_2 arithmeticTheory.MOD_PLUS)), arithmeticTheory.EVEN_MOD2])
  THEN (Q.ABBREV_TAC `n = 2 * m`)
  THEN (`EVEN n` by ALL_TAC)
  THENL [
    (FULL_SIMP_TAC (srw_ss()) [Abbr `n`, arithmeticTheory.EVEN_DOUBLE])
    ,
    ALL_TAC
  ]
  THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
);

val mult

PROVE_TAC [arithmeticTheory.RIGHT_ADD_DISTRIB]

EVAL_TAC

METIS_TAC [arithmeticTheory.RIGHT_ADD_DISTRIB]
RW_TAC (arith_ss) [arithmeticTheory.RIGHT_ADD_DISTRIB]
RW_TAC (arith_ss) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB]
FULL_SIMP_TAC (arith_ss) []

if x then (2=3) else (4=5)

(SIMP_CONV (srw_ss())  [arithmeticTheory.RIGHT_ADD_DISTRIB]) ``((m:num) + 1) * 2`` 


prove(``^goal``,
	(REPEAT GEN_TAC)
	THEN (Q.ABBREV_TAC `z = y + 1`)
	THEN (FULL_SIMP_TAC (srw_ss()) [SUM_2EXP_EQ])
	THEN (FULL_SIMP_TAC (srw_ss()) [Abbr `z`])
	
	THEN (Cases_on `EVEN y`)
(* EVEN_MOD2 ODD_EVEN EVEN_DIV_EQ_SUC *)
	THENL [
	  (FULL_SIMP_TAC (pure_ss) [Once (GSYM arithmeticTheory.ADD1)])
	  THEN (FULL_SIMP_TAC (pure_ss) [Once (EVEN_DIV_EQ_SUC)])
	  THEN (FULL_SIMP_TAC (pure_ss) [GSYM EVEN_DIV_EQ_SUC])
	  
	  THEN (FULL_SIMP_TAC (pure_ss) [plus1mod2_thm])
	  THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2])
	  ,
	  ALL_TAC
	]
	
	THEN (FULL_SIMP_TAC (pure_ss) [GSYM arithmeticTheory.ODD_EVEN])
	THEN (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ODD_EXISTS])

	THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ADD1])

	THEN (FULL_SIMP_TAC (pure_ss) [mult2plus1div2_thm, mult2plus2mod2, mult2plus1mod2, mult2plus2div2])

	THEN (FULL_SIMP_TAC (arith_ss) []) (* arithmeticTheory.MULT_0 *)
);


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
