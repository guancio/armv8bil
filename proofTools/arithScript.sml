(* ========================================================================= *)
(* FILE          : arithScript.sml                                           *)
(* DESCRIPTION   : Arithmetic supporting theorems.                           *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;
open wordsTheory arithmeticTheory proofTools;

val _ = new_theory "arith";
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*  Theorems - Supporting important theorems                                 *)
(* ------------------------------------------------------------------------- *)

val ADD_SUB_COMM = store_thm("ADD_SUB_COMM", ``∀(n:num) (h:num). (h <= n) ==> (n + h - h = n - h + h)``, numLib.ARITH_TAC);
val PREC_EXISTS = store_thm("PREC_EXISTS"
  , ``∀ (n:num). (0 < n) ==> (∃m. n = m + 1)``
  ,       (REPEAT STRIP_TAC)
    THEN  (EXISTS_TAC ``(n:num) - 1``)
    THEN  (RW_TAC (arith_ss) []) 
);

val MULT_MOD2_01 = store_thm("MULT_MOD2_01", ``∀ (j:num) (k:num). (j MOD 2 * k MOD 2 = 0) ∨ (j MOD 2 * k MOD 2 = 1)``, (RW_TAC (srw_ss()) [arithmeticTheory.MOD_2]));

(* This theorem comes from ARMv7 lifter by Hamed Nemati *)
val BIT_DIV_MOD = store_thm("BIT_DIV_MOD"
  , ``∀ (n:num) (h:num). BIT h n = ((n DIV 2**h) MOD 2 = 1)``
  , (RW_TAC (srw_ss()) [bitTheory.MOD_2EXP_def, bitTheory.DIV_2EXP_def, bitTheory.BIT_def, bitTheory.BITS_def, arithmeticTheory.ADD1])
);

val MOD_LESS_ALT = store_thm("MOD_LESS_ALT"
  , ``∀ (j:num) (n:num) (m:num). (0 < n) ==> ((n <= m) ==> (j MOD n < m))``
  ,       (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC ((UNDISCH_ALL o (SPECL [``j:num``, ``n:num``])) arithmeticTheory.MOD_LESS))
    THEN  (FULL_SIMP_TAC (arith_ss) [])
);

val BITS_LT_2EXP = store_thm("BITS_LT_2EXP"
  , ``∀ (h:num) (j:num) (k:num). BITS h j k < 2**(SUC h)``
  , (RW_TAC (arith_ss) [bitTheory.MOD_2EXP_def, bitTheory.BITS_def, MOD_LESS_ALT])
);

val MODN_MODM = store_thm("MODN_MODM"
  , ``∀n k m. (0 < n) ==> ((n <= m) ==> (k MOD n MOD m = k MOD n))``
  , (RW_TAC (srw_ss()) [MOD_LESS_ALT])
);

val EXP2_LT_ALT = store_thm("EXP2_LT_ALT"
  , ``∀ (n:num) (m:num) (j:num). ((j < 2**n) ==> ((j DIV 2**m) < 2**(n - m)))``
  ,       (REPEAT STRIP_TAC)
    THEN  (Cases_on `(n:num) <= m`)
    THENL [
            (ASSUME_TAC ((UNDISCH_ALL o fst o EQ_IMP_RULE o GSYM o (SPECL [``n:num``, ``m:num``])) arithmeticTheory.SUB_EQ_0))
      THEN  (ASSUME_TAC ((UNDISCH_ALL o fst o EQ_IMP_RULE o GSYM o (SPECL [``m:num``, ``n:num``])) (DISPOSE_HYP (SPEC ``2:num`` arithmeticTheory.EXP_BASE_LE_MONO))))
      THEN  (SIMP_TAC (arith_ss) [arithmeticTheory.DIV_LT_X, GSYM arithmeticTheory.EXP_BASE_LE_MONO])
      THEN  (RW_TAC (arith_ss) [])
    ,       (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.EXP_ADD, arithmeticTheory.DIV_LT_X])
    ]
);

val n2w_w2w_concat_0 = store_thm("n2w_w2w_concat_0", 
    ``∀(w :β word) (z :α word) (c :γ word). FINITE 𝕌((:α) :α itself) ==> (dimindex (:β) <= dimindex (:γ) ==> ((z = 0w) ==> ((c = (n2w (w2n w) :γ word)) ==> (c = z @@ w))))``
  ,       (RW_TAC (pure_ss) [])
    THEN  (ASSUME_TAC (ISPEC ``w :β word`` wordsTheory.w2n_lt))
    THEN  (ASSUME_TAC ((UNDISCH_ALL o CONJ_IMP o (SPECL [``w:β word``, ``w2n (w:β word)``])) wordsTheory.word_concat_0_eq))
    THEN  ((FULL_SIMP_TAC (srw_ss()) []))
);

val ADDN_DIVN_DIVN_ADD1 = store_thm("ADDN_DIVN_DIVN_ADD1"
  , ``∀(n :num). (2 + n) DIV 2 = 1 + n DIV 2``
  ,       GEN_TAC
    THEN  (ASSUME_TAC (MP ((DISCH_ALL o (SPECL [``1:num``, ``n:num``]) o UNDISCH_ALL o (SPEC ``2:num``)) arithmeticTheory.ADD_DIV_ADD_DIV) (prove(``(0:num) < 2``, EVAL_TAC))))
    THEN  (FULL_SIMP_TAC (srw_ss()) [])
);

val MULT_SUM = store_thm("MULT_SUM"
  , ``∀ (n:num) (m:num). (m * n = SUM m (λx.n))``
  ,       (Induct_on `m`)
    THEN  (FULL_SIMP_TAC (arith_ss) [sum_numTheory.SUM_def,arithmeticTheory.MULT_SUC])
);

val MULT_SUM_COMM = store_thm("MULT_SUM_COMM"
  , ``∀ (j:num) (k:num). SUM j (λx. k) = SUM k (λx. j)``
  , (RW_TAC (arith_ss) [GSYM MULT_SUM])
);

val EVENS_DIV2_ADD = store_thm("EVENS_DIV2_ADD"
  , ``∀ (j:num) (k:num). (EVEN j ∧ EVEN k) ==> (j DIV 2 + k DIV 2 = (j + k) DIV 2)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_EXISTS])
    THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD1, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
    THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
    THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD1, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
);

val ODDS_DIV2_ADD = store_thm("ODDS_DIV2_ADD"
  , ``∀ (j:num) (k:num). (ODD  j ∧ ODD  k) ==> (j DIV 2 + k DIV 2 = (j + k - 2) DIV 2)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD_EXISTS])
    THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD1, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
    THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
    THEN  (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
    THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD1, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
);

val ODDS_DIV2_ADD_ALT = store_thm("ODDS_DIV2_ADD_ALT"
  , ``∀ (j:num) (k:num). (ODD  j ∧ ODD  k) ==> (j DIV 2 + k DIV 2 = (j + k) DIV 2 - 1)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD_EXISTS])
    THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD1, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
    THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
    THEN  (FULL_SIMP_TAC (pure_ss) [Once arithmeticTheory.ADD_ASSOC])
    THEN  (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
    THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [ADDN_DIVN_DIVN_ADD1])
    THEN  (FULL_SIMP_TAC (pure_ss) [MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
    THEN  (FULL_SIMP_TAC (srw_ss()) [(UNDISCH_ALL o (SPEC ``2:num``)) arithmeticTheory.MULT_DIV])
);

val EVEN_ODD_MIX_DIV2_ADD = store_thm("EVEN_ODD_MIX_DIV2_ADD"
  , ``∀ (j:num) (k:num). (EVEN j ≠ EVEN k) ==> (j DIV 2 + k DIV 2 = (j + k - 1) DIV 2)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (Cases_on `EVEN j`)
    THEN  (
            (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
      THEN  (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.EVEN_ODD, arithmeticTheory.EVEN_EXISTS])
      THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD_EXISTS])
      THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD1, MULT_SUM, MULT_SUM_COMM])
      THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
      THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
      THEN  (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
      THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD_COMM])
      THEN  (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD_DIV_ADD_DIV])
      THEN  (FULL_SIMP_TAC (pure_ss) [MULT_SUM, MULT_SUM_COMM])
      THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
      THEN  (FULL_SIMP_TAC (arith_ss) [])
    )
);

val ODD_POS = store_thm("ODD_POS"
  , ``∀ (n:num). (ODD n) ==> (0 < n)``
  , Induct THEN (FULL_SIMP_TAC (arith_ss) [])
);

val ODD_MOD2 = store_thm("ODD_MOD2"
  , ``∀ (n:num). (ODD n) = (n MOD 2 = 1)``
  ,       (RW_TAC (arith_ss) [arithmeticTheory.MOD_2])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_ODD])
);

val ODD_SUM_GT1 = store_thm("ODD_SUM_GT1"
  , ``∀ (j:num) (k:num). ODD j ==> (ODD k ==> (1 < j + k))``
  , Induct THEN Induct THEN (FULL_SIMP_TAC (arith_ss) [])
);

val GT1_DIV2_GT0 = store_thm("GT1_DIV2_GT0"
  , ``∀ (n:num). 1 < n ==> (0 < n DIV 2)``
  ,       Induct
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (Induct_on `n`)
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (RW_TAC (arith_ss) [arithmeticTheory.ADD1])
    THEN  (SIMP_TAC (pure_ss) [Once arithmeticTheory.ADD_COMM])
    THEN  (FULL_SIMP_TAC (arith_ss) [ADDN_DIVN_DIVN_ADD1])
);

val GT1_DIV2_GE1 = prove(
    ``∀ (n:num). 1 < n ==> (1 ≤ n DIV 2)``
  ,       Induct
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (Induct_on `n`)
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (RW_TAC (arith_ss) [arithmeticTheory.ADD1])
    THEN  (SIMP_TAC (pure_ss) [Once arithmeticTheory.ADD_COMM])
    THEN  (FULL_SIMP_TAC (arith_ss) [ADDN_DIVN_DIVN_ADD1])
);

val SUB2_DIV2_DIV2_SUB1 = store_thm("SUB2_DIV2_DIV2_SUB1"
  , ``∀(n :num). (n - 2) DIV 2 = n DIV 2 - 1``
  ,       Induct
    THENL [
      (FULL_SIMP_TAC (arith_ss) [])
    ,
            (Induct_on `n`)
      THENL [
              (FULL_SIMP_TAC (arith_ss) [])
      ,       (RW_TAC (pure_ss) [])
        THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ADD1])
        THEN  (RW_TAC (pure_ss) [Once arithmeticTheory.ADD_COMM, ADDN_DIVN_DIVN_ADD1])
        THEN  (FULL_SIMP_TAC (arith_ss) [])
      ]
    ]
);

val EVEN_DIV_EQ_SUC = store_thm("EVEN_DIV_EQ_SUC"
  , ``∀ (n:num). (EVEN n) = (n DIV 2 = (SUC n) DIV 2)``
  ,       GEN_TAC
    THEN  EQ_TAC
    THENL [
              (REPEAT STRIP_TAC)
        THEN  (FULL_SIMP_TAC (pure_ss) [SPEC_ALL arithmeticTheory.EVEN_EXISTS])
        THEN  (RW_TAC (pure_ss) [arithmeticTheory.ADD1, MULT_SUM, MULT_SUM_COMM])
        THEN  (RW_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
        THEN  (RW_TAC (srw_ss()) [arithmeticTheory.MULT_DIV])
      ,
              (Cases_on `EVEN n`)
        THEN  (FULL_SIMP_TAC (arith_ss) [])
        THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_ODD])
        THEN  (FULL_SIMP_TAC (pure_ss) [SPEC_ALL arithmeticTheory.ODD_EXISTS])
        THEN  (RW_TAC (pure_ss) [arithmeticTheory.ADD1, MULT_SUM, MULT_SUM_COMM])
        THEN  (RW_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
        THEN  (FULL_SIMP_TAC (arith_ss) [])
        THEN  (RW_TAC (pure_ss) [
                    EVALBOOL ``(2:num) * m + 2 = 2*m + 2*1``
                  , GSYM arithmeticTheory.LEFT_ADD_DISTRIB
                ]
              )
        THEN  (RW_TAC (pure_ss) [MULT_SUM, SPECL [``2:num``, ``(m:num) + 1``] MULT_SUM_COMM])
        THEN  (RW_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
        THEN  (FULL_SIMP_TAC (arith_ss) [])
    ]
);

val EXP2_LT_ALT2 = store_thm("EXP2_LT_ALT2"
  , ``∀ (n:num) (m:num). (m < 2**n = 2*m < 2** SUC n) ∧ (m < 2**n = 2*m + 1 < 2** SUC n)``
  ,       (REPEAT STRIP_TAC)
    THENL [
              (REWRITE_TAC [Once (prove(``m = ((2:num)*m) DIV 2``, FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.MULT_DIV, Once arithmeticTheory.MULT_COMM]))])
        THEN  (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EXP2_LT])
      ,       (REWRITE_TAC [Once (prove(``m = ((2:num)*m) DIV 2``, FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.MULT_DIV, Once arithmeticTheory.MULT_COMM]))])
        THEN  (ASSUME_TAC (prove(``EVEN (2*m)``, PROVE_TAC [arithmeticTheory.EVEN_EXISTS])))
        THEN  (FULL_SIMP_TAC (srw_ss()) [SPEC ``2*m:num`` EVEN_DIV_EQ_SUC])
        THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ADD1, arithmeticTheory.EXP2_LT])
    ]

);

val ODDSUC_DIV2_EQ_SUC = store_thm("ODDSUC_DIV2_EQ_SUC"
  , ``∀ (n:num). (ODD (SUC n)) = (n DIV 2 = (SUC n) DIV 2)``
  , (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD, GSYM arithmeticTheory.EVEN_ODD, EVEN_DIV_EQ_SUC])
);

val ODD_DIV2_EQ_PREC = store_thm("ODD_DIV2_EQ_PREC"
  , ``∀ (n:num). 0 < n ==> ((ODD n) = (n DIV 2 = (n - 1) DIV 2))``
  ,       (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC ((UNDISCH_ALL o SPEC_ALL) PREC_EXISTS))
    THEN  (FULL_SIMP_TAC (srw_ss()) [])
    THEN  (ASSUME_TAC ((UNDISCH_ALL o (SPEC ``m:num``)) ODDSUC_DIV2_EQ_SUC))
    THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD1])
    THEN  (RW_TAC (arith_ss) [ODDSUC_DIV2_EQ_SUC])
);

val EVEN_ODD_MIX_DIV2 = prove(
    ``∀ (j:num) (k:num). (EVEN j ≠ EVEN k) ==> ((j + k - 1) DIV 2 = (j + k) DIV 2)``
  ,       (REPEAT STRIP_TAC)
    THEN  (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EVEN_ODD, GSYM arithmeticTheory.ODD_ADD, GSYM ODD_DIV2_EQ_PREC, ODD_POS])
);

val SUM_LT_2EXP = store_thm("SUM_LT_2EXP"
  , ``∀ (n:num) (j:num) (k:num). (j + k < 2**n) ==> (j < 2**n)``
  , (RW_TAC (arith_ss) [])
);

(*
    Lemmas/Theorems dependency:

     EVENS_DIV2_ADD
     ODDS_DIV2_ADD
     SUB2_DIV2_DIV2_SUB1
     ODD_SUM_GT1
     GT1_DIV2_GT0
     EVEN_ODD_MIX_DIV2_ADD
*)
val SUM_2EXP_EQ = store_thm("SUM_2EXP_EQ"
  , ``∀ (n:num) (j:num) (k:num). (j + k < 2**(SUC n)) = ((j DIV 2) + (k DIV 2) + (j MOD 2) * (k MOD 2) < 2**n)``
  ,       (REPEAT STRIP_TAC)
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
(* ---- *)

val SUM_CONST_LT_2EXP = store_thm("SUM_CONST_LT_2EXP"
  , ``∀ (n:num) (j:num) (k:num) (c:num). (j < 2**n) ∧ (k < 2**n) ==> (c < 2 ==> ((j + k + c < 2**(SUC n))))``
  , (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ADD1, arithmeticTheory.EXP_ADD])
);

val RIGHT_SHIFT_SUM_LT_2EXP = store_thm("RIGHT_SHIFT_SUM_LT_2EXP"
  , ``∀ (n:num) (j:num) (k:num). (j < 2**(SUC n)) ∧ (k < 2**(SUC n)) ==> ((j DIV 2 + k DIV 2 + 1 < 2**(SUC n)) ∧ (j DIV 2 + k DIV 2 < 2**(SUC n)))``
  ,       (RW_TAC (pure_ss) [])
    THENL [
            (ASSUME_TAC (SPECL [``n:num``, ``j DIV 2``, ``k DIV 2``, ``1:num``] SUM_CONST_LT_2EXP))
      THEN  (RW_TAC (srw_ss()) [(fst o EQ_IMP_RULE o SPEC_ALL) (GSYM arithmeticTheory.EXP2_LT)])
    ,       (ASSUME_TAC (SPECL [``n:num``, ``j DIV 2``, ``k DIV 2``, ``0:num``] SUM_CONST_LT_2EXP))
      THEN  (FULL_SIMP_TAC (arith_ss) [(fst o EQ_IMP_RULE o SPEC_ALL) (GSYM arithmeticTheory.EXP2_LT)])
    ]
);

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

val MOD_2EXP_EQ = store_thm("MOD_2EXP_EQ"
  , ``∀ (n :num) (j :num). j MOD 2**(SUC n) = 2 * ((j DIV 2) MOD 2**n) + j MOD 2``
  ,       (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ADD1, arithmeticTheory.EXP_ADD, arithmeticTheory.DIV_MOD_MOD_DIV])
    THEN  (REWRITE_TAC [Once ((SIMP_RULE arith_ss [] o SPECL [``2:num``, ``j MOD ((2 :num) * (2 :num) ** n)``] o (SIMP_RULE (pure_ss) [arithmeticTheory.MULT_COMM]) o GEN_ALL o DISCH_ALL o CONJUNCT1 o SPEC_ALL o UNDISCH_ALL o SPEC_ALL) arithmeticTheory.DIVISION)])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_MULT_MOD])
);

val ADD_DIV2_DIV2_ADD_MULT_MOD2 = store_thm("ADD_DIV2_DIV2_ADD_MULT_MOD2"
  , ``∀ (j:num) (k:num). (j + k) DIV 2 = j DIV 2 + k DIV 2 + j MOD 2 * k MOD 2``
  ,       (REPEAT STRIP_TAC)
    THEN  (Cases_on `EVEN j`)
    THENL [
              (Cases_on `EVEN k`)
        THEN  (FULL_SIMP_TAC (srw_ss()) [EVENS_DIV2_ADD, ODDS_DIV2_ADD, EVEN_ODD_MIX_DIV2_ADD, EVEN_ODD_MIX_DIV2, arithmeticTheory.EVEN_MOD2])
      ,       (Cases_on `EVEN k`)
        THENL [
            (FULL_SIMP_TAC (srw_ss()) [EVENS_DIV2_ADD, ODDS_DIV2_ADD, EVEN_ODD_MIX_DIV2_ADD, EVEN_ODD_MIX_DIV2, arithmeticTheory.EVEN_MOD2])
          ,       (`0 < j` by FULL_SIMP_TAC (arith_ss) [ODD_POS, arithmeticTheory.EVEN_ODD])
            THEN  (`0 < k` by FULL_SIMP_TAC (arith_ss) [ODD_POS, arithmeticTheory.EVEN_ODD])
            THEN  (`1 ≤ (j + k) DIV 2` by FULL_SIMP_TAC (arith_ss) [ODD_POS, ODD_POS, GT1_DIV2_GE1])
            THEN  (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EVEN_ODD, ODDS_DIV2_ADD_ALT, ODD_MOD2, (SPECL [``(j + k) DIV 2``, ``1:num``] o GSYM) ADD_SUB_COMM])
        ]
    ]
);

val ADD_MOD2_XOR = store_thm("ADD_MOD2_XOR"
  , ``∀ (j:num) (k:num). (j + k) MOD 2 = if (j MOD 2) = (k MOD 2) then 0 else 1``
  ,       (REPEAT STRIP_TAC)
    THEN  (Cases_on `EVEN j`)
    THEN  (
            (Cases_on `EVEN k`)
      THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2, ODD_MOD2, GSYM arithmeticTheory.ODD_EVEN, Once (GSYM arithmeticTheory.MOD_PLUS)])
    )
);

val PLUS_MOD_2EXP_EQ = store_thm("PLUS_MOD_2EXP_EQ"
  , ``∀ (n :num) (j :num) (k :num). (j + k) MOD 2**(SUC n) = 2 * ((j DIV 2 + k DIV 2 + (j MOD 2)*(k MOD 2)) MOD 2**n) + (j MOD 2 + k MOD 2) MOD 2``
  , (FULL_SIMP_TAC (arith_ss) [MOD_2EXP_EQ, ADD_DIV2_DIV2_ADD_MULT_MOD2, ADD_MOD2_XOR])
);

val MULT_DIV_LE = store_thm("MULT_DIV_LE"
  , ``∀ (n:num) (j:num). (0 < n) ==> (n * (j DIV n) <= j)``
  , (REPEAT STRIP_TAC) THEN (ASSUME_TAC ((SPEC ``j:num`` o UNDISCH_ALL o SPECX) arithmeticTheory.DIVISION)) THEN (RW_TAC (arith_ss) [])
);

val extract_v2w_alt = store_thm("extract_v2w_alt"
  , ``∀ (h :num) (l :num) (w :α word). (dimindex (:β) = SUC h − l) ==> dimindex (:β) < dimindex (:α) ==> (((h >< l) w :β word) = (v2w (field h l (w2v w)) :β word))``
  , (RW_TAC (srw_ss()) [GSYM bitstringTheory.extract_v2w])
);

val bits_v2w = store_thm("bits_v2w"
  , ``∀ (h :num) (l :num) (w :α word). ((h -- l) w = (v2w (field h l (w2v w)) :α word))``
  ,       (REPEAT GEN_TAC)
    THEN  (ASSUME_TAC (SPEC_ALL (prove (``∀ (w :α word). ∃ (v :bitstring). (w = v2w v)``, (PROVE_TAC [bitstringTheory.v2w_w2v])))))
    THEN  (FULL_SIMP_TAC (srw_ss()) [bitstringTheory.word_bits_v2w, bitstringTheory.w2v_v2w])
);

val extract_v2w_alt = store_thm("extract_v2w_alt"
  , ``∀ (h :num) (l :num) (w :α word). (dimindex (:β) = SUC h − l) ==> dimindex (:β) < dimindex (:α) ==> (((h >< l) w :β word) = (v2w (field h l (w2v w)) :β word))``
  , (RW_TAC (srw_ss()) [GSYM bitstringTheory.extract_v2w])
);

val bits_v2w = store_thm("bits_v2w"
  , ``∀ (h :num) (l :num) (w :α word). ((h -- l) w = (v2w (field h l (w2v w)) :α word))``
  ,       (REPEAT GEN_TAC)
    THEN  (ASSUME_TAC (SPEC_ALL (prove (``∀ (w :α word). ∃ (v :bitstring). (w = v2w v)``, (PROVE_TAC [bitstringTheory.v2w_w2v])))))
    THEN  (FULL_SIMP_TAC (srw_ss()) [bitstringTheory.word_bits_v2w, bitstringTheory.w2v_v2w])
);

val word_lsl_v2w_alt = store_thm("word_lsl_v2w_alt"
  , ``∀ (w :α word) (n :num). w << n = v2w (shiftl (w2v w) n)``
  ,       (REWRITE_TAC [Once (prove(``w << n = (v2w (w2v w) << n)``, (RW_TAC (srw_ss()) [])))])
    THEN  (FULL_SIMP_TAC (srw_ss()) [bitstringTheory.word_lsl_v2w])
);

val shiftl_0 = store_thm("shiftl_0"
  , ``∀v. shiftl v 0 = v``
  , EVAL_TAC THEN (FULL_SIMP_TAC (srw_ss()) [])
);

val MIN_SUB_EQ = store_thm("MIN_SUB_EQ"
  , ``∀ (n :num) (m :num). MIN n (n - m) = (n - m)``
  ,       (RW_TAC (arith_ss) [arithmeticTheory.MIN_DEF])
    THEN  (CCONTR_TAC)
    THEN  (RW_TAC (arith_ss) [arithmeticTheory.MIN_DEF])
);

val DROP_GENLIST = store_thm("DROP_GENLIST"
  , ``∀n m f. (DROP m (GENLIST f (n + m)) = GENLIST (λt. f (t + m)) n)``
  ,       (Induct_on `m`)
    THEN  (EVAL_TAC THEN (SIMP_TAC (arith_ss) []))
    THEN  (RW_TAC (srw_ss()++ARITH_ss) [arithmeticTheory.ADD1, listTheory.GENLIST_APPEND, arithmeticTheory.LESS_EQ_SUB_LESS])
    THEN  (REWRITE_TAC [prove(``t + 1 = 1 + t:num``, SIMP_TAC (arith_ss) [arithmeticTheory.ADD_COMM])])
    THEN  (SIMP_TAC (pure_ss) [listTheory.GENLIST_APPEND, arithmeticTheory.ADD_ASSOC])
    THEN  (REWRITE_TAC [((ISPEC ``(+) 1 :num -> num``) o (GEN ``g:α -> γ``) o GSYM) combinTheory.o_ABS_R])
    THEN  (REWRITE_TAC [((ISPEC ``(+) (m + 1) :num -> num``) o (GEN ``g:α -> γ``) o GSYM) combinTheory.o_ABS_R])
    THEN  (REWRITE_TAC [prove(``(\x. 1 + (x:num)) = SUC``, EVAL_TAC THEN (FULL_SIMP_TAC (arith_ss) [FUN_EQ_CONV ``(+) (1:num) = SUC``]))])
    THEN  (REWRITE_TAC [prove(``(\x. n + 1 + (x:num)) = SUC o (\x. n + (x:num))``, EVAL_TAC THEN (FULL_SIMP_TAC (arith_ss) [FUN_EQ_CONV ``(+) (n + (1:num)) = SUC o ((+) n)``]))])
    THEN  (REWRITE_TAC [prove(``(\x. m + x) = (\x. x + (m:num))``, SIMP_TAC (arith_ss) [arithmeticTheory.ADD_COMM])])
    THEN  (SIMP_TAC (pure_ss) [combinTheory.o_ASSOC, combinTheory.o_ABS_R, (SPECL [``f o SUC``] o GSYM) listTheory.GENLIST_APPEND])
    THEN  (REWRITE_TAC [(SPEC ``f o SUC`` o SPECX o ASSUME) ``∀n f. DROP m (GENLIST f (n + m)) = GENLIST (λt. f (t + m)) n``])
);

val DROP_GENLIST_alt = store_thm("DROP_GENLIST_alt"
  , ``∀ n m f. DROP m (GENLIST f n) = GENLIST (λt. f (t + m)) (n − m)``
  ,       (REPEAT STRIP_TAC)
    THEN  (Cases_on `m <= n:num`)
    THENL [
              (REWRITE_TAC [Once ((UNDISCH_ALL o GSYM o SPECL [``n:num``, ``m:num``]) arithmeticTheory.SUB_ADD)]) 
        THEN  (FULL_SIMP_TAC (arith_ss) [(SPECL [``n - m:num``, ``m:num``, ``f:num -> 'a``]) DROP_GENLIST])
      ,
              (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [listTheory.LENGTH_GENLIST, listTheory.DROP_LENGTH_TOO_LONG, arithmeticTheory.NOT_LESS_EQUAL])
        THEN  (ASSUME_TAC (UNDISCH_ALL (SIMP_RULE (bool_ss) [] (SIMP_CONV (arith_ss) [] ``(n:num) < m ==> n <= m``))))
        THEN  (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [(UNDISCH_ALL o snd o EQ_IMP_RULE o SPECL [``n:num``, ``m:num``]) arithmeticTheory.SUB_EQ_0])
    ]
);

val DROP_SUC = store_thm("DROP_SUC"
  , ``∀ n l. DROP (SUC n) l = DROP n (DROP 1 l)``
  ,       (Induct_on `l`)
    THEN  (SIMP_TAC (arith_ss) [listTheory.DROP_def])
    THEN  (RW_TAC (arith_ss) [listTheory.DROP_0, listTheory.DROP_def])
);

val DROP_COMM1 = store_thm("DROP_COMM1"
  , ``∀ n l. DROP n (DROP 1 l) = DROP 1 (DROP n l)``
  ,       (Induct_on `l`)
    THEN  (SIMP_TAC (arith_ss) [listTheory.DROP_def])
    THEN  (RW_TAC (srw_ss()) [listTheory.DROP_0, listTheory.DROP_def])
    THEN  (Induct_on `n`)
    THEN  (SIMP_TAC (arith_ss) [listTheory.DROP_def])
    THEN  (RW_TAC (arith_ss) [DROP_SUC])
);

val DROP_COMM = store_thm("DROP_COMM"
  , ``∀ a b l. DROP b (DROP a l) = DROP a (DROP b l)``
  ,       (Induct_on `a`)
    THEN  (RW_TAC (arith_ss) [listTheory.DROP_0])
    THEN  (Induct_on `b`)
    THEN  (RW_TAC (arith_ss) [listTheory.DROP_0])
    THEN  (RW_TAC (pure_ss) [DROP_SUC])
    THEN  (REWRITE_TAC [Once DROP_COMM1])
);

val DROP_ADD = store_thm("DROP_ADD"
  , ``∀ a b l. DROP a (DROP b l) = DROP (a + b) l``
  ,       (Induct_on `l`)
    THEN  (SIMP_TAC (arith_ss) [listTheory.DROP_def])
    THEN  (RW_TAC (arith_ss) [listTheory.DROP_def])
    THEN  (Induct_on `a`)
    THEN  (RW_TAC (arith_ss) [listTheory.DROP_0])
    THEN  (Induct_on `b`)
    THEN  (RW_TAC (arith_ss) [listTheory.DROP_0])
    THEN  (RW_TAC (arith_ss) [DROP_SUC, arithmeticTheory.ADD1])
    THEN  (REWRITE_TAC [Once DROP_COMM1])
);

val DROP_SUB = store_thm("DROP_SUB"
  , ``∀ n m l. m ≤ n ⇒ (DROP n l = DROP (n - m) (DROP m l))``
  , (FULL_SIMP_TAC (arith_ss) [DROP_ADD])
);

val DROP1_CONS = store_thm("DROP1_CONS"
  , ``∀l. LENGTH l > 1 ==> ∃h t. DROP 1 l = h::t``
  ,       (REPEAT STRIP_TAC)
    THEN  ((Cases_on `l`) THEN (FULL_SIMP_TAC (arith_ss) [listTheory.LENGTH]))
    THEN  (Cases_on `LENGTH t > 0`)
    THEN  (FULL_SIMP_TAC (arith_ss) [listTheory.LENGTH, listTheory.DROP_def, listTheory.DROP_0])
    THEN  ((Cases_on `t`) THEN (FULL_SIMP_TAC (arith_ss) [listTheory.LENGTH, listTheory.CONS_11]))
    THEN  (FULL_SIMP_TAC (arith_ss) [listTheory.LENGTH])
);

val LENGTH_CONS = store_thm("LENGTH_CONS"
  , ``∀l. LENGTH l > 0 ==> ∃h t. l = h::t``
  , ((Cases_on `l`) THEN (FULL_SIMP_TAC (arith_ss) [listTheory.LENGTH, listTheory.CONS_11]))
);

val GREATER_MONO_ADD_EQ = store_thm("GREATER_MONO_ADD_EQ"
  , ``∀ (m:num) n p. (m + p > n + p) = (m > n)``
  , (numLib.ARITH_TAC)
);

val DROP_LENGTH_LONG_ENOUGH = store_thm("DROP_LENGTH_LONG_ENOUGH"
  , ``∀l n. LENGTH l > n ==> LENGTH (DROP n l) > 0``
  , (FULL_SIMP_TAC (srw_ss()) [])
);

val LENGTH_DROP = store_thm("LENGTH_DROP"
  , ``∀l n. LENGTH (DROP n l) = LENGTH l - n``
  , (FULL_SIMP_TAC (srw_ss()) [])
);

val LENGTH_DROP_CONS = store_thm("LENGTH_DROP_CONS"
  , ``∀l n. LENGTH l > n ⇒ ∃h t. DROP n l = h::t``
  , (FULL_SIMP_TAC (srw_ss()) [LENGTH_CONS])
);

val DROP1_APPEND = store_thm("DROP1_APPEND"
  , ``∀l k. (LENGTH l >= 1) ==> (DROP 1 l ++ k = DROP 1 (l ++ k))``
  , ((Cases_on `l`) THEN (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [listTheory.LENGTH, listTheory.DROP_0, listTheory.DROP_def]))
);

val DROP_APPEND = store_thm("DROP_APPEND"
  , ``∀l k n. (LENGTH l >= n) ==> (DROP n l ++ k = DROP n (l ++ k))``
  , ((Induct_on `n`) THEN (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [arithmeticTheory.ADD1, GSYM DROP_ADD, DROP1_APPEND]))
);

val DROP_APPEND_SHORT = store_thm("DROP_APPEND_SHORT"
  , ``∀l k n. (LENGTH l <= n) ==> (DROP n (l ++ k) = DROP (n - LENGTH l) k)``
  ,       (Induct_on `n`)
    THEN  (
              (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [arithmeticTheory.ADD1, Once arithmeticTheory.ADD_COMM, DROP1_APPEND])
        THEN  ((Induct_on `l`) THEN (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [arithmeticTheory.SUC_NOT]))
      )
    THEN  (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [arithmeticTheory.ADD1, Once arithmeticTheory.ADD_COMM, DROP1_APPEND])
    THEN  (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC (SIMP_RULE arith_ss [listTheory.DROP_LENGTH_TOO_LONG] ((UNDISCH_ALL o (SPECL [``n + 1 :num``, ``LENGTH l``, ``l ++ k``])) DROP_SUB)))
    THEN  (ASSUME_TAC ((SIMP_RULE (arith_ss) [] o SPECL [``l :'a list``, ``k :'a list``, ``LENGTH l``] o GSYM) DROP_APPEND))
    THEN  (FULL_SIMP_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (arith_ss) [listTheory.DROP_LENGTH_TOO_LONG, listTheory.APPEND])
);

val v2w_shiftl_fixwidth = store_thm("v2w_shiftl_fixwidth"
  , ``∀(w:bool['a]) m n. (m = word_len w) ==> (v2w (shiftl (fixwidth (SUC (m - n - 1)) (w2v w)) n) :bool['a] = v2w (shiftl (w2v w) n) :bool['a])``
  ,       (REPEAT STRIP_TAC)
    THEN  EVAL_TAC
    THEN  ((Cases_on `n < dimindex(:'a)`) THEN (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [arithmeticTheory.ADD1, DROP_APPEND, listTheory.APPEND, listTheory.LENGTH, listTheory.DROP_def]))
    THEN  (ASSUME_TAC (UNDISCH_ALL (prove(``¬((n:num) < dimindex(:'a)) ==> (dimindex(:'a) - (n + 1) + 1 = 1)``, numLib.ARITH_TAC))))
    THEN  (ASSUME_TAC (prove(``1 - dimindex(:'a) = 0``, (ASSUME_TAC ((fst o EQ_IMP_RULE o SPECL [``0:num``, ``dimindex(:'a)``]) arithmeticTheory.LESS_EQ)) THEN (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD1]) THEN (FULL_SIMP_TAC (srw_ss()) []))))
    THEN  (FULL_SIMP_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [DROP_ADD, DROP_APPEND])
);

val fixwidth_fixwidth_alt = store_thm("fixwidth_fixwidth_alt"
  , ``∀n m v. (m ≤ n) ==> (fixwidth m (fixwidth n v) = fixwidth m v)``
  ,      (REPEAT STRIP_TAC)
    THEN  (FULL_SIMP_TAC (srw_ss()) [bitstringTheory.fixwidth_def, LET_DEF])
    THEN  (RW_TAC (arith_ss) [])
    THENL [
              (* 1/4 *)
              (REPEATN (2, EVAL_TAC THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM bitstringTheory.extend, bitstringTheory.zero_extend_def, bitstringTheory.sign_extend_def]))
        THEN  (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM DROP_APPEND, DROP_GENLIST_alt, combinTheory.K_DEF])

              (* 2/4 *)
      ,       (REPEATN (2, EVAL_TAC
        THEN SIMP_TAC (srw_ss()++ARITH_ss) [GSYM bitstringTheory.extend, bitstringTheory.zero_extend_def, bitstringTheory.sign_extend_def]))
        THEN  (ASSUME_TAC ((UNDISCH_ALL o SPECL [``LENGTH (v :bitstring)``, ``n:num``]) arithmeticTheory.LESS_IMP_LESS_OR_EQ))
        THEN  (ASSUME_TAC ((UNDISCH_ALL o SIMP_RULE bool_ss [] o SIMP_CONV arith_ss []) ``LENGTH (v:bitstring) < n ==> ¬(LENGTH v < m) ==> (n <= LENGTH v + (n - m))``))
        THEN  (ASSUME_TAC ((UNDISCH_ALL o SIMP_RULE (arith_ss) [listTheory.LENGTH_GENLIST] o ISPECL [``(GENLIST (K F) (n − LENGTH (v:bitstring)))``, ``v:bitstring``, ``n - m :num``]) DROP_APPEND_SHORT))
        THEN  (FULL_SIMP_TAC (arith_ss) [])

              (* 3/4 *)
      ,       (REPEATN (2, EVAL_TAC
      THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM bitstringTheory.extend, bitstringTheory.zero_extend_def, bitstringTheory.sign_extend_def]))

              (* 4/4 *)
      ,       (FULL_SIMP_TAC (srw_ss()++ARITH_ss) [DROP_ADD])
    ]
);


(* ------------------------------------------------------------------------- *)
val _ = export_theory();
 
