theory DFP_DFfive
imports DFP.DFP_law_DFkev
begin



datatype DFfivePN = DFfive

primrec
  DFfivefun ::  "(DFfivePN, 'event) pnfun"
where
  "DFfivefun (DFfive) = (! x1 ->  ! x2 ->  ! x3 ->  ! x4 ->  ! x5 ->  $(DFfive)) "


overloading Set_DFfivefun == 
  "CSP_syntax.PNfun :: (DFfivePN, 'event) pnfun"
begin
  definition "CSP_syntax.PNfun :: (DFfivePN, 'event) pnfun == DFfivefun"
end
  
declare Set_DFfivefun_def [simp]


lemma guardedfun_DFfivefun [simp]: "guardedfun DFfivefun"
  apply (simp add: guardedfun_def)
  by (rule allI, induct_tac p, simp)



fun DF_IH :: "DFfivePN \<Rightarrow> (DFnonTickPN, 'e) proc"
where
    "DF_IH (DFfive) = $DFnonTick"

lemma Lemma_isMapping_procfun_DF_IH [simp]:
    "isMapping_procfun DF_IH"
  by (simp add: isMapping_procfun_def, auto, induct_tac x, simp_all)

lemma dfnt_DFfive :
    "$DFnonTick <=F $DFfive"
  apply (rule_tac Pf="DFfivefun" and f="DF_IH" in cspF_fp_induct_ref_right, simp_all)
  apply (induct_tac p, rule Lemma_fp_induct_refF_isMapping_procfun, simp_all, simp_all)
  apply (cspF_step, rule cspF_decompo, simp)+
  apply (cspF_unwind_left, cspF_step, rule cspF_decompo, simp)+
  by (cspF_unwind_left)

lemma DFtick_DFfive :
    "$DFtick <=F $DFfive"
  by (rule cspF_trans, rule dfp_DFnonTick, rule dfnt_DFfive)

lemma DFfive_isDeadlockFree:
    "(($DFfive) :: (DFfivePN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule DFtick_DFfive)




fun DFkev_IH :: "DFfivePN \<Rightarrow> (DFkevPN, 'e) proc"
where
    "DFkev_IH (DFfive) = $DFkev 5 5"

lemma Lemma_isMapping_procfun_DFkev_IH [simp]:
    "isMapping_procfun DFkev_IH"
  by (simp add: isMapping_procfun_def, auto, induct_tac x, simp_all)

lemma DFfive_eqF_KEv_5_5 :
    "FPmode = CMSmode \<or> FPmode = MIXmode \<Longrightarrow> $DFkev 5 5 =F $DFfive"
  apply (rule_tac Pf="DFfivefun" and f="DFkev_IH" in cspF_fp_induct_eq_right, simp_all)
  apply (induct_tac p, simp)
  by (rule cspF_rw_left, rule DFkev_5_5_unwind, cspF_simp)


end