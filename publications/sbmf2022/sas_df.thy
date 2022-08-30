theory sas_df
imports "sas_analysis"
        "CSP_F.CSP_F_law_step_aux"
        "DFP_DFfive"
begin


overloading Set_FPmode == 
  "CSP_syntax.FPmode :: fpmode"
begin
  definition "CSP_syntax.FPmode == CMSmode"
end
declare Set_FPmode_def [simp add]



declare inj_def [simp add]
declare Let_def [simp add]

declare Rec_prefix_def [simp add]
declare Send_prefix_def [simp add]

fun DFfive_to_ACE_PCUadj :: "ActuatorId \<Rightarrow> DFfivePN \<Rightarrow> (PN, Events) proc"
where
    "DFfive_to_ACE_PCUadj i (DFfive) =
           (!<adjust i> adj .. !<rawPosition i> p0 ..
             $ACE i
             |[ {| servoCmd i, feedbackPos i |}\<^sub>c ]|
             PCUadj i p0 adj)"


lemma Lemma_DFfive_to_ACE_PCUadj :
    "(DFfivefun p) << (DFfive_to_ACE_PCUadj i) <=F DFfive_to_ACE_PCUadj i p"
  apply (induct_tac p)
  apply (auto)

  (* Expand RIGHT *)
  apply (rule cspF_rw_right, rule unwind_ACE_PCUadj)
  apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
    apply (rule cspF_reflex, rule cspF_reflex, simp)
    apply (cspF_simp_right)

  (* STEP - controlCmd OR adjust is the 1\<ordmasculine> event *)
  apply (rule cspF_Ext_choice_right)
  
    (* REFINED - controlCmd is the 1\<ordmasculine> event *)
    apply (cspF_step_left)
    apply (rule cspF_decompo_ref, simp, simp)
    apply (erule rangeE, simp)

      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex, rule cspF_reflex, simp)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
  
      (* REFINED - adjust is the 2\<ordmasculine> event *)
      apply (cspF_step_left)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)
  
      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
            apply (rule unwind_EHSV)
            apply (rule cspF_rw_left, rule unwind_Raw)
            apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
            apply (simp)
            apply (cspF_simp_left)
            apply (cspF_simp_left)
          apply (rule unwind_LVDT)
          apply (simp)
          apply (cspF_simp_left)
          apply (cspF_simp_left)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
    
      (* REFINED - rawPosition is the 3\<ordmasculine> event *)
      apply (cspF_step_left)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)
  
      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex, simp)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex, cspF_simp_left)
          apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
          apply (simp)
          apply (cspF_simp_left)
          apply (cspF_simp_left)
        apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
        apply (simp)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
  
      (* REFINED - feedbackPos is the 5\<ordmasculine> event *)
      apply (cspF_step_left)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)
  
      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex)
        apply (cspF_simp_left)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex, rule unwind_LVDT, simp)
          apply (cspF_simp_left)
          apply (cspF_simp_left)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
  
      (* REFINED - servoCmd is the 6\<ordmasculine> event *)
      apply (cspF_step_left)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)
  
      apply (rule cspF_Rep_int_choice_left, simp)
      apply (rule_tac x="(saturate (aa + a) - disp (dOmega (saturate (x - saturate (aa + a)))))" in exI, simp)
      apply (rule cspF_Rep_int_choice_left, simp)
      apply (rule_tac x="(saturate (aa + a))" in exI, simp)
  
      apply (rule cspF_decompo, simp, simp)
  
      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex, rule cspF_reflex, simp)
          apply (cspF_simp_left)
          apply (cspF_simp_left)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
  
      apply (simp add: PCUadj_def)
      apply (rule cspF_decompo, simp, simp)
      apply (rule cspF_decompo, simp)
      apply (rule cspF_decompo, simp, simp)
      apply (rule cspF_rw_right, rule cspF_IF, simp)
      apply (rule cspF_eq_ref, rule unwind_LVDT)

    (* REFINED - adjust is the 1\<ordmasculine> event *)
    apply (cspF_step_left)
    apply (rule cspF_decompo_ref, simp, simp)
    apply (simp)

      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule unwind_EHSV)
          apply (rule cspF_rw_left, rule unwind_Raw)
          apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
          apply (simp)
          apply (cspF_simp_left)
          apply (cspF_simp_left)
        apply (rule unwind_LVDT)
        apply (simp)
        apply (cspF_simp_left)
        apply (cspF_simp_left)
      apply (cspF_simp_right)
  
      (* STEP - controlCmd OR rawPosition is the 2\<ordmasculine> event *)
      apply (rule cspF_Ext_choice_right)
  
      (* REFINED - controlCmd is the 2\<ordmasculine> event *)
      apply (cspF_step_left)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (erule rangeE, simp)

        (* Expand RIGHT *)
        apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex, rule cspF_reflex, simp)
        apply (cspF_simp_right)
        apply (cspF_simp_right)

        (* REFINED - rawPosition is the 3\<ordmasculine> event *)
        apply (cspF_step_left)
        apply (rule cspF_decompo_ref, simp, simp)
        apply (simp)

        (* Expand RIGHT *)
        apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex)
          apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
            apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
            apply (rule cspF_reflex, cspF_simp_left)
            apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
            apply (simp)
              apply (cspF_simp_left)
              apply (cspF_simp_left)
          apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
          apply (simp)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
    
        (* REFINED - feedbackPos is the 4\<ordmasculine> event *)
        apply (cspF_step_left)
        apply (rule cspF_decompo_ref, simp, simp)
        apply (simp)
    
        (* Expand RIGHT *)
        apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex, cspF_simp_left)
          apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex, rule unwind_LVDT, simp)
          apply (cspF_simp_left)
          apply (cspF_simp_left)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
    
        (* REFINED - servoCmd is the 5\<ordmasculine> event *)
        apply (cspF_step_left)
        apply (rule cspF_decompo_ref, simp, simp)
        apply (simp)

        apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule_tac x="saturate (aa + a) - disp (dOmega (saturate (x - saturate (aa + a))))" in exI, simp)
        apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule_tac x="(saturate (aa + a))" in exI, simp)
    
        apply (rule cspF_decompo, simp, simp)
    
        (* Expand RIGHT *)
        apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
          apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
            apply (rule cspF_reflex, rule cspF_reflex, simp)
            apply (cspF_simp_left)
            apply (cspF_simp_left)
          apply (cspF_simp_right)
          apply (cspF_simp_right)
  
        (* REFINED *)
        apply (simp add: PCUadj_def)
        apply (rule cspF_decompo, simp, simp)
        apply (rule cspF_decompo, simp)
        apply (rule cspF_decompo, simp, simp)
        apply (rule cspF_rw_right, rule cspF_IF, simp)
        apply (rule cspF_eq_ref, rule unwind_LVDT)

      (* REFINED - rawPosition is the 2\<ordmasculine> event *)
      apply (cspF_step_left)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)

        (* Expand RIGHT *)
        apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex)
          apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
            apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
            apply (rule cspF_reflex)
            apply (cspF_simp_left)
            apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
            apply (simp)
            apply (cspF_simp_left)
            apply (cspF_simp_left)
          apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
          apply (simp)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
    
        (* REFINED - controlCmd is the 3\<ordmasculine> event *)
        apply (cspF_step_left)
        apply (rule cspF_decompo_ref, simp, simp)
        apply (erule rangeE, simp)
  
        (* Expand RIGHT *)
        apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex, rule cspF_reflex, simp)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
    
        (* REFINED - feedbackPos is the 4\<ordmasculine> event *)
        apply (cspF_step_left)
        apply (rule cspF_decompo_ref, simp, simp)
        apply (simp)
    
        (* Expand RIGHT *)
        apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex)
        apply (rule cspF_rw_left, rule cspF_IF)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex)
        apply (rule unwind_LVDT)
        apply (simp)
        apply (cspF_simp_left)
        apply (cspF_simp_left)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
    
        (* REFINED - servoCmd is the 5\<ordmasculine> event *)
        apply (cspF_step_left)
        apply (rule cspF_decompo_ref, simp, simp)
        apply (simp)
    
        apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule_tac x="(saturate (aa + a) - disp (dOmega (saturate (x - saturate (aa + a)))))" in exI, simp)
        apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule_tac x="(saturate (aa + a))" in exI, simp)
    
        apply (rule cspF_decompo, simp, simp)
    
        (* Expand RIGHT *)
        apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex)
        apply (rule cspF_reflex)
        apply (simp)
        apply (rule cspF_rw_left, rule cspF_Ext_choice_unit_r_hsf)
        apply (rule cspF_rw_left, rule cspF_Ext_choice_unit_r_hsf)
        apply (rule cspF_reflex)
        apply (rule cspF_reflex)
        apply (simp)
        apply (cspF_simp_right)
        apply (cspF_simp_right)
  
        (* REFINED *)
        apply (simp add: PCUadj_def)
        apply (rule cspF_decompo, simp, simp)
        apply (rule cspF_decompo, simp)
        apply (rule cspF_decompo, simp, simp)
        apply (rule cspF_rw_right, rule cspF_IF, simp)
        apply (rule cspF_eq_ref, rule unwind_LVDT)
done



lemma DFtick_ACE_PCUadj : "$DFtick <=F ((ACE_PCUadj i p adj)::(PN,Events) proc)"
  apply (rule cspF_trans, rule DFtick_DFfive)
  apply (rule_tac Pf="DFfivefun" and f="DFfive_to_ACE_PCUadj i" in cspF_fp_induct_ref_left)
  apply (simp, simp, simp, simp)
  apply (rule cspF_Rep_int_choice_left, simp)
    apply (rule_tac  x="adj" in exI, simp)
  apply (rule cspF_Rep_int_choice_left, simp)
    apply (rule_tac  x="p" in exI, simp)
  apply (simp add: ACE_PCUadj_def)
  by (rule Lemma_DFfive_to_ACE_PCUadj)



lemma DF_ACE_PCU : "$DFtick <=F ((ACE_PCU i p)::(PN,Events) proc)"
  (* Expand RIGHT *)
  apply (rule cspF_rw_right, rule unwind_ACE_PCU)
    apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
      apply (rule cspF_reflex)
      (* PCU = ( EHSV |[ ... ]| Raw ) |[ ... ]| LVDT *)
      apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
       apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex)
        apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
        apply (simp)
       apply (cspF_simp_left)
        apply (cspF_simp_left)
        apply (cspF_simp_left)
        apply (cspF_simp_right)
    apply (rule cspF_rw_right, rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)

    (* 1\<ordmasculine> STEP IS REFINED - rawPosition OR controlCmd is the first event*)
    apply (cspF_unwind_left, cspF_step_left, rule cspF_Int_choice_left1)
    apply (rule cspF_decompo_ref, simp, simp)
    apply (clarsimp, erule disjE)

    (* rawPosition is the first event *)
    apply (simp)
    apply (cspF_simp_right)
    apply (cspF_simp_right)

      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex)
          apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
          apply (simp)
        apply (cspF_simp_left)
        apply (cspF_simp_left)
      apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
      apply (simp)
      apply (cspF_simp_right)
      apply (cspF_simp_right)

      (* 2\<ordmasculine> STEP IS REFINED - controlCmd is the second event *)
      apply (cspF_unwind_left, cspF_step_left, rule cspF_Int_choice_left1)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (erule rangeE, simp)
  
      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex, rule cspF_reflex, simp)
      apply (cspF_simp_right)
      apply (cspF_simp_right)
  
      (* 3\<ordmasculine> STEP IS REFINED - feedbackPos is the third event *)
      apply (cspF_unwind_left, cspF_step_left, rule cspF_Int_choice_left1)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)

      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex, cspF_simp_left)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex, rule unwind_LVDT, simp)
        apply (cspF_simp_left)
        apply (cspF_simp_left)
      apply (cspF_simp_right)
      apply (cspF_simp_right)
  
      (* 4\<ordmasculine> STEP IS REFINED - servoCmd is the fourth event *)
      apply (cspF_unwind_left, cspF_step_left, rule cspF_Int_choice_left1)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)

      (* REFINED BY TRANS DFtick_ACE_PCUadj *)
      apply (rule cspF_trans)
      apply (rule_tac i="i" and p="p" and adj="(p - disp (dOmega (saturate (x - p))))" in DFtick_ACE_PCUadj)
      apply (simp add: ACE_PCUadj_def)
      apply (rule cspF_decompo, simp, simp)
      apply (simp add: PCUadj_def)

      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
      apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
       apply (rule cspF_reflex, rule cspF_reflex, simp)
        apply (cspF_simp_left)
        apply (cspF_simp_left)
      apply (cspF_simp_right)
      apply (cspF_simp_right)

      (* REFINED BY DECOMPO *)
      apply (rule cspF_decompo, simp, simp)
      apply (rule cspF_decompo, simp)
      apply (rule cspF_decompo, simp, simp)
      apply (cspF_simp_right)
      apply (rule cspF_eq_ref, rule unwind_LVDT)


    (* controlCmd is the first event *)
    apply (cspF_simp_right)
    apply (erule rangeE, simp)

      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
      apply (rule cspF_reflex, rule cspF_reflex, simp)
      apply (cspF_simp_right)
      apply (cspF_simp_right)

      (* 2\<ordmasculine> STEP IS REFINED - rawPosition is the second event *)
      apply (cspF_unwind_left, cspF_step_left, rule cspF_Int_choice_left1)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)
  
      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
          apply (rule cspF_reflex)
          apply (rule cspF_rw_left, rule cspF_IF)
            apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
          apply (simp)
        apply (cspF_simp_left)
        apply (cspF_simp_left)
        apply (rule cspF_Ext_choice_step_Ext_pre_choice_disjnt, simp add: disjnt_def)
        apply (simp)
      apply (cspF_simp_right)
      apply (cspF_simp_right)

      (* 3\<ordmasculine> STEP IS REFINED - feedbackPos is the third event *)
      apply (cspF_unwind_left, cspF_step_left, rule cspF_Int_choice_left1)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)

      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex, cspF_simp_left)
      apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
        apply (rule cspF_reflex, rule unwind_LVDT, simp)
      apply (cspF_simp_left)
      apply (cspF_simp_left)
      apply (cspF_simp_right)
      apply (cspF_simp_right)

      (* 4\<ordmasculine> STEP IS REFINED - servoCmd is the fourth event *)
      apply (cspF_unwind_left, cspF_step_left, rule cspF_Int_choice_left1)
      apply (rule cspF_decompo_ref, simp, simp)
      apply (simp)

      (* REFINED BY TRANS DFtick_ACE_PCUadj *)
      apply (rule cspF_trans)
      apply (rule_tac i="i" and p="p" and adj="(p - disp (dOmega (saturate (x - p))))" in DFtick_ACE_PCUadj)
      apply (simp add: ACE_PCUadj_def)
      apply (rule cspF_decompo, simp, simp)
      apply (simp add: PCUadj_def)

      (* Expand RIGHT *)
      apply (rule cspF_rw_right, rule cspF_Parallel_step_choice)
        apply (rule cspF_rw_left, rule cspF_Parallel_step_choice)
         apply (rule cspF_reflex, rule cspF_reflex, simp)
        apply (cspF_simp_left)
        apply (cspF_simp_left)
      apply (cspF_simp_right)
      apply (cspF_simp_right)

      (* REFINED BY DECOMPO *)
      apply (rule cspF_decompo, simp, simp)
      apply (rule cspF_decompo, simp)
      apply (rule cspF_decompo, simp, simp)
      apply (cspF_simp_right)
      apply (rule cspF_eq_ref, rule unwind_LVDT)
  done

lemma DF_ACE_PCU_isDeadlockFree : "((ACE_PCU i p)::(PN,Events) proc) isDeadlockFree"
  apply (simp only: DeadlockFree_DFtick_ref)
  by (rule DF_ACE_PCU)


theorem SimpleActuator_isDeadlockFree : "((SimpleActuator i)::(PN,Events) proc) isDeadlockFree"
  apply (simp only: SimpleActuator_def)
  by (rule DF_ACE_PCU_isDeadlockFree)



declare inj_def [simp del]
declare Let_def [simp del]

declare Rec_prefix_def [simp del]
declare Send_prefix_def [simp del]

end