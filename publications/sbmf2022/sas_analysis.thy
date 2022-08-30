theory sas_analysis
imports "sas" "DFP.DFP_law_DFtick"
begin



declare inj_def [simp add]
declare Let_def [simp add]

declare Rec_prefix_def [simp add]
declare Send_prefix_def [simp add]

lemma rawPosition_Int_adjust_eq_empty [simp]: "{| rawPosition i |}\<^sub>c \<inter> {| adjust i |}\<^sub>c = {}"
  by (auto)


lemma rawPosition_Int_servoCmd_eq_empty [simp]: "{| rawPosition i |}\<^sub>c \<inter> {| servoCmd i |}\<^sub>c = {}"
  by (auto)


lemma adjust_DONT_Renames_rawPosition [simp]: "a \<in> {| rawPosition i |}\<^sub>c \<Longrightarrow>
       {x::Events \<in> {| rawPosition i |}\<^sub>c.
                      (x, a) \<in> ehsvOutput i<==adjust i} = { a }"
  apply (simp add: Renaming2_channel_def Renaming2_channel_fun_def fun_to_rel_def Image_def)
  by (auto)


lemma adjust_DONT_Renames_servoCmd [simp]: "a \<in> {| servoCmd i |}\<^sub>c \<Longrightarrow>
       {x::Events \<in> {| servoCmd i |}\<^sub>c.
                      (x, a) \<in> ehsvOutput i<==adjust i} = { a }"
  apply (simp add: Renaming2_channel_def Renaming2_channel_fun_def fun_to_rel_def Image_def)
  by (auto)


lemma unwind_EHSV : "$EHSV i [[ ehsvOutput i <== adjust i ]] =F
            ? p:{| rawPosition(i) |}\<^sub>c -> ? e:{| servoCmd(i) |}\<^sub>c -> ? f:{ adjust(i) ((inv (rawPosition i) p) - disp (dOmega (inv (servoCmd i) e))) } -> $EHSV i [[ ehsvOutput i <== adjust i ]]"
  apply (cspF_unwind_left, simp_all, cspF_ren_left)
  by (rule cspF_decompo, simp, cspF_step_left, cspF_step_left, cspF_ren_left)+


lemma unwind_Raw : "$Raw i p0 =F ? p:{ rawPosition(i) p0 } -> (? p:{ rawPosition(i) p0 } -> $Raw i p0
                                                               [+] (? adj:{| adjust(i) |}\<^sub>c \<rightarrow> $Raw i (saturate (p0 + (inv (adjust i) adj))) ))
                                 [+] (? adj:{| adjust(i) |}\<^sub>c \<rightarrow> $Raw i (saturate (p0 + (inv (adjust i) adj))) )"
  apply (cspF_unwind_left, cspF_hsf_left)
  apply (rule cspF_decompo, simp)
  apply (rule cspF_decompo, simp)
  by (cspF_unwind_left)


lemma feedbackPos_DONT_Renames_rawPosition [simp]: "a \<in> {| rawPosition i |}\<^sub>c \<Longrightarrow>
       {x::Events \<in> {| rawPosition i |}\<^sub>c.
                      (x, a) \<in> lvdtOutput i<==feedbackPos i} = { a }"
  apply (simp add: Renaming2_channel_def Renaming2_channel_fun_def fun_to_rel_def Image_def)
  by (auto)


lemma rawPosition_Renaming_coreMoved_simp [simp]: "a \<in> {| rawPosition i |}\<^sub>c \<Longrightarrow>
       {x::Events \<in> {| coreMoved i |}\<^sub>c.
                      (x, a) \<in> coreMoved i<==rawPosition i} = { coreMoved i (inv (rawPosition i) a) }"
  apply (simp add: Renaming2_channel_def Renaming2_channel_fun_def fun_to_rel_def Image_def)
  by (auto)

lemma unwind_LVDT : "$LVDT i [[coreMoved i<==rawPosition i]] [[lvdtOutput i<==feedbackPos i]] =F
            ? p:{| rawPosition(i) |}\<^sub>c \<rightarrow> ? f:{ feedbackPos i (inv (rawPosition i) p) } \<rightarrow> $LVDT i [[ coreMoved i <== rawPosition i ]] [[ lvdtOutput i <== feedbackPos i ]]"
  apply (cspF_unwind_left, cspF_step_left, cspF_step_left)
  apply (rule cspF_decompo, simp, erule rangeE)
  by (cspF_step_left)+



lemma unwind_PCU : "PCU i p0 =F (
              ? p:{| rawPosition(i) |}\<^sub>c -> ? e:{| servoCmd(i) |}\<^sub>c -> ? f:{ adjust(i) ((inv (rawPosition i) p) - disp (dOmega (inv (servoCmd i) e))) } -> $EHSV i [[ ehsvOutput i <== adjust i ]]
              |[ {| rawPosition i, adjust i |}\<^sub>c ]|
              ( ? p:{ rawPosition(i) p0 } -> (? p:{ rawPosition(i) p0 } -> $Raw i p0
                                        [+] (? adj:{| adjust(i) |}\<^sub>c \<rightarrow> $Raw i (saturate (p0 + (inv (adjust i) adj))) ))
                [+] (? adj:{| adjust(i) |}\<^sub>c \<rightarrow> $Raw i (saturate (p0 + (inv (adjust i) adj))) ))
            )
            |[ {| rawPosition i |}\<^sub>c ]|
            ( ? p:{| rawPosition(i) |}\<^sub>c \<rightarrow> (? f:{ feedbackPos(i) (modulate (senseVoltage (inv (rawPosition i) p))) } -> ($LVDT i [[ coreMoved i <== rawPosition i ]] [[ lvdtOutput i <== feedbackPos i ]])) )"

  apply (simp add: PCU_def)
  apply (rule cspF_decompo, simp)
  apply (rule cspF_decompo, simp)
  apply (rule unwind_EHSV)
  apply (rule unwind_Raw)
  apply (rule unwind_LVDT)
  done


lemma unwind_ACE : "$ACE i =F (? p:{| controlCmd(i) |}\<^sub>c -> ? f:{| feedbackPos(i) |}\<^sub>c ->
                              ? x:{ servoCmd(i) (saturate((inv (controlCmd i) p) - (inv (feedbackPos i) f))) } -> $ACE i)"
  by (cspF_auto)






lemma unwind_ACE_PCU :
    "ACE_PCU i p0 =F
            (? p:{| controlCmd(i) |}\<^sub>c -> ? f:{| feedbackPos(i) |}\<^sub>c ->
                              ? x:{ servoCmd(i) (saturate((inv (controlCmd i) p) - (inv (feedbackPos i) f))) } -> $ACE i)
            |[ {| servoCmd i, feedbackPos i |}\<^sub>c ]|
            ((? p:{| rawPosition(i) |}\<^sub>c -> ? e:{| servoCmd(i) |}\<^sub>c -> ? f:{ adjust(i) ((inv (rawPosition i) p) - disp (dOmega (inv (servoCmd i) e))) } -> $EHSV i [[ ehsvOutput i <== adjust i ]]
              |[ {| rawPosition i, adjust i |}\<^sub>c ]|
              ( ? p:{ rawPosition(i) p0 } -> (? p:{ rawPosition(i) p0 } -> $Raw i p0
                                        [+] (? adj:{| adjust(i) |}\<^sub>c \<rightarrow> $Raw i (saturate (p0 + (inv (adjust i) adj))) ))
                [+] (? adj:{| adjust(i) |}\<^sub>c \<rightarrow> $Raw i (saturate (p0 + (inv (adjust i) adj))) ))
             )
             |[ {| rawPosition i |}\<^sub>c ]|
             ( ? p:{| rawPosition(i) |}\<^sub>c \<rightarrow> (? f:{ feedbackPos(i) (modulate (senseVoltage (inv (rawPosition i) p))) } -> ($LVDT i [[ coreMoved i <== rawPosition i ]] [[ lvdtOutput i <== feedbackPos i ]])) ))"

  apply (simp add: ACE_PCU_def)
  apply (rule cspF_rw_left, rule cspF_decompo, simp, rule unwind_ACE)
  apply (rule unwind_PCU)
  by (cspF_hsf)








definition PCUadj
where "PCUadj i aa adj ==
       ? x:{adjust i adj} 
        -> ( ($EHSV i [[ehsvOutput i<==adjust i]] 
             |[{| rawPosition i, adjust i |}\<^sub>c]|
             $Raw i (saturate (aa + inv (adjust i) x)) 
             |[{| rawPosition i |}\<^sub>c]|
             $LVDT i [[coreMoved i<==rawPosition i]] [[lvdtOutput i<==feedbackPos i]]))"


definition ACE_PCUadj
where "ACE_PCUadj i aa adj == $ACE i |[{| servoCmd i, feedbackPos i |}\<^sub>c]| PCUadj i aa adj"



lemma unwind_ACE_PCUadj :
    "$ACE i |[{| servoCmd i, feedbackPos i |}\<^sub>c]| PCUadj i aa adj =F 
       (? p:{| controlCmd(i) |}\<^sub>c -> ? f:{| feedbackPos(i) |}\<^sub>c ->
                              ? x:{ servoCmd(i) (saturate((inv (controlCmd i) p) - (inv (feedbackPos i) f))) } -> $ACE i)
       |[{| servoCmd i, feedbackPos i |}\<^sub>c]|
       ? x:{adjust i adj} -> (($EHSV i [[ehsvOutput i<==adjust i]] 
                             |[{| rawPosition i, adjust i |}\<^sub>c]|
                             $Raw i (saturate (aa + inv (adjust i) x)) 
                             |[{| rawPosition i |}\<^sub>c]|
                             $LVDT i [[coreMoved i<==rawPosition i]] [[lvdtOutput i<==feedbackPos i]]))"
  
  apply (rule cspF_decompo, simp)
  apply (rule unwind_ACE)
  apply (simp add: PCUadj_def)
  done



declare inj_def [simp del]
declare Let_def [simp del]

declare Rec_prefix_def [simp del]
declare Send_prefix_def [simp del]


end