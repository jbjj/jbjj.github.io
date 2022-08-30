theory pcu
imports "df"
begin


typedef ActuatorId = "{1..4}::nat set" morphisms to_nat to_ActuatorId
by (auto)

setup_lifting type_definition_ActuatorId

declare [[coercion to_ActuatorId]]

code_thms to_ActuatorId


type_synonym displacement = real
type_synonym angularVelocity = real
type_synonym voltage = real



definition dMAX :: "displacement"
where "dMAX = 40"

definition dMIN :: "displacement"
where "dMIN = -40"
            
fun gain :: "real \<times> real \<Rightarrow> real"
where "gain(x,k) = x * k"

fun saturate :: "real \<Rightarrow> real"
where "saturate(x) = max dMIN (min x dMAX)"

fun dOmega :: "displacement \<Rightarrow> angularVelocity"
where "dOmega(e) = saturate(gain(e,20))"

fun disp :: "angularVelocity \<Rightarrow> displacement"
where "disp(v) = v / 20"

fun modulate :: "voltage \<Rightarrow> displacement"
where "modulate(v) = v / 10"

fun senseVoltage :: "displacement \<Rightarrow> voltage"
where "senseVoltage(p) = gain(p,10)"



datatype Events = rawPosition ActuatorId displacement
                | adjust ActuatorId displacement
                | coreMoved ActuatorId displacement
                | lvdtOutput ActuatorId voltage



datatype PN = Raw ActuatorId displacement displacement
            | LVDT ActuatorId voltage


primrec PNfun :: "PN \<Rightarrow> (PN,Events) proc"
where
    "PNfun(Raw i p adj) =
           rawPosition(i)!p \<rightarrow> (let d = disp(dOmega(adj))
                                in $(Raw i (p+d) (adj-d)))
           [+] adjust(i) ? e \<rightarrow> $(Raw i p e)"

  | "PNfun(LVDT i v) =
           lvdtOutput(i)!(modulate v) \<rightarrow> $(LVDT i v)
           [+] coreMoved(i) ? p \<rightarrow> $(LVDT i (senseVoltage p))"


overloading Set_PNfun == 
  "CSP_syntax.PNfun :: (PN,Events)pnfun"
begin
  definition "CSP_syntax.PNfun == PNfun::((PN,Events) pnfun)"
end
declare Set_PNfun_def [simp add]


lemma guardedfun_PNfun : "guardedfun PNfun"
  apply (simp add: guardedfun_def)
  apply (rule allI, induct_tac p)
  apply (simp_all add: Let_def)
done


overloading Set_FPmode == 
  "CSP_syntax.FPmode :: fpmode"
begin
  definition "CSP_syntax.FPmode == MIXmode"
end
declare Set_FPmode_def [simp add]



definition ActuatorRawLVDT :: "ActuatorId \<Rightarrow> displacement \<Rightarrow> voltage \<Rightarrow> (PN,Events) proc"
where "ActuatorRawLVDT i p v ==
           $Raw i p 0
           |[ {| rawPosition i |}\<^sub>c ]|
           $LVDT i v [[ coreMoved i <== rawPosition i ]]"


definition SimpleActuator :: "ActuatorId \<Rightarrow> (PN,Events) proc"
where "SimpleActuator i == ActuatorRawLVDT i 0 0"






fun DF_to_ActuatorRawLVDT :: "ActuatorId \<Rightarrow> DFtickName \<Rightarrow> (PN, Events) proc"
where
    "DF_to_ActuatorRawLVDT i (DFtick) =
           !<rawPosition i> p .. !<adjust i> a .. !<lvdtOutput i> v ..
           $Raw i p a
           |[ {| rawPosition i |}\<^sub>c ]|
           $LVDT i v [[ coreMoved i <== rawPosition i ]]"


declare inj_def [simp add]

declare gain.simps [simp del]
declare saturate.simps [simp del]
declare dOmega.simps [simp del]
declare disp.simps [simp del]
declare modulate.simps [simp del]
declare senseVoltage.simps [simp del]



lemma Lemma_DF_to_ActuatorRawLVDT :
    "(DFtickfun p) << (DF_to_ActuatorRawLVDT i) <=F DF_to_ActuatorRawLVDT i p"
  apply (induct_tac p, auto)
  apply (cspF_auto)+
  apply (rule cspF_Int_choice_left1)
  apply (cspF_prefix_left)
  apply (rule cspF_decompo_ref)
  apply (force)
  apply (force)

  apply (cspF_auto)
  apply (erule disjE)

    apply (simp)
    apply (cspF_auto)
    apply (cspF_auto)
    apply (simp add: image_def Let_def)
    apply (cspF_auto_right)
    apply (cspF_auto_right)
    apply (cspF_auto_right)
    apply (rule cspF_Rep_int_choice_left, simp)
      apply (rule_tac x="(a + disp (dOmega aa))" in exI, simp)
    apply (rule cspF_Rep_int_choice_left, simp)
      apply (rule exI, simp)
    apply (rule cspF_Rep_int_choice_left, simp)
      apply (rule_tac x="senseVoltage (a)" in exI, simp)
    apply (rule cspF_decompo, simp)
    apply (rule cspF_decompo, simp add: Let_def)
    apply (cspF_hsf_right)
    apply (cspF_hsf_right, simp add: image_def)
    apply (cspF_ren)

    apply (simp add: image_def Let_def, auto)

      apply (cspF_hsf_right)
      apply (cspF_hsf_right)
      apply (cspF_hsf_right)
      apply (cspF_hsf_right)
      apply (cspF_hsf_right)
      apply (cspF_auto_right)
      apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule_tac x="a" in exI, simp)
      apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule exI, simp)
      apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule_tac x="ab" in exI, simp)
      apply (rule cspF_decompo, simp)
      apply (rule cspF_decompo, simp add: Let_def)
      apply (cspF_hsf_right)
      apply (cspF_hsf)

      apply (cspF_ren)
      apply (cspF_hsf)
      apply (cspF_hsf)
      apply (cspF_hsf, simp add: Image_def)
      apply (rule cspF_decompo, simp add: Renaming2_channel_def Renaming2_channel_fun_def fun_to_rel_def)
      apply (auto)
      apply (cspF_auto)
      apply (simp add: Renaming2_channel_def Renaming2_channel_fun_def fun_to_rel_def)
      apply (cspF_hsf)
      apply (cspF_hsf)
      apply (cspF_hsf)
      apply (cspF_hsf)
      apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule_tac x="x" in exI, simp)
      apply (simp add: Renaming2_channel_def Renaming2_channel_fun_def fun_to_rel_def)

      apply (cspF_hsf_right)
      apply (cspF_hsf_right)
      apply (cspF_hsf_right)
      apply (cspF_hsf_right)
      apply (cspF_hsf_right)
      apply (cspF_auto_right)
      apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule_tac x="a" in exI, simp)
      apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule exI, simp)
      apply (rule cspF_Rep_int_choice_left, simp)
        apply (rule_tac x="ab" in exI, simp)
      apply (rule cspF_decompo, simp)
      apply (cspF_auto)
      apply (cspF_auto)
      apply (cspF_auto)
      apply (rule cspF_decompo, simp add: image_def)
      apply (cspF_auto)
      apply (simp add: image_def)
      apply (cspF_auto)+
done


lemma DF_ActuatorRawLVDT : " $DFtick <=F ((ActuatorRawLVDT i p v)::(PN,Events) proc)"
  apply (rule_tac Pf="DFtickfun" and f="DF_to_ActuatorRawLVDT i" in cspF_fp_induct_ref_left)
  apply (simp, simp, simp, simp)
  apply (simp add: ActuatorRawLVDT_def)
  apply (rule cspF_Rep_int_choice_left, simp)
    apply (rule_tac  x="p" in exI, simp)
  apply (rule cspF_Rep_int_choice_left, simp)
    apply (rule_tac  x="0" in exI, simp)
  apply (rule cspF_Rep_int_choice_left, simp)
    apply (rule_tac  x="v" in exI, simp)
by (rule Lemma_DF_to_ActuatorRawLVDT)


theorem ActuatorRawLVDT_isDeadlockFree : "((ActuatorRawLVDT i p v)::(PN,Events) proc) isDeadlockFree"
  apply (simp only: DeadlockFree_DFtick_ref)
by (rule DF_ActuatorRawLVDT)


theorem SimpleActuator_isDeadlockFree : "((SimpleActuator i)::(PN,Events) proc) isDeadlockFree"
  apply (simp only: SimpleActuator_def)
by (rule ActuatorRawLVDT_isDeadlockFree)



end