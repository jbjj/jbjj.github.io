theory sas
imports "../../CSP-Prover/CSP_F/CSP_F"
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



lemma modulate_senseVoltage [simp]: "(modulate (senseVoltage a)) = a"
by (auto)

lemma senseVoltage_modulate [simp]: "(senseVoltage (modulate a)) = a"
by (auto)

declare gain.simps [simp del]
declare saturate.simps [simp del]
declare dOmega.simps [simp del]
declare disp.simps [simp del]
declare modulate.simps [simp del]
declare senseVoltage.simps [simp del]


datatype Events = rawPosition ActuatorId displacement
                | adjust ActuatorId displacement
                | coreMoved ActuatorId displacement
                | lvdtOutput ActuatorId voltage
                | ehsvOutput ActuatorId displacement
                | servoCmd ActuatorId displacement
                | controlCmd ActuatorId displacement
                | feedbackPos ActuatorId voltage


datatype PN = ACE ActuatorId
            | EHSV ActuatorId
            | Raw ActuatorId displacement
            | LVDT ActuatorId


primrec PNfun :: "PN \<Rightarrow> (PN,Events) proc"
where
    "PNfun(ACE i) =
           controlCmd(i) ? p \<rightarrow> feedbackPos(i) ? feedback \<rightarrow> servoCmd(i) ! (saturate(p - feedback)) \<rightarrow> $ACE i"
  | "PNfun(EHSV i) =
           rawPosition(i) ? p \<rightarrow> servoCmd(i) ? e \<rightarrow> ehsvOutput(i) ! (p - disp (dOmega e)) \<rightarrow> $EHSV i"
  | "PNfun(Raw i p) =
           rawPosition(i) ! p \<rightarrow> $Raw i p
           [+] adjust(i) ? adj \<rightarrow> $Raw i (saturate (p + adj))"
  | "PNfun(LVDT i) =
           coreMoved(i) ? p \<rightarrow> lvdtOutput(i) ! (modulate (senseVoltage p)) \<rightarrow> $LVDT i"


overloading Set_PNfun == 
  "CSP_syntax.PNfun :: (PN,Events)pnfun"
begin
  definition "CSP_syntax.PNfun == PNfun::((PN,Events) pnfun)"
end
declare Set_PNfun_def [simp add]


lemma guardedfun_PNfun [simp]: "guardedfun PNfun"
  apply (simp add: guardedfun_def)
  by (rule allI, induct_tac p, simp_all add: Let_def)



definition PCU
where "PCU i p0 ==
            (
              $EHSV i [[ ehsvOutput i <== adjust i ]]
              |[ {| rawPosition i, adjust i |}\<^sub>c ]|
              ( $Raw i p0 )
            )
            |[ {| rawPosition i |}\<^sub>c ]|
            ( $LVDT i [[ coreMoved i <== rawPosition i ]] [[ lvdtOutput i <== feedbackPos i ]] )"


definition ACE_PCU
where "ACE_PCU i p0 ==
           $ACE i
           |[ {| servoCmd i, feedbackPos i |}\<^sub>c ]|
           PCU i p0"


definition SimpleActuator
where "SimpleActuator i == ACE_PCU i 0"




end