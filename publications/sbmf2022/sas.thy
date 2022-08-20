theory sas
imports DFP
begin

typedef ActuatorId = "{1..4}::nat set"
by (auto)

type_synonym displacement = int
type_synonym angularVelocity = int
type_synonym voltage = int

definition dMAX :: "displacement"
where "dMAX = 40"

definition dMIN :: "displacement"
where "dMIN = -40"
            
fun gain :: "int $\times$ int $\Rightarrow$ int"
where "gain(x,k) = x * k"

fun saturate :: "displacement $\Rightarrow$ angularVelocity"
where "saturate(x) = max dMIN (min x dMAX)"

fun dOmega :: "displacement $\Rightarrow$ angularVelocity"
where "dOmega(e) = saturate(gain(e,20))"

fun disp :: "angularVelocity $\Rightarrow$ displacement"
where "disp(v) = (* omitted *)"

fun modulate :: "voltage $\Rightarrow$ displacement"
where "modulate(v) = (* omitted *)"

fun senseVoltage :: "displacement $\Rightarrow$ voltage"
where "senseVoltage(p) = (* omitted *)"

datatype Events = rawPosition ActuatorId displacement
                | adjust ActuatorId displacement
                | coreMoved ActuatorId displacement
                | lvdtOutput ActuatorId voltage

datatype PN = Raw ActuatorId displacement displacement
            | LVDT ActuatorId voltage
            | SimpleActuator ActuatorId


primrec
     PNfun :: "PN => (PN,Events) proc"
where
    "PNfun(Raw i p adj) =
           rawPosition(i)!p -> (let d = disp(dOmega(e))
                                in $\$$(Raw i (p+d) (adj-d)))
           [] adjust(i)?e -> $\$$(Raw i p e)"
  | "PNfun(LVDT i v) =
           lvdtOutput(i)!modulate(v) -> $\$$(LVDT i v)
           [] coreMoved(i)?p -> $\$$(LVDT i senseVoltage(p))"

  | "PNfun(SimpleActuator i) =
           $\$$(Raw i 0 0)
           [| \{| rawPosition |\} |]
           ( $\$$(LVDT i 0) [[ coreMoved <- rawPosition ]] )"

end