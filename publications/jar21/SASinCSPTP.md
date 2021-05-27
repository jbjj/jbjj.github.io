# Simple Actuator System (SAS) in CSP-Prover

---

To specify the SAS using CSPTP we create an Isabelle/HOL theory file SAS.thy with the structure presented in Listing 1. In particular, the theory is based on the theory DFP, essential for *deadlock* analysis and derived from the theory CSP_F (the encoding of the *CSP* *failures* model **F**).

  ```haskell
theory SAS
imports DFP
begin
typedef ActuatorId = "{1..4}::nat set" by (auto)
  ```
  > Listing 1 Simple Actuator System Theory File (SAS.thy) in CSPTP

The type {ActuatorId} we defined in CSPM as a **nametype** (an alias) could be defined in CSPTP using a *type_synonym*, however, it a *type_synonym* cannot define the set of values. So, in order to impose this constraint we use a *typedef* and prove it using the command **by** and the proof method *auto* provided by Isabelle/HOL [^1].

The types **displacement**, **angularVelocity** and **voltage** were also defined in CSPM as a **nametypes** and can be defined in CSPTP using the *type_synonyms* and type *int*. However, whereas the definition of constants and functions in CSPM is very succinct, it is more verbose in CSPTP. Isabelle/HOL commands *definition*, {fun} and *primrec* are used in those cases. Furthermore, Isabelle/HOL types must be fully specified, so, the events/channels for our Simple Actuator System specification in CSPTP are put together in an Isabelle/HOL *datatype* definition, see Listing 2.

  ```haskell
datatype Events = rawPosition ActuatorId displacement
                  | adjust ActuatorId displacement
                  | coreMoved ActuatorId displacement
                  | lvdtOutput ActuatorId voltage
  ```
  > Listing 2 SAS events and channels in CSPTP

Moreover, *CSP-Prover* requires the definition of process names as long as it assumes that a process-name-function **PNfun** must be specified for giving the meaning (process body/equation) of each process-name. In our example, the **datatype** in Listing 3 solves this requirement.

  ```haskell
datatype PN = Raw ActuatorId displacement displacement
              | LVDT ActuatorId voltage
              | SimpleActuator ActuatorId
  ```
  > Listing 3 PN (Process Names) type in CSPTP

In particular, the {Raw} process needs an **ActuatorId** and two integer values (one for its position and another for adjusting its position); the **LVDT** process also needs the **ActuatorId** but only stores a single integer value for its internal sensed voltage; finally, the **SimpleActuator** process just needs the **ActuatorId**.

As required by *CSP-Prover*, when defined a type for process names a function (for instance, an Isabelle/HOL *primrec* definition) must be specified and used to overload the definition of the function **CSP_syntax.PNfun**. So, we use our types {PN} (for process names) and **Events** (for channels and events) to create our **SAS.PNfun** as presented in Listing 4.

  ```haskell
primrec PNfun :: "(PN,Events) pnfun"
where
    "PNfun(Raw i p adj) =
           rawPosition(i)!p -> (let d = disp(dOmega(e))
                                in $\$$(Raw i (p+d) (adj-d)))
           [+] adjust(i)?e -> $\$$(Raw i p e)"
  | "PNfun(LVDT i v) =
           lvdtOutput(i)! (modulate v) -> $\$$(LVDT i v)
           [+] coreMoved(i)? p -> $\$$(LVDT i (voltage p))"
  | "PNfun(SimpleActuator i) =
           $\$$(Raw i 0 0)
           |[ {| rawPosition i |} ]|
           ( $\$$(LVDT i 0) [[ coreMoved i <== rawPosition i ]] )"
  ```
  > Listing 4 SAS.PNfun function to specify processes bodies in CSPTP

It is important to note that the type **pnfun** is used to defined the constant **PNfun** users need to overload and is just a *type_synonym* for the function type from a type p' to the process type ('p,'a) proc from theory **CSP_syntax**. So, using our **SAS.PNfun** we specify the overloading of the **CSP_syntax.PNfun**, see Listing 5.

  ```haskell
overloading Set_PNfun == 
  "CSP_syntax.PNfun :: (PN,Events)pnfun"
begin
  definition "CSP_syntax.PNfun == PNfun::((PN,Events) pnfun)"
end
declare Set_PNfun_def [simp add]
  ```
  > Listing 5 CSP_syntax.PNfun overloading for the Simple Actuator System

Moreover, as a consequence of *unguardedness* of our SAS.PNfun function, we are restricted to the use of *CPO* semantic domain [^2]:.

---

[^1]: In Isabelle/HOL, a type is valid if and only if it is a set with at least one element.

[^2]: *CSP-Prover* requires the process equations obey the *guardedness* property to use complete metric spaces semantic model, see~\cite{Isobe}

---
