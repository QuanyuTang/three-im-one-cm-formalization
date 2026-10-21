module

import Solution
import Lean.Util.CollectAxioms

/-!
Checks the public theorem type and permits only the standard axioms.
The official Comparator independently checks the exported proof and its axioms.
-/

#check ThreeIM.three_IM_one_CM
#check ThreeIMOneCM.three_IM_one_CM

open Set in
example {f g : ℂ → ℂ}
    (hf : ThreeIMOneCM.IsNonconstMeroOn f univ)
    (hg : ThreeIMOneCM.IsNonconstMeroOn g univ)
    (a : Fin 4 → ThreeIMOneCM.Sphere) (ha : Function.Injective a)
    (him : ∀ i : Fin 3, ThreeIMOneCM.SharesIMOn univ f g (a i.castSucc))
    (hcm : ThreeIMOneCM.SharesCMOn univ f g (a 3)) :
    ∀ i, ThreeIMOneCM.SharesCMOn univ f g (a i) :=
  ThreeIMOneCM.three_IM_one_CM hf hg a ha him hcm

run_cmd do
  let declarations := #[``ThreeIM.three_IM_one_CM, ``ThreeIMOneCM.three_IM_one_CM]
  let permitted := #[``propext, ``Quot.sound, ``Classical.choice]
  for declaration in declarations do
    let used ← Lean.collectAxioms declaration
    for axiomName in used do
      unless permitted.contains axiomName do
        throwError "{declaration} uses an unpermitted axiom: {axiomName}"
    Lean.logInfo "Axiom whitelist accepted for {declaration}: {used}"

#print axioms ThreeIM.three_IM_one_CM
#print axioms ThreeIMOneCM.three_IM_one_CM
