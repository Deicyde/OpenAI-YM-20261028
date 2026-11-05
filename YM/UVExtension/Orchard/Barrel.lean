import Lean
/-!
# The `vintage` derivation notation (a mechanical proof shorthand)

`vintage YM.A.foo` means use the TYPE & EXACT PROOF from the source
`YM.A.foo` here, with identifiers primed (Vintage.X) if VINTAGE variants
declared. Includes theorem consequences found along way with types mentioning
these identifiers. Does NOT infer changes; variants e.g. of important projection
records written explicitly. No changing hypothesis by weakening inference:
kernel checks proofs afresh. Syntactic here: if an important ingredient is
hidden behind a projected or definally unfolded type, THE PROOF may fail. Need
to declare the required variant explicitly first. We apply this when dependence
(e.g. on `.reaches`) is removable in this obvious way, and get the statements
on ACTUAL Wilson objects of course (see consumers). Especially handy retaining
long induction arguments in YM library that prove stronger results than
their historical types. For any lemma thus generated verify the statement
from the type; see fresh proofs consuming them later.

Transparent algorithm: change each constant reference to prefixed name iff
that VINTAGE variant exists, for type and term both. As with much Lean this
shorthand relies on exact elaboration of cited lemmas at pinned revisions.
Convenience for dependent proofs and auxiliary defs (incl private auxs from
cited source lemma): also invoke Vintage on YM constants used by cited proof
walk when their types themselves mention such identifiers. (May REQUIRE
declaring any lacking lemma or rephrased definition first!) `set_option
trace.aging true` for expansion list.

All just checked in Lean: produces proof terms; generates no axioms.
Individual generated consequences can `#print` as usual. Notation runs
`Lean.addDecl` (checked as for definitions/lemmas), propagates errors.
Generated definitions used only noncomputably.
-/
namespace Aging
open Lean Elab Command
private def agingName (n : Name): Name:= `Vintage ++ n
private partial def ferment (env:Environment) (e:Expr): Expr:=e.replace (fun t=>
    match t with
    | .const n ls => if env.contains (agingName n) then some <| .const (agingName n) ls else none
    | .proj n i e=> if env.contains (agingName n) then some <| .proj (agingName n) i (ferment env e) else none
    | _=> none)
private def wine (n:Name): Bool := (`YM).isPrefixOf (privateToUserName n)
initialize registerTraceClass `aging
private partial def store (n:Name) (s:Std.HashSet Name) (requested := false): CoreM (Std.HashSet Name) := do
  if s.contains n || !wine n then return s
  let nm := agingName n
  if (← getEnv).contains nm then return s
  let c ← getConstInfo n
  let search ← c.type.getUsedConstants.foldlM (fun S p=> store p S false) (s.insert n)
  if !(requested || ferment (← getEnv) c.type != c.type) then return search
  let finish (v : Expr) (D: Expr→Expr→Declaration) := do
      let used ← v.getUsedConstants.foldlM (fun S p=> store p S false) search
      let env ← getEnv
      let decl := D (ferment env c.type) (ferment env v)
      trace[aging] "aging {n}"
      try addDecl decl
      catch ex => throwError "aged version of {n}: {ex.toMessageData}"
      return used
  match c with
  | .thmInfo x=> finish x.value (fun t v=> .thmDecl { name := nm, type := t, levelParams := c.levelParams, value := v })
  | .defnInfo x=>
    match x.safety with
    | .safe => finish x.value (fun t v=> .defnDecl { name := nm, type := t, levelParams := c.levelParams, value := v, hints := x.hints, safety := .safe })
    | _=> throwError "refusing unsafe vintage: {n}"
  | _=> throwError "vintage: explicit variant required for constant {n}"

elab "vintage" i:ident : command => do
   liftCoreM <| withOptions (fun o=> Elab.async.set o false) do
     discard <| store i.getId {} true
     unless (← getEnv).contains (agingName i.getId) do
        throwError "no Vintage variant available for {i}"
end Aging
