import YM.Next.EXTRACTION.Basis
import YM.Push.PRICE_COMPILER.Compiler

/-!
# Further fixed-L buys: value of a grant in the post-L exponent currency

Convert an actual pressure charge to suppression, in the actual β-band.
No E/K/forms, locality or cluster conclusion is drawn; of course there may
be (very large) other factors/debts in such a proof. As an example give
exact delay gates for using one family of polynomial-multiplier bounds WITH
this price, and fitting the resulting exponential to the `PostCost` &
`Calendar.forcedAllowance` rate. These extra gates buy in the very same
compiler (before `Bar`, but *after* the post-choices affecting the rate).
Uniform also when applied per-share (any count).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG RG.Supply Wilson Precision Pressure Bid Tree
open scoped Topology Matrix.Norms.Frobenius BigOperators

section Eventual






end Eventual

section Prices
variable {G : Gauge} {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)} (M : Preparations P D)





/-- Further numerical bills, can be given independently for each
transition after L. Normalize to these real powers (no restriction to
integer powers). This pays only the indicated type of multiplier;
not every e.g., q gas expense in E section. -/
structure Multiplier where
  C : ℕ → ℕ → ℝ
  power : ℕ → ℕ → ℝ
  order : ℕ → ℕ → ℝ
  pC i j : 0 < C i j
  pk i j : 0 ≤ power i j
  pd i j : 0 ≤ order i j

def Multiplier.pay (d : Multiplier) (j i : ℕ) (y : ℝ) := d.C j i * y^ (d.power j i) * mon y ^ (d.order j i)

structure Earns (q : AfterBill) (d : Multiplier) (j i : ℕ) (x : ℝ) : Prop where
  pays : let y := betaF G x (D.L j)
         d.pay j i y * Real.exp (-(M.rate j / 2)* (mon y)^2) ≤ Real.exp (-(M.budget q).g j * (mon y)^2)
  covers : Real.exp (-(M.budget q).g j * (mon (betaF G x (D.L j)))^2) ≤ Real.exp (-(mon x ^ ((1:ℝ)/5)))



variable {M} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Permit M I a)
include h

end Prices
end YM.Push.PriceCompiler
