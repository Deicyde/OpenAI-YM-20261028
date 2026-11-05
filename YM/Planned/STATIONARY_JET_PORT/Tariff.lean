import YM.Planned.STATIONARY_JET_PORT.Legacy
import YM.Push.STATIONARY_UNIFORM.Cost
import YM.Push.STATIONARY_UNIFORM.Switches

set_option warningAsError false
/-!
# L-power accounting. Pre-L quotes; apply on the actual recipes

`Lit j`: strictly positive there, L-power bound (exists u and C>0,
independent of every L at that J, absolute value ≤ C L^u) *also on
the reciprocal*. For exponential and counting bills here need another clause,
that the rates themselves are bounded independent of L; we check that TOO.
In particular no exponentials of L inadvertently purchased at Tame prices.
Keep input loop factor `1+Λ` separate (`clock.loopCap` not a pre-L constant).
Weighted in fine units of THIS approximation; fixed-L quantitative real
input is no proof of persistent scheduled analytic width/support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push Push.Uniform Lattice RG Precision Before.Service
open scoped Topology ContDiff BigOperators Classical

variable {j : ℕ} {f g h : Patch → ℝ}
structure Thin (j : ℕ) (f : Patch → ℝ) : Prop extends Lit j f where
  roof : ∃ C : ℝ, ∀ P : Patch, P.J=j → f P ≤ C


lemma Thin.earn (h : Thin j f) (hL : Lit j g) (hl : ∀ P : Patch,P.J=j → g P ≤ f P) : Thin j g := by
  obtain ⟨C,H⟩ := h.roof; exact ⟨hL,C,fun x hx => (hl x hx).trans (H x hx)⟩
lemma Thin.halve (h : Thin j f) : Thin j (fun x => f x/2) := h.earn
  (h.toLit.div (lit_k (show (0:ℝ)<2 by norm_num))) (fun x hx => (half_lt_self (h.pos x hx)).le)




-- countCost not a new width; price always derived from the same Thin rate
lemma Thin.count_charge (h : Thin j f) : Tame j (fun x => countCost (f x)) := by
  obtain ⟨C,H⟩ := h.roof; exact h.toLit.count H

lemma Thin.console (hf : Thin j f) (hg : Lit j g) (K : ℕ) : Lit j (fun x => console (f x) (g x) K) :=
  (lit_k one_pos).add_left (hg.high.mul ((tame_k _).mul hf.halve.count_charge))
    (fun x hx => by have h := count_pos (half_pos (hf.pos _ hx)); have hh := hg.pos x hx; positivity)
lemma Thin.ground (hf : Thin j f) (hm : Lit j g) (hc : Lit j h) (K : ℕ) : Thin j (fun x => groundRate (f x) (g x) (h x) K) := by
  have hd : Lit j (fun x => diminish (f x) (g x) (h x) K) := (lit_k one_pos).min'
    ((hm.div (lit_k (show (0:ℝ)<2 by norm_num))).div (hf.console hc K))
  refine hf.halve.earn (hd.mul hf.halve.toLit) ?_
  intro x hx; apply mul_le_of_le_one_left (half_pos (hf.pos x hx)).le (min_le_left ..)










/-- Including BOTH sleeve widths for shifted cable estimates (`.switch`)
and the Ł² constants, logs with one-order step. -/
structure MatRates {j : ℕ} (K : ℕ) (f g h : Patch → ℝ) : Prop where
  cable : Thin j f
  initial : Lit j g -- charge
  inputs : Lit j h -- cost
  floor : Thin j (fun x => groundRate (f x) (g x) (h x) K)
  lines (k : ℕ) :
    Thin j (fun x => directRate K k (f x) (g x) (h x)) ∧
      Lit j (fun x => directCost K k (f x) (g x) (h x))
  traces (k : ℕ) :
    Thin j (fun x => logRate K k (f x) (g x) (h x)) ∧
      Lit j (fun x => logging K k (f x) (g x) (h x))


section Per
variable {G : Gauge} {μ C : ℝ} {Q : KernelChoices} {N : ℕ} (A : Before G μ C j Q (N+3)) (p : Clip) (hμ : 0<μ)
include A hμ
local notation "Y" => A.tables p

def worker (Q : Patch → ChartPrices) (g : ChartPrices → ℝ) := fun x => g (Q x)

/-- Tame through both types of matching on the actual uniform prices (once
per stages, i.e. p : Clip fixed from paid Stage not to grow with L; there is
no `α` invoice here; `A` is ANY Before -- no further choice of prices
when proving this compatibility). All k ≤ tested order needs are included (no
need to bound factorials w.r.t. L). Includes inverse energy constant (using
gap/2 even in the presence of shift) and e.g. get polynomial costs on all
weighted row sums by `Thin.count_charge` at half these rates. -/
structure Prices (j N : ℕ) (G : Gauge) (μ Z : ℝ) (P : Patch → ChartPrices) (M : ℕ) : Prop where
  radius : Lit j (worker P ChartPrices.horizon)
  zone : Lit j (worker P ChartPrices.zone)
  safety : Lit j (worker P ChartPrices.safety)
  initial : Lit j (worker P ChartPrices.initial)
  fullValue : Lit j (worker P ChartPrices.value)
  gap : Lit j (worker P ChartPrices.gap)
  rate : Thin j (worker P ChartPrices.width)
  path : Thin j (worker P (fun y => pathRate y N))
  fare (k : ℕ) : Lit j (worker P (fun y => pathCost y k))
  trail : Lit j (worker P (fun y => trailCost y (N+3)))
  classRate : Thin j (worker P (fun y => classicalRate y N))
  classCost : Lit j (worker P (fun y => classicalBill y N))
  heirs : Thin j (fun x => heirRate (P x) N x.L μ) ∧ Lit j (fun x => heirToll G (P x) N x.L μ Z)
  off : MatRates (j:=j) M (worker P ChartPrices.width) (worker P (fun y => y.gap/2)) (worker P ChartPrices.value)
  positions : MatRates (j:=j) M (worker P (fun y => transit y N)) (worker P (fun y => y.gap/2))
    (worker P (fun y => chargeBill y N))
  heated (O : ChartRatio G) (h : LocalRatio O) (D : FiberFee O (N+1)) :
    Lit j (worker P (fun y => warm O y N)) ∧
      Lit j (worker P (fun y => heatLimit G y (N+3) O)) ∧
      Lit j (worker P (fun y => tax O D.cost y N)) ∧
      Thin j (fun x => caloricRate (P x) N x.L μ) ∧
      Lit j (fun x => caloricToll O D.cost (P x) N x.L μ Z)


end Per
end YM.Planned.JetPort
