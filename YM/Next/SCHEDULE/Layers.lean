import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Craft
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Laurent.Rune
import YM.Ovens.Coffee
import YM.PREC.Derivative
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06
import YM.Work.B17
import YM.Work.G03




/-!
# Scheduling: finite demands, primary layer

Name and pay everything per smoothing index (`j`). A demand can of course be a MAX
of bills (e.g. for a whole family of weights), not a single operation. Distinguish
pre-L powers from post-L ones. No assertion in this library that RG calls *have*
all the indicated costs! We prove numerical availability before any rollout, and a
number of application lemmas usable with estimates of the indicated shape.

Everything is explicit data; nothing to be found by inferring physics typeclasses.
Directions of pairs throughout the package: `j` fine, `i` coarse,
`i ≤ j ≤ i+1`. Step index `m` is coarse; the step uses L(stage of m+1).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling

open Filter Source RG RG.Supply Bid Precision Function Finset

/-- Numeric needs. Use a countable exhaustion of FINITE lists (bills may be upper
bounds, so e.g. a support exponent request uses a natural ceiling). Not an
enumeration of continuum tests. The estimate supplier must prove uniformity over
what each such request is meant to buy. -/
structure Need where
  smoothing : ℕ   -- min index incl e.g. two more than all spatial differences
  order : ℕ
  power : ℕ
  exponent : ℕ

/-- Include all needs up through `d` (use e.g. tranche d of finite comparison needs
along with ordinary engineering weight d). If a tranche tests HIGHER weights too,
use it *only* when those also admitted. Can postpone first admission arbitrarily.
The finite step here does not require admitting e.g. all the CONSEQUENCES of a
field through d that will use d+1. -/
def Admits (a : ℕ → Need) (j d : ℕ) : Prop :=
  d+3 ≤ j ∧ ∀ i ≤ d, (a i).smoothing ≤ j

lemma Admits.later {a : ℕ → Need} {i j d : ℕ} (h : Admits a i d) (hi : i ≤ j) : Admits a j d :=
  ⟨h.1.trans hi, fun x hx => (h.2 x hx).trans hi⟩

lemma Admits.down {a : ℕ → Need} {i x d : ℕ} (h : Admits a i d) (he : x ≤ d) : Admits a i x :=
  ⟨le_trans (Nat.add_le_add_right he _) h.1,fun y hy => h.2 y (hy.trans he)⟩

lemma Need.exhaust (a : ℕ → Need) (d : ℕ) : ∀ᶠ j : ℕ in atTop, Admits a j d := by
  let H := (range (d+1)).sup (fun i => (a i).smoothing)
  filter_upwards [eventually_ge_atTop H,eventually_ge_atTop (d+3)] with i hi hx
  exact ⟨hx,fun j hj => (le_sup (s:=range (d+1)) (f:=fun i => (a i).smoothing) (mem_range.mpr (by omega))).trans hi⟩

/-- The increasing-order part of what must be chosen before L. -/
structure Rungs (a : ℕ → Need) where
  k : ℕ → ℕ
  P : ℕ → ℕ
  A : ℕ → ℝ
  six i : 6 ≤ k i
  two i : 2 ≤ P i
  pos i : 0 < A i
  dk : Monotone k
  dP : Monotone P
  dA : Monotone A
  eng i d : Admits a i d → d+1 ≤ k i ∧ d ≤ P i
  covers i d : Admits a i d → (a d).order ≤ k i ∧ (a d).power ≤ P i ∧ ((a d).exponent : ℝ) ≤ A i

/-- `v` also requests arbitrary stage minima (the `.smoothing` field there
is unused). No hidden cap on how big. -/
theorem Rungs.available (a v : ℕ → Need) : ∃ o : Rungs a,
    ∀ i,(v i).order ≤ o.k i ∧ (v i).power ≤ o.P i ∧ ((v i).exponent : ℝ) ≤ o.A i := by
  let s (i) (n : ℕ → Need) := (n i).order+(n i).power+(n i).exponent
  let m i := s i a+s i v+i+7
  let b i := (range (i+1)).sup m
  have hB : Monotone b := fun i j hij ↦ sup_mono (range_mono (by omega))
  have hm i : m i ≤ b i := le_sup (mem_range.mpr (by omega))
  have hn i : 6 ≤ b i := by have := hm i; unfold m at *; omega
  let o : Rungs a := {
    k := b
    P := b
    A := fun i => (b i:ℝ)
    six := hn
    two i := (by have := hn i; omega)
    pos i := by exact_mod_cast (by have := hn i; omega : 0 < b i)
    dk := hB
    dP := hB
    dA := fun i j hij => by dsimp; exact_mod_cast hB hij
    eng i d h := by have := hm i; obtain ⟨hl,-⟩ := h; unfold m at *; omega
    covers i d h := by
      have ht := (hm d).trans (hB <| Nat.le_trans (Nat.le_add_right ..) h.1)
      unfold m s at ht
      refine ⟨by omega,by omega,?_⟩
      exact_mod_cast (show (a d).exponent ≤ b i by omega) }
  refine ⟨o,fun i => ?_⟩
  change _ ≤ b i ∧ _ ≤ b i ∧ _ ≤ ((b i:ℕ):ℝ)
  have := hm i; unfold m s at *; refine ⟨by omega,by omega,?_⟩
  exact_mod_cast (show (v i).exponent ≤ b i by omega)

/-- Commit to the kernel parameters, chart and source books. `.credit` costs
independent of ANY scale parameters incl t, at chosen finite orders. -/
structure Authorities (G : Gauge) where
  kernel : KernelChoices
  has : ∀ P : Patch, P.Branches kernel G
  chart : ChartRatio G
  chartRatio : LocalRatio chart
  hol : Hol G
  frames : Labels.Frames G
  entry : ∀ d : ℕ, SectionData (frames.level d)
  sound d : (entry d).Sound hol
  profile d : pop (entry d)
  fee : ℕ → ℕ → ℕ → ℝ
  credit d k p : Credit (entry d) k p (fee d k p)



/-- Convenient increasing pre-L price: can dominate arbitrary real *estimates*,
not a claim that such estimates for the RG procedure are available. -/
def worth (f : ℕ → ℝ) : Worth := by
  let m := Nat.ceil ∘ f
  let k i := (range (i+1)).sup m + 1
  have hM : Monotone k := fun i j hij ↦ Nat.add_le_add_right (sup_mono (range_mono (Nat.add_le_add_right hij _))) _
  exact ⟨fun i ↦ k i,fun i => by exact_mod_cast (Nat.le_add_left 1 ((range (i+1)).sup m)),fun i j hij => by dsimp; exact_mod_cast hM hij⟩

lemma worth_ge (f : ℕ → ℝ) (i : ℕ) : f i ≤ (worth f).K i := by
  unfold worth
  apply (Nat.le_ceil _).trans
  change (((Nat.ceil ∘ f) i : ℕ) : ℝ) ≤ (((range (i+1)).sup (Nat.ceil ∘ f)+1 : ℕ) : ℝ)
  exact_mod_cast (le_trans (le_sup (s:=range (i+1)) (f:=Nat.ceil ∘ f) (mem_range.mpr i.lt_add_one)) (Nat.le_add_right _ 1))

/-- Inputs at survey stage: choose direct coefficient using prior analysis, and
commit to provisional linear prices `X`. `.first` initial stage (no transition
m=0 from a lower stage). Fields independent of all Roll parameters. Auxiliary
stage floors may of course depend on the chosen X. -/
structure Survey (G : Gauge) where
  B : Authorities G
  requests : ℕ → Need
  o : Rungs requests
  direct : ℕ → ℝ
  linear : ℕ → ℝ
  direct_pos i : 0 < direct i
  direct_cap i : direct i ≤ 1
  linear_pos i : 0 < linear i
  kink i : linear i < direct i/16
  X : MapPrices
  first : ℕ
  cut : 4 ≤ first
  floorL : ℕ → ℕ

/-- Both transitions fine to coarse are needed, even when the stage equals
`.first`. -/
def Adj (j i : ℕ) : Prop := i ≤ j ∧ j ≤ i+1

lemma Adj.cases_forward {i j} (h : Adj j i) : j=i ∨ j=i+1 := by obtain ⟨h,h'⟩:=h; omega
lemma Adj.cases_back {i j} (h : Adj j i) : i=j ∨ i=j-1 := by obtain ⟨h,h'⟩:=h; omega

namespace Survey
variable {G : Gauge} (S : Survey G)

/-- First quotation table. Its WHOLE stage isn't fixed -- only components
used to commit to the map prices. We will repin results relative to the paid
stage via a lowering lemma. Small path/column/drift asks here enable that. -/
def sheet : Sheet G where
  kernel := S.B.kernel
  has := S.B.has
  profile j := ⟨⟨S.direct j,S.linear j,12,S.direct_pos j,S.linear_pos j,S.kink j,by norm_num⟩,
    S.o.k j,S.o.P j,S.o.A j,1,1,0,1,S.o.six j,S.o.two j,S.o.pos j,by norm_num,by norm_num,
    by simp,by norm_num,le_rfl⟩
  first := S.first
  cut := S.cut
  orders := S.o.dk
  powers := S.o.dP
  prices := S.o.dA
  floorL := S.floorL
end Survey
end YM.Next.Scheduling
