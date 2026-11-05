import YM.Analysis.SmoothJets
import YM.Bid.Source

/-!
# T singleton REFERENCE cone currency & lease across any offset

Signed progress measures the true post-subtraction data.

DOESN'T yield them
from the two summands' costs after running.

Don't substitute outcome without that.

Order: choose one `Worth` mass before all ratios (upper monotone chosen).

Needs to
pay all contours with that choice.

P.stage columns deliberately >= next; general
primary schedule no implicit type catches insufficient P!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Filter Function Set RG Wilson Lattice Supply Labels Source Drops InnerProductSpace MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators NNReal
variable {G : Gauge}

structure Worth where
  K : ℕ → ℝ
  prices i : 1 ≤ K i
  growth : Monotone K

def puffs (L : Side) := (L.val:ℝ)^((1:ℝ)/8)
def barunit (L : Side) := (puffs L)⁻¹^ (3:ℕ)
def roomCost (A : Levels G) (P : Worth) : Prop := ∀ i : ℕ,
    let j:=A.clock.J i
    let h:=P.K (j+1)
    64*h^ (2:ℕ) ≤ (A.params i).columns

def terms (P : Sheet G) (C : Worth) (j : ℕ) : ℝ := 100000*(C.K (j+1))^6*(1+(P.profile j).columns)^2

def Bank (W : Worth) (A : Levels G) : Prop := ∀ i : ℕ,
    let j:=A.clock.J (i+1)
    let p:= A.params (i+1)
    100000*(W.K (j+1))^6*(1+p.columns)^2 ≤ puffs (A.S.block i)

lemma buffer (W : Worth) (P : Sheet G) (h : ∀ j, 64*(W.K (j+1))^2≤(P.profile j).columns) :
    ∃ k : ℕ → ℕ, ∀ v : ℕ → ℕ, k ≤ v → ∀ D : Rolls { P with floorL := v }, ∀ M : Levels G,
      M.clock.factor = D.L → M.clock.stage=P.profile → Bank W M ∧ roomCost M W := by
  have ht : Tendsto (fun L : ℕ => (L:ℝ)^((1:ℝ)/8)) atTop atTop :=
    (tendsto_rpow_atTop (y := (1:ℝ)/8) (by positivity)).comp tendsto_natCast_atTop_atTop
  choose k hk using fun i => eventually_atTop.mp (ht.eventually_ge_atTop (terms P W i))
  refine ⟨k,fun v hv D L hm hp => ⟨fun i => ?_, fun i => ?_⟩⟩
  · unfold Levels.params Calendar.params
    rw [hp, show L.S.block i= D.L _ from (L.fits.sameFactor i).symm.trans (congr_fun hm (L.clock.J (i+1)))]
    exact hk _ _ ((hv _).trans (D.large _).need)
  unfold Levels.params Calendar.params; rw [hp]; exact h _

variable {d N p : ℕ}

-- PSREC upper tested with THIS production, after extra constraints. smaller γ=1/8.
def vowel (F : Labels.Frame G d) (L : Side) (x : F.Coeff) : F.Coeff := fun i => (L.val:ℂ)^(d-(F.grades i).1)*x i

def direction {d} (H : History G) (W : Worth) (i : ℕ) (F : Labels.Frame G d) (u v : F.Coeff) (r t : ℝ) :=
    let L := H.S.block i; let y := vowel F L v; let z:= H.levels.clock.J (i+1); let ex := barunit L
    0≤r ∧ 0≤t ∧ ∃ B : F.Coeff ≃ₗ[ℂ] F.Coeff,
      (∀ x,F.coeffSize (B x) ≤ W.K z * F.coeffSize x ∧ F.coeffSize (B.symm x) ≤ W.K z * F.coeffSize x ∧ F.core (B x)=B (F.core x)) ∧
      F.coeffSize (u-B y) ≤ ex*(F.coeffSize (F.core v)+t) ∧ r ≤ W.K z * F.coeffSize (F.core y) + ex*t

-- NOTE psection.C open H.C Pace. not grants/hyp reconstruct.
structure Paper {d} (H : History G) (N p : ℕ) (F : Labels.Frame G d) where
  inits : ∀ i, F.Coeff → Coefficient F (H.S.side i p)
  paid : ∀ (_ : ℕ), F.Coeff → ℝ

namespace Paper
variable {F : Labels.Frame G d} {H : History G}

structure Clocks (P : Paper H N p F) (X : SectionData F) (A : Hol G) (W : Worth) (k : ℕ) : Prop where
  ahead : k ≤ N
  knees i (h : k ≤ i) (q : i ≤ N) v :
    (P.inits i v).Format 0 A (H.rep N p i) ∧ (P.inits i v).remBound 0 (H.rep N p i)
            (Real.sqrt (H.levels.clock.forcedAllowance i)) (P.paid i v)
  thick v : P.paid N v ≤ F.coeffSize (F.core v)
  owns i (h : k ≤ i) (t : i<N) v :
    direction H W i F (P.inits i v).x (P.inits (i+1) v).x (P.paid i v) (P.paid (i+1) v)
  steps m (h : k≤m) (ht : m<N) v :
    (P.inits m v).density 0 X (H.rep N p m) = ((H.S.block m).val : ℂ)^d • (H.levels.clock.op m p).push (H.β N p (m+1))
        ((P.inits (m+1) v).density 0 X (H.rep N p (m+1)))
  charges v U : (P.inits N v).density 0 X (H.rep N p N) U =
    ((H.S.a N : ℂ)^d) * ((H.rep N p N).eval U : ℂ) * initial X H N p v 0 U
  outfeet v : (P.inits N v).x=v ∧ (P.inits N v).regular=0
  units m (h : k ≤ m) (t : m≤N) : (P.inits m (unitVec F H N)).x=unitVec F H m
  linear i (h : k ≤ i) (t : i ≤ N) :
    IsLinearMap ℂ (fun v => (P.inits i v).x) ∧ IsLinearMap ℂ (fun v => (P.inits i v).regular) ∧
       IsLinearMap ℂ (fun v => (P.inits i v).forced) ∧ ∀ v, (P.inits i v).support=(P.inits i 0).support
  moves i (h : k ≤ i) (t : i ≤ N) v :
    ((P.inits i (star v)).x=star ((P.inits i v).x)) ∧ ∀ s : Signed,(P.inits i (F.act s.ortho v)).x=F.act s.ortho (P.inits i v).x
end Paper

def G08 : Prop := ∀ {G : Gauge} (W : Worth) (H : History G), roomCost H.levels W → Bank W H.levels →
      ∀ N p d k (F : Labels.Frame G d) (P : Paper H N p F) (S : SectionData F) (A : Hol G), Paper.Clocks P S A W k →
        ∃ T : TransferData F H N p, T.entries = P.inits ∧ T.Based A S k

structure Duet (H : History G) (F : Labels.Frame G d) (N p l m : ℕ) where
  voice : ∀ i, Coefficient F (H.S.side i p)
  cost : ℕ → ℝ
  atPoint i : Site (H.S.side i p)

namespace Duet
variable {H : History G} {F : Labels.Frame G d}

-- Comparison. Put sign magnitude first. Transport `o` ancestors. A separate producer must
-- justify Duet.Voice INITIAL exactly serves the difference and supply matching x!
structure Woke {l m} (P : Duet H F N p l m) (A : Hol G) (W : Worth) (B : SectionData F) (w : ℝ) : Prop where
  basic : l ≤ m ∧ m ≤ N
  origin (i : ℕ) (h : l ≤ i) (t : i ≤ m) :
    (P.voice i).Format (P.atPoint i) A (H.rep N p i) ∧ (P.voice i).remBound (P.atPoint i) (H.rep N p i)
      (Real.sqrt (H.levels.clock.forcedAllowance i)) (P.cost i)
  ancestry (i : ℕ) (h : l ≤ i) (t : i<m) : P.atPoint i=(H.levels.clock.op i p).ratio.parent (P.atPoint (i+1))
  funds i : l ≤ i → i < m → direction H W i F (P.voice i).x (P.voice (i+1)).x (P.cost i) (P.cost (i+1))
  transfers m' (h : l ≤ m') (ht : m'<m) : (P.voice m').density (P.atPoint m') B (H.rep N p m') =
      ((H.S.block m').val : ℂ)^d • (H.levels.clock.op m' p).push (H.β N p (m'+1))
        ((P.voice (m'+1)).density (P.atPoint (m'+1)) B (H.rep N p (m'+1)))
  pairing : (P.voice l).x =0
  spread :
    P.cost m ≤ w+(H.levels.params m).columns * (w+F.coeffSize (P.voice m).x)
end Duet

def gainChart {G : Gauge} (H : History G) (k i : ℕ) := Real.exp (((1:ℝ)/8)*(H.S.scale k-H.S.scale i))

-- quantitative; post leg sensitivity. `ξ` branch. Leaf tested demand in successor-H0,
-- E γ shrunk may use at rents proof after shaping; ensure discrepancy formulas there.
def G09 : Prop := ∀ {G : Gauge} (W : Worth) (H : History G), roomCost H.levels W → Bank W H.levels →
    ∀ (N p d k o : ℕ) (F : Labels.Frame G d) (B : SectionData F) (A : Hol G), ∀ P : Duet H F N p k o, ∀ w : ℝ,0≤ w → Duet.Woke P A W B w →
    ∀ i : ℕ, k ≤ i → i ≤ o →
      gainChart H o i*(P.cost i+F.coeffSize (P.voice i).x) ≤ 4*(1+(H.levels.params o).columns)*w

-- observable paper red from Unmarked.Power & G.P.Bounds assembles.
variable {H : History G}
structure RefLi (H : History G) (f : Frames G) (X : ∀ d,SectionData (f.level d)) (Y : Hol G) (r : ℕ → ℕ) : Prop where
  gets (d : ℕ) : (X d).Sound Y
  order (d : ℕ) : d+3 ≤ H.levels.clock.J (r d) ∧ ∀ i,r d ≤ i → d+1 ≤ (H.levels.params i).order ∧ d ≤ (H.levels.params i).power
  fits (d N p : ℕ) : r d ≤ N → ∀ x∈ (X d).stencil, ∀ i : Axis,20*((x i).natAbs+1) ≤ (H.S.side N p).val
  loaded (d N : ℕ) : r d ≤ N → Credit (X d) (H.levels.budget N).order (H.levels.budget N).power (H.levels.params N).columns


end YM.Bid
