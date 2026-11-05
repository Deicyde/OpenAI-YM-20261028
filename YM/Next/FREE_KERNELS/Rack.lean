import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Next.FREE_KERNELS.Priced
import YM.Spark.Limit
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06
import YM.Work.F06
import YM.Work.F08
import YM.Work.F09


/-!
# Providing Rack and RShape: actual metrics with sharp enough uniformity

R-level assumptions are an actual `Levels G`, common kernel, and two tables
of numerical receipts bought *before* all block lengths. Pledging requires
NO look into the Levels. No dependency on nonlinear estimates presumed; in
particular even if RLevel eventually needs more elsewhere it may restrict
to these prices before calling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open scoped Topology BigOperators ComplexConjugate
variable {j t : ℕ}

section passage
variable (K : KernelChoices) (l m : ℝ) (hl : 0≤l) (hm : 0≤m) (P : Flight j t) (ht : 4≤t) (W Y : Bed)
    (hW : Defined K.penalty m P.wing W) (hY : Defined K.penalty l P.land Y)
    {c f : Side} (hc : f.val=c.val*P.L.val)
include hl hm ht hW hY
lemma diagonal : Towers.Diagonal (P.visit K hc) W Y (P.duo K.penalty) := by
  let k := K.penalty
  obtain ⟨h₁,h₂,h₃⟩ := Flight.tangent P K ht hc
  refine ⟨?_,h₂,?_⟩
  · have hh : Precision.K (W.metric.acts f)=Precision.K ((record (pulse k P.wing)).acts f) := by
      rw [hW.metric]; unfold Precision.K
      rw [Matrix.mul_assoc,show (amend _ _ _).acts f*d 1 f=_ from (obligations k m K.penalty_pos hm P.legal P.wing f).2.2.1, Matrix.mul_assoc]; rfl
    have hy : Precision.K (Y.metric.acts c)=Precision.K ((record (pulse k P.land)).acts c) := by
      rw [hY.metric]; unfold Precision.K
      rw [Matrix.mul_assoc,show (amend _ _ _).acts c*d 1 c=_ from (obligations k l K.penalty_pos hl ht P.land c).2.2.1,Matrix.mul_assoc]; rfl
    refine ⟨?_,?_⟩; rw [hh,hy]; exact h₁.primal
    rw [hy]; exact h₁.dual
  rw [hY.diag,hW.diag]; exact h₃
lemma check_bleep : Bleeps (P.visitRatio hc) W Y (P.duo K.penalty) K.penalty (P.rollFunds K.penalty m l) := by
  unfold Bleeps defect; rw [hY.inverse,hW.inverse,hY.metric]; exact Flight.rebased K m l hl hm ht P hc
end passage

section ready
variable {G : Gauge}

def stageHop (A : Levels G) (i : ℕ) (v : Train (A.clock.J (i+1))) : Flight (A.clock.J (i+1)) (A.clock.J i) :=
    ⟨A.S.block i,A.S.block_odd _,A.S.block_large _,A.clock.adm _,A.fits.mono (Nat.le_succ i),A.fits.stepSlow i,v⟩

def flying (A : Levels G) (d i : ℕ) : Train (A.clock.J i) := match d with
    | 0 => Train.top _
    | k+1 => (stageHop A i (flying A k (i+1))).land

/-- The actual stack `through` length from N; padding unused times may have
a distinct recipe. -/
def location (A : Levels G) (N i : ℕ) := flying A (N-i) i
def destination (A : Levels G) (N i : ℕ) := stageHop A i (location A N (i+1))

lemma loc_land (A : Levels G) (N i : ℕ) (h : i<N) : location A N i = (destination A N i).land := by
  unfold destination location; rw [show N-i=N-(i+1)+1 by omega,flying]
lemma loc_top (A : Levels G) (N) : location A N N = Train.top _ := by rw [location,Nat.sub_self,flying]

/-- Floor choices and the exact kernel equations are usable again by
path producers; not selecting a new trajectory when moving to Suffices. -/
def Present (A : Levels G) (M : Horizon A) (l : ℕ → ℝ) :=
    (∀ N i,i ≤ N → Defined A.clock.kernel.penalty (l (A.clock.J i)) (location A N i) (M.H N i)) ∧
    (∀ N i,i < N → (M.towers N i).A0=((destination A N i).duo A.clock.kernel.penalty).A0 ∧
      (M.towers N i).T=((destination A N i).duo A.clock.kernel.penalty).T)

def Credit (A : Levels G) (γ : ℕ → ℝ) (b : ℕ → ℕ) :=
    (∀ i, (A.params i).clip.direct ≤ γ (A.clock.J i)) ∧ ∀ i, b (A.clock.J (i+1)) ≤ (A.S.block i).val

lemma shelves (A : Levels G) (X : MapPrices) (l γ b) (h : Catalog A.clock.kernel X l γ b) (ht : Credit A γ b) :
    ∃ M : Horizon A, Craft.Rack A X M ∧ Present A M l := by
  classical
  let K := A.clock.kernel
  choose H hH h1 h2 h3 h4 using fun i N => h.bottom _ (A.clock.adm i) _ (ht.1 i) (location A N i)
  let M : Horizon A := ⟨fun N i => H i N,fun N i => (destination A N i).duo K.penalty⟩
  have hm (i N : ℕ) : Mag (A.clock.J (i+1)) (A.clock.J i) := by
    let P := destination A N i; have ht := P.narrow; have hh := P.mono
    exact ⟨A.clock.adm _,A.clock.adm _,by omega⟩
  refine ⟨M,?_,⟨fun N i _ => hH i N,fun _ _ _ => ⟨rfl,rfl⟩⟩⟩
  constructor
  · intro N i hi; exact h1 _ _
  · intro N i hi n; exact h2 _ _ n
  · intro N i n hi; exact h3 _ _ _ _
  · intro N n; exact h4 _ _ (loc_top A N) n
  · intro N i hi
    exact (h.hop _ _ (hm i N) (destination A N i)).1
  · intro N i p hi; let P := destination A N i
    have hh : (location A N i)=P.land := loc_land A N i hi
    have he := (A.S.oneStep i p).exact_size
    exact diagonal K (l (A.clock.J i)) (l (A.clock.J (i+1))) (h.net _) (h.net _) P (A.clock.adm i)
      (H (i+1) N) (H i N) (hH (i+1) N) (hh ▸ hH i N) (c:=A.S.side i p) (f:=A.S.side (i+1) p) he
  intro N i hi; let P := destination A N i
  obtain ⟨hb,he,hf⟩ := h.hop _ _ (hm i N) P
  let Q := P.rollFunds K.penalty (l (A.clock.J (i+1))) (l (A.clock.J i))
  refine ⟨Q,he,?_,?_⟩
  · intro p hp; obtain ⟨ha,hg⟩ := hf (ht.2 i) p hp
    exact ⟨ha,fun x => (hg _).1⟩
  intro p; have hh : location A N i=P.land := loc_land A N i hi
  exact check_bleep K (l (A.clock.J i)) (l (A.clock.J (i+1))) (h.net _) (h.net _) P (A.clock.adm i)
      (H (i+1) N) (H i N) (hH (i+1) N) (hh ▸ hH i N) (c:=A.S.side i p) (f:=A.S.side (i+1) p) (A.S.oneStep i p).exact_size
lemma retained_presents (A : Levels G) (X : MapPrices) (M H : Horizon A) {l} (h : Present A M l) (g : Craft.Rack A X M)
    (hr : Bid.Retained H M) : Present A H l ∧ ∀ N m n, m≤N → Bid.Sworn (H.H N m) n G := by
  refine ⟨⟨fun N i hi => ?_,fun N i hi => ?_⟩,fun N i n hi => ?_⟩
  · rw [hr.1]; exact h.1 N i hi
  · obtain ⟨h1,h2⟩ := h.2 N i hi; obtain ⟨g1,g2⟩ := hr.2 N i hi; exact ⟨g1.trans h1,g2.trans h2⟩
  rw [hr.1]; exact g.oath N i n hi
end ready

/-- RRack/RShape producer. Quantifier order permits K-prices `T` also
fixed before all L. `Sheet` ensures the same profiles are being used in
the pinning service. Levels' matching and numerical `Credit` is the only
contextual assumption. (No need for e.g. all earlier portions of RPost.)
Uses F09 via its actual redescription algebra, together with F06--8. -/
theorem retained_support {G : Gauge} (K : KernelChoices) :
    ∃ X l γ b, Catalog K X l γ b ∧ ∀ P : Supply.Sheet G, P.kernel=K →
    ∃ T : MapPrices, ∀ A : Levels G, A.clock.kernel=P.kernel → A.clock.stage=P.profile → Credit A γ b →
      ∃ M H : Horizon A, Craft.Rack A X M ∧ Present A M l ∧ Bid.Retained H M ∧ H.Suffices T ∧
        Present A H l ∧ ∀ N m n, m≤N → Bid.Sworn (H.H N m) n G := by
  obtain ⟨X,l,γ,b,h⟩ := pledges K
  refine ⟨X,l,γ,b,h,fun P hp => ?_⟩
  obtain ⟨T,hT⟩ := Bid.pinning Work.F06.answer Work.F07.answer Work.F08.answer Work.F09.answer P X
  refine ⟨T,fun A ha hb it => ?_⟩
  obtain ⟨M,hm,ht⟩ := shelves A X l γ b (by rw [ha,hp]; exact h) it
  obtain ⟨H,hH,hh⟩ := hT A hb ha M hm
  exact ⟨M,H,hm,ht,hH,hh,retained_presents A X M H ht hm hH⟩

end YM.Next.Free
