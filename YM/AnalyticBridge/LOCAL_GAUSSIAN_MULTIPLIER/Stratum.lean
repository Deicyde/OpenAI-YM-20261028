import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Desk

/-!
# Full profile, coverage and K gates at a spot

Physical choice law (including switches and zeros); no identifying
multiplicities. Outside the original K list support, keep one flag
predicate per site. A possible later clearing of defaults must prove
its identities on the *individual* addresses. Here none cleared.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Next.Fluctuations.Sector
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S}
namespace Desk
variable (d : Desk G S)

abbrev labels := d.input.activities

def Owners (b : Finset ℕ) := b.biUnion (fun i => (d.labels.forced i).support)
def Nonoverlap (b : Finset ℕ) := (b:Set ℕ).Pairwise fun i j => Disjoint (d.labels.forced i).support (d.labels.forced j).support

/-- q padded even at suppressed addresses. -/
def qVoid (b : Finset ℕ) (x : Site f) (U : Config G f) :=
    if x ∈ d.Owners b ∨ x∉flags d.input.p.threshold U then (1:ℝ) else 0

lemma qProd {U : Config G f} {b : Finset ℕ} :
    ∏ i : Site f, d.qVoid b i U = if RG.flags d.input.p.threshold U ⊆ d.Owners b then 1 else 0 := by
  split
  next h =>
    simp_rw [show ∀ i, d.qVoid b i U=1 from fun i => if_pos (or_not_of_imp (fun hv => h hv)),Finset.prod_const_one]
  next h =>
    obtain ⟨i,hi,h⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (not_or.mpr ⟨h,not_not.mpr hi⟩))


end Desk
namespace Spot
variable (u : Spot d)

def fineBit (j : Cell f) (U : Config G f) :=
    let t := d.profile.innerShare (fiery G d.betaHat S.patch.L/4) (toll U j)
    if j∈u.A.costs then 1-t else t
def noiseBit (j : Bond c) (V : Config G c) (U : Config G f) :=
    let t := d.profile.innerShare (d.W * fiery G d.betaHat S.patch.L) (wire (S.prediction U u.k) V j)
    if j∈u.A.aisles then 1-t else t

def frameBit (j : Site c) (U : Config G f) :=
    (Fintype.card S.patch.FrameTag:ℝ) * S.patch.frameMass S.kernel (expandAt (S.ratio.embed j) U) (u.k.1 j)
def connectorBit (j : Bond c) (U : Config G f) :=
    (Fintype.card S.patch.Points:ℝ) * S.patch.predictorMass S.kernel (S.connector U u.k.1 j) (u.k.2 j)

def doorBit (j : u.ActiveKey) (V : Config G c) (p : u.Visual) :=
    broad d.broadCut d.radius ((displaced (u.m V p.1) d.g p.2) j)

/-- This naming preserves physical query multiplicities. -/
abbrev TestIndex := Cell f ⊕ Bond c ⊕ Site c ⊕ Bond c ⊕ u.ActiveKey
abbrev Gates (b : Finset ℕ) := u.TestIndex ⊕ (b ⊕ Site f)

def test (V : Config G c) (p : u.Visual) : u.TestIndex → ℝ
  | .inl i => u.fineBit i (u.hard V p)
  | .inr (.inl i) => u.noiseBit i V (u.hard V p)
  | .inr (.inr (.inl i)) => u.frameBit i (u.hard V p)
  | .inr (.inr (.inr (.inl i))) => u.connectorBit i (u.hard V p)
  | .inr (.inr (.inr (.inr i))) => u.doorBit i V p

def gate (b : Finset ℕ) (i : u.Gates b) : u.Event := fun V p =>
  match i with
  | .inl i => u.test V p i
  | .inr (.inl i) => d.labels.K i (u.hard V p)
  | .inr (.inr i) => d.qVoid b i (u.hard V p)

private lemma both_parts {I : Type} [Fintype I] [DecidableEq I] (f : I → ℝ) (s : Finset I) :
    (∏ i : I, if i∈s then 1-f i else f i) = (∏ i∈s,(1-f i)) * ∏ i∈sᶜ,f i := by
  rw [← Finset.prod_mul_prod_compl s]; congr 1
  · apply Finset.prod_congr rfl; intro i hi; exact if_pos hi
  exact Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_compl.mp hi)

lemma disburse (V : Config G c) (h : u.Flags V) (U : Config G f) :
    (∏ i : Cell f,u.fineBit i U)*(∏ j : Bond c,u.noiseBit j V U) = d.allocation.bill u.A u.k U V := by
  unfold Desk.allocation Chi.profiles
  dsimp only [Chi.distribute]
  rw [if_pos h.symm]
  unfold fineBit noiseBit Chi.fineShare Chi.bondShare Chi.share
  congr 1 <;> exact both_parts (fun i => _) _

lemma fallback (U : Config G f) :
    (∏ i,u.frameBit i U)*(∏ i,u.connectorBit i U) = Fintype.card S.Choices*S.likelihood U u.k := by
  unfold frameBit connectorBit StepData.likelihood StepData.Choices StepData.SitesChoice StepData.BondChoice
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_pi,
    Nat.cast_mul,Nat.cast_pow]; ring

lemma checked_at (V : Config G c) (h : u.Flags V) (p : u.Visual) :
    (∏ i : u.TestIndex,u.test V p i) =
      Fintype.card S.Choices * (doors d.broadCut d.radius (displaced (u.m V p.1) d.g p.2) *
        d.allocation.bill u.A u.k (u.hard V p) V * S.likelihood (u.hard V p) u.k) := by
  let U := u.hard V p
  let a := ∏ i,u.fineBit i U; let b := ∏ i,u.noiseBit i V U
  let c := ∏ i,u.frameBit i U; let e := ∏ i,u.connectorBit i U; let z := ∏ i,u.doorBit i V p
  simp_rw [TestIndex,Fintype.prod_sum_type]
  change a*(b*(c*(e*z)))=Fintype.card S.Choices*(z*(d.allocation.bill u.A u.k U V)*_)
  rw [show d.allocation.bill u.A u.k U V=a*b from (u.disburse V h U).symm,
    show a*(b*(c*(e*z))) = z*(a*b)*(c*e) by ring,show c*e=Fintype.card S.Choices*S.likelihood U u.k from u.fallback U]; ring


end Spot
end YM.AnalyticBridge.LocalGaussian
