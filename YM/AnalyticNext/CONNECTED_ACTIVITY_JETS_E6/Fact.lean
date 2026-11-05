import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Unified
import YM.Push.SECTOR_MEASURE.LabelSum

/-!
# Intact real ledger factors

Pointwise equality primitives; dimension counts on actual scope i. Keep Z integral
charges (Gaussian map and cores) at same real T,P. No normalization by dividing
a flagged vacuum term! Multiply accordingly even at zero indicators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Coat Presented LabelSum Sector
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ μ : ℝ}

namespace Raw
lemma repel (R : Rep G f) (u : Config G f) (M : ℕ) : R.beta * cutR R M u+R.exponent u = R.v*Fintype.card (Site f) -
    (averaged fun s => reduced R M (pull s 0 u)) - R.activities.additive R.p u := by
  let r := R.path
  have he : r.inChannels R.clip R.p R.beta u =
      averaged (fun s => reduced R M (pull s 0 u)) + R.beta*cutR R M u := by
    let q (s : Signed) := ∑ i, crown r R.clip M 1 R.p.threshold (pull s 0 u) i
    have hk (s : Signed) : r.principal R.clip R.p R.beta (pull s 0 u) = reduced R M (pull s 0 u) + R.beta *q s := by
      simp only [PathData.principal,q,Presented.reduced,cuff,Finset.sum_sub_distrib,mul_sub,mul_add,r]; abel
    have hv : r.inChannels R.clip R.p R.beta u=averaged (fun s => reduced R M (pull s 0 u)+R.beta*q s) := by
      simp only [PathData.inChannels,hk,averaged]
    rw [hv,av_add]; unfold q cutR averaged; rw [← Finset.mul_sum]; unfold r; ring
  unfold Rep.exponent; rw [he]; ring

lemma estate {R : Rep G f} (h : Intake P T A R) (u : Config G f) (V : Config G c) (l : Finset ℕ) :
    sieve T R.beta A V * separate R (till A) l u =
      Real.exp (R.v*Fintype.card (Site f))*stone T R.beta A V*
        Real.exp (∑' i, expo T A R u V i) * R.activities.gasOccurrence R.p l u := by
  unfold separate; rw [← Real.exp_add,repel,full_sieve, (income h u V).tsum_eq]
  simp_rw [sub_eq_add_neg,Real.exp_add]; ring

lemma fused (T : Tube G S) (_h : P.Funds S T) (β x : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) :
    enters T β x k V U=prefactor S G β*S.likelihood U k * Real.exp (-β * (wholeGap T x U V+∑ i, monetary S (S.prediction U k) V i)) := by
  let M := ∑ i, monetary S (S.prediction U k) V i
  rw [enters,taggedKernel]
  have he : S.noise β (S.prediction U k) V=prefactor S G β * Real.exp (-β * M) := by
    unfold StepData.noise M prefactor
    rw [prod_mul_distrib,prod_const,card_univ,Finset.mul_sum,Real.exp_sum]; congr 1; apply Finset.prod_congr rfl; intro i _
    unfold StepData.penaltyWeight monetary wire; rw [G.chord_price]; ring_nf
  rw [he, mul_add,Real.exp_add]; unfold M; ring
end Raw

namespace Coat
variable (X : Coat T F)

def dozing := (univ : Finset (Tubular f G)).filter (fun i=> ¬ X.Hot i.1)
def arised := X.tier×ˢ (univ:Finset G.ColorIndex)
def freeSet (S : StepData c f) (F : Forest S.ratio) := univ.filter (fun i:Bond f=> i∉F.trunks)

lemma count_dots : X.arised.card=X.tier.card*Fintype.card G.ColorIndex := by simp only [arised,card_product,card_univ]
lemma measure_count : X.arised.card+X.dozing.card = Fintype.card (Tubular f G) := by
  have hp : X.arisedᶜ=X.dozing := by
    ext i; simp only [dozing,arised,mem_filter,mem_univ,true_and, mem_compl,mem_product,and_true,tier]
  simpa only [← hp,Nat.add_comm] using Finset.card_compl_add_card X.arised

lemma table_free : (freeSet S F).card=Fintype.card F.Free := by
  let e : F.Free≃ (↥(freeSet S F)) := Equiv.subtypeEquivRight (fun i => by simp [freeSet])
  rw [Fintype.card_congr e, Fintype.card_coe]
lemma tier_plus : X.tier.card + (X.pens X.seeds).card=(freeSet S F).card := by
  have hp (i) : i∈X.pens X.seeds ↔ i∈freeSet S F ∧ i∉ X.tier := by
    simp only [freeSet,tier,pens,visit,mem_filter,mem_univ,true_and,Hot,active]; unfold voyage frozen
    tauto
  have he : X.pens X.seeds=freeSet S F\X.tier := Finset.ext fun i => (hp i).trans mem_sdiff.symm
  have ht : X.tier⊆freeSet S F := fun i hi => mem_filter.mpr ⟨mem_univ _,((mem_filter.mp hi).2).1⟩
  rw [he]; exact (Nat.add_comm ..).trans (Finset.card_sdiff_add_card_eq_card ht)

def channelOne (Ñ : ChartRatio G) (β : ℝ) := Ñ.scale*(Real.sqrt (2*Real.pi)*gStep β)^Fintype.card G.ColorIndex

def levy (R : Rep G f) := prefactor S G R.beta * Real.exp (R.v* Fintype.card (Site f)) * Raw.stone T R.beta X.x X.V



def deducted (Ñ : ChartRatio G) (β : ℝ) := measure_g Ñ β ^ (Fintype.card F.Free) *
    Real.exp (-Real.log X.blank.plate.det/2)

def bell := Real.sqrt (2*Real.pi)
def thetaRef (z : Air f G) := ((bell)^Fintype.card (Tubular f G))⁻¹ * Real.exp
    (-Real.log X.relating.det/2-dotProduct z.ofLp (X.relating⁻¹ *ᵥ z.ofLp)/2)

def ribbons (z : Air f G) (Ñ : ChartRatio G) (β a : ℝ) :=
    ((bell)^X.dozing.card)⁻¹*gStep β^X.arised.card*Ñ.scale^X.tier.card *
       Real.exp (-X.ghost z + ∑ j∈ X.tier,X.gentry Ñ a (X.liftA β z) j)

lemma payment (Ñ : ChartRatio G) {β : ℝ} (hp : 0<β) (h : LocalRatio Ñ) :
    ((bell)^X.dozing.card)⁻¹*gStep β^X.arised.card*Ñ.scale^X.tier.card =
      ((bell)^Fintype.card (Tubular f G))⁻¹ * (measure_g Ñ β)^(Fintype.card F.Free)* Real.exp
        (-(X.pens X.seeds).card * Real.log (measure_g Ñ β)) := by
  let c := measure_g Ñ β
  have he : 0<c := by have := h.scale; unfold c measure_g gStep; positivity
  let u := (X.pens X.seeds).card
  change _=_ * c^(_ : ℕ) * _
  rw [← table_free (F:=F), ← X.tier_plus, pow_add, ← X.measure_count, neg_mul, Real.exp_neg]
  change _=_*(c^_ * c ^ u)* (Real.exp ( (u:ℝ)*Real.log c))⁻¹
  rw [Real.exp_nat_mul, Real.exp_log he, mul_assoc _ _ ((c^u)⁻¹),mul_assoc (c^_) (c^u), mul_inv_cancel₀ (pow_ne_zero _ he.ne'),mul_one]
  unfold c measure_g; rw [pow_add]; unfold bell; rw [X.count_dots]; simp only [mul_pow, ← pow_mul]
  have he : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  field_simp; ring
end Coat
end YM.ConnectedActivityE6
