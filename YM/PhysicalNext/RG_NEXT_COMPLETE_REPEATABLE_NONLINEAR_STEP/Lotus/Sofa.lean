import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Satin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Greenbelt
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Leaf
variable (M : Leaf R) (X : Coat T F) (k:Finset ℕ)
private theorem likely_product {A B K : Type} (s : Finset A) (Y : A → Finset B) (h : (s:Set A).PairwiseDisjoint Y)
    [Fintype B] [Fintype K] [Nonempty K] [P : Fintype (B→K)] (f : A→(B→K)→ℝ) (he : ∀ i ∈ s,∀ r r', (∀ j∈Y i,r j=r' j) → f i r=f i r') :
    @likely _ P (fun r=> ∏ i∈s,f i r)= ∏ i∈s,@likely _ P (f i) := by
  let Q : Fintype (B→K):=@Pi.instFintype B _ _ _ _; rw [show P=Q from Subsingleton.elim ..]; exact jurisdictions s Y h f he

open Greenbelt
variable (T) (x : ℝ) (χ : Chi) (K : ℝ)
def lotus (W a : ℝ)(Ñ:ChartRatio G)(l:ℕ)(V: Config G c)(p:Molecule S):ℝ:= likely (fun r:Greenbelt.Reserve S=> M.bloom (Greenbelt.prism T x χ K V (allot r)) W a Ñ l p)
def blossom (W a : ℝ)(Ñ:ChartRatio G)(l:ℕ)(V:Config G c)(p:Finset (Molecule S)):=if joints T R l (radiusB x) p∧ permitsA x V p then
    ∑ i∈p, M.lotus T x χ K W a Ñ l V i * ∏ j∈p.erase i,Greenbelt.poolA T x χ K Ñ V R W a l j else 0
-- exact averaging.Full paths multiplicative disjoint with tags.
variable (H:Cash W x μ L Q o C T R)
include H
lemma together (V: Config G c)(s: Finset (Molecule S)):
    likely (fun r:Greenbelt.Reserve S=> M.froth (prism T x χ o.K V (allot r)) W o.a Q.table Q.halo s)=M.blossom T x χ o.K W o.a Q.table Q.halo V s:=by
  letI : Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
  let X (r:Greenbelt.Reserve S):= prism T x χ o.K V (allot r)
  let b i r:= M.bloom (X r) W o.a Q.table Q.halo i; let u i r:=proceedsA R (X r) W o.a Q.halo Q.table i
  by_cases hp:joints T R Q.halo (radiusB x) s ∧ permitsA x V s
  · let f0 i r:=b i r*∏ j∈s.erase i,u j r
    have he(r:Greenbelt.Reserve S): M.froth (prism T x χ o.K V (allot r)) W o.a Q.table Q.halo s=∑ i∈s,f0 i r:=if_pos hp
    unfold blossom; rw [if_pos hp]; simp_rw [he]; change _=∑i∈s,likely (b i)*∏ j∈s.erase i,likely (u j)
    have hz : likely (fun r=>∑ i∈s, f0 i r)=∑ i∈s, likely (f0 i):= by unfold likely; rw [sum_comm,Finset.mul_sum]
    rw [hz]; refine Finset.sum_congr rfl fun i hi=> ?_
    let g j:= if j=i then b i else u j
    have hF r: f0 i r=∏ j∈s,g j r:=by
      rw [← Finset.mul_prod_erase _ _ hi]; simp only [g,if_true]; exact congr_arg (_*·) (prod_congr rfl fun j hj=>by rw [if_neg (ne_of_mem_erase hj)])
    let Y i:=ground R T Q.halo (radiusB x) i; have hG(j)(_:j∈s)(u v:Greenbelt.Reserve S)(hs:∀z∈Y j,u z=v z):g j u=g j v:=by
      unfold g; have hh (k:Site f)(hk:S.ratio.parent k∈Y j):(allot u).up k= (allot v).up k:=by change (u _).up k = (v _).up k; rw [hs _ hk]
      split
      next he => exact he ▸ M.sailV (X u) (X v) i rfl rfl rfl rfl rfl H (he ▸ hh)
      exact Horticulture.Travels.sails (X u) (X v) j rfl rfl rfl rfl rfl rfl H hh
    rw [funext hF, likely_product s Y hp.1.2 g hG,← mul_prod_erase _ _ hi]; simp only [g,if_true]
    exact congr_arg (_*·) (prod_congr rfl fun j hj=>by rw [if_neg (ne_of_mem_erase hj)])
  have he(r:Greenbelt.Reserve S): M.froth (prism T x χ o.K V (allot r)) W o.a Q.table Q.halo s=0:=if_neg hp
  unfold blossom; rw [if_neg hp]; simp_rw [he]; exact likely_constant _

lemma summons (F' : Forest S.ratio) (V: Config G c) : HasSum (fun p : Finset (Molecule S)=> overhead (prism T x χ o.K V F') R Q.table * M.blossom T x χ o.K W o.a Q.table Q.halo V p) (S.push R.beta M.cicada V):=by
  letI: Nonempty (Forest S.ratio):=⟨F'⟩
  let X:=prism T x χ o.K V F'; let Y(r:Greenbelt.Reserve S):= prism T x χ o.K V (allot r)
  have he r : overhead (Y r) R Q.table= overhead X R Q.table:= TreeColor.overhead_eq (Y r) X rfl H.laws.intake.ready rfl Q.table R
  have hz:=Greenbelt.hasAvg _ (fun _:Greenbelt.Reserve S=> S.push R.beta M.cicada V) (fun r=> M.streetP (Y r) H rfl)
  simp only [he, Greenbelt.likely_constant, Greenbelt.likely_mul] at hz; unfold Y at hz; simp_rw [M.together T x χ H] at hz; exact hz
end Leaf
end YM.PhysicalNext.Repeat.Lotus
