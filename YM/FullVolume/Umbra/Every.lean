import YM.FullVolume.Umbra.Glade
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Wisteria
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "za'" => za M H (n:=n)
variable {t Y₁ g z c₁ v₁ b₁ κ' e:ℝ}
variable (h: Herd H N.conduit A B n)
open Next.Foundations
variable (p:Clusters H.ThinP) (χ' : Chi)
include N
lemma lighting (V:Config G c)(p:H.ThinP): M.lotus T x χ o.K W o.a Q.table Q.halo V p.val=masked (Pressure.temp x) (H.smallAt p) (fun V=> libs M H χ V p) V:=by
   letI : Nonempty (Forest S.ratio):=Tree.select _ S.patch.odd_side
   let X(r:Greenbelt.Reserve S):= prism T x χ o.K V (allot r)
   let f r V:= M.picture (vary (X r) V) p.val W o.a Q.table Q.halo
   have hf r: M.bloom (X r) W o.a Q.table Q.halo p.val=masked (Pressure.temp x) (H.smallAt p) (f r) V:=by
       rw [M.pictured _ _ H rfl rfl p.property.2]; by_cases h : Healthy (Pressure.temp x) (H.smallAt p) V
       · rw [masked_eq _ _ _ _ h]; rw [masked_eq _ _ _ _ (show Healthy (Pressure.temp x) (H.unionP p.val) (X r).V from h)]; exact (M.arc (X r) p.val H N.oboe rfl rfl rfl p.property.2 h (show Mode (fun _:ℝ=> V) 0 j v from ⟨N.position.le,fun i=> a_oneB _ _ N.position.le⟩) rfl).self_of_nhds.symm
       rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _  (show ¬Healthy (Pressure.temp x) (H.unionP p.val) (X r).V from h)]
   change likely (fun r=> M.bloom (X r) W o.a Q.table Q.halo p.val)=_; simp_rw [hf]
   by_cases h : Healthy (Pressure.temp x) (H.smallAt p) V
   · simp_rw [masked_eq _ _ _ _ h];rfl
   simp_rw [masked_ne _ _ _ _ h]; exact Greenbelt.likely_constant _
lemma scatterC (V:Config G c) : HasDerivAt (fun t=> H.trainedMill (color M H χ V t) p) (masked (Pressure.temp x) (H.bookFoot (.inr p)) (matin M H p χ) V) 0:=by
  let d:ℝ:=coefficient H.seam p.2/(p.1+1).factorial; let f i t:= color M H χ V t (p.2 i).val; let f' i:= M.lotus T x χ o.K W o.a Q.table Q.halo V (p.2 i).val
  have hp i : HasDerivAt (f i) (f' i) 0:=by
    simpa [f,f',color] using! (((hasDerivAt_id' (0:ℝ)).mul_const (f' i)).const_add (H.spawn χ V (p.2 i).val))
  have hx:= (HasDerivAt.fun_finsetProd (u:= Finset.univ) (fun i _=>hp i)).const_mul d
  have ht t : H.trainedMill (color M H χ V t) p=d*∏ i,f i t:=by unfold Cash.trainedMill Gas.term d f; unfold Cash.entriesMill; ring
  simp_rw [ht]
  suffices hf : masked (Pressure.temp x) (H.bookFoot (.inr p)) (matin M H p χ) V=d * ∑ i,(∏ b ∈ univ.erase i, f b 0) • f' i by rw [hf]; exact hx
  let H' i:= H.smallAt (p.2 i); let Q':= H.bookFoot (.inr p)
  have hc i : H' i⊆ Q':= subset_biUnion_of_mem (H.smallAt ∘ p.2) (mem_univ i)
  have hh(i): f i 0 = masked (Pressure.temp x) (H' i) (fun V=> leaflet H χ V (p.2 i)) V:= by unfold f; rw [color0]; exact (N.collective ..).1
  have hM(i): f' i = masked (Pressure.temp x) (H' i) (fun V=>libs M H χ V (p.2 i)) V:=lighting M H N V (p.2 i)
  by_cases hu:Healthy (Pressure.temp x) Q' V
  · have hp i : Healthy (Pressure.temp x) (H' i) V:=Finset.disjoint_of_subset_left (hc i) hu
    rw [masked_eq _ _ _ _ hu]; unfold matin; simp_rw [hh,hM,masked_eq _ _ _ _ (hp _), smul_eq_mul]; rfl
  rw [masked_ne _ _ _ _ hu]; obtain ⟨j,hj,hq⟩:= Finset.not_disjoint_iff.mp hu
  rw [Finset.sum_eq_zero,mul_zero]; intro i hi
  obtain ⟨k,hk,hv⟩:= mem_biUnion.mp hj
  have he : ¬ Healthy (Pressure.temp x) (H' k) V:=fun h=>Finset.disjoint_left.mp h hv hq
  rcases eq_or_ne k i with rfl|hq
  · rw [hM,RG.masked_ne _ _ _ _ he,smul_zero]
  exact smul_eq_zero.mpr (Or.inl (Finset.prod_eq_zero (mem_erase.mpr ⟨hq,hk⟩) ((hh k).trans (masked_ne _ _ _ _ he))))
end Charity
end YM.PhysicalNext.Repeat.Daisy
