import YM.R2I.Vale.Anchor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Foam
/-!
 # Π invariant on alias: compare in Z stronger than footprint, using Plane helper. Uses ONLY the true hol Deck lift & finite fares for moved Θ stems. Never moves Projections for winding.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof.Vale.Calibre
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide Trio Marlin
open Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Averaging Averaging.Anchor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f : Side} {a d w t v : ℝ} {u m : ℕ}
local notation "z" => (axes01)
@[simp] private lemma zeroRule (x:RegularAddress c): projection x (0:Pot G c) z z = 0 := projectedNull _ 0 rfl ..
lemma apportion (g:G.Simple) (hn:4 ≤ c.val)(A:Activities G c)(B:BudgetPoint) (h : Projects A B t)(hp:∀ s b,Nonempty (A.Moves s b)) :
    (Fintype.card (Site c):ℝ) * Averaging.delta A=∑' i, projection (A.reg i) (A.E i) z z:= by
  have he x: ∑' i, censusAt A x z z i= delta A := by simpa only [if_true,Averaging.total] using isotropic g h hn x hp z z
  rw [show (Fintype.card (Site c):ℝ)* _ =∑ i:Site c,delta A from by rw [sum_const,nsmul_eq_mul,card_univ] ] -- bracket
  rw [Finset.sum_congr rfl (fun i (_:i∈Finset.univ)=> (he i).symm), ← Summable.tsum_finsetSum (fun i _=> h.seriesAt g z z i)] -- `simp_rw [← he]` loops he quant x variable; need direct
  exact tsum_congr fun i=> by simp [censusAt]
-- shared library for all Contours. x𝛥 explicit computations.
variable (B:BudgetPoint) (A:Listing G c)(F S:Collection.Source G c) (p:Finset ℕ)(y k:ℕ) (f g:Trio.Offer G c) (x :ℝ)
local notation "L" => Marlin.lodge A y k
local notation "T" => Marlin.bison S f g
local notation "R" => pluck B L
local notation "W" => poursP B L T
set_option quotPrecheck false
local notation "V" => (R).read W
-- volume support by radius for ALL buoy tags. h∞ carries Furnishes budget.
lemma nonshelf (hn:20<c.val)(A:RegularAddress c)(o : Site c)(v:ℕ)(hv:20*v<c.val)(he : A.support⊆ neighbors v o): Nonwrapping (expand A) A.site:= by
  intro y h; rcases mem_union.mp h with hx| hx; · have ht:=(neighbors_mem ..).1 (he hx); have hh:=(neighbors_mem ..).1 (he A.anchor); rw [separation_comm]; have h := separation_triangle A.site o y; rw [separation_comm _ o] at h; omega
  obtain ⟨b,hp,ha⟩:= halo_spec.mp hx; rw [mem_singleton.mp hp,separation_comm] at ha; omega
lemma crestwrap (hn:20<c.val)(hy:20*y<c.val)(i:Door c) : Nonwrapping (expand (sea y i)) (sea y i).site := by
  apply nonshelf hn _ (affine i.1.1 i.1.2 i.2) y hy ?_
  intro x hx; obtain ⟨j,hj,rfl⟩:= mem_image.mp hx; apply (neighbors_mem ..).2 -- inspect anchor orientation; revolve i
  rw [spin_separation]; exact (neighbors_mem ..).mp hj
variable (h:G.Simple)(hn:20<c.val)(hy : 20*y<c.val)
variable (hp:∀ i∈p,Nonwrapping (AnalyticBridge.VerifiedReset.expand (A.reg i)) (A.reg i).site) (hF:∀ i∈p,B.Regular (A.reg i).support (F.logRead i)) (hS:∀ i,S.logRead i= if i∈p then 0 else F.logRead i)
   (hZ:∀ U:Config G c,flags B.threshold U=∅→x+∑ i:Door c, choir f i U = ∑ i∈p,F.logRead i U)
    (hV : Collection.Local (Marlin.pluck B (Marlin.lodge A y k)) B (Marlin.poursP B (Marlin.lodge A y k) (Marlin.bison S f g)) t v)
include hp hF hS h hy hn hV hZ
set_option maxHeartbeats 400000 in
lemma oriented : (Fintype.card (Site c):ℝ)* delta (V)=∑' i, projection (A.reg i) (F.logRead i) z z := by
  let D:ℕ→ℝ:= fun i=> projection (A.reg i) (F.logRead i) z z; let t (i : Door c) := projection (sea y i) (choir f i) z z
  let m i:=projection ((V).reg i) ((V).E i) z z
  let E i:= if i∈p then 0 else D i
  let Q:= leanU c; let W' := Sum.elim E t
  have hX i:((V).reg i)=Sum.elim A.reg (sea y) (Q i)∧ (V).E i=Sum.elim S.logRead (choir f) (Q i):= ⟨rfl,rfl⟩
  have hm i:m i=W' (Q i):= by
    unfold m; rw [(hX i).1,(hX i).2]; rcases he:Q i with i|i; swap; · rfl
    dsimp only [Sum.elim]; rw [hS]; unfold W'; dsimp only [Sum.elim]; unfold E; split; · exact zeroRule _
    rfl
  have hf : Summable E:= by
    have he : Summable (W' ∘ Q):= (hV.projects.series h z z).congr hm
    have hg : Summable W':= (Q.summable_iff).1 he; have hc : Function.Injective (Sum.inl : ℕ → Civ c):= Sum.inl_injective; exact (hg.comp_injective hc : Summable (W' ∘ (Sum.inl : ℕ → Civ c)))
  have hh : Summable (fun i=>if i∈p then D i else 0) := (hasSum_sum_of_ne_finset_zero (s:=p) (fun i hi=> if_neg hi)).summable
  have hE (i:Door c): B.Regular (sea y i).support (choir f i):= by
    have ht:= hV.smooth (Q.symm (.inr i)); change B.Regular ((V).reg _).support ((V).E _) at ht; rw [(hX _).1,(hX _).2, Equiv.apply_symm_apply] at ht; exact ht
  have hD :(∑ i,t i)=∑ i∈p,D i:= by
    have hG:4≤c.val:=by omega
    let X:Support c:= Finset.univ
    have he i := planar h hG _ z (crestwrap y hn hy i) (hE i)
    have hF' i : B.Regular X (choir f i):= VerifiedReset.reg_larger (hE i) (subset_univ _)
    let g:= Function.const (Config G c) x
    let g':= ∑ i: Door c, choir f i
    let g'' := ∑ i∈p,F.logRead i
    have hi : plane z g''=plane z g' := by
       have he : germ (g+g')=ᶠ[𝓝 0] VerifiedReset.germ g'':= by
         have hm:Tendsto (increment (1:Config G c)) (𝓝 0) (𝓝 1) := by
           have he: Continuous (increment (1:Config G c)):= by unfold increment; fun_prop
           have h:= he.tendsto 0; rw [VerifiedReset.at_zero] at h; exact h
         have hk : (1:Config G c)∈Boulevard.sunny B:= fun i=> by simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using B.threshold_pos
         filter_upwards [hm.eventually ((Boulevard.sky B).mem_nhds hk)] with i hi
         change x+g' _=g'' _; simp only [g',g'',Finset.sum_apply]; exact hZ _ (Boulevard.smoky hi)
       exact (germ_coach _ _ he z).symm.trans ((plane_add (VerifiedReset.reg_const (p:=B) (X:=X) _) (Meadow.regularA _ (fun i _=> hF' i)) z).trans (by change plane z g + plane z g'=plane z g'; rw [show plane z g = 0 from plane_zero ..,zero_add])) -- assembly
    unfold D t; rw [sum_congr rfl (fun i _=> he i), sum_congr rfl (fun i (hi:i∈p)=> planar h hG _ z (hp i hi) (hF i hi)), ← plane_sum z _ _ (fun i _=> hF' i),← hi, plane_sum z p F.logRead (fun i hi=> VerifiedReset.reg_larger (X:=_) (Y:=X) (hF i hi) (subset_univ _))]
  rw [apportion h (by omega) _ B hV.projects hV.transforms]
  let a i:=if i∈p then D i else 0; have hd i:D i=E i+a i:= by unfold E a; split <;> simp
  change (∑' i,m i)=∑' i,D i; calc
     _ = ∑' i, W' i := (tsum_congr hm).trans (Q.tsum_eq W')
     _ = (∑' i,E i)+∑' i,t i:= Summable.tsum_sum (f:=W') hf Summable.of_finite
     _ = (∑' i,E i)+∑' i,a i:= by
         rw [tsum_fintype t,hD,tsum_eq_sum (s:=p) (show ∀ i∉p,a i=0 from fun i hi=> if_neg hi)]; congr 1; exact sum_congr rfl fun i hi=> (if_pos hi).symm
     _ = ∑' i,D i:= (hf.tsum_add hh).symm.trans (tsum_congr fun i=>(hd i).symm)
end YM.PhysicalNext.Repeat.Roof.Vale.Calibre
