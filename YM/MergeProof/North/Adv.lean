import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.MergeProof.Hens
import YM.MergeProof.Magma
import YM.MergeProof.Plaza


set_option autoImplicit false
noncomputable section
namespace YM.Merge.Photo
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ: Chi) (A:Rep G c) (rA:ι→ℝ) (K:ℝ → Finset ι → Code G c)

open Marker GridRenewal.Rain Filter
variable {V:Type}[DecidableEq V] (B : Marker.Census V) (z:ι→Poly B)(hZ:∀ i,z i*z i=0) {y' ex dk:ℝ}(h: Usable M Y χ A rA K dk ex y')
open MergeProof Accent Set GridApprox.Nil
variable (b':V→Site c)(hw:∀ i,GridApprox.Nil.Scoped (A:= {x| b' x∈ (M i).crest.image S.ratio.parent}) (z i)) (rV:V→ℝ)(hV:∀ i,0<rV i)(hx:∀ i, Poly.price rV (z i) ≤ 1) (ho:∀ i,(z i).part B.quiet=0)
open Menu
variable [Fintype V](D:GaugeDoor R A) (q:ι→Menu.Hat B R)
set_option quotPrecheck false
local notation "σ'"=> fun i=> Menu.sing (q i) rV
local notation "q'"=> fun i=> (q i).M
local notation "f"=> fun i=> sumFee (q i) rV
local notation "F₀"=> fun j U t p=> K t p j U
include hV
lemma hue {u e:ℝ}{P:BudgetPoint} (hd:SoundDoor S D) (ho:∀ i, (q i).s.val.image b' ⊆ (q' i).crest.image S.ratio.parent) (hr: Usable (fun i=>(q i).M) Y χ A (fun i=>sumFee (q i) rV) K dk ex y')(hk:Pays A.activities P K u e)(hc:P.B=A.p.B) (he:0 ≤ e)
    (hQ:∀ j U (p:ι),Switch.jet (fun t i=>K t i j U) {p}=sumFee (q p) rV*D.hinge (q p).M j U): let F:= spine (q') Y χ (f) B (σ'); let K':= chain A K B (σ')
    Towed rV id F A.p.B dk ex ∧ (∀ i,Burns b' i (F i) A.p.threshold) ∧ Towed rV Prod.fst K' A.p.B e u ∧ (∀ i,Flow b' i (K' i) A.p.threshold) ∧ S.push R.beta (Expense q rV S)=play A B K' (fun U=>∑ i,F i U) ∧ (∀ i U,(K' i U).part B.quiet=profile A.activities (fun j=> Complex.ofReal ∘ A.activities.K j) i U)∧ ∀ i U j,(K' i U).part (B.fire j)= ∑ l,owl (q l) D j i U:=by
   let z:=σ'; let X':=chain A K B z
   have hZ : ∀ i,(z i).part B.quiet=0:=fun i => (virtue (q i) rV).1
   have hz:∀ i,Poly.price rV (z i)≤1:=fun i=> Menu.paid (q i) hV
   have hw(i):Scoped {x| b' x∈ (q' i).crest.image S.ratio.parent} (z i):= scope_send _ _ _ ((Accent.room _ _ _).2 (ho i))
   intro F K'
   refine ⟨exquisite q' Y χ A f K B z hr rV hV hz,serenade q' Y χ A f K B z hr b' hw rV hV hz hZ,hc ▸ excavation A K B z rV hV hz hk he, heavily q' Y χ A f K B z hr b' hw rV hV hz,funext (fun i=>scored q' Y χ A f K B z (fun i=>(virtue (q i) rV).2) hr rV hV hz hZ i),fun i U=> selfie q' Y χ A f K B z hr rV hV hz hZ U i,fun i U j=>?_⟩
   let A':= A.activities; let k:ℕ→Poly B:=fun t=> Fleece K B z t U; let l(t) (p:ι):ℂ:= (↑(D.hinge (q p).M t U):ℂ)*(stamp (q p)).part (B.fire j)
   have hx(t): (k t).part (B.fire j)=∑ i,l t i:=by
      unfold k Fleece; rw [Accent.quality (fun U t' p=>K t' p t U)]; refine sum_congr rfl fun i _=>?_ ; rw [hQ]; unfold l; rw [← purchase _ hV,Poly.part_smul,Complex.ofReal_mul]; ring
      exact hZ
   have hh(i'):Summable (fun t=> l t i'):=by
       obtain ⟨v,hR⟩:=hd.volume
       obtain ⟨c,h,hB⟩:=hR (q' i')
       exact ((h.2.1.of_norm_bounded («f»:=fun i=> (↑(D.hinge (q i'|>.M) i U):ℂ)) fun t=> ((hB t).2 _).trans (A.p.loMass _ _ (hB t).1))).mul_right _
   change (∑' t:{t // barcode A.activities t=i},k t.val).part (B.fire j)=_
   rw [Poly.share];
   · simp_rw [hx]; rw [Summable.tsum_finsetSum]; apply sum_congr rfl; intro p _; unfold l stamp owl; simp_rw [tsum_mul_right,Poly.part_send]; split_ifs with hp hQ he
     · rw [mul_comm];rfl
     · exact False.elim (hQ hp.symm)
     · exact False.elim (hp he.symm)
     · rw [mul_zero]
     intro p _; exact (hh p).comp_injective Subtype.val_injective
   exact (Towed.repair (flag_K A K B z rV hV hz hr.gas A.p.exponent_pos.le) hV U).2.comp_injective Subtype.val_injective
end YM.Merge.Photo
