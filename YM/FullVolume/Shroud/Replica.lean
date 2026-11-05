import YM.FullVolume.Shroud.Parks
import YM.FullVolume.Shroud.Homer
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Shroud
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Source Labels Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Next.Foundations Push Precision WilsonStartup
open UVNext.CouplingReset UVNext.PricedKernels Ovens Ovens.Pipes Progress.DirectedRecipe BudgetPoint Extra.Iteration
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side} {P:BudgetPoint}{D:PathData G}{c:Clip}{σ C Λ b w:ℝ}
open Quake Well
namespace Muslin
abbrev Hearts (n: Side):= {x: Support n// x.Nonempty}
variable (R:Rep G n)
set_option quotPrecheck false
local notation "A"=> R.activities
local notation "V"=> R.p.threshold
def dyed (G:Gauge) (x:Hearts n): ForcedAddress G n:= ⟨Finset.univ,x.val,x.property,Finset.subset_univ _,fun _=>True⟩
def song (t:ℝ)(U:Config G n):ℝ:= (Real.exp (-t* Well.leg R U) -1)*(A).gas R.p U -- parser

def chart (t:ℝ)(x:Hearts n)(U:Config G n):= if flags R.p.threshold U=x.val then song R t U else 0
variable (t:ℝ) (h:R.Lawful σ C Λ b w)
abbrev mood := numbering (ℕ⊕ Graft n)
abbrev guardK := numbering (ℕ⊕Hearts n)
def stitchE (i:ℕ⊕Graft n):= i.elim (A).E (grain R.path R.clip t)
def stitchK (i:ℕ⊕Hearts n):= i.elim (A).K (chart R t)
def stitch : Activities G n:= ⟨Sum.elim (A).reg herb ∘ mood, Sum.elim (A).forced (dyed G) ∘ guardK,stitchE R t ∘ mood,stitchK R t ∘ guardK⟩
local notation "S"=> stitch R t
lemma es (i): (S).reg ((mood (n:=n)).symm i)= Sum.elim (A).reg herb i:=by unfold stitch; simp
lemma es' (i): (S).E ((mood (n:=n)).symm i)= Sum.elim (A).E (grain R.path R.clip t) i:=by unfold stitch; simp;cases i<;>rfl
lemma ks (i): (S).forced ((guardK (n:=n)).symm i)= Sum.elim (A).forced (dyed G) i:=by unfold stitch; simp
lemma ks' (i): (S).K ((guardK (n:=n)).symm i)= Sum.elim (A).K (chart R t) i:=by unfold stitch; simp;cases i<;>rfl
variable (hp : Decent R.clip R.p)
include h hp
lemma estate (hk:n.val≥4): S|>.RegularFamily R.p :=by
    obtain ⟨b,hB,hT⟩:=Quake.honorary (n:=n) R.path R.clip h.paths hp t; constructor <;> intro i <;> obtain ⟨i,rfl⟩:= (mood (n:=n)).symm.surjective i
    · rw [es,es']; cases i; exact h.labels.regular.smooth _; exact (hB _).1
    · rw [es']; cases i; exact h.labels.regular.at_flat _; exact (hB _).2.2
    rw [es,es']; cases i; exact h.labels.regular.vanish _; intro hv; exact False.elim (nonwrap _ hk hv)
lemma budgets : S|>.EBound R.p (b+costs G n R.p t R.clip σ C):=by
    obtain ⟨u,hu,hU⟩:= Quake.honorary (n:=n) R.path R.clip h.paths hp t; obtain ⟨q,hq,ht⟩:= h.labels.boundE; let f:= Sum.elim q u; let e:=mood (n:=n); let g:=f∘e; have hf i:g (e.symm i)=f i:=congr_arg f (e.apply_symm_apply i)
    refine ⟨g,fun i=>?_,fun x=>?_⟩
    · obtain ⟨i,rfl⟩:=e.symm.surjective i; unfold e; rw [es, es',show g ((mood (n:=n)).symm i)=f i from hf i]; cases i;exact hq _; exact (hu _).2.1
    let v i:= if ((S).reg i).site=x then R.p.mass ((S).reg i).support (g i) else 0; have hh:SumBudget (fun i=> v (e.symm i)) (b+ costs G n R.p t R.clip σ C):=by
       unfold v; simp_rw [hf]; dsimp only [e]; simp_rw [es]; apply Extra.Iteration.Cost.sum (show _ from ht x); exact Extra.Multi.Budget.mono hU (fun i=>by split; exact hU.1 _;rfl) (fun i=>by split; exact le_rfl; exact hU.1 i) le_rfl -- if syntax
    exact transfer_budget e.symm.toEmbedding (fun i=>rfl) (fun i hi=> False.elim (hi (e.symm.surjective i))) hh
omit hp
lemma strands : S|>.ForcedFamily R.p:=by
   have hv := h.labels.forced
   constructor <;> intro i <;> obtain ⟨i,rfl⟩:= (guardK (n:=n)).symm.surjective i
   · rw [ks']; rcases i with i|i
     · exact hv.sym i
     intro k U; change chart R t i (gauge k U)= _; unfold chart song; simp only [Sum.elim_inr,gauge_flags,Well.axial h k U,Well.oiled h k U]
   · rw [ks]; cases i; exact hv.symtest _; exact fun _ _=>Iff.rfl
   · rw [ks']; cases i; exact hv.meas _; refine Measurable.ite (flags_measurable_eq ..) ((((Real.continuous_exp.measurable.comp (measurable_const.mul (Push.BetaTransport.kinetic_env h.paths).meas)).sub measurable_const).mul (Activities.gas_measurable hv))) measurable_const
   · rw [ks]; cases i; exact hv.meas_test _; exact MeasurableSet.univ
   · rw [ks,ks']; cases i
     · exact hv.reads _
     intro U V' hu hv; rw [show U=V' from funext (fun i=> hu i (Finset.mem_univ _) (Finset.mem_univ _))]
   · rw [ks]; cases i; exact hv.reads_test _; exact fun U V' he hv=>rfl
   · rw [ks,ks']; rcases i with i|i; exact hv.permit _
     intro U hu; have hx: flags (V) U=i.val:=not_not.mp (fun h=>hu (show chart R t i U=0 from if_neg h)); exact ⟨(Finset.univ_inter _).trans hx,trivial⟩
-- perms.
variable (m: Signed) (x : Site n)(he:R.activities.Moves m x)
local notation "D"=> Seat.move m x
open Motion MergeProof
omit h in
def rest : Equiv.Perm (Hearts n) := by
    let T: Equiv.Perm (Support n):= sky (m,false) x
    refine ⟨fun i=> ⟨T i.val, (by unfold T; rw [shading]; exact Finset.Nonempty.image i.property _)⟩,fun i=> ⟨T.symm i.val,?_⟩,fun i=>Subtype.ext (T.symm_apply_apply i.val),fun i=>Subtype.ext (T.apply_symm_apply i.val)⟩ -- need Nonempty_image membership syntax.(A).Replace
    apply Finset.nonempty_iff_ne_empty.mpr; intro H; apply i.property.ne_empty; exact (T.apply_symm_apply i.val).symm.trans ((congr_arg T H).trans (by simp [T,sky]))
omit h in
private lemma journey (p:Hearts n): (rest m x p).val= p.val.image (affine m x):= shading ..
omit h
include he
lemma carve (q:Hearts n) (U:Config G n): chart R t (rest m x q) U = chart R t q (pull m x U):=by
    unfold chart song; rw [journey, mirrors m x U,Well.defended _ _ he]; have h: flags (V) U=(q.val.image (affine m x)) ↔ flags V (pull m x U)=q.val:=by rw [← Work.H03.flags_send m x]; exact (Finset.image_injective (Push.Local.turnSites m x).injective).eq_iff
    simp only [h]
lemma involves : Nonempty ((S).Moves m x):=by
    let k:= guardK (n:=n); let e:= mood (n:=n); let B:Hearts n≃Hearts n:=rest m x; let U:Equiv.Perm (Graft n):=D|>.prodCongr (Equiv.refl _); let f:=Equiv.sumCongr he.kp B; let b:= Equiv.sumCongr he.ep U
    let E:=e.trans (b.trans e.symm);let K:=k.trans (f.trans k.symm)
    have hp i:E (e.symm i)=e.symm (b i):=by simp [E]
    have hk i:K (k.symm i)=k.symm (f i):=by simp [K]
    have hw:(Finset.univ: Support n).image (affine m x)=Finset.univ:= everywhere (m,x)
    refine ⟨E,K,fun i=>?_ ,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_⟩ -- Nonempty angle
    · obtain ⟨i,rfl⟩:=e.symm.surjective i; rw [hp]; unfold e; rw [es R t,es R t]; cases i; exact he.reg_site _;rfl
    · obtain ⟨i,rfl⟩:=e.symm.surjective i; rw [hp]; unfold e; rw [es,es];cases i; exact he.reg_support _;exact hw.symm
    · obtain ⟨i,rfl⟩:=k.symm.surjective i; rw [hk]; unfold k; rw [ks,ks]; cases i; exact he.forced_support _; exact hw.symm
    · obtain ⟨i,rfl⟩:=k.symm.surjective i; rw [hk]; unfold k; rw [ks,ks]; cases i; exact he.forced_inventory _; exact journey ..
    · obtain ⟨i,rfl⟩:=k.symm.surjective i; intro U; rw [hk]; unfold k; rw [ks,ks]; cases i; exact he.forced_tests ..; rfl
    · obtain ⟨i,rfl⟩:=e.symm.surjective i; intro V';rw [hp]; unfold e; rw [es',es']; rcases i with i|i; exact he.valuesE ..
      change grain R.path R.clip t (U i) V'=grain R.path R.clip t i _; simp_rw [grain]; change (t*_)*_=(t*_)*_; exact congr_arg ((t*factor)*·) (congr_arg (read R.path R.clip i.2 (0:Site n)) (congr_fun (Seat.view_move _ m x) V'))
    obtain ⟨i,rfl⟩:= k.symm.surjective i; intro V'; rw [hk]; unfold k; rw [ks',ks']; cases i; exact he.valuesK ..; exact carve R t m x he _ V'
end Muslin
end YM.FullVolume.Shroud
#print axioms YM.FullVolume.Shroud.Muslin.strands
#print axioms YM.FullVolume.Shroud.Muslin.involves
#print axioms YM.FullVolume.Shroud.Muslin.estate
#print axioms YM.FullVolume.Shroud.Muslin.budgets
