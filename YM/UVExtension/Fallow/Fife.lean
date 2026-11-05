import YM.UVExtension.Fallow.Micro
import YM.UVExtension.Harvest.Wheat
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth
open Lease Dash Bid MergeProof RelayDifference Opening Local Next.Foundations Source
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(hG:G.Simple)(H:Vintage.YM.Family.Makes C)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D) (hF:Fridge C u ζ) {d N p:ℕ}
open Extra.Histories Motion
variable (V:SectionData (C.labels.level d))(he: V.Sound C.params)(x:ℕ→ C.label d) (Y:∀ N p:ℕ,C.label d≃ₗ[ℂ] C.label d) {X:∀ N p,(C.labels.level d).Index→ C.label d}{E:ℕ→ℝ}
    (hp:MergeProof.Hearth V ζ E Y X)
set_option quotPrecheck false
local notation "ρ"=> Motion.Tally (C.labels.level d)
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "Q"=> (fun a:ρ=> badge T (fun j=> Motion.patch F a.1 (X j p a.2)) p - badge V (fun j=> Motion.patch F a.1 (Size.axis F a.2)) p)
local notation "μ"=> (fun a:ρ=> fun j=> Motion.chips F (x j) a)
local notation "y"=> (fun j=> (C.factory d j p).terminal ((Y j p) (x j)))
local notation "Ζ'"=> thor (d:=d) y p - badge V x p

set_option maxRecDepth 8000 in
private lemma decor_at (H:Labels.Frame G d)(v:H.Index→H.Coeff)(x:H.Coeff): decor H v x=repaint H v x:=by
    simp only [MergeProof.decor, LinearMap.coe_mk, AddHom.coe_mk]
set_option maxRecDepth 4000 in
 
include hp in
lemma engages (p:ℕ) : ∀ᶠ i in atTop,(thor (d:=d) (fun j=> (C.factory d j p).terminal ((Y j p) (x j))) p - badge V x p) i= ∑ k:Motion.Tally (C.labels.level d), (Motion.chips (C.labels.level d) (x i) k) • ((badge T (fun j=> Motion.patch F k.1 (X j p k.2)) p - badge V (fun j=> Motion.patch F k.1 (Size.axis F k.2)) p) i):=by
   filter_upwards [hp.stamped] with i hi
   let T0:=Y i p; let f := IsLinearMap.mk' _ (notationL C.path d _ V i p 0); let g:= IsLinearMap.mk' _ (notationL C.path d _ T i p 0)
   have hz : thor (fun j=> (C.factory d j p).terminal ((Y j p) (x j))) p i=g (T0 (x i)):=by unfold thor Family.O TransferData.cylinder; rw [LinearEquiv.symm_apply_apply]; rfl
   rw [Pi.sub_apply]; rw [hz]
   change g (T0 (x i))-f (x i)= ∑ k:ρ, μ k i • (g (Motion.patch F k.1 (X i p k.2))-f (Motion.patch F k.1 (Size.axis F k.2)))
   simp_rw [smul_sub,Finset.sum_sub_distrib,←map_smul, ←map_sum]; rw [show T0 (x i)=decor F (X i p) (x i) from (hi p).1 (x i),decor_at]
   change _ =g (repaint F (X i p) (x i))- f (repaint F (Size.axis F) (x i)); rw [show repaint F (Size.axis F) (x i)=x i from repaint_same F LinearMap.id (fun x i=>rfl) _]

open Next.Extract Extra.Multi
include hp he H B
set_option maxRecDepth 4000 in
lemma fumes (hv:Rested C x)(a':Motion.Tally (C.labels.level d))(p:ℕ) : Faded C (p:=p) (fun i=> Motion.chips (C.labels.level d) (x i) a' • ((badge T (fun j=> Motion.patch F a'.1 (X j p a'.2)) p - badge V (fun j=> Motion.patch F a'.1 (Size.axis F a'.2)) p) i)):=by
   let hV: (C.localSection d).Sound C.params:= Vintage.YM.Family.Makes.sections H d
   let P : Stem C p:= badge T (fun j=> Motion.patch F a'.1 (X j p a'.2)) p - badge V (fun j=> Motion.patch F a'.1 (Size.axis F a'.2)) p
   let S: ℕ→ ℂ:= fun j=> Motion.chips F (x j) a'
   have hM: Pasted P:= (marked T hV _ p).subH (marked V he _ p)
   have hw:Rested C S:=by
       let a:= Motion.share* orbitCost F; have hp:= (Slow.const (C:=C) a).mul (coords_slow (C:=C) (d:=d) (fun i=> x i.1) hv); refine hp.reduce (Eventually.of_forall fun i=> ?_)
       change ‖S i.1‖ ≤ _; rw [show S i.1= chips F (x i.1) a' from rfl,norm_chips]; exact (mul_le_mul_of_nonneg_left ((BasisCost.coord_le _ _).trans (patch_cost ..)) share_pos.le).trans (le_trans (le_of_eq (mul_assoc _ _ _).symm) (Real.le_norm_self _))
   refine ⟨hM.smulT S,(eventually_ge_atTop (C.ref d)).mono fun m hm ε hZ=>?_⟩
   let k:= Stock.Tabs.chosen C.path.levels 1 B m; have hk:Stock.Tabs.opens C.path.levels 1 m k:= Stock.Tabs.opened ..
   let U (t:ℕ):= cider C ζ d m k*E t; have ht:Rested C U:= (Slow.const (C:=C) _).mul (hp.coined Order.full)
   have hI: ∀ᶠ i in atTop, ‖S i‖ * U i*flight C (-RelayDifference.gamma) (i,p) ≤ ε:= Rested.sinking (w:=fun i=> ‖S i‖*U i) (Slow.mul (Slow.norm hw) ht) (show 0<RelayDifference.gamma by norm_num [RelayDifference.gamma]) hZ p
   filter_upwards [hp.stamped,eventually_gt_atTop k,hI] with i hi hK hI hn
   let L:= center C.S p hn 0; let g:=C.beta i p; have hT: L.rootTest g (P i) ≤ U i * flight C (- RelayDifference.gamma) (i,p):=by
       let b:=X i p a'.2; let K:=a'.1; let A(i'):=(initial V C.path i p i' 0); let f(i'):=(initial T C.path i p i' 0); have hp:= (hi p).2.2 a'.2 k m (hm.trans hk.1) hK hk K hn
       change L.rootTest g (f (Motion.patch F K b) - A (Motion.patch F K (Size.axis F a'.2))) ≤ _; apply le_trans ?_ hp; apply le_of_eq; rw [MergeProof.unitsC,_root_.neg_sub]; rw [show dance K (initial V C.path i p (Size.axis F a'.2) 0-initial T C.path i p b 0)=A (Motion.patch F K (Size.axis F a'.2))-f (Motion.patch F K b) from ?_]
       rw [show dance K (A (Size.axis F a'.2)-f b)=dance K (A (Size.axis F a'.2))-dance K (f b) from funext fun U=>by unfold dance scalar; split <;>simp]; rw [signed_intro C V he, signed_intro C T hV]
   change L.rootTest g (S i • P i) ≤ _; rw [Next.Extract.root_smul]; exact (mul_le_mul_of_nonneg_left hT (norm_nonneg _)).trans ((mul_assoc ..).symm.trans_le hI)
omit hp he B in
lemma faded_sum {ι:Type*}(s:Finset ι)(M:ι→ Stem C p)(h:∀ i∈s,Faded C (M i)): Faded C (∑ i∈s, M i):=by
    induction s using Finset.induction with
    | empty=> rw [Finset.sum_empty]; refine ⟨Pasted.nil,Eventually.of_forall fun i ε h=> Eventually.of_forall fun j k=>?_⟩; change (center C.S p k 0).rootTest (G:=G) (C.beta j p) 0 ≤ ε; rw [show (0: Config G (C.side j p)→ℂ)=(0:ℂ) • (fun _=> 1) from (zero_smul ..).symm, root_smul]; simp [h.le] -- use root_smul
    | insert i s hi ih=> rw [Finset.sum_insert hi]; exact ((h i (mem_insert_self ..)).plus (ih (fun i hi=> h i (mem_insert_of_mem hi))) H)
omit hp he B H in
lemma lateFade {f v:Stem C p}(h : Faded C f)(hp:∀ᶠ i in atTop,f i=v i): Faded C v:=by
    obtain ⟨⟨r,hf⟩, hF⟩:=h; exact ⟨⟨r,(hf.and hp).mono fun i hi=> hi.2 ▸ hi.1⟩, hF.mono fun i hi ε he=> by filter_upwards [hi ε he,hp] with i hx h; unfold bills; rw [← h]; exact hx⟩
lemma drawn (hv:Rested C x)(p:ℕ) : Faded C (thor (d:=d) (fun j=> (C.factory d j p).terminal ((Y j p) (x j))) p - badge V x p):=by
   let P (a':ρ):Stem C p:= (fun i=> Motion.chips (C.labels.level d) (x i) a' • ((badge T (fun j=> Motion.patch F a'.1 (X j p a'.2)) p - badge V (fun j=> Motion.patch F a'.1 (Size.axis F a'.2)) p) i))
   have hM:= faded_sum H Finset.univ P (fun i _=> fumes H B V he x Y hp hv i p)
   apply lateFade hM; filter_upwards [engages V x Y hp p] with i hi; rw [hi]; exact Finset.sum_apply ..
end YM.UVExtension.Fallow
