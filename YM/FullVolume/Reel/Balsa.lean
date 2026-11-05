import YM.FullVolume.Reel.Mold
import YM.FullVolume.Reel.Goals
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q s t' t t₂:ℝ}{N n m d:ℕ}{L:Lyrics R t t}
open UniformSpace
open Luna Graces Mallow Extra.Histories Planned.GuardedAtom Guard
open MergeProof MergeProof.Matric Next.Foundations
set_option maxHeartbeats 420000
set_option synthInstance.maxHeartbeats 130000
set_option quotPrecheck false
variable (H:Chord R N m n t t) (g:G.Simple)(Z:Ticket A N m n)
local notation "s₀"=> A.B.a.S.side m n
local notation "s₁"=> A.B.a.S.side (m+1) n
variable {W:Bid.Worth}{c₁:ℕ→ℝ}(b:Legato.Bandage R c₁ W) (hd:d+3 ≤ A.B.a.clock.J m)(U0:Heading ((Labels.frames G).level d))(hU:EntryP H b hd U0)
local notation "k₀"=> A.B.a.clock.J m
local notation "k₁"=> A.B.a.clock.J (m+1)
local notation "L_"=> D.L k₁
local notation "ℓ"=> ((L_).val:ℂ)^d
local notation "F_"=> (Labels.frames G).level d
local notation "p_"=>localSection G d
local notation "o_"=>Next.Foundations.hol G
local notation "R_"=> Z.val.val
local notation "O_"=> H.moment Z.val
local notation "κ"=> A.B.a.clock.forcedAllowance m
local notation "va"=> authors A.B.a m
local notation "D_"=> Orchard.portal H Z.val
-- inspect portal namespace
namespace Splint
open Graces Mallow MergeProof.Menu Circlet Blush Lotus Orchard
variable {S: Set Wing}
variable (hx:Orchard.Visit H Z.val)
include g b hd
local notation "D0s"=>portal H Z.val
local notation "u'"=> Real.sqrt κ
local notation "p0"=> A.B.a.budget m
local notation "p1"=> A.B.a.budget (m+1)
local notation "ST"=> (Labels.frames G).level d
local notation "n'"=> A.B.a.S.side (m+1) n
local notation "ρ"=> Doors.rate L_
set_option quotPrecheck false
open YM.Source Labels
open YM.MergeProof.Matric Next.Foundations
open YM.UVNext.CouplingReset
variable {I:Type}[Fintype I]
include g hd
open Cub
set_option maxHeartbeats 480000 in
private lemma sounded {Z':Chord.Flight A N m n}(hx:Visit H Z') (p:Cloud Z'.val) (q:I→Cloud Z'.val) (a:I→ℝ)(h:Merge.Grouped p.live a (fun i=>(q i).live))(h':Merge.Grouped p.pale a (fun i=>(q i).pale))(he:∃ e t,Graces.Effort (p_) (H.moment Z') o_ (Blush.scope (H.sight Z') p 0) (Luna.plot H Z' ℓ F_ p) 0 va κ e t)(ht:∀ i,∃ a t,Graces.Effort (p_) (H.moment Z') o_ (Blush.scope (H.sight Z') (q i) 0) (Luna.plot H Z' ℓ F_ (q i)) 0 va κ a t): moi H Z' p d= ∑ i,(a i:ℂ) • moi H Z' (q i) d:=by
    -- use grouping at real springs. Scope defeq unlike values. NO movement data from candidate chosen across V, just certificate
    obtain ⟨x,y,K',T,t,hp,hQ,hV⟩:=hx
    obtain rfl:Z'=Cryst.flown T t:=Subtype.ext hV
    let Xv:=Cryst.flown T t; let Rv:= H.moment Xv; let O(v:Cloud (K' t)):=scope (H.sight Xv) v 0
    have hu(i):O (q i)=O p:=by
       let F:= H.sight Xv; have hZ : Daisy.Charity.locus (q i).live F (0:Site s₀)=Daisy.Charity.locus p.live F 0:=by funext j; unfold Daisy.Charity.locus Daisy.Charity.speaks; rw [h.turn i]
       unfold O Blush.scope; unfold F at hZ; rw [hZ]
    let Ξ(x:Cloud (K' t)):= plot H Xv ℓ F_ x
    have hh(z'): Ξ z'= Cub.innerT T t z' (d:=d):= eye H T t hp hQ z'
    obtain ⟨av,bv,hF⟩:=he; choose t' s' hK using ht
    have hz(v:Cloud (K' t)){a v':ℝ}(h:Graces.Effort (p_) Rv o_ (O v) (Ξ v) 0 va κ a v'): Matric.Have Rv (Ξ v) (O v) (p_) o_ va κ (Real.sqrt κ):=by obtain ⟨x,y,t,hv,h,-⟩:=h; exact ⟨hv,x,y,t,h⟩
    have h2(w:Cloud (K' t)): Blush.scope (houseS T t) w (0:Site s₀)=O w:=rfl
    unfold moi codY; change coda p_ o_ 0 (O p) (Ξ p) Rv = ∑ i,(a i:ℂ) • coda p_ o_ 0 (O (q i)) (Ξ (q i)) Rv; simp_rw [hu]
    refine moldW (keeperF H g Xv) _ ((Apse.savory g H Xv).valid) (Real.sqrt_pos.mpr (forcedPos ..)) (livelyCard b.clock (?_: d≤ A.B.a.clock.J m)) (hz p hF) (fun i=> hu i ▸ hz _ (hK i)) ?_
    · omega
    · intro i; simp_rw [hh]; exact Cub.colors H.paid T t b.r a h h' (fun j=>show Blush.scope _ _ _ = _ from hu _) i
include hx
omit [Fintype I]
private lemma regSubF {s:Support (A.B.a.S.side (m+1) n)} {f f':Config G (A.B.a.S.side (m+1) n)→ℂ}(hf: RegFit Z.val.val 0 d (hol G) s f) (hg:RegFit Z.val.val 0 d (hol G) s f'): RegFit Z.val.val 0 d (hol G) s (f-f'):=by
    let h:=Reads (Next.Foundations.hol G) 0 s (0:Labels.Label G d); have hh:= reads_sub ((reads_null_iff ..).mpr ⟨hf.unit_null,hf.proj⟩) ((reads_null_iff ..).mpr ⟨hg.unit_null,hg.proj⟩); rw [sub_zero] at hh
    obtain ⟨ha,hb⟩:= (reads_null_iff ..).mp hh; exact ⟨regular_sub hf.smooth hg.smooth,hf.anchor,ha,hb⟩
variable (i:ℕ){f f':Config G (A.B.a.S.side (m+1) n)→ℂ}{w w':ℝ}
lemma coolE (hC:RegFit Z.val.val 0 d (Next.Foundations.hol G) (mapSeat i) f)(he:Z.val.val.p.supBounds 0 (mapSeat i) f w)(hC':RegFit Z.val.val 0 d (Next.Foundations.hol G) (mapSeat i) f')(he':Z.val.val.p.supBounds 0 (mapSeat i) f' w'): regMoney H Z.val Z.property i (f-f') d=regMoney H Z.val Z.property i f d-regMoney H Z.val Z.property i f' d:=by
   let E':= Z.val; let P:=E'.val; let s:= mapSeat (n:=s₁) i; let q:= f-f'
   have hp :=regSubF H g Z b hd hx hC hC'; have hP : P.p.supBounds 0 s (f-f') (w+w'):= Next.Foundations.bound_sub hC.smooth hC'.smooth he he'
   obtain ⟨ha,Hx,h1,hA⟩:= fitting H g Z.val Z.property i f d hC he; obtain ⟨hb,Hy,h2,hB⟩:= fitting H g Z.val Z.property i f' d hC' he'; obtain ⟨hc,Hz,h3,hD⟩:=fitting H g Z.val Z.property i q d hp hP
   let u(F:Config G s₁→ℂ):=sInf {v| P.p.supBounds 0 s F v}
   let X0:=Blush.float P 0 s (spot _ _) f (u f) hC.smooth ha Z.property; let X1:=Blush.float P 0 s (spot _ _) f' (u f') hC'.smooth hb Z.property; let X2:=Blush.float P 0 s (spot _ _) q (u q) hp.smooth hc Z.property
   let M:Bool→Cloud P:=fun i=>if i then X0 else X1; let z':Bool→ℝ:=fun i => if i then 1 else -1
   have hG : Merge.Grouped X2.live z' (fun i=>(M i).live):=by
       have hi: (fun i=>(M i).live)=fun i:Bool=> if i then X0.live else X1.live:= funext fun i=>by cases i<;>rfl
       rw [hi]; refine Cub.purport ?_ ?_ ?_;rfl;rfl; funext j
       have hh:= congr_fun (map_sub (Local.maskLinear P.p.threshold s) f f') j; exact (congr_arg Complex.reCLM hh).trans (map_sub Complex.reCLM _ _)
   have hG' : Merge.Grouped X2.pale z' (fun i=>(M i).pale):=by
       have hi: (fun i=>(M i).pale)=fun i:Bool=> if i then X0.pale else X1.pale:= funext fun i=>by cases i<;>rfl
       rw [hi]; refine Cub.purport ?_ ?_ ?_;rfl;rfl; funext j
       have hh:= congr_fun (map_sub (Local.maskLinear P.p.threshold s) f f') j; exact (congr_arg Complex.imCLM hh).trans (map_sub Complex.imCLM _ _)
   have hx' : P.p=(A.B.a.budget (m+1)):=Z.val.property.1.point
   have ht:= sounded H g b hd hx X2 M z' hG hG' ⟨_,_,RegX H g b hd _ _ _ hx'.symm _ (spot _ _) hc hp Z.property⟩ (fun t=> by cases t; exact ⟨_,_, RegX H g b hd _ _ _ hx'.symm _ (spot _ _) hb hC' Z.property⟩; exact ⟨_,_, RegX H g b hd _ _ _ hx'.symm _ (spot _ _) ha hC Z.property⟩)
   change regMoney _ _ _ _ q d = _; rw [h1,h2,h3]; rw [Fintype.sum_bool] at ht; simp only [z',M,if_true,Bool.false_eq_true,if_false,Complex.ofReal_neg,Complex.ofReal_one,one_smul,neg_smul] at ht; rw [sub_eq_add_neg]; exact ht
lemma coolK (hC:SlotFit Z.val.val 0 i f)(hC':SlotFit Z.val.val 0 i f')(hx':∀ U, ‖f U‖≤ w)(hh:∀ U,‖f' U‖≤w'): inkMoney H Z.val i (f-f') d = inkMoney H Z.val i f d - inkMoney H Z.val i f' d:=by
    let P0:=Z.val; let P:=P0.val; let S:=inkMoney H Z.val i
    have hZ : S 0 d=0:=dif_neg (fun ⟨_,h,_⟩=>h rfl)
    have hz:P.p=(A.B.a.budget (m+1)):=Z.val.property.1.point;
    change S (f-f') d= S f d-S f' d
    by_cases he:f=f';rw [he,sub_self,hZ,sub_self]
    by_cases hv : f'=0; rw [hv,hZ,sub_zero,sub_zero]
    have hH:=slotSub hC hC'; let q:= f-f'; have ht (U): ‖q U‖≤ w+w':= (norm_sub_le ..).trans (add_le_add (hx' U) (hh U))
    obtain ⟨C0,_,hU,hR⟩:= fitted H g Z.val i q d hH (sub_ne_zero.mpr he) ht
    obtain ⟨C1,_,hV,hR'⟩:= fitted H g Z.val i f' d hC' hv hh
    let cX(f: Config G s₁→ℂ):= sInf {y| ∀ V,‖f V‖≤y}; let U:=fan P 0 i q (cX q) C0 hH; let V:=fan P 0 i f' (cX f') C1 hC'; let F(u:Cloud P):=moi H Z.val u d
    have hu: S q d= F U:=hU; have hV: S f' d= F V:=hV
    have he0:= heavyX H g b hd Z.val i q _ hH (sub_ne_zero.mpr he) C0 hz.symm
    have he1:= heavyX H g b hd Z.val i f' _ hC' hv C1 hz.symm
    by_cases hf:f=0
    · have hr(t:ℂ→L[ℝ]ℝ)(i): t (q i)= -1*t (f' i):=by simp [q,hf]
      let a:Unit→ℝ:=fun _=>-1; let M:Unit→Cloud P:=fun _=> V
      have hh(p p':Lotus.Leaf P)(h:p'.turn=p.turn)(he:∀ V,p.ingredient V=-1 * p'.ingredient V): Merge.Grouped p a (fun _=>p'):=⟨fun _=> h,Summable.of_finite,fun V=> by simpa only [a,he,Fintype.sum_unique] using hasSum_fintype (fun _:Unit => -1*p'.ingredient V)⟩
      have hG:Merge.Grouped U.live a (fun i=>(M i).live):= hh _ _ rfl fun V=>hr Complex.reCLM V; have hG':Merge.Grouped U.pale a (fun i=>(M i).pale):= hh _ _ rfl fun V=>hr Complex.imCLM V
      have hx0:= sounded H g b hd hx U M a hG hG' ⟨_,_,he0⟩ (fun _=>⟨_,_,he1⟩)
      have hv: S f d=0:=by rw [hf,hZ]
      change S q d= _; rw [hu,hv,hV]; simpa [M,F,a] using hx0
    obtain ⟨C,_,hA,hS'⟩:= fitted H g Z.val i f d hC hf hx'
    let W:=fan P 0 i f (cX f) C hC; let M:Bool→Cloud P:=fun i=> if i then W else V; let a:Bool→ℝ:=fun i=> if i then 1 else -1
    have hG: Merge.Grouped U.live a (fun i=>(M i).live):=by
       have hi: (fun i=>(M i).live)=fun i:Bool=> if i then W.live else V.live:= funext fun i=>by cases i<;>rfl
       rw [hi]; refine Cub.purport ?_ ?_ ?_;rfl;rfl; funext j
       exact map_sub Complex.reCLM _ _
    have hG' : Merge.Grouped U.pale a (fun i=>(M i).pale):=by
       have hi: (fun i=>(M i).pale)=fun i:Bool=> if i then W.pale else V.pale:= funext fun i=>by cases i<;>rfl
       rw [hi]; refine Cub.purport ?_ ?_ ?_;rfl;rfl; funext j
       exact map_sub Complex.imCLM _ _
    have he2:=heavyX H g b hd Z.val i f _ hC hf C hz.symm
    have ht:= sounded H g b hd hx U M a hG hG' ⟨_,_,he0⟩ (fun i=> by cases i; exact ⟨_,_,he1⟩; exact ⟨_,_,he2⟩)
    rw [show S (f-f') d= F U from hu, hV, show S f d=F W from hA]; rw [Fintype.sum_bool] at ht; simp only [a,M,if_true,Bool.false_eq_true,if_false,Complex.ofReal_neg,Complex.ofReal_one,one_smul,neg_smul] at ht; rw [sub_eq_add_neg]; exact ht
end Splint
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Splint.coolK
