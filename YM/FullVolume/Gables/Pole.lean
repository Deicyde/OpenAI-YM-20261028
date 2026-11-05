import YM.FullVolume.Gables.Crown
import YM.FullVolume.Gables.Honors
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}(hG:G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) {Y:Bolt A}
open YM.MergeProof
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Matric Guard
open RG.Shoot Lark Rain Blush Motion FullVolume.Shadow
variable {N p k r d:ℕ}{q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p}{f:ℕ→ℕ}
variable {D:∀ m,Desk G (A.B.a.S.side m p)} (hz:Nest X Y)(hc:∀ i,Boutique.Feeling A i p (D i))(hR:k ≤ r)(ht:d+3≤A.B.a.clock.J r)(B':∀ n,Branch X (q n) (f n) p k)
open Boutique
set_option quotPrecheck false
local notation "F"=> (Labels.frames G).level d
local notation "H"=> fun i=> A.B.bake.make (q i)
namespace Branch
include hG hz hR ht B' b hc
def schedule (m:ℕ)(h:r ≤ m)(i:ℕ): CircleK (A:=A) D d m:= tuition hG b hz hc hR ht (B' i) m h
variable (L':Helmet A p f q k)(hZ:Jams.Wild X.shape A.delay)
local notation "T'"=> schedule hG b hz hc hR ht B'
section channel
variable (m:ℕ)(hr:r ≤ m) {u v:ℕ→ℕ}(hu:Tendsto u atTop atTop)(hv:Tendsto v atTop atTop)(hf:Lark.Near A m (f∘u))(hp:Lark.Near A m (f∘v)) (Q:Gram ((Labels.frames G).level d) (hol G) (D (m+1)) (A.B.a.params (m+1)).columns) (x:(Labels.frames G|>.level d|>.Coeff))
include hu hv hf hp hZ L'
local notation "A'"=>fun n=> T' m hr n
local notation "R₀"=>fun i=> (A' i).leanings Q
local notation "R₁"=>fun i=> (A' i).drift Q
set_option maxHeartbeats 460000 in
lemma skis : Tendsto (fun n=> (R₀ (u n)) x- (R₀ (v n)) x) atTop (𝓝 0) ∧ Tendsto (fun n=> (R₁ (u n)) x- (R₁ (v n)) x) atTop (𝓝 0):= by
    let hU(i:ℕ):m<f (u i):=(hf i).1; let hV(i:ℕ):m<f (v i):=(hp i).1; let he:= ht.trans (A.B.a.fits.mono hr)
    let U:= fun i=>(B' (u i)).steps m (hR.trans hr) (hU i); let V:=fun i=>(B' (v i)).steps m (hR.trans hr) (hV i)
    let A₀ i:= (B' (u i)).notices hc (hR.trans hr) (hU i).le; let A₁ i:=(B' (u i)).notices hc (hR.trans (hr.trans m.le_succ)) (hU i); let T₀ i:= (B' (v i)).notices hc (hR.trans hr) (hV i).le; let T₁ i:=(B' (v i)).notices hc (hR.trans (hr.trans m.le_succ)) (hV i); let E:=(hc m).aboard
    have hx:= Boutique.cams (q:= q∘u) (q':=q∘v) (f:=f∘u) (g:=f∘v) (m:=m) hG b Y U V (fun i=> (B' (u i)).choice) (fun i=> (B' (v i)).choice) he L'.cfront L'.rises hZ hf hp (L'.sails.comp hu) (L'.sails.comp hv) (L'.atlas B' m (hR.trans hr) hu hv hU hV) A₀ T₀ A₁ T₁ hz E (fun i=> ((hc m).carnival i).some) Q x
    -- use eventually congr rew.C.
    refine ⟨hx.1.congr' (Eventually.of_forall fun n=>?_),hx.2.congr' (Eventually.of_forall fun n=>?_)⟩
    · exact congr_arg₂ (·-·) (congr_arg (fun v : (F).Coeff≃ₗ[ℂ] (F).Coeff=>v x) ((B' (u n)).sights hG b hz hc hR ht m hr (hU n) Q).symm) (congr_arg (fun v:(F).Coeff≃ₗ[ℂ](F).Coeff=>v x) ((B' (v n)).sights hG b hz hc hR ht m hr (hV n) Q).symm)
    exact congr_arg₂ (·-·) (congr_arg (fun v: (F).Coeff →ₗ[ℂ] Coin F (hol G) (D m)=> v x) ((B' (u n)).better hG b hz hc hR ht m hr (hU n) Q).symm) (congr_arg (fun v: (F).Coeff→ₗ[ℂ] Coin F (hol G) (D m)=>v x) ((B' (v n)).better hG b hz hc hR ht m hr (hV n) Q).symm)
omit hu hv hf hp
include hr
set_option maxHeartbeats 440000 in
lemma tiers: Matric.Ritzy (T' m hr):=by
    apply ether (A.B.a.params m).columns_ge (A.B.a.params (m+1)).columns_ge (rubies ..)
    intro P u v hu hv x
    have he:= L'.sails.comp hu; have ha:= L'.sails.comp hv
    obtain ⟨n,hn⟩:= eventually_atTop.mp ((follows L'.cfront he m).and ((follows L'.cfront ha m).and ((he.eventually (eventually_gt_atTop m)).and (ha.eventually (eventually_gt_atTop m)))))
    let g(i:ℕ):=i+n; have hg:Tendsto g atTop atTop:= tendsto_atTop_mono (f:=id) (fun i=> Nat.le_add_right ..) tendsto_id
    have h(i):n≤g i:= Nat.le_add_left ..
    obtain ⟨hf,hp⟩:= skis hG b hz hc hR ht B' L' hZ m hr (u:=u∘g) (v:=v∘g) (hu.comp hg) (hv.comp hg) (fun i=>⟨(hn _ (h i)).2.2.1,(hn _ (h i)).1⟩) (fun i=> ⟨(hn _ (h i)).2.2.2,(hn _ (h i)).2.1⟩) P x
    exact ⟨Pith.high n hf,Pith.high n hp⟩
end channel
end Branch
end Bandage
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Branch.tiers
