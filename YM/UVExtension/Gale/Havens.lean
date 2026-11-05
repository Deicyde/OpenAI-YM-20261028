import YM.UVExtension.Gale.Swap
import YM.UVExtension.Harvest.Barn
import YM.UVExtension.Forest.Glue
import YM.MergeProof.North.Bonus
import YM.UVExtension.Case.Expound

/-! Calendared proof thru actual Base+Seed. Can pay more beforeL, delays and Wait. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
-- Can use for other payments. order pressure. Extant reading‐Z every point, Tied Stories mongoose.Beta.
variable (hG:G.Simple){K:KernelChoices}(hK :∀ p : Patch,p.Branches K G){v:Orders}(hp:ThroughLaunch.Draft v)(Q:ℕ→ℕ) (hQ:Monotone Q)(hQ':∀ i,1 ≤ Q i)
include hp hQ hQ' hK hG
lemma uv_havens (he:∀ i,100 ≤ v.supportExp i): ∃ (s:Sheet G)(T:MapPrices)(BudgetVar:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= UVExtension.Case.provider s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J')∧∃ (b:Bandage X BudgetVar K'), ∃ T t, ∃ (N: UVExtension.Spire.Uses X hG) (hv:UVExtension.Upland.Arc X N T) (hk:UVExtension.Mast.Lisle t B.a),
 let S:= UVExtension.Mast.cellar N b hv t hk; let Y:= UVExtension.Mast.centerB N hv; let p:= UVExtension.Mast.roseA N
 Chateau b Q Y t (UVExtension.Mast.Cellar.gate p S) (UVExtension.Orchard.roof N p) ∧  Stock.Tabs B.a ∧ Velour (UVExtension.Mast.Cellar.yard p S) (renal B.a) (mutt B.a Q) (UVExtension.Orchard.roof N p) ∧ UVExtension.Harvest.Barn N b Q S ∧ UVExtension.Cloud.Leases (BudgetVar) X.shape V' ∧ (∀ i j,(X.target i j).rate ≤ -(7/16:ℝ)) := by
    obtain ⟨V,W,hV⟩:= Push.Mark.commissioned G (hol G) (Labels.frames G)
    obtain ⟨s,T,C,K',hP,hv,hC⟩ := uv_footed hG hK v hp Q
    let u:Tariffs:=⟨fun _=>0,fun _=>le_rfl,fun _=>1⟩
    let X:Extra.Multi.Scope:=⟨fun _=>1,fun _=>0,fun _=>1,fun _=>le_rfl,fun _=>Nat.zero_lt_one⟩
    obtain ⟨t,hT,hx⟩:= hC u X; obtain ⟨Kc,L,hL⟩:= oyster s W V hV
    have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
    obtain ⟨z,p,μ,-,-,hμ,hf⟩:= capitalSnow s (UVExtension.Case.actualPay s T) ho
    obtain ⟨A⟩:= Next.Rank.exists_budget G
    refine ⟨s,T,C,K',hP,hv,t⊔ L⊔μ,hT.trans (le_sup_left.trans le_sup_left),fun k ht=>?_⟩
    intro M; obtain ⟨hK,hB⟩:= sup_le_iff.mp ht; obtain ⟨hK,hl⟩:=sup_le_iff.mp hK
    obtain ⟨hi,hk⟩:= hx k hK
    let ξ:Extra.Multi.Tariff:= ⟨1,0,fun _=>le_rfl⟩
    refine ⟨hi,fun P=>?_⟩; obtain ⟨w,hk⟩:= hk P; refine ⟨w,fun w' hw Qt E=>?_⟩
    obtain ⟨F,hk⟩:=hk w' hw Qt E ξ; refine ⟨F,fun θ₀ hθ=>?_⟩; obtain ⟨θ,hθ,hk⟩:= hk _ hθ
    refine ⟨θ,hθ,fun Ht J V0=>?_⟩
    let S:Delays θ:= {V0 with shells:= fun i => max (V0.shells i) (snows P i)}
    obtain ⟨a,hα,hδ⟩:= shower Kc S
    obtain ⟨l,h₁,h₂⟩:= hiss Q a; obtain ⟨q,hφ,hM,h₃⟩:= hk Ht J l
    refine ⟨q, (show DelayLe V0 S from ⟨le_rfl,le_rfl,fun _=>le_max_left ..,le_rfl⟩).trans (hα.trans (h₁.trans hφ)),fun V' h D W0=>?_⟩
    have hw:= hα.trans (h₁.trans (hφ.trans h))
    have hG'(i):0≤ generator G i := by unfold generator; positivity
    obtain ⟨Q',Z,hZ,h₄⟩:= franchise M.K A (generator G) hG' hG (hf k).1 (hf k).2 (fun i=> (hB i).trans (P.large i).need) hμ W0
    refine ⟨Z,⟨hZ.1,hZ.2.2,hZ.2.1⟩,fun U ha hb hc aX hz hD=>?_⟩
    obtain ⟨T,B,hF,hA,R,hR,hR₂,hR₃,hR₄,hR₅,⟨b⟩,⟨h_lei,h_rat⟩,hp,hπ,H₈,⟨S⟩,htx,hF₁,hF₂,f,h₅⟩:=h₃ V' h D U aX hz hD
    refine ⟨T,B,hF,R,⟨hR,hR₂,hR₃,hR₄,hR₅⟩,b,?_⟩
    choose t ht using fun d=> (aX.fits.deep.eventually_ge_atTop (d+3)).exists
    have ht':∀ d,d+3 ≤ B.a.clock.J (t d):=by rw [hF]; exact ht
    obtain ⟨N⟩:= UVExtension.Spire.utilize R hG S
    obtain ⟨Y,hY,hy⟩:= N.exists_bolt
    have hr: UVExtension.Upland.Arc R N Y:=⟨hY,UVExtension.Roads.Unum.commute R (show UVExtension.Roads.Tags.Tax R.shape _ from htx) hF₁ hF₂ hG N,hF₂,hF₁,htx⟩
    have hB':UVExtension.Mast.Lisle t B.a:= UVExtension.Mast.paidLinen t (A:=(Alloy.mk F θ V' D U T B : Alloy M P)) hl ht' hL -- M maybe def D
    refine ⟨Y,t,N,hr,hB',?_⟩; intro H Yc u; let D₁:=UVExtension.Orchard.roof N u
    let F':= UVExtension.Mast.Cellar.gate u H
    let S:= Family.mk (Issue.trail Yc) (hol G) (Labels.frames G) (localSection G) t F'
    have hy := UVExtension.Mast.ridge N hr
    have hx0:= UVExtension.Mast.calibrated N b hr H
    have hc': Spec.Calibrated S:= UVExtension.Mast.Cellar.hardy H (UVExtension.Mast.roseA N)
    have hd N' m p hm:= UVExtension.Mast.cliffs N hr m N' p hm
    have hft d N' p (hm:t d ≤N'):=UVExtension.Mast.charts (S:=N) (R:=b) (U:=H) (a:=hr) d N' p hm -- S:=N shadow
    have hi:= h₂ V' (hφ.trans h)
    have hm:= hF.symm ▸ hA
    have huv:Mix.paidL S:= hm.factorial
    have hp' :∀ i, 100 ≤ (B.a.budget i).supportExponent:=by
       intro i; change _ ≤ (B.a.params i).supportExponent; rw [params_eq B.valid]; change _ ≤ (s.profile (B.a.clock.J i)).supportExponent; rw [hv.prices]; exact he _
    obtain ⟨hx',P',A',hS⟩:= chaletrail Q b (UVExtension.Mast.centerB N hr) t hi hQ hQ' hp hp' hG ht' hy hd hft Kc L V W hV (hδ V' (h₁.trans (hφ.trans h))) hL hl hx0
    have ht : Extraction.Wcmain S:= gardena S (by exact hm.tabs) hx0 hx'.1 hx'.2 hG huv
    obtain ⟨B',HH,hH⟩:= castle R Yc h₅ (C:=S) rfl (fun i=> (le_max_right ..).trans (hw.shells i))
    have hX : Chateau b Q Yc t F' D₁:= ⟨ht',hy,hp,hi, hd,hft, hc',hx0,huv,hx',ht, B',HH,hH,W,P',A',hS, fun g=>rated (B:=B') hx0 hS hG ht g hx' Q' hG' M.O (h₄ S (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) B' hH)⟩
    refine ⟨hX,hm.tabs,exodus hG b Yc Q t F' D₁ hX hp' H₈ hπ,⟨hm.tabs,?_,?_⟩,h_lei,h_rat⟩
    swap
    · refine ⟨_,_,_,hS,fun g=>?_⟩
      obtain ⟨u,T,M,S,x,E,I,hs,hB,-⟩:= rated (B:=B') hx0 hS hG ht g hx' Q' hG' M.O (h₄ S (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) B' hH)
      exact ⟨u,T,M,S,x,E,I,hs,hB⟩
    intro v
    let U':= UVExtension.Mast.Cellar.yard v H; have hv0:= Vintage.YM.PhysicalNext.Repeat.Legato.chaletrail Q b (UVExtension.Orchard.ministry N v) t hi hQ hQ' hp hp' hG ht' (UVExtension.Orchard.housed N v) (fun v' m p hm=> UVExtension.Orchard.routes N v v' p m hm) (UVExtension.Mast.Cellar.freed v H) Kc L V W hV (hδ V' (h₁.trans (hφ.trans h))) hL hl (UVExtension.Mast.Cellar.intakeV v H)
    obtain ⟨hs,P',T',hQ⟩:=hv0; exact ⟨insured hG t ht' (UVExtension.Orchard.housed N v) (UVExtension.Mast.Cellar.gate v H) Kc L V W hV (hδ V' (h₁.trans (hφ.trans h))) hL hl, hs, Vintage.YM.MergeProof.Accent.gardena U' (by exact hm.tabs) (UVExtension.Mast.Cellar.intakeV v H) hs.1 hs.2 hG (show Mix.paidL U' from hm.factorial)⟩
end YM.PhysicalNext.Repeat.Legato
