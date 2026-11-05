import YM.OPE.Replicas.Pass
import YM.MergeProof.North.Bourse
import YM.OPE.Columns.Buy

/-!
# Expose triangular transfer & re-announcement supplies

Strengthening of YM/MergeProof/North/Bourse.lean; most of the proof is
the *same* construction. Adapted from that file, retaining the baseline.
-/
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
lemma bally_columns (he:∀ i,100 ≤ v.supportExp i): ∃ (s:Sheet G)(T:MapPrices)(Y:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.currency s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J')∧∃ (b:Bandage X Y K'), ∃ T t S D,Chateau b Q T t S D ∧ Stock.Tabs B.a ∧ (∀ d N p, t d ≤ N → Bandage.StackedColumns T (S d N p) (t d) K') ∧ Fridge (Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S) (far B.a) (fly B.a) ∧ Velour (Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S) (renal B.a) (mutt B.a Q) D ∧ VelourArity (Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S) (renal B.a) (mutt B.a Q) D := by
    obtain ⟨V,W,hV⟩:= Push.Mark.commissioned G (hol G) (Labels.frames G)
    obtain ⟨s,T,C,K',hP,hv,hC⟩ := ruese hG hK v hp Q
    let u:Tariffs:=⟨fun _=>0,fun _=>le_rfl,fun _=>1⟩
    let X:Extra.Multi.Scope:=⟨fun _=>1,fun _=>0,fun _=>1,fun _=>le_rfl,fun _=>Nat.zero_lt_one⟩
    obtain ⟨t,hT,hx⟩:= hC u X; obtain ⟨Kc,L,hL⟩:= oyster s W V hV
    have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
    obtain ⟨z,p,μ,-,-,hμ,hf⟩:= capitalSnow s (ThroughLaunch.bearing s T) ho
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
    obtain ⟨T,B,hF,hA,R,hR,hR₂,hR₃,hR₄,hR₅,⟨b⟩,hp,hπ,H₈,f,h₅⟩:=h₃ V' h D U aX hz hD
    refine ⟨T,B,hF,R,⟨hR,hR₂,hR₃,hR₄,hR₅⟩,b,?_⟩
    choose t ht using fun d=> (aX.fits.deep.eventually_ge_atTop (d+3)).exists
    have ht':∀ d,d+3 ≤ B.a.clock.J (t d):=by rw [hF]; exact ht
    obtain ⟨Y,hy⟩:=Graces.winnow hG R
    obtain ⟨D₁,F',hx0,hc',hd,h_tt⟩:= squad_columns hG b Y hy t ht'
    let S:=Family.mk (Issue.trail Y) (hol G) (Labels.frames G) (localSection G) t F'
    have hi:= h₂ V' (hφ.trans h)
    have hm:= hF.symm ▸ hA
    have huv:Mix.paidL S:= hm.factorial
    have hp' :∀ i, 100 ≤ (B.a.budget i).supportExponent:=by
       intro i; change _ ≤ (B.a.params i).supportExponent; rw [params_eq B.valid]; change _ ≤ (s.profile (B.a.clock.J i)).supportExponent; rw [hv.prices]; exact he _
    obtain ⟨hx',P',A',hS⟩:= chaletrail Q b Y t hi hQ hQ' hp hp' hG ht' hy hd (fun d N p hn => (h_tt d N p hn).1) Kc L V W hV (hδ V' (h₁.trans (hφ.trans h))) hL hl hx0
    have ht : Extraction.Wcmain S:= gardena S (by exact hm.tabs) hx0 hx'.1 hx'.2 hG huv
    obtain ⟨B',HH,hH⟩:= castle R Y h₅ (C:=S) rfl (fun i=> (le_max_right ..).trans (hw.shells i))
    have hX : Chateau b Q Y t F' D₁:= ⟨ht',hy,hp,hi, hd,fun d N p hn => (h_tt d N p hn).1, hc',hx0,huv,hx',ht, B',HH,hH,W,P',A',hS, fun g=>rated (B:=B') hx0 hS hG ht g hx' Q' hG' M.O (h₄ S (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) B' hH)⟩
    have h_fr : Fridge S (far B.a) (fly B.a) :=
      freezes hG (fun N p=>⟨Planned.GuardedAtom.Guard.Keeper.sufficient (hy.born N p)⟩) (fun i => by
        change step_cost (B.a.params i) ≤ B.a.clock.hatBeta i
        rw [params_eq B.valid]
        exact (hδ V' (h₁.trans (hφ.trans h)) _ _ (step_paid _ i) _ (B.valid.pays i)).1)
    exact ⟨Y,t,F',D₁,hX,hm.tabs,fun d N p hn => (h_tt d N p hn).2,h_fr,exodus hG b Y Q t F' D₁ hX hp' H₈ hπ, exodusN hG b Y Q t F' D₁ hX hp' H₈ hπ⟩
end YM.PhysicalNext.Repeat.Legato
