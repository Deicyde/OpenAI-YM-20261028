import YM.TraceExtension.Shelves.Picnic
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Slate Perfect Turret Margin
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
open Next.UVStress Asymptotics
variable {S: Table C.book} (HE:S.Hierarchy)(hx:CellHyp C F)(hp:F.PointLimits C S) {Y:DiffPlan S}(hf:Y.Derivatives S)
variable {i:Bend}{L:PaceBook C}(hV:Rod t i (𝓛:Filter (ℕ×ℕ)) L)
include P h θ K hM hT ht hb HE hx hp hu hV
lemma merit (a b:Axis) : Fast C.S (fun k=> Storm S L k a b-Storm S L k b a):=by
    let F(i j)(k):= Storm S L k i j - Storm S L k j i
    have he(i' j:Axis)(hp':i'<j):Fast C.S (F i' j):=by
       cases i with
       | none=>
         let Y':= shineT t i' j; have hy a:∀ᶠ k:ℕ in atTop,∀ᶠ p:ℕ×ℕ in b!, Jade (C.path.rep p.1 p.2 k) (H! k) (Y' a k p.1 p.2) a:=hu.mono fun i h=>h.mono fun p hp=>hp.sea.floors _ _ a
         choose L' hl hF using fun a=> microphone P h θ K ht hM hT hb hu HE hx hp (Y' a) a (hy a)
         let A':Unit→Guilds C:=fun _=> Pick t none i' j; let Q:=Sum.elim (fun (_:Unit)=> Pick t none j i') (fun a=> Clutch (Y' a) a)
         let T':Unit→ Logs C 4:=fun _=> L.T i' j; let X:= Sum.elim (fun (_:Unit)=> L.T j i') L'
         have ht a b : Credible (Pick t none a b) b!:= (eager hu none).mono fun i h=> h.mono fun p hp=>hp.peek a b
         let w(k):=∑ a:Axis,Portrait S (L' a) k
         have hξ: Fast C.S (fun k=> Portrait S (L.T i' j) k-(Portrait S (L.T j i') k+w k)):=by
            have hx:= bake_sum P h K hb HE hx hp A' Q T' X (fun _=>hV.pole ..) (fun i=> Sum.rec (fun _=> hV.pole ..) (fun i=> hl i) i) (fun _=> ht ..) (fun i=> Sum.rec (fun _=>ht ..) (fun a=> (hy a).mono (fun i h=>h.mono fun p hp=>hp.heart)) i) (by
                filter_upwards with k; filter_upwards with p; let V:=Meld (t k p.1 p.2).J (H! k); let c(a):= Y' a k p.1 p.2; simp only [A',Q,Fintype.sum_unique,Fintype.sum_sum_type, Sum.elim_inl,Sum.elim_inr]; change V i' j 0= V j i' 0+∑ a:Axis,twig a (c a) 0; rw [add_comm,← Finset.sum_apply (g:=fun a=>twig a (c a))]; exact eq_add_of_sub_eq (show _= _ from congr_fun (Turret.spirit _ _ i' j hp') 0))
            simpa only [Fintype.sum_unique,Fintype.sum_sum_type,T',X,Sum.elim_inl,Sum.elim_inr,w] using! hx
         have hσ : Fast C.S w:= fast_fin (fun a=>Portrait S (L' a)) univ (fun i _=>hF i)
         exact (show (fun k=> Portrait S (L.T i' j) k-(Portrait S (L.T j i') k+w k))+w=F i' j from funext (fun k=>by simp[Storm,F]; abel)) ▸ hξ.add hσ
       | some c=>
         let t':= some c; have hz(a b):= (show Credible (Pick t t' a b) b! from (eager hu t').mono fun i h=> h.mono fun p hp=> hp.peek a b)
         unfold F; simpa only[Fintype.sum_unique] using! bake_sum P h K hb HE hx hp (fun (_:Unit)=>Pick t t' i' j) (fun (_:Unit)=>Pick t t' j i') (fun _=> L.T i' j) (fun _=>L.T j i') (fun _=>hV.pole ..) (fun _=>hV.pole ..) (fun _=> hz ..) (fun _=>hz ..) (by filter_upwards with k;filter_upwards with p; simp only[Fintype.sum_unique]; exact congr_fun (Plint_sym G _ c i' j) 0)
    rcases lt_trichotomy a b with h|h|h; exact he _ _ h; rw [h]; simpa using! (fast_zero (A':=C.S) (E:= S.Field 4)); simpa [F] using! fast_neg (he _ _ h)
end YM.Trace.Shelves
