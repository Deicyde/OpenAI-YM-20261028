import YM.TraceExtension.Shelves.Final
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
section small
variable {E:Type*}[NormedAddCommGroup E] {A':Schedule}
lemma fast_fin {V:Type*}(f:V→ℕ→E)(s:Finset V)(hp:∀ i∈s,Fast A' (f i)): Fast A' (fun k=>∑ i∈s,f i k):=by rw [show (fun k=>∑ i∈s,f i k)=∑ i∈s,f i from funext fun _=>(Finset.sum_apply ..).symm]; exact fast_sum f s hp
lemma fast_neg {f:ℕ→E}(hp:Fast A' f): Fast A' (fun k=> -f k):=⟨hp.choose,hp.choose_spec.1,hp.choose_spec.2.neg_left⟩
lemma fast_zero: Fast A' (fun _=>(0:E)):= ⟨-1,by norm_num,isBigO_zero ..⟩
end small
include P h hb K HE hx hp
lemma bake_sum{V V': Type}[Fintype V][Fintype V'](f:V→ Guilds C)(g:V'→ Guilds C)(L:V → Logs C d)(Q:V'→ Logs C d)(hl:∀ i,Loan (f i) b! (L i))(hq:∀ i,Loan (g i) b! (Q i))(he:∀ i,Credible (f i) b!)(hh:∀ i,Credible (g i) b!)(hy:∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ×ℕ in (𝓛:Filter (ℕ×ℕ)),∑ j,f j k i.1 i.2=∑ j,g j k i.1 i.2) : Fast C.S (fun k=> (∑ j, Portrait S (L j) k)-(∑ j, Portrait S (Q j) k)):=by
    let Z(v: V⊕V'):= Sum.elim (fun _=> (1:ℝ)) (fun _=> - (1:ℝ)) v; let L':= Sum.elim L Q
    have ht:= fumes P h K hb HE hx hp Z (Sum.elim f g) L' (fun i=> Sum.rec (fun i=>hl i) (fun i=>hq i) i) (fun i=> match i with|.inl i=>he i|.inr i=>hh i) (by filter_upwards [hy] with k hp; filter_upwards [hp] with i hi; rw [Fintype.sum_sum_type]; simp [Z,hi])
    simpa only [Fintype.sum_sum_type,Sum.elim_inl, Sum.elim_inr, Z, L',one_smul,neg_one_smul, Finset.sum_neg_distrib, sub_eq_add_neg] using ht
lemma bake_zero{V: Type}[Fintype V](f:V→ Guilds C)(L:V → Logs C d)(hl:∀ i,Loan (f i) b! (L i))(he:∀ i,Credible (f i) b!)(hy:∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ×ℕ in (𝓛:Filter (ℕ×ℕ)),∑ j,f j k i.1 i.2=0): Fast C.S (fun k=>∑ j,Portrait S (L j) k):=by
    have ht:= fumes P h K hb HE hx hp (fun _=>1) f L hl he (by simpa only[one_smul] using hy); simp_rw [one_smul] at ht; exact ht
abbrev Storm(S:Table C.book)(L:PaceBook C)(k:ℕ):=fun i j=> Portrait S (L.T i j) k
abbrev StormP(C:Family G)(L:PaceBook C)(k:ℕ):= fun i j=> (L.T i j).x k
include hu
lemma sky (i:Bend)(L:PaceBook C)(hV:Rod t i (𝓛:Filter (ℕ×ℕ)) L)(b:Axis): Fast C.S (fun k=>(∑ j, Portrait S (L.Zp j b) k)- Portrait S (L.Z b) k):=by
   have ht':= eager hu i; let u:= fun a=> PeakPart t i a b; let Y'(_v: Unit):= PeakG t i b; simpa only[Fintype.sum_unique] using! bake_sum P h K hb HE hx hp u Y' (fun j=> L.Zp j b) (fun _=>L.Z b) (fun j=> hV.bare j b) (fun _=>hV.bend b) (fun j=>ht'.mono (fun i h=>h.mono fun x hx=>hx.piece j b)) (fun _=>ht'.mono (fun i h=>h.mono fun x hx=>hx.full b)) (by filter_upwards with k; filter_upwards with x; simp only [Fintype.sum_unique];rfl)
omit hu
variable {x: Bend}{L:PaceBook C}
abbrev pulseN (t:Tickets C)(a:Axis): Crux C:=fun k N p=> pluck (rim (H! k)) (t k N p).J a
abbrev shineT (t:Tickets C)(b c a:Axis): Crux C:=fun k N p=> pluckD (rim (H! k)) (t k N p).J b c a
include hu ht hM hT θ
lemma trace_sf(hV:Rod t none (𝓛:Filter (ℕ×ℕ)) L): Fast C.S (fun k=> ∑ j:Axis, Storm S L k j j):=by
   let v:= pulseN t; have hp' j : ∀ᶠ k in atTop,∀ᶠ i:ℕ×ℕ in b!, Jade (C.path.rep i.1 i.2 k) (H! k) (v j k i.1 i.2) j:=hu.mono (fun k h=> h.mono fun i hi=>hi.sea.flames j)
   choose L' hl hF using fun j=> microphone P h θ K ht hM hT hb hu HE hx hp (v j) j (hp' j)
   let X:=fun i=> Pick t none i i; let T' i:= Clutch (v i) i;let y(k):=∑ j:Axis, Portrait S (L.T j j) k; let y'(k):= ∑ j:Axis, Portrait S (L' j) k
   have hξ: Fast C.S (fun k=> y k-y' k):=bake_sum P h K hb HE hx hp X T' _ L' (fun i=>hV.pole i i) hl (fun j=>(eager hu none).mono fun i h=>h.mono fun p hp=>hp.peek j j) (fun j=> (hp' j).mono fun i h=>h.mono fun p hp=>hp.heart) (by
        filter_upwards with k;filter_upwards with p; let Q:=t k p.1 p.2; have hu : ((∑ j:Axis,Meld Q.J (H! k) j j) 0)= _:= congr_fun (cones (rim (H! k)) Q.J) 0; rw [Finset.sum_apply,Finset.sum_apply] at hu; exact hu)
   change Fast C.S y; rw [show y=(fun k=>y k-y' k)+y' from funext fun k=>(sub_add_cancel (y k) (y' k)).symm]; exact hξ.add (fast_fin (Portrait S ∘ L') univ fun i _=>hF i)
lemma trace_bs(hV:Rod t (.some false) (𝓛:Filter (ℕ×ℕ)) L):Fast C.S (fun k=> ∑ i:Axis, Storm S L k i i):=by
   let b:= some false
   apply bake_zero P h K hb HE hx hp (fun j=> Pick t b j j) (fun i=> L.T i i) (fun i=>hV.pole i i) (fun j=> (eager hu b).mono fun i h=>h.mono fun p hp=>hp.peek j j)
   filter_upwards with k; filter_upwards with p; have hx : (∑ i:Axis, Plint G (C.side k p.2) false i i) 0=0:= congr_fun (Plint_thin G _) 0; rw [Finset.sum_apply] at hx; exact hx
end YM.Trace.Shelves
