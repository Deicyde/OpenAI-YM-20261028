import YM.TraceExtension.Shelves.Fame
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
-- finite linear hull, use actual dimensions.Books K linear
lemma fast_sum {S:Schedule}{V E:Type*} [NormedAddCommGroup E](f:V→ℕ→E)(s:Finset V)(hp:∀ i∈s,Fast S (f i)): Fast S (∑ i∈s,f i):=by induction s using Finset.induction_on with
    | empty=> simp only[sum_empty]; exact ⟨-1,by norm_num,isBigO_zero ..⟩
    | insert i s hi ih=> rw [sum_insert hi]; exact (hp i (mem_insert_self ..)).add (ih (fun j hj=>hp j (mem_insert_of_mem hj)))
include P h hb HE hx hp K
lemma plans (v:Guilds C)(L:Logs C d) (h:Loan v (𝓛:Filter (ℕ×ℕ)) L)(hV:Credible v b!)(I:Watch C):∃ E:ℕ→ℝ, Fast C.S E ∧ ∀ᶠ k:ℕ in atTop,∀ᶠ p:ℕ×ℕ in b!, ‖ Fold I k p.1 p.2 d (v k p.1 p.2) 0 - I.tester S d (Portrait S L k)‖ ≤ ‖E k‖ :=by
    obtain ⟨c,hc,E,hE,H⟩:= Trespass P ‹_› K hb HE hp hx hV h I; refine ⟨E,hE,H.mono fun k ht=> ?_⟩; have hz:= ht 0 0 (by simp[hc.le]); filter_upwards [hz,(link_mesh hb).eventually_ge_atTop k] with p hp hi
    rw [Fold_eq I k p.1 p.2 d v _ hi] at hp; simpa [tester_home] using hp
lemma fumes {V:Type}[Fintype V](f:V→ ℝ) (v:V→ Guilds C)(L:V→ Logs C d)(h:∀ i,Loan (v i) b! (L i))(h':∀ i, Credible (v i) b!)(hv:∀ᶠ k:ℕ in atTop,∀ᶠ p:ℕ×ℕ in (𝓛:Filter (ℕ×ℕ)),(∑ i:V, f i • v i k p.1 p.2)=0): Fast C.S (fun k=>∑ i:V, f i • Portrait S (L i) k) := by
    refine response_fast HE _ fun I=> ?_
    choose E he H' using fun i=> plans P ‹_› K hb HE hx hp _ _ (h i) (h' i) I; let S':= I.tester S d;let w k:= ∑ i,f i • Portrait S (L i) k; refine ⟨fun _=>S',fun z=>tendsto_const_nhds,?_⟩
    let F(i)(k):= ‖f i‖*‖E i k‖; let q(k):=∑ i,F i k; have hp':Fast C.S q:=by rw[show q=∑ i,F i from funext fun x=>(Finset.sum_apply ..).symm]; apply fast_sum; intro i _; exact (he i).smaller ((isBigO_norm_left.mpr (isBigO_refl ..)).const_mul_left ‖f i‖)
    refine hp'.smaller (isBigO_iff.mpr ⟨1,?_⟩); filter_upwards [eventually_all.mpr H',hv,eventually_all.mpr h'] with k hk hx hL; obtain ⟨i,hp,ht,hH,hy⟩:= (hx.and ((eventually_all.mpr hk).and ((eventually_all.mpr hL).and ((link_mesh hb).eventually_ge_atTop k)))).exists
    let Q(v:Peat G (C.side k i.2)):= Fold I k i.1 i.2 d v 0; let V'(j):= v j k i.1 i.2; let t j:= S' (Portrait S (L j) k)
    have hx: S' (w k)=∑ j,f j • t j:=by let Z:= S'.restrictScalars ℝ; unfold w; rw[map_sum]; exact sum_congr rfl fun i _=>Z.map_smul ..
    have hG: ∑ j,f j • Q (V' j)=0:=by
        have he:= (fade_w I (k:=k) (N:=i.1) (d:=d) (fun j=> f j • V' j) univ fun j _=>fade_ss (V' j) (cylinder_env (lumen (hH j))) (f j)).2 hy 0
        simp_rw [book_s I _ _ hy] at he; rw[show ∑ j,f j • V' j=0 from hp, Fold_null I _ hy] at he; exact he.symm
    change ‖S' (w k)‖ ≤_; rw [hx]; have he1:(∑ j,f j • t j)= ∑ j,f j • (t j-Q (V' j)):=by simp_rw [smul_sub,sum_sub_distrib,hG,sub_zero]
    rw [he1,one_mul]; apply le_trans _ (Real.le_norm_self _); exact (norm_sum_le ..).trans (sum_le_sum (fun j _=>by unfold F; rw[norm_smul,norm_sub_rev]; exact mul_le_mul_of_nonneg_left (ht j) (norm_nonneg _)))
end YM.Trace.Shelves
