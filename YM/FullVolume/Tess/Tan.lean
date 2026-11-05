import YM.FullVolume.Tess.Stream
import YM.FullVolume.Tess.Scope
/- Acquire tariff & eventual canopy budgets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
local notation "S"=> R.alloy.B.a.S
open MergeProof.Ribbons Next.Rank Next.Rank.Spindle
namespace Face
open Metric
open Ray
variable {W:Pillars R T}{p:ℕ}
local notation "P!"=>R.alloy.B.a
namespace Fan
variable (F:Fan T W p){n:ℕ}(V₀:Fin n→ R.family.book.Token)
local notation "δ"=> intervalClock R
local notation "a"=> R.family.S.a
variable (l:List (MotionIndex n))
open Tess
variable {K:Set (Points n)}{w:sun}{P:ℕ→ℝ}{L r:ℝ}{t:ℝ}{U:ℕ→ℕ→Positions n→ Beam ℂ}
local notation "T!"=>Beam ℂ
structure Bows (w:sun)(K:Set (Points n))(l:List (MotionIndex n)) (U:ℕ→ Positions n→Beam ℂ)(g:Points n→ Beam ℂ):Prop where
   song : ∀ᶠ N in atTop,∀ y:Positions n,tag (R.family.S.a N) y∈K→ ∀ s:sun, read ℂ s (U N y)= kFilm F V₀ l N (scaleSun w s) y
   part : ∀ ε:ℝ, 0<ε→∀ᶠ N in atTop,∀ y:Positions n, tag (R.family.S.a N) y∈K→ dist (U N y) (g (tag (R.family.S.a N) y)) <ε
   landed: ContinuousOn g K
namespace Spines
variable (h:IsCompact K)(hp:0<t) (hk:Spines F V₀ w U (cthickening t K) l L r P)
abbrev ports (R:Run G)(i:ℕ) (y:Points n):Positions n:= Extraction.address (R.family.S.a i) y
local notation "p!"=> ports (n:=n) R
local notation "O!"=> cthickening t K
include h hk hp
lemma mercury :∀ᶠ i in atTop,∀ x∈ K,tag (a i) (p! i x)∈ O!:=by
     have hv: ∀ᶠ i in atTop, ∀ x:Points n, dist (tag (a i) (p! i x)) x < t:= nearest Extraction.Sequence.full hp (C:=R.family)
     filter_upwards [hv] with i hi x hx; exact mem_cthickening_of_dist_le _ _ _ _ hx (hi x).le
local notation "Q!"=> Scope.tip U (p!)
lemma bandScope: Tess.Scope (U:=K) (P:=P) U (ports R):=by
      obtain ⟨a₀,hA⟩:= eventually_atTop.mp (mercury F V₀ l h hp hk); refine ⟨fun j=> Tess.finite_addresses h, hk.launched, hk.ends,?_,?_⟩
      · filter_upwards [hk.views,eventually_ge_atTop a₀] with i h k x hx; exact h _ (hA _ k x hx)
      filter_upwards [hk.earns,eventually_ge_atTop a₀] with i hh hi N ht x hx; refine hh _ _ _ ht (hA i hi x hx) (hA _ (hi.trans i.le_succ) x hx) ?_
      apply le_trans (dist_triangle _ x _); unfold tac; rw [dist_comm x]
      have h':=approximate (R.family.S.a_pos i) x; have h:= approximate (R.family.S.a_pos (i+1)) x; unfold ports
      nlinarith only [h',h,mul_le_mul_of_nonneg_left (R.family.S.strictAnti i.lt_succ_self|>.le) (show (0:ℝ)≤ n from Nat.cast_nonneg n)]
variable {g:Points n→ Beam ℂ} (hv:TendstoUniformlyOn (Tess.Scope.tip U (ports R)) g atTop K)
lemma tips : ∀ᶠ N in atTop,∀ x:Positions n,tag (a N) x∈O! →∀ s:sun, read ℂ s (U N N x)= kFilm F V₀ l N (scaleSun w s) x:=by
    filter_upwards [hk.emits] with N h x hx s; rw [h N le_rfl x hx]
    unfold swellK FullVolume.terrace; rw [show FullVolume.ascending (S) p (n:=n) (le_refl N)=id from funext fun x=>FullVolume.arriving (S) p x,Function.comp_id]; rfl
include hv
lemma within (x y:Points n)(hx:x∈K)(hy:y∈K)(hp': dist x y< r)(s:sun): dist (read ℂ s (g x)) (read ℂ s (g y)) ≤ L* dist x y:=by
    let u i:=tag (a i) (p! i x); let v i:= tag (a i) (p! i y)
    have hx': Tendsto u atTop (𝓝 x):=Extraction.chosen x; have hy': Tendsto v atTop (𝓝 y):=Extraction.chosen y
    have hℓ:=(read ℂ s).continuous
    have he(y')(h:y'∈ K):Tendsto (fun i=>read ℂ s (U i i (p! i y'))) atTop (𝓝 (read ℂ s (g y'))):= hℓ.continuousAt.tendsto.comp (TendstoUniformlyOn.tendsto_at hv h)
    apply le_of_tendsto_of_tendsto ((he x hx).dist (he y hy)) ((hx'.dist hy').const_mul L)
    filter_upwards [tips F V₀ l h hp hk, mercury F V₀ l h hp hk,hk.old.paths,(hx'.dist hy').eventually (ge_mem_nhds hp')] with i h he hp' hi
    rw [h _ (he x hx), h _ (he y hy)]; exact hp' _ _ (he y hy) hi s
lemma coasts (s:sun): ContinuousOn (fun x=> read ℂ s (g x)) K:=by
     intro x hx; refine Metric.continuousWithinAt_iff.mpr (fun ε he=>?_)
     let p':= L+1; have hh:0<p':=by unfold p'; linarith [hk.old.rates]
     let u:=min r (ε/p'); have hu:0 < u:= lt_min hk.old.quiet (by positivity)
     refine ⟨u,hu,fun y hy hT=>?_⟩ ; have h:= within F V₀ l h hp hk hv y x hy hx (lt_of_lt_of_le hT (min_le_left ..)) s
     refine h.trans_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by unfold p'; linarith : L≤p') dist_nonneg) ((lt_div_iff₀' hh).mp (lt_of_lt_of_le hT (min_le_right ..))))
lemma raysEra : ∃ C:ℝ,∀ x∈ K, ‖g x‖≤ C:=by
    obtain ⟨i,hi⟩:= (Metric.tendstoUniformlyOn_iff.mp hv 1 zero_lt_one).exists
    have hp:(U i i '' (p! i '' K)).Finite:= (Tess.finite_addresses (t:=R.family.S.a i) h).image (U i i)
    obtain ⟨C,hC⟩:= (hp.image norm).bddAbove
    refine ⟨C+1,fun u hu=>?_⟩; let P':=U i i (p! i u)
    rw [add_comm]; exact (norm_le_norm_sub_add (g u) P').trans (add_le_add ((dist_eq_norm (g u) P').symm.trans_le (hi u hu|>.le)) (hC ⟨_,⟨_,⟨u,hu,rfl⟩,rfl⟩,rfl⟩)) -- lemma
lemma arced (x:sun)(hx:|x.val|<1): Bows F V₀ (scaleSun x w) K l (fun N y=> Amp.Beam.fit x (U N N y)) (fun y=> Amp.Beam.fit x (g y)):=by
     refine ⟨?_,?_,?_⟩
     · filter_upwards [tips F V₀ l h hp hk] with i hi y hy s; have hg:= hi y (mem_cthickening_of_dist_le _ _ _ _ hy (le_trans (le_of_eq (dist_self _)) hp.le)); rw [fitL,hg]; exact congr_arg (fun v:sun=> kFilm F V₀ l _ v y) (px ..)
     · intro ε he
       filter_upwards [Metric.tendstoUniformlyOn_iff.mp hv ε he] with i hi y hy; rw [dist_eq_norm,← fitD]; have hh: p! i (tag (a i) y)=y:= address_matched (R.family.S.a_pos i) y
       have h := hi _ hy; change dist (g _) (U i i (p! i (tag (a i) y)))<ε at h; rw [hh,dist_comm,dist_eq_norm] at h; exact (fitN ..).trans_lt h
     obtain ⟨C,hc⟩:= raysEra F V₀ l h hp hk hv
     intro v hV
     apply tendsto_of_seq_tendsto; intro y hy
     have hU:∀ᶠ i in atTop, ‖g (y i)‖ ≤ C:=(hy.eventually self_mem_nhdsWithin).mono fun i hi=>hc _ hi
     have H(s:sun):Tendsto (fun i=>read ℂ s (g (y i))) atTop (𝓝 (read ℂ s (g v))):= ((coasts F V₀ l h hp hk hv s v hV)|>.tendsto.comp hy)
     exact damp x hx hU (g v) H
end Spines
variable {v:ℕ→ℕ→ℝ}{Θ:Luna.Tableau T.width 300} (h:IsCompact K)(hp:K⊆ NoHit R.alloy.B.a.S p n)(H:T.Winter) (h':Jams.Wild R.kit.shape R.alloy.delay) (hk:Sky R T Θ v)
include H h' h hp hk
lemma charted :∃ w U g,0 < (w:sun).val∧ Bows F V₀ w K l U g:=by
    obtain ⟨r,hr,hK⟩:= h.exists_cthickening_subset_open (nohitOpen ..) hp
    obtain ⟨L,M,w,U,p,hw,hB⟩:= astronomer F V₀ l H h' h.cthickening hK hk -- output
    let x:sun:=⟨1/2,by norm_num [sun]⟩
    obtain ⟨X,hX⟩:= (Spines.bandScope F V₀ l h hr hB).rosary _ _
    exact ⟨scaleSun x w,_,_,mul_pos hw (by norm_num [x]), Spines.arced F V₀ l h hr hB hX x (by norm_num [x])⟩
end Fan
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.charted
