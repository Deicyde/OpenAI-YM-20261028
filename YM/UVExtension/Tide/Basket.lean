import YM.UVExtension.Tide.Earning
import YM.UVExtension.Tide.Fjord
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tide
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open Swell Stock Harvest
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {Q:Factor A} {S: Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w} {t:ℕ→ℕ}(L:Cellar S t R)
    (N n m k d:ℕ) {a:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
open Cellar Gale.Circuit
local notation "T"=> A.B.a.S
local notation "φ"=> A.B.a
local notation "P"=> A.B.a.budget m
local notation "R0"=> desk a ha
local notation "ℍ"=> Row a
set_option quotPrecheck false
local notation "V0"=> Cellar.yard (roseA S) L
variable (I:ℕ→ℕ)(H':Harvest.Barn S R I L)(hK:Mix.paidL (Cellar.yard (roseA S) L))
variable (u:Fin k→ (roster L).Token) (Q':∀ (d N:ℕ),t d ≤ N→Nonempty (Circuit S d N n R L a))
variable (hx: UVExtension.Cloud.Leases C Q.shape A.delay)(hr:∀ i j,(Q.target i j).rate ≤ -(7/16:ℝ))
include ha hp I H' hK hx hr Q'
lemma wheeling: ∃ c v, ∃ hc:0<c,∃ hp:Metric.ball (0:ℂ) c⊆Camp.Broad A.B.a, 0<v ∧∀ᶠ j in atTop,∀ N (h:j ≤N)(q:Fin k→ Site (A.B.a.S.side j n)), Injective q→ Sail (desk c hc) (fun d:Row c=> served N n L (roseK S hc hp d) k u (anchor A.B.a.S n h∘q)) (expS A.B.a.S v j):=by
   obtain ⟨b,hb,hP⟩:= streams (a:=a) L n k I H' hK u
   obtain ⟨C₀,c,hc,hl,hC,h⟩:= upper L n k ha u hx hr hp
   let Q:= T
   have hA:ball (0:ℂ) c⊆Broad A.B.a:= (ball_subset_ball hl).trans hp
   obtain ⟨s,hs,hV,p,hJ⟩:= cordage Q (φ).fits.mesh C₀ hC hc (1/32) (by norm_num)
   let v:ℝ:=b+1; have he : 1<v:=by unfold v; linarith only [hb]
   obtain ⟨f,hF,hW,hY⟩:= trapeze Q v he (φ).fits.mesh
   have hz : ∀ᶠ i in atTop,b*Q.scale i≤Q.scale (f i) :=by
      filter_upwards [hY.eventually (le_mem_nhds (show b<v by unfold v; linarith only)),Q.divergent.eventually_gt_atTop 0] with i hx hi; exact (le_div_iff₀ hi).mp hx
   obtain ⟨z,hz',hG⟩:= (PolyB.fromNote ((Note.bell_exp Q C₀).relay f hF hY)).add (PolyB.const Q (max 0 p))
   refine ⟨s,z,hs,(ball_subset_ball hV).trans hA,hz',?_⟩
   obtain ⟨i,hi⟩:= eventually_atTop.mp h
   filter_upwards [eventually_ge_atTop i,hP,hW,hz,hG,hF.eventually hJ,eventually_all.mpr (fun j=>eventually_ge_atTop (t (u j).1))] with j hj he hW hx₀ hM ht hv N htN q hq
   have hv':∀ l,t (u l).1≤N:= fun l=>(hv l).trans htN; let U(l):= Classical.choice (Q' (u l).1 N (hv' l)) -- replace
   let F(b:Row c):= served N n L (roseK S hc hA b) k u (anchor Q n htN∘ q)
   have hm: expS Q C₀ (f j)+max 0 p ≤ expS Q z j:=by
       have h:0 ≤ expS Q C₀ (f j)+max 0 p:= add_nonneg (Real.exp_pos _).le (le_max_left ..); exact (le_abs_self _).trans hM -- awaiting composition congr
   have hT:Sail (desk c hc) F (expS A.B.a.S C₀ N):= (hi j hj N htN).1 _ hv' (fun i=> ⟨U i⟩)
   by_cases hN:f j ≤ N
   swap
   · obtain ⟨g,hg,hB,hL⟩:=hT; have hh: DifferentiableOn ℂ g (ball 0 c):=hg _ id isOpen_ball (mapsTo_id _) differentiableOn_id; refine ⟨g,bumps _ g (hh.mono (ball_subset_ball hV)),fun d=> hB ⟨d.val,d.2.trans_le hV⟩,fun v hv=> (hL _ (ball_subset_ball hV hv)).trans ?_⟩
     exact (Real.exp_monotone (mul_le_mul_of_nonneg_left ((bob Q).monotone (le_of_lt (lt_of_not_ge hN))) hC.le)).trans ((le_add_of_nonneg_right (le_max_left ..)).trans hm)
   have hj₀: j ≤ f j:= le_trans (Nat.le_add_right j 1) hW.le
   let x(m:ℕ)(h:f j ≤ m) (d:Row c):= fancy L N n m k u U (fun i=> (hv i).trans (hj₀.trans h)) (anchor Q n (hj₀.trans h)∘ q) d.val
   let w(m:ℕ)(d:Row c) := if hm:m=N then F d else if hp:f j ≤ m then x m hp d else 0; have h₁ : w N= F:= by unfold w; simp
   have h₂(m)(ht:f j ≤ m)(h:m≤N) : Sail (desk c hc) (w m) (expS Q C₀ m) :=by
     rcases eq_or_lt_of_le h with h|h; · subst m; rw [h₁]; exact hT
     rw [show w m=x m ht from funext fun i=>by unfold w; rw [dif_neg h.ne,dif_pos ht]]; exact (hi m (hj.trans (hj₀.trans ht)) N h.le).2 _ _ _
   have hw:= ht N hN w h₂ (fun m hk hm d=>?_); swap
   · rcases eq_or_lt_of_le hm with h'|h'; · subst m; rw [sub_self,norm_zero]; exact (Real.exp_pos _).le
     let z:= roseK S hc hA d; let V:Keys S:=fun _ _=>z; let Y:= anchor Q n htN∘ q
     obtain ⟨p,hP⟩:= he m (hj₀.trans hk) (hx₀.trans ((bob Q).monotone hk)); have hx₀: F d=(yard V L).numeric N n u Y:= (cordial N n L V k u hv' _).symm
     rw [h₁,hx₀]; unfold w; rw [dif_neg h'.ne,dif_pos hk]; exact hP q hq N h' U V (ball_subset_ball hl (desk c hc |>.within d))
   rw [h₁] at hw; exact hw.mono ((add_le_add_right (le_max_right 0 p) (expS Q C₀ (f j))).trans hm) -- ambiguous
end YM.UVExtension.Tide
