import YM.FullVolume.Finale.Real
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
open Tess
local notation "S!"=>R.family.S
local notation "C"=> Beam ℂ
open Tess Tess.Scroll
/-- Public interpretation of the analytic amplitudes on a local scope. In
normalized disk coordinates (origin is bar-β),

* D is the kernel; Q reads its spatial derivatives (`Pearl`, using fderiv)
  and their continuation on that disk. Use only on e.g. x∈K, z∈optics;
* Y and X are the continuations of the actual mesh quantities (values of the
  normalized stencils and their spatial interpolants resp.); only for the
  indicated points and sufficiently large cutoffs (similarly A for smears);
* limits uniform both in disk coordinate on strict interiors and in position
  on the compact patch.

No claim about continuity at collisions or outside optics.
-/
structure TargetSpace (w : sun) (K : Set (Points n)) (l : List (Reach n)) (D : ℂ → Points n → ℂ) : Prop where
  sky : ∃ Q : Points n → ℂ → ℂ,
    (∀ z ∈ optics, ContinuousOn (fun x : Points n => Q x z) K) ∧
    (∀ x ∈ K, AnalyticOnNhd ℂ (Q x) optics ∧ EqOn (Q x) (Pearl l D x) optics) ∧
    ∃ (Y : ℕ → Positions n → ℂ → ℂ) (X : ℕ → Points n → ℂ → ℂ),
      (∀ i : ℕ, (∀ y, AnalyticOnNhd ℂ (Y i y) optics) ∧ ∀ x, AnalyticOnNhd ℂ (X i x) optics) ∧
      (∀ᶠ N in atTop,
        (∀ x : Positions n, tag ((R.family.S).a N) x ∈ K →
          ∀ s : sun, Y N x (s.val : ℂ) = Face.physF F V₀ l w N s x) ∧
        ∀ x ∈ K, ∀ s : sun, X N x (s.val : ℂ) = interpolated R.family.S N (Face.physF F V₀ l w N s) x) ∧
      (∀ d : ℕ, ∀ J : Set ℂ, IsCompact J → J ⊆ optics →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
          (∀ x : Positions n, tag ((R.family.S).a i) x ∈ K → ∀ z ∈ J,
            dist (iteratedDeriv d (Y i x) z) (iteratedDeriv d (Q (tag ((R.family.S).a i) x)) z) < ε) ∧
          ∀ x ∈ K, ∀ z ∈ J, dist (iteratedDeriv d (X i x) z) (iteratedDeriv d (Q x) z) < ε) ∧
      ∀ t : Test n, suitable R.family.S p t → tsupport t ⊆ K →
        ∃ (A : ℕ → ℂ → ℂ) (e : ℂ → ℂ),
          (∀ᶠ i in atTop, ∀ s : sun, A i (s.val : ℂ) = sumOn (fun i => Face.physF F V₀ l w i s) R.family.S p i t) ∧
          (∀ i, AnalyticOnNhd ℂ (A i) optics) ∧ AnalyticOnNhd ℂ e optics ∧
          (∀ z ∈ optics, Integrable (fun x : Points n => t x * Q x z) ∧ e z = t.applyTo (fun x => Q x z)) ∧
          ∀ d : ℕ, ∀ J : Set ℂ, IsCompact J → J ⊆ optics →
            TendstoUniformlyOn (fun i => iteratedDeriv d (A i)) (iteratedDeriv d e) atTop J
lemma phenomenon {D:ℂ→Points n→ℂ}{w:sun}{K:Set (Points n)} (l:List (Reach n))(ht:Polar F V₀ w K l D):TargetSpace F V₀ w K l D:=by
   obtain ⟨Q,hQ,hV,Y,X,hX,hB,hT,hU⟩:= ht.sky
   refine ⟨⟨Q,hQ,hV,Y,X,hX,?_,hT,?_⟩⟩
   · filter_upwards [hB,eventually_ge_atTop 1] with N hh hn; simp_rw [Face.onReal F V₀ l w N hn]; exact hh
   intro t ht hh; obtain ⟨A,e,hQ,hX,hV,hU,H⟩:=hU t ht hh; refine ⟨A,e,?_,hX,hV,hU,H⟩
   filter_upwards [hQ,eventually_ge_atTop 1] with i hi hn s
   rw [hi s]; unfold sumOn; simp_rw [onReal F V₀ l w i hn s]
/-- Works simultaneously for all the indicated spatial derivative requests. -/
structure Spending (K : Set (Points n)) (h : ℕ) : Prop where
  work :
    ∃ (w : sun) (Ω : Set (Points n)) (D : ℂ → Points n → ℂ), 0 < (w:sun).val ∧ w.val ≤ 1/4 ∧
      IsOpen Ω ∧ K ⊆ Ω ∧ Ω ⊆ NoHit (S!) p n ∧
      (∀ z ∈ optics, ContDiffOn ℝ h (D z) Ω) ∧
      (∀ x ∈ Ω, AnalyticOnNhd ℂ (fun z => D z x) optics) ∧
      ∀ l : List (Reach n), l.length ≤ h → ∀ K' ⊆ Ω, IsCompact K' → TargetSpace F V₀ w K' l D
variable {k:ℕ} {v:ℕ→ℕ→ℝ}{Θ:Luna.Tableau T.width 300} (H:T.Winter) (h':Jams.Wild R.kit.shape R.alloy.delay) (hk:Sky R T Θ v)
include H h' hk
lemma standing {K:Set (Points n)} (h:IsCompact K)(hp:K ⊆ NoHit R.family.S p n) : Spending F V₀ K k:=by
    obtain ⟨t,ht,hT⟩:=h.exists_cthickening_subset_open (nohitOpen ..) hp; let V:=cthickening t K
    have he:IsCompact V:= h.cthickening; have hh:K⊆ interior V:=by
       intro x hx; rw [mem_interior_iff_mem_nhds]; exact Filter.mem_of_superset (closedBall_mem_nhds _ ht) (fun y hy=>mem_cthickening_of_dist_le _ _ _ _ hx (mem_closedBall.mp hy))
    obtain ⟨w₁,U₁,P₁,hΩ,hX₁⟩:= ArcPays.voyage F V₀ (fun l=> by obtain ⟨w,u,g,hv,H⟩:= charted F V₀ l he hT H h' hk; exact ⟨w,hv,u,g,H⟩) k
    let s:sun:=⟨1/4,by norm_num [sun]⟩; let w:= scaleSun s w₁; let P i x:= Amp.Beam.fit s (P₁ i x); let U i j x:=Amp.Beam.fit s (U₁ i j x)
    have hX (l:List (MotionIndex n))(h:l.length ≤ k): Bows F V₀ w V l (U l) (P l):= Bows.shrinks F V₀ l (hX₁ l h) s
    let D(z:ℂ)(x):=heartX (P [] x) z; refine ⟨w,interior V,D,mul_pos hΩ (by norm_num [s]),by change w₁.val*(1/4)≤1/4; linarith only [show w₁.val≤1 from w₁.2.2],isOpen_interior,hh,interior_subset.trans hT,fun z hz=> galaxyX F V₀ hX hz,fun x _=> hearts _,fun l hl K' hK' hp' =>?_⟩
    let l':= l.map Reach.where_; have heq : l'.length ≤ k:=by simpa [l'] using hl
    obtain ⟨X,hK,hU,hB⟩:= exists_compact_between hp' (isOpen_interior) hK'; have hx := polaris F V₀ l (hX l' heq) hK hB
    apply phenomenon F V₀ l; exact peaking F V₀ l hp' hK hU D (fun z hz y hy=>genealogy F V₀ hX hz l' heq (hK' hy)) hx.1 hx.2
end Fan
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.standing
