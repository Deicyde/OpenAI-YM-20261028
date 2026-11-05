import YM.MergeProof.East.Suds
import YM.TraceExtension.Prom.Orion.Plume
import YM.TraceExtension.Prom.Orion.Reach
import YM.TraceExtension.Prom.Front.West.Lys
import YM.TraceExtension.Prom.Front.West.Tael
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Coordinates
import YM.TraceExtension.Prom.Hill.Incoming
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.MergeProof.East.Suds for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ℕ→ ι → Tapes.Panel D) (Z:ArcSky P) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels

variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
open Analysis Next.UVStress Climb Ward
section
-- natural of position.fit on wider intervals.Deterministic ceil.
variable {V:Levels G}{b R:ℝ}

include h in
lemma open_readSky (R:ℝ)(V:Levels G)(m:ℕ): ∀ᶠ k:ℕ in atTop, ∀ b, AllowedSky V b k → ∀ x:Fin m→ Cover,
    let y:= tag (mag V b k)⁻¹ x
    y ∈ generic m→ ‖y‖ ≤ R→ FitSky V b k y:=by
   filter_upwards [(mag_rate V h (show (0:ℝ)<1 from zero_lt_one)).eventually_ge_atTop 1,(mag_rate V h (show (0:ℝ)<2 by norm_num)).eventually_ge_atTop (8*R)] with k hv hp b hx x y hg ht
   have he:= (authentic (V:=V) (k:=k) (b:=b) x).2
   have hq : Next.Rank.Station.key V b k y=gap V b k • y := by rw [Next.Rank.Station.anchored,show Next.Rank.Station.tested V b k y=y from he]
   have hv : 0<gap V b k:=gap_pos ..
   constructor
   · rw [hq]; exact scales_wild hv _ hg
   intro i j; rw [hq]; change |gap V b k * y i j| ≤ _; rw [abs_mul,abs_of_pos hv]
   have he: |y i j| ≤ R:= (PiLp.norm_apply_le (y i) j).trans ((PiLp.norm_apply_le y i).trans ht)
   have hB : 8*R ≤ V.clock.monitor k^2:=by apply le_trans hp; exact (Real.rpow_two _).le
   have hP:=hx.dilation; rw [le_div_iff₀ (V.S.a_pos _)] at hP; unfold gap at *
   linarith only [hP,mul_le_mul_of_nonneg_left ((show 8* _ ≤ V.clock.monitor k ^ 2 from (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤8)).trans hB)) hv.le]
end
include H h hp hZ Z
lemma sightSky (F:Extraction.Order)(hs:(standard C).Smooth) (R:ℝ)(hn:2≤n)(hi:0<R)(x:ι)(χ:ℝ)
    (t:Caps m)(ht:∀ i,t i ≤ D)(w:Ribbon (Bel C.book) t)(he:m ≤ n):∃ κ:ℝ,∀ᶠ k:ℕ in atTop, ∀ Y,PoisedSky (P k) B H O J n z k Y→
       (wok C D k (P k x).arc χ Y).inspection F (κ*Ship.budget (A) n k) (Scaling.window (2*R) m) ht w:=by
    cases m with
    | zero=> refine ⟨0,Eventually.of_forall fun k Y hQ x hx hc a' ha=>?_⟩
             -- empty numeric moment =1
             unfold Extraction.Order.late; refine Eventually.of_forall fun j=> Eventually.of_forall fun l=> ?_
             let u:=hang t w;let L:= standard C
             have he(U:Points 0):disc (hang t w) U=1:=by change L.useAt L U u=_; exact (Maxwell.table_regular C.labels).trivial (fun i => ⟨(u i).1,L.representative _ (u i).2⟩) U
             rw [he]; dsimp only; rw [Family.num]
             simp [ha.le]
    | succ m =>
       let I(i:Fin (m+1)):Fin (D+1):= ⟨t i,Nat.lt_succ_of_le (ht i)⟩
       let v:(i:Fin (m+1))→ C.label (I i):= fun i=> ladder C (t i) (w i)
       have hW : jointX (d0:=fun i=>(I i).val) v=hang t w:=by funext i; exact congr_arg (Sigma.mk (t i)) (ladder_reads (w i))
       let T:= Scaling.window (2*R) (m+1);have hh:IsCompact T:=window_closed ..
       have hz:T ⊆ conf (m+1):= fun i hi' => spaced_conf (by positivity : 0<(2*R)⁻¹) hi'.1
       let O'(y) := Poly.price (fun _=>1) (Read.maxProfile C y (jointX (d0:=fun i=> t i) v))
       have hT: ContinuousOn O' T:= by unfold O' Read.maxProfile Poly.price; exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((Read.profile_part_cont (standard C) hs _ _).norm.mono hz)
       obtain ⟨c,hc⟩:=(hh.image_of_continuousOn hT).bddAbove
       refine ⟨c,?_⟩
       filter_upwards [lava_vSky P Z B H h hp O J z hZ v x (t:=I) hh hz hn he,open_readSky h (2*R) A (m+1)] with k he ha Y hY i hi hk ε hε
       let b:= (P k x).arc
       specialize ha b
       let Q:= wok C D k b χ Y; let μ:= Next.Rank.Station.mag A b k; let y:= tag μ⁻¹ i
       rw [wok_spacing] at hi hk
       have hA :AllowedSky A b k:=by obtain ⟨p,q,u,h⟩:= hY.supply x; unfold b; rw [← (P k x).factor (C.path.levels.clock.J k)]; exact u.age.allot.permitted
       have hf:=ha hA i hk hi.2; change FitSky A b k y at hf
       obtain ⟨h1,h2⟩:= authentic (V:=A) (b:=b) (k:=k) i
       unfold Extraction.Order.late
       refine Eventually.of_forall fun l=>?_
       have hc' := F.mesh.cofinal.eventually (eventually_all.mpr (fun z : Fin (m+1)=> hf.stencils (F:=C) H (t z)))
       filter_upwards [F.mesh.cofinal.eventually (eventually_gt_atTop k),hc'] with j hj hx
       let N:=F.mesh j;let p:=F.per l; let a : (q:Fin (m+1))→ C.label (t q) := fun i=> ladd C μ k N p _ (Y N p (I i)) (v i); let W := q_asked (C:=C) a
       have he : ∀ s,s.val.Nonempty → (Ship.yardSky C b (show k ≤ N from hj.le) p).rootTest (C.beta N p) (fun U=> (Ship.invoiceSky (jointX (d0:=fun i=> (I i).val) v) W hf N p U).part s) ≤ Ship.budget (A) n k:=
          he Y hY N p hj y (h2.symm ▸ hi) hf
       have hr:∀ i,Interior _ (Read.probes C N p k (Next.Rank.Station.choose (A) b k y) W i):= fun i => (hx i).choose_spec p i (a i)
       have hu:= Read.full_cost H (Ship.fittingSky hf) (Ship.budget_pos (A) n k).le (Ship.yardSky C b (show k≤N from hj.le) p) hr he
       have hy : O' y ≤ c:= hc (mem_image_of_mem _ hi)
       have hm:= (Ship.budget_pos (A) n k).le
       change Next.Rank.Station.choose A b k y=i at h1; change Next.Rank.Station.tested A b k y=y at h2; rw [h1,h2] at hu
       change ‖C.numeric N p W (fun x=>Cells.location C.S k N p (i x))-disc (hang t w) (tag Q.spacing i)‖ ≤ _
       rw [show Q.spacing=μ⁻¹ from wok_spacing ..]
       -- ht disc equality.
       refine le_trans (show ‖_ - disc (hang t w) y‖ ≤ O' y * Ship.budget (A) n k from ?_) ((mul_le_mul_of_nonneg_right hy hm).trans (le_add_of_nonneg_right hε.le)); rw [← hW]; exact hu
end YM.MergeProof.East
