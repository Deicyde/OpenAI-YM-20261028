import YM.UVExtension.Beach.Under
/-!
 # Finite mesh analyticity

 Main U.V. proofs give hol convergence on strict interiors using disks
 that are uniform **over entire regulator tails**. One may shrink the
 disk again to require the continuation even on the finite prefix (cutoffs
 for which the fields are calibrated, i.e. at least the reference levels).
 No growth bound on that prefix is requested below. No change of the
 physical columns at a requested cutoff N/p for different ambient Keys
 sharing the given offset: cf. `Circuit.blazes` and `Hearth.cordial`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open Swell Stock Harvest Extraction Fallow Poppy Upland
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D}
    {Q:Factor A} {S: Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w}
    {t:ℕ→ℕ}(L:Cellar S t R)
    (N p n:ℕ) {a b:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
open Cellar
variable (u:Fin n→ (roster L).Token)
-- cutoff condition displayed; outside that condition, arbitrary padding
-- in the amplitudes is acceptable (the field is not calibrated there).
def Realizes (W:ℕ→ℂ→ Tabletop n→ℂ) (a:ℝ) :=
    ∀ N:ℕ, (∀ i, t (u i).1 ≤ N) →
      (∀ x:Tabletop n,AnalyticOnNhd ℂ (fun z=> W N z x) (ball 0 a)) ∧
        ∀ v: Orchard.Keys S, ( (v N p).val:ℂ) ∈ Metric.ball 0 a →
          W N ((v N p).val:ℂ) = Extraction.lifted (yard v L) N p u

private lemma one_cut {c:ℝ} (hc:0<c) (hcP:Metric.ball (0:ℂ) c ⊆ Camp.Broad A.B.a)
    (hc':∀ d N,t d ≤ N → Nonempty (Circuit S d N p R L c)) :
    ∃ b:ℝ,0<b ∧ ∃ W:ℂ→Tabletop n→ℂ,
      (∀ i,t (u i).1 ≤ N) →
      (∀ x:Tabletop n,AnalyticOnNhd ℂ (fun z=> W z x) (ball 0 b)) ∧
        ∀ v: Orchard.Keys S, ( (v N p).val:ℂ) ∈ Metric.ball 0 b →
          W ((v N p).val:ℂ) = Extraction.lifted (yard v L) N p u := by
  by_cases hN:∀ i,t (u i).1 ≤ N
  · let Y (i:Fin n) := Classical.choice (hc' _ N (hN i))
    obtain ⟨s,z,hs,hm,hz,hF⟩:= Pier.mounted S p N n hc hcP
    have hv: Metric.ball (0:ℂ) s ⊆ Camp.Broad A.B.a:= (ball_subset_ball hm).trans hcP
    have hh:= Swell.presto L N p n hc hs hm hv u Y (hF N le_rfl) hz
    choose F hf hF _ using hh
    refine ⟨s,hs,fun z x=> F (wrap (A.B.a.S.side N p) ∘ x) z,fun _=>?_⟩
    refine ⟨fun x=> DifferentiableOn.analyticOnNhd (?_) isOpen_ball,fun v hV=>?_⟩
    · exact hf _ _ id isOpen_ball (mapsTo_id _) differentiableOn_id
    funext i
    let y : Row s:= ⟨(v N p).val, mem_ball_zero_iff.mp hV |> (Complex.norm_real (v N p|>.val)).symm.trans_lt⟩
    have he: roseK S hs hv y=v N p:=Subtype.ext rfl
    refine (hF _ y).trans ?_
    dsimp only
    rw [he]
    exact (cordial N p L v n u hN _).symm
  exact ⟨1,zero_lt_one,fun _ _=>0,fun hp=>False.elim (hN hp)⟩

private lemma Stamp.shorter {I:Type} [MetricSpace I]{Y:Set I}{f:ℂ→ I→ℂ}
    {P W:ℕ→ℂ→ I→ℂ} (h:Stamp a Y f W) (hp:b ≤ a) (hc:P=ᶠ[atTop] W) : Stamp b Y f P := by
  have hu: ball (0:ℂ) b ⊆ ball 0 a:=ball_subset_ball hp
  refine ⟨fun x hx=> (h.analytic x hx).mono hu,fun U ht hU=>?_,fun K hK hA S hs ht j ε he=>?_⟩
  · obtain ⟨g,hg,⟨B,hh⟩,hx⟩:= h.debt U ht hU
    exact ⟨g,hg.mono hu,⟨B,fun z hz=> hh z (hu hz)⟩,fun x=> (hx x).mono hu⟩
  filter_upwards [hc,h.converges K hK (hA.trans hu) S hs ht j ε he] with i hi hv z hz x hx
  rw [show P i=W i from hi]
  exact hv z hz x hx

variable {F:ℕ→ℂ→Tabletop n→ℂ}{f:ℂ→Points n→ℂ}{m:ℕ}
include ha
lemma keep_prefix {c:ℝ} (hc:0<c) (hcP:Metric.ball (0:ℂ) c ⊆ Camp.Broad A.B.a)
    (hc':∀ d N,t d ≤ N → Nonempty (Circuit S d N p R L c))
    (H: Shoal L p n u a hp F f m) :
    ∃ b:ℝ, ∃ _hb:0<b,∃ hr:Metric.ball (0:ℂ) b⊆ Broad A.B.a, ∃ V:ℕ→ℂ→ Tabletop n→ℂ,
       Shoal L p n u b hr V f m ∧ Realizes L p n u V b := by
  obtain ⟨k,hk⟩:= eventually_atTop.mp H.top
  choose r hr P hP using fun N=> one_cut L N p n u hc hcP hc'
  let v:= (Finset.range (k+1)).inf' (show (Finset.range (k+1)).Nonempty from ⟨0,Finset.mem_range.mpr (by omega)⟩) r
  have hv: 0<v := by unfold v; exact (Finset.lt_inf'_iff ..).2 (fun i _=> hr i)
  let b := min a v; have hd: b≤a:= min_le_left ..
  let V N:= if N<k then P N else F N
  have hm: V=ᶠ[atTop] F:= (eventually_ge_atTop k).mono (fun i h=> if_neg (by omega))
  have hU: ball (0:ℂ) b ⊆ ball 0 a:=ball_subset_ball hd
  refine ⟨b,lt_min ha hv,hU.trans hp,V,⟨?_,fun x hx=> H.central x (hU hx),?_,fun t ht=> ?_⟩,?_⟩
  · filter_upwards [H.top,hm] with i hi hV
    rw [show V i=F i from hV]
    exact ⟨fun x=>(hi.1 x).mono hU,fun v hv=>hi.2 v (hU hv)⟩
  · refine ⟨fun l hl=> (H.roles.loop l hl).shorter hd ?_,fun z l i x hl hz hx=> H.roles.walk z l i x hl (hU hz) hx,fun l hl=> (H.roles.wand l hl).shorter hd ?_⟩
    · filter_upwards [hm] with i hi
      funext z x; unfold rails Ink
      dsimp only; rw [show V i=F i from hi]
    filter_upwards [hm] with i hi; unfold tideL; rw [show V i= F i from hi]
  · refine ⟨fun z hz=> (H.sampled t ht).1 _ (hU hz), ((H.sampled t ht).2.1).mono hU,fun j=> ?_⟩
    apply (((H.sampled t ht).2.2 j).mono hU).congr_inseparable
    filter_upwards [hm] with i hi x hx
    have he: glass A.B.a.S p F t i=glass A.B.a.S p V t i:=by funext z; unfold glass crumbs; rw [show V i=F i from hi]
    rw [he]
  intro N hN
  by_cases hx:N< k
  · have hR : ball (0:ℂ) b ⊆ ball 0 (r N):=ball_subset_ball ((min_le_right ..).trans (Finset.inf'_le _ (Finset.mem_range.mpr (by omega))))
    rw [show V N=P N from if_pos hx]
    exact ⟨fun x=> ((hP N hN).1 x).mono hR,fun x hx=> (hP N hN).2 _ (hR hx)⟩
  obtain ⟨hB,hY⟩:= hk N (by omega)
  rw [show V N=F N from if_neg hx]
  exact ⟨fun x=> (hB x).mono hU, fun x hx=> hY x (hU hx)⟩
end YM.UVExtension.Beach
