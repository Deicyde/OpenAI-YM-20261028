import YM.RG17.Joint
import YM.RG17.DensityClock
import YM.SharpGram.Lenses.Mantle
/-!
Buy compatible Mantle/slack with Pillars, Services is enough. No Directions as post comparison premises.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Lenses
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open PhysicalNext.RankCovariance Org Spec Next.UVStress Further.CorrectedLift MergeProof.East Weak
open scoped Topology ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
variable {u:Filter (ℕ×ℕ)}
local notation "S'"=> (Bel C.book)
local notation "P"=> C.path.levels.clock.hatBeta
local notation "σ"=> F.room.kernel.spin
local notation "θ"=> Maxwell.Free.spin_free C.labels
local notation "V"=> F.sector.derivatives

include F
variable [u.NeBot] (hf:u≤f.fuse) {D : ℕ} (Q : Portfolio C F.room.cutoff D u)
variable (S0 : OPE.Services C f S)
include Q hf S0
open Weak.Portfolio
set_option maxHeartbeats 700000 in
lemma ledges17 (hm : CanSmear Q) : ∃ Y : ℕ → Canopy S, ∀ᶠ k in atTop, Ledger F u k D Q (Y k) := by
   let hg:=S0.simpleGate
   obtain ⟨W,r,T₀,hr⟩:= S0.purchase
   let ht:= hr.toTableTickets
   obtain ⟨Y,H,He⟩:= Q.tune_grades F ht hf hg
   have hp (d:Fin (D+1)) : ∀ᶠ k in atTop, Costs C k d u (Y k d):=by
      let δ:= margin C d
      have he : 0<δ := (Weak.Portfolio.freely (C:=C) d).choose_spec.1
      let K:=δ/2+‖model C d‖
      have hx : 0 ≤ K := by unfold K; positivity
      filter_upwards [stayNear (Q.aligned F ht hf hg d (He d)) (half_pos he), Q.entry_cap_use F ht hf hg d K hx, Q.departUse F ht hf hg d (δ/2) (half_pos he)] with i hv hr hz
      exact ⟨hr (Y i d) (normBy hv),hz (Y i d) (absorb _ _ δ _ (Weak.Portfolio.freely (C:=C) d).choose_spec.2 (by simpa only [sub_half] using hv))⟩
   have hSize : 0 < sizeHint D := by unfold sizeHint; positivity
   have hr (n:Fin (D+1)) (t:Fin n → Fin (D+1)) (v:record C (fun i=>(t i).val)):=
     Q.progresses F hg ht hf hm Y He (t:=fun i=>(t i).val) ((Nat.le_of_lt_succ n.isLt).trans (Nat.le_add_right ..))
        (fun i=>Nat.le_of_lt_succ (t i).isLt) (depthWord _ v) |>.reads _ (window_closed (sizeHint D) n.val) (fun _ h=>spaced_conf (inv_pos.mpr hSize) h.1)
          (sizeHint D) hSize (costHint D) (cost_pos _)
   refine ⟨Y,?_⟩; filter_upwards [Q.onLevel,Q.length_power hg,H,eventually_all.mpr hp, (Q.detonates hg).eventually (ge_mem_nhds (cost_pos D)),eventually_all.mpr (fun i=>eventually_all.mpr (fun v=>eventually_all.mpr (hr i v)))]
      with k ⟨h1,h2,h3,h4⟩ hF hv ht hx hV
   refine ⟨h4,h3,h1,hF.1,hx,hF.2,h2,ht,hv,⟨fun {n} hn p hp a=> ?_⟩⟩
   let j : Fin (D+1) := ⟨n,Nat.lt_succ_of_le hn⟩
   exact hV j (fun i : Fin j=> (⟨p i, Nat.lt_succ_of_le (hp i)⟩:Fin (D+1))) a
omit Q hf S0 [u.NeBot]
include S0
variable (v : Ultrafilter (ℕ×ℕ)) (hφ : (v:Filter _) ≤ f.fuse)
include hφ
theorem attains_mantle17 (hc : Dense.Coverage C F.room.cutoff) : Nonempty (Mantle F (v:Filter _)) := by
   choose Q0 hQ using fun d : ℕ=> smearsFromCoverage (D:=d) hc v hφ
   choose y hy using fun d=> ledges17 F hφ (Q0 d) S0 (hQ d) -- argument order
   obtain ⟨h,hh,hR,hT⟩:= advances _ hy
   exact ⟨⟨h,hR,hh,fun i=> y (h i) i,fun i=> Q0 (h i), hT⟩⟩
end YM.SharpGram.Lenses

namespace YM.RG17
set_option maxHeartbeats 1200000
open Function Filter YM.PhysicalNext YM.PhysicalNext.Repeat YM.PhysicalNext.Repeat.Legato
open YM.FullVolume YM.FullVolume.Final Extraction Campaign
open scoped Topology BigOperators Classical

/-- Adds Dense Coverage hence also Mantle BEFORE extraction on ANY such fuse; same Full-volume UV and every-phase joint endpoint with OPE Services and
an ordinary exact OPE Reader, weak leading correlation estimates (as
`FirstExtension`), actual beta limits all fixed levels. Still not
physical Wilson perturbative comparison. Same hierarchy, fields, and
`Pillars`; this selects ONCE on a schedule further paying halos. -/
theorem denseSupplies (G:Gauge) (h:G.Simple) (δ:ℝ) (hd:0<δ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      R.family.path.levels.clock.kernel.penalty = δ ∧ Jewel R T W ∧ SharpGram.Dense.Coverage R.family R.makes ∧
      ∀ f : Extraction.Order,
        ∃ (g : Extraction.Order) (S : Table R.family.book)
          (F : Spec.Final R.family (f.refine g) S),
          (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered R.family S ∧
          PositionsUV R.family Extraction.Sequence.full ∧
          ∃ (L : YM.EveryPhase.Almanac F) (P:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
              (X:Climb.Scaling S) (B:ℕ→ℝ), YM.EveryPhase.Completed F L ∧
              OPE.Services R.family (f.refine g) S ∧ OPE.Orbits.Foundation F P ∧ Pert.FirstExtension F X ∧
              (∀ m:ℕ,(f.refine g).limits (fun _=>True) (fun N p=>R.family.path.β N p m) (B m)) ∧
              PertExtension.Running.isLimit R.family (f.refine g) B ∧
              ∀ U:Ultrafilter (ℕ×ℕ), (U:Filter _) ≤ (f.refine g).fuse → Nonempty (SharpGram.Lenses.Mantle F (U:Filter _)) := by
   obtain ⟨R,T,hT,hY,⟨W⟩,hP,hV,hG,hCov,v,Θ,hW⟩:= Campaign.operaShipDens17 h δ hd
   have J:= jewelOf17 T W h hT hY v Θ hW
   have he:= Campaign.opePackage17 W h hV hG hW
   refine ⟨R,T,W,hP,J,hCov,fun f=>?_⟩
   obtain ⟨g,B,hB⟩ := PertExtension.Running.extraction R.family J.actual f
   obtain ⟨w,S,F,X,hS,hX⟩:= R.extractible17 h he (f.refine g)
   obtain ⟨L,hL⟩:= EveryPhase.all_characters F
   let t:=F.phase.transport
   obtain ⟨p,hp⟩:= OPE.Prescription.chosen F.room.kernel.laws.toSymmetric t.injection
   let r:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin := ⟨p,hp,F.room.kernel,t.injection,t.rights,t.spots⟩
   have hb m:=Extraction.Order.retained (g:=w) (hB m)
   have hf : f.refine (g.refine w) = (f.refine g).refine w := rfl
   refine ⟨g.refine w, ?_⟩
   rw [hf]
   exact ⟨S,F,from_spec ((f.refine g).refine w) ⟨F⟩ J.fullMesh,J.fullMesh,L,r,X,B,
     hL,hS,OPE.Orbits.produce F r hS,hX,hb,(fun m=> Order.along (hb m)),fun U hl=> SharpGram.Lenses.attains_mantle17 F hS U hl hCov⟩
end YM.RG17

#print axioms YM.SharpGram.Lenses.ledges17
#print axioms YM.SharpGram.Lenses.attains_mantle17
#print axioms YM.RG17.denseSupplies
