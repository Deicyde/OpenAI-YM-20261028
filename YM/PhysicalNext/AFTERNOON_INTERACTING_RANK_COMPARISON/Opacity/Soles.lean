import YM.AnalyticBridge.GAUSSIAN_INTERIOR_COMPARISON.Padding
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hyssop
import YM.Extra.ITERATION_NO_LOSS.Kernels
import YM.Extra.MULTISOURCE_BOUNDS.Trajectory
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Archives
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Crust
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Siren
import YM.Progress.DIRECTED_RECIPE.Rollout
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Picks
import YM.Push.STRESS_FLUX.FreeBridge
import YM.SectorNext.VACUUM_NORMALIZATION.Clinic
import YM.UVNext.FREE_STRESS_CERTIFICATE.Cube
/-!
# Material visibility on each footprint, even before commitment to a Store
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A B : Stores S}
    {F F' : Forest S.ratio} {k k' : S.Choices} {X X' : Support c} {p q : Pilot G S x} {P : Teller G}
lemma openedHere (i : Bond f) : i∈Aff.activeB A F (radiusB x) ↔ Physical.openBond A F x i:= by
  by_cases he:i∈ F.trunks
  · exact iff_of_false (fun hh=> Milk.sweepB i hh he) (fun h=> (Physical.mask ..|>.1 h).1 he)
  let a:F.Free:= ⟨i,he⟩; exact (Milk.stillActive F A x a).trans (Dictionary.Print.sees_breeze x A F a).symm

namespace Dyed
variable (v : Dyed G S) (W : ℝ)

lemma theater (h : Hears X p q) (i : Bond c) (hv : Coverage.shutters S.patch + 1 ≤ radiusB x)
    (hT : Boosted v.things P x) (hp : Shields X i.1 (23*radiusB x+17)) :
    Aff.αSite (v.top p) i.1 p.tag=Aff.αSite (v.top q) i.1 q.tag ∧ Aff.αBond (v.top p) i p.tag=Aff.αBond (v.top q) i q.tag ∧ S.prediction (v.top p) p.tag i=S.prediction (v.top q) q.tag i:= by
  have hz : pinPos i ⊆ X:= fun j hj=>hp _ ((Physical.pin_diam i (mem_insert_self ..) hj).trans (by omega))
  refine Coverage.connector_at _ _ _ _ _ hT.produced.branched (fun j hj=> ?_) (h.reads.frame _ hp.center) (h.reads.frame _ (hz (by simp [pinPos]))) (h.reads.bond _ hz)
  exact peak_record v h j hT.ready (hp.shift (by omega))

lemma footage_read (i : Fleck S) (hT : Boosted v.things P x) (hv : Coverage.shutters S.patch+1 ≤ radiusB x) (hd : 0<v.arc) (hr : 2*v.arc<firstRadius G) (h : ∀ j∈foot S i, Shields X j (23*radiusB x+17)) :
    Pulled (fun (p:Pilot G S x)=>ask v W p i) X:= by
  constructor
  · exact fun A F k=> footage v W hT hd hr A F k i
  have hh := h _ (footfall S i); have hl : foot S i ⊆ X:=fun j hj=> (h j hj).center
  intro p q _ _ hx
  rcases i with i|i|i|i|i
  · change Aff.fine _ _ _ _ _= Aff.fine _ _ _ _ _
    unfold Aff.fine
    -- Fine face
    have he:toll (v.top p) i=toll (v.top q) i:= congr_arg G.chord (travel_local _ _ _ _ (fun j hj _=> peak_record v hx j hT.ready ((h _ (mem_image_of_mem _ (List.mem_toFinset.mpr hj))).shrink (by omega))))
    simp only [he,hx.reads.cost i hl]
  · change Aff.wireMask _ _ _ _ _ _ _ _=Aff.wireMask _ _ _ _ _ _ _ _; unfold Aff.wireMask
    simp only [hx.reads.aisle i hl,wire,theater v hx i hv hT hh|>.2.2,hx.reads.configuration i hh.center (hl (by change _∈pinPos _; simp [pinPos]))]
  · exact (theater v hx ((i,0):Bond c) hv hT hh).1
  · exact (theater v hx i hv hT hh).2.1
  change door v p i= door v q i; unfold door
  change Shields X (S.ratio.parent i.1) (23*radiusB x+17) at hh
  have he := openedHere (A:=p.key) i (F:=p.park) (x:=x) |>.trans ((hx.reads.frozen_bits hT.produced.scale i (hh.shrink (by omega))).trans (openedHere i).symm)
  split
  next hk =>
    rw [dif_pos (he.1 hk)]
    apply congr_arg
    exact tape_scans v hT.ready (Milk.fundedB i hk) (Milk.fundedB i (he.1 hk)) hx (hh.shrink (by omega)) rfl
  next hk=> rw [dif_neg (mt he.2 hk)]

-- sign exact at α copies, not likelihood product continuity
lemma menu_turn (s : Signed) (b : Site c) (U : Config G f) (k : S.Choices) (h : S.patch.Branches S.kernel G) (i : Site c) (j : Bond c) :
    Aff.αSite (pull s (S.ratio.embed b) U) i k = Aff.αSite U (orient (s,b) i) (S.withinChoice s b k) ∧ Aff.αBond (pull s (S.ratio.embed b) U) j k=Aff.αBond U (StepData.sendBonds s b j) (S.withinChoice s b k) := by
  unfold Aff.αSite Aff.αBond
  constructor
  · apply congr_arg₂ _ rfl; change _=S.patch.frameMass _ (expandAt (S.ratio.embed (affine s b i)) U) (S.withinSites s b _ (affine s b i)); rw [S.port_site,expandAt_pull,S.port]; exact (S.patch.frames_channel h ..).1
  apply congr_arg₂ _ rfl
  obtain ⟨o,t⟩:=j; let j : Bond c:= (o,t)
  change _=S.patch.predictorMass _ (S.connector U (S.withinSites s b k.1) (sendEdge s b (o,t))) (S.withinBond s b k.2 (sendEdge s b (o,t))); rw [S.port_bond]
  cases he:s.flip t
  · rw [S.positive h _ _ _ _ o t he]; exact (S.patch.bond_pull (h:=h) ..).1
  rw [S.negative h _ _ _ _ o t he]; exact (S.patch.bond_inv (h:=h) ..).1
lemma move_bond (e : Wheel c) (i : Bond f) : i∈Aff.activeB (book e.1 e.2 A) (Locations.forest e.1 e.2 F) (radiusB x) ↔ sendEdge e.1 (S.ratio.embed e.2) i∈Aff.activeB A F (radiusB x):= by
  let s:=e.1;let b:=e.2
  let Q:=Locations.active s b A F x; let i' := sendEdge s (S.ratio.embed b) i
  constructor
  · intro h; let k:=Milk.fundedB i h; exact (Milk.stillActive ..).2 (Q k).property
  intro h; let k:=Milk.fundedB i' h
  obtain ⟨z,hz⟩:=Q.surjective k
  have hv:z.val.val=i:= sendEdge_injective s _ (show _=sendEdge s (S.ratio.embed b) i from congr_arg (fun a : Active A x F=> a.val.val) hz)
  exact hv ▸ (Milk.stillActive ..).2 z.property
lemma top_ship (e : Wheel c) (h : P.Funds S v.things) (p : Pilot G S x) : v.top (spires e p)=pull e.1 (S.ratio.embed e.2) (v.top p):=fans p.key p.park e.1 e.2 _ h ..
lemma footship (e : Wheel c) (h : P.Funds S v.things) (i : Fleck S) (p : Pilot G S x) : ask v W (spires e p) i=ask v W p (pursuit S e i):= by
  let s:= e.1;let b:=e.2;let c:=S.ratio.embed b;let Y:=spires e p
  let U:= v.top p
  have ht:v.top Y=pull s c U:= top_ship v e h p
  have hz:S.withinChoice s b Y.tag=p.tag:= Equiv.apply_symm_apply ..
  let x' : ℝ:=x
  have hh i j:= menu_turn s b U Y.tag (funds_branch h) i j
  rw [hz] at hh
  rcases i with i|i|i|i|i
  · change Aff.fine _ _ _ (v.top Y) _=Aff.fine p.key _ _ _ (shiftFaces s c i); unfold Aff.fine
    rw [ht, show toll (pull s c U) i=toll U (shiftFaces s c i) from Face.send_price U i s c _ G.chord_inv fun u z=> G.chord_conj z u]
    simp only [spires,book,mem_map_equiv,Equiv.symm_symm]; rfl
  · let j:=StepData.sendBonds s b i
    change Aff.wireMask Y.key v.chi W x _ Y.tag Y.view i=Aff.wireMask p.key v.chi W x _ p.tag p.view j
    unfold Aff.wireMask; rw [ht,S.prediction_channel (funds_branch h),hz]; simp only [Y,spires,book,mem_map_equiv,Equiv.symm_symm]
    let H:= S.prediction U p.tag; let V:=p.view
    have hT: wire (pull s b H) (pull s b V) i=wire H V j:=by
      unfold wire; simp only [Channels.read_back]; split
      next he =>
        change G.chord ((V j)⁻¹*((H j)⁻¹)⁻¹) = _
        rw [← G.chord_inv (V j*(H j)⁻¹), show (V j*(H j)⁻¹)⁻¹=V j*((V j)⁻¹*((H j)⁻¹)⁻¹)*(V j)⁻¹ by group, G.chord_conj]
      rfl
    apply if_congr Iff.rfl <;> first |exact (congr_arg (fun a=>1-v.chi.innerShare _ a) hT)|exact (congr_arg (fun a=>v.chi.innerShare _ a) hT)
  · change Aff.αSite (v.top Y) i Y.tag=_; rw [ht]; exact (hh i (i,0)).1
  · change Aff.αBond (v.top Y) i Y.tag=_; rw [ht]; exact (hh i.1 i).2
  change door v Y i = door v p (sendEdge s c i)
  let j:=sendEdge s c i; change _ = door v p j
  have hk : i∈Aff.activeB Y.key Y.park (radiusB x) ↔ j∈Aff.activeB p.key p.park (radiusB x):=move_bond ..
  by_cases he:i∈Aff.activeB Y.key Y.park (radiusB x)
  swap; · unfold door; rw [dif_neg he,dif_neg (mt hk.2 he)]
  let q:=Milk.fundedB i he;let l:=Locations.active s b p.key p.park x q
  rw [show door v Y i=_ from active_door v q,show door v p j=_ from active_door v l,tape_ship v e h p]
  unfold Next.SectorChange.broad; rw [LinearIsometry.norm_map]
lemma top_steam (h : Boosted v.things P x) (p : Pilot G S x) (hp : Matched p) (f : Site c→G.El) : v.top (burnish f p)=Lattice.gauge (constantGauge f S.ratio) (v.top p):=
  (winding p.key p.park x v.source.beta v.arc p.view _ h.funded f p.tag v.chi p.y (h.fogged p.key p.park _ p.tag (hp.bright f))).symm

lemma bootup (h : Boosted v.things P x) (p : Pilot G S x) (i : Fleck S) (v' : Site c→G.El) (hp : Matched p) : ask v W p i=ask v W (burnish v' p) i:= by
  let f:= constantGauge v' S.ratio; let u:=v.top p; let q:=burnish v' p; let V:=p.view
  have hs: v.top q=Lattice.gauge f u:= top_steam v h p hp v'
  have hb := funds_branch h.funded; rcases i with i|i|i|i|i
  · change Aff.fine p.key _ _ _ i= Aff.fine p.key _ _ (v.top q) i; unfold Aff.fine; rw [hs,show toll (Lattice.gauge f u) i=toll u i from by unfold toll; rw [face_gauge,G.chord_conj]]
  · change Aff.wireMask p.key _ _ _ _ _ _ i=Aff.wireMask p.key _ _ _ (v.top q) p.tag q.view i
    have hx:f ∘ S.ratio.embed=v':= funext fun i=>by simp [f,Function.comp_def,constantGauge, Ratio.embed_parent]
    let H:= S.prediction u p.tag; unfold Aff.wireMask; rw [hs,(choice_gauge hb u p.tag f).2,hx, show wire (Lattice.gauge v' H) q.view i=wire H V i from ?_]
    unfold wire; rw [show q.view i*(Lattice.gauge v' H i)⁻¹ = v' i.1*(p.view i*(H i)⁻¹)*(v' i.1)⁻¹ from by unfold H Lattice.gauge; dsimp only [burnish,q,Lattice.gauge]; group, G.chord_conj]
  · change Aff.αSite _ i p.tag= Aff.αSite (v.top q) _ p.tag; rw [hs]; exact (Aff.symmetric_mass u (i,0) p.tag hb f).1.symm
  · change Aff.αBond _ i p.tag= Aff.αBond (v.top q) _ p.tag; rw [hs]; exact (Aff.symmetric_mass u i p.tag hb f).2.symm
  change door v p i= door v q i; by_cases he:i∈Aff.activeB p.key p.park (radiusB x)
  swap; · unfold door; rw [dif_neg he,dif_neg (show _ from (show i∉Aff.activeB q.key q.park (radiusB x) from he))]
  let H:=Milk.fundedB i he
  rw [show door v p i=_ from active_door v H, show door v q i=_ from active_door (p:=q) v H,tape_spin v h p hp]
  unfold Next.SectorChange.broad; rw [G.norm_adjoint]
lemma starlet (h : Boosted v.things P x) (p : Pilot G S x) (hp : Matched p) (v' : Site c→G.El) (e : Wheel c) : Playing v W p → Playing v W (burnish v' (spires e p)):= by
  intro he
  let q:= spires e p; unfold Playing
  rw [show (∏ i,ask v W (burnish v' q) i)=∏ i,ask v W p i from ?_]; exact he
  refine Fintype.prod_equiv (pursuit S e) _ _ fun i=> ?_
  rw [← bootup v W h q i _ (hp.signed e)]; exact footship v W e h.funded i p
end Dyed
end YM.PhysicalNext.InteractingRank.Pump
