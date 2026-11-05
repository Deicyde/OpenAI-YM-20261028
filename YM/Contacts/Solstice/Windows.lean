import YM.Contacts.Solstice.Puncture
/-!
# Geometry for availability & scaling

Build the normalized root routes on *arbitrary* parameter families of subtraction lengths and
shrinking support scales in the indicated regime. Need detectors/horizon permits & small-scale
domain. Also the `stage` is allowed to include exterior coordinates when testing a whole relative
placement and requiring clearance. The small length is needed for the actual extension; support
domain here may also extend to a larger fixed aperture (then include in budgeting). No claim of
independence of the contact terms from the choices. The overlaps work on tests through the interior
of ANY such admissible stages. Strict placements on a separated group can always be included.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Harvest Route
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E W I J : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {G: Gauge}{C : Family G}{F : Extraction.Order}{S: Table C.book}{Z : Final C F S}
variable {k : ℕ}{g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k} {Q : Pieces g}
local notation "GN" => Normal.Group k
local notation "K!" => normalOn P g
lemma posture (r : Route P Q I W)(x:W) : IsCompact (r.stage x):= limit_compact.of_isClosed_subset (r.closedStage x) (r.limited_stage x)

lemma hangs {t : ℝ} (ht : t≠0) : Proper (resize K! t ht) t K!:= ⟨fun _=> slip .., fun _ hx=> slip_mem _ t hx⟩
structure NormalRange (P:E→ₗᵢ[ℝ] Points k)(g:GN)(s r : W→ℝ)(o : W→Points k)(U : W→ Set E)(B : ℝ) : Prop where
   sized : B ∈ Ioc 0 1
   weld : ∀ w, Collapsed g (o w) -- typo
   plane : plane g ≤ LinearMap.range P.toLinearMap
   lengths : ∀ w,0<s w ∧ 2*s w ≤ B
   reaches : ∀ w,r w∈Ioc 0 1
   regime : ∃ T ≥(1:ℝ),∀ w, r w ≤ T*s w
   authority : ∀ w,U w⊆strip (normalOn P g) B
   bound : ∃ V ≥(1:ℝ),∀ w (h:r w ≠0), U w ⊆ limited (resize (normalOn P g) (r w) h) V
   closed : ∀ w,IsClosed (U w)

-- enough in a compact set of the **normalized** relative tests. All estimates can use this request; authority for the probes in Stage given independently.
lemma normed_bound {T : Set E} (h : IsCompact T){g:GN}{r:W→ℝ}{U:W→ Set E} (hu : ∀ w (h:r w≠0), U w⊆ (resize (normalOn P g) (r w) h).symm ⁻¹' T) : ∃ V≥(1:ℝ),∀ w (h:r w≠0), U w⊆ limited (resize (normalOn P g) (r w) h) V:= by
   obtain ⟨V,hV⟩:= h.isBounded.subset_closedBall (0:E); refine ⟨max V 1,le_max_right ..,fun w H=>?_⟩; exact (hu w H).trans (Set.preimage_mono (hV.trans (closedBall_subset_closedBall (le_max_left ..))))
lemma easy_permit {T B : ℝ} {r:W→ℝ}{U:W→ Set E}(hp : ∀ w,0< r w)(h : ∀ w,U w⊆ limited (resize (normalOn P g) (r w) (hp w).ne') T)(he : ∀ w,T*r w≤ B) : ∀ w,U w ⊆ strip K! B:= fun w _ hx=> le_trans (rel_limit K! (hangs (hp w).ne') (hp w) (h w hx)) ( (mul_comm _ _).trans_le (he w): r w*T ≤ B) -- namespace

namespace NormalRange
variable {r s : W→ℝ}{U : W→ Set E}{B : ℝ}{o:W→ Points k}(R : NormalRange P g s r o U B)
def build : Route P (root g) Unit W where
    ceiling:=B
    allows:=R.sized
    length:=s
    offset:=o
    diameter _:=r
    frame w:= resize (normalOn P g) (r w) (R.reaches w).1.ne'
    stage:=U
    register _:= ()
    tagalong:=R.regime.choose
    leading:=R.regime.choose_spec.1
    reserve:=R.bound.choose
    positive:=R.bound.choose_spec.1
    short:= R.lengths
    accounted _:= R.reaches
    aligned w _ hi:=(R.weld w).subgroups ((root g).le hi)
    displaysNormals _ hi:= (plane_le ((root g).le hi)).trans R.plane
    accommodates w _ hi:= (hangs (R.reaches w).1.ne').within (normal_le P ((root g).le hi))
    in_budget w _ _ _:= R.regime.choose_spec.2 w
    limited_stage w := R.bound.choose_spec.2 w ((R.reaches w).1.ne')
    closedStage:= R.closed
    clear w _ hi:= (R.authority w).trans (inherit_strip (normalOn P g) (normal_le P ((root g).le hi)))
lemma holds : Run R.build:= rfl
lemma sized_on : scale R.build=r:= rfl
end NormalRange

-- useful in fixed(s) geometry not necessarily root. Blank route for ANY compact patch U, with scale=1 all blocks.
structure EmptyBank (P : E→ₗᵢ[ℝ] Points k)(Q : Pieces g) (s : ℝ)(o : Points k)(U : Set E)(B : ℝ) : Prop where
   leads : B∈ Ioc 0 1
   along i : i∈ Q.parts → Collapsed i o
   contains i : i∈ Q.parts → plane i ≤ LinearMap.range P.toLinearMap
   clear i : i∈ Q.parts → U ⊆ strip (normalOn P i) B
   paid : 0<s ∧2*s≤B
   compact : IsCompact U
namespace EmptyBank
variable {s B : ℝ}{o:Points k}{U:Set E}(T : EmptyBank P Q s o U B)
include T
lemma reserve_size : ∃ V ≥(1:ℝ), U ⊆ limited (ContinuousLinearEquiv.refl ℝ E) V:= by
   obtain ⟨V,hV⟩:= T.compact.isBounded.subset_closedBall (0:E); exact ⟨max 1 V,le_max_left .., hV.trans (closedBall_subset_closedBall (le_max_right ..))⟩
def route : Route P Q Unit Unit where
    ceiling:= B
    allows:= T.leads
    length _:= s
    offset _:= o
    diameter _ _:=1
    frame _:=ContinuousLinearEquiv.refl ℝ E
    stage _:=U
    register _:= ()
    tagalong:= max 1 s⁻¹
    leading:= le_max_left ..
    reserve:= T.reserve_size.choose
    positive:= T.reserve_size.choose_spec.1
    short _:= T.paid
    accounted _ _:= ⟨one_pos,le_rfl⟩
    aligned _ i:= T.along i
    displaysNormals:= T.contains
    accommodates _ _ _:= Proper.identity
    in_budget _ _ _ _ := le_trans ((inv_mul_cancel₀ T.paid.1.ne').symm.le) (mul_le_mul_of_nonneg_right (le_max_right ..) T.paid.1.le)
    limited_stage _:= T.reserve_size.choose_spec.2
    closedStage _:= T.compact.isClosed
    clear _:= T.clear
end EmptyBank

/- check sufficient strictness simply on slots in closed **convex** neighborhoods. Useful for backdrops embedded or separately. No available i,j if no parts. -/
variable (r : Route P Q I W)
lemma slot_centroid {x:E}{w:W}{p : GN} (hp : p.Nonempty) {U:Set E4} (h : Convex ℝ U)(hx : ∀ i∈p,r.actualAt w x i∈U): r.oculus w p x∈ U:= by
   let F:= (p.card:ℝ)⁻¹; have hf: 0<(p.card:ℝ):= by exact_mod_cast hp.card_pos
   let Y:= r.actualAt w x; unfold oculus; rw [centroid_formula, Finset.smul_sum]; apply h.sum_mem (fun i hi=> (inv_pos.mpr hf).le) _ hx; rw [Finset.sum_const,nsmul_eq_mul,mul_inv_cancel₀ hf.ne']
lemma palette_area (w:W)(x:E) (i : Q.parts) {U : Set E4}(h : Convex ℝ U)(hx : ∀ j∈ i.val,r.actualAt w x j∈U) : r.palette w i.val x ⊆ U:= by
   rintro y ⟨p,rfl⟩; exact slot_centroid r p.property.2 h (fun j hj=> hx _ (p.property.1 hj))
structure Corridors (r : Route P Q I W)(v : Q.parts → W→ E→ Set E4)(δ : ℝ): Prop where
   lies w x (hx:x∈r.stage w) (i : Q.parts) : ∀ j∈ i.val,r.actualAt w x j∈v i w x
   apart w x (hx:x∈r.stage w) (i j : Q.parts) : i≠j→∀a∈v i w x,∀b∈v j w x, δ ≤ ‖a-b‖
   convex w x (hx:x∈r.stage w) (i : Q.parts) : Convex ℝ (v i w x)
lemma Corridors.includes {v : Q.parts → W→ E→ Set E4}{δ : ℝ} (h : Corridors r v δ) (i:Q.parts)(w:W){x : E}(hx:x∈r.stage w): r.palette w i.val x⊆ v i w x:= palette_area r _ _ i (h.convex _ _ hx i) (h.lies _ _ hx i)
lemma Corridors.sober {v : Q.parts → W→ E→ Set E4}{δ : ℝ} (h : Corridors r v δ): Sober r δ:= fun i j he w x hx a ha b hb=> h.apart w x hx i j he a (h.includes r i w hx ha) b (h.includes r j w hx hb)
lemma Backdrop.fromCorridors {v : Q.parts → W→ E→ Set E4}{δ : ℝ}(hp : 0<δ){d : J→ℕ}(θ : Backdrop S r d) (h : Corridors r v δ) (he : ∀ w,∀ x∈ r.stage w, (Set.univ:Set J).Pairwise (fun i j=> δ ≤ ‖θ.values w x i-θ.values w x j‖)) (hx : ∀ w,∀ x∈r.stage w,∀ i(j:Q.parts),∀ a∈v j w x,δ≤ ‖a-θ.values w x i‖) : Eligible θ δ:= ⟨hp, h.sober r,he,fun w x hx' i j a he=> hx w x hx' i j a (h.includes r j w hx' he)⟩

end YM.Contacts.Solstice
