import YM.Contacts.Harvest.Gather
/-!
# Every-character Euclidean hierarchy reader on strict geometry

No *relative* blown-up clearance at the boundary of a child shell is needed at the final
root reading on strict exterior geometry. We can vary spectator positions freely, e.g.
nominally by translation and frame of the cluster, within the demand about clearance from all
possible placements on the indicated support. This class includes also the root projection read
via a separate loan. None of these conditions are charge estimates; they solely specify the tests,
exteriors, fields, and geometry. Empty initial clusters allowed (including partitions splitting
all the points of a configuration); no normalization imposed on reader there.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E W I J : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {G: Gauge}{C : Family G}{F : Extraction.Order}{S: Table C.book}{Z : Final C F S}
variable {k : ℕ}{g : Normal.Group k}{Q : Pieces g}{P:E→ₗᵢ[ℝ] Points k} {v : ℝ} {d : J→ℕ}
local notation "GN" => Normal.Group k
local notation "Z!" => Z.sector.derivatives
variable (r : Route P Q I W)
def Sober (γ : ℝ) := ∀ i j:Q.parts,i≠j → ∀ w,∀ x∈ r.stage w,∀ f∈r.palette w i.val x,∀ h∈r.palette w j.val x, γ ≤ ‖f-h‖

lemma sober_single {q : Q.parts}(h : Q.parts={q.val}) (γ : ℝ) : Sober r γ:= by
    intro i j he; have hi(x:Q.parts) : x=q:= Subtype.ext (by have hi:=x.property; -- motive
                                                                     exact Finset.mem_singleton.mp (( Finset.ext_iff.mp h x.val).1 hi)) -- name
    exact (he ((hi i).trans (hi j).symm)).elim

-- compatibility of exterior fields in a bigger ambient. They need not be additional stage variables
-- or centers fixed or on a compact; only continuity in the region and bounded label spaces.
-- When including them in E use ordinary integration and tests there, either as spectator groups via
-- Q or just this backdrop. Actual exterior offsets, no vertical dependence even outside support.
structure Backdrop (S : Table C.book)(r : Route P Q I W) (d : J→ ℕ) where
  values : W→ E→ J → E4
  labels : (i:J) → W→ E→ S.Field (d i)
  still : ∀ w (i:Q.parts) {x y:E}, x-y∈ normalOn P i.val → values w x=values w y
  held : ∀ j w (i:Q.parts){x y:E}, x-y∈ normalOn P i.val → labels j w x=labels j w y
  bounds : ∃ c : ℝ,∀ i w, ∀ t∈ r.stage w, ‖labels i w t‖ ≤ c
  continuous (w:W) : ContinuousOn (values w) (r.stage w)
  known (j : J)(w:W) : ContinuousOn (labels j w) (r.stage w)

namespace Backdrop
variable {r}
variable (θ : Backdrop S r d) [Fintype J]
structure Eligible (θ : Backdrop S r d) (δ : ℝ) : Prop where
    pos : 0<δ
    sober : Sober r δ
    apart w : ∀ x∈ r.stage w, (Set.univ:Set J).Pairwise fun i j=> δ ≤ ‖θ.values w x i-θ.values w x j‖
    border w : ∀ x∈ r.stage w, ∀ i (j:Q.parts),∀ a∈r.palette w j.val x, δ ≤ ‖a- θ.values w x i‖

variable (M : Devices Z.sector.derivatives)
abbrev haloWord (w : W)(x : E) : Expression Z.sector.derivatives:= ∏ j, insertField M.basis (θ.values w x j) (d j) (θ.labels j w x)
lemma frame_still {x y : E} (w) (i : Q.parts)(h : x-y ∈ normalOn P i.val) : θ.haloWord M w x=θ.haloWord M w y:= Finset.prod_congr rfl fun j _=> by rw [θ.still _ i h,θ.held j _ i h]
variable (α : W → Viewers Z)
def finalReading (w : W) (x:E) : Expression Z.sector.derivatives→ₗ[ℂ] ℂ:= (readExpr M.basis (spectator Z (α w))).comp (LinearMap.mulRight ℂ (θ.haloWord M w x)) -- order check
lemma finalSight (w x f) : θ.finalReading M α w x f= readExpr M.basis (spectator Z (α w)) (f*θ.haloWord M w x) := rfl
-- at an unprojected forest using indicated exteriors

def polls : Reader E W ℂ k Z.sector.derivatives:= fun w x=> (θ.finalReading M α w x).comp eraseTags.toLinearMap
lemma final_fixed (w) (i : Q.parts){x y:E}(h : x-y∈ normalOn P i.val): θ.finalReading M α w x=θ.finalReading M α w y:= by unfold finalReading; rw [frame_still _ M w i h]
lemma anchored : Fixed (θ.polls M α) Q P:= ⟨fun w i _ _ h=> by unfold polls; rw [final_fixed _ M α w i h]⟩
lemma voted (w) (x:E) (f : GN→ Expression Z.sector.derivatives) : θ.polls M α w x (∏ i∈ Q.parts,tag i (f i))= θ.finalReading M α w x (∏ i∈Q.parts,f i) := by
    have hh : eraseTags (∏ i∈Q.parts, tag i (f i)) = ∏ i∈Q.parts,f i:= by rw [map_prod]; exact Finset.prod_congr rfl fun i hi=> erase_tags i (f i)
    exact congrArg (θ.finalReading M α w x) hh

variable {θ M α} {δ:ℝ} (h : Eligible θ δ)
include h
omit [Fintype J] in
lemma other_palettes (w:W) {x:E}(hx : x∈r.stage w) : (Q.parts:Set GN).Pairwise fun i j=> Disjoint (r.palette w i x) (r.palette w j x):= by
   intro i hi j hj he; refine Set.disjoint_left.mpr (fun y hf hg=>?_); have hp:=h.sober (⟨i,hi⟩:Q.parts) ⟨j,hj⟩ (fun h=> he (congr_arg Subtype.val h)) w x hx y hf y hg; rw [sub_self,norm_zero] at hp; exact hp.not_gt h.pos
lemma displays {V : Type}[TopologicalSpace V] {f : V→E}{U:Set V}(hp : ContinuousOn f U) {w:W}(he : MapsTo f U (r.stage w)) : Displays U (fun i=>Set.range (θ.values w (f i))) (fun i=> θ.haloWord M w (f i)) := Displays.word (x:=θ.values w ∘ f) (fun _ _=>by rfl) (fun i hi j k h' => Classical.byContradiction (fun he'=> by
       have ht:= h.apart w (f i) (he hi) (Set.mem_univ j) (Set.mem_univ k) he'
       change θ.values w (f i) j= θ.values w (f i) k at h'; dsimp only at ht; rw [h',sub_self,norm_zero] at ht; exact ht.not_gt h.pos)) (θ.continuous w|>.comp hp he) (fun j=>θ.known j w|>.comp hp he)
lemma final_plot {V : Type} [TopologicalSpace V] {U : Set V}{v : V → E} (w : W) (hv' : ContinuousOn v U)(hv : MapsTo v U (r.stage w))
    {f : GN→ V→ Expression Z.sector.derivatives}(hf : ∀ i∈Q.parts, Displays U (r.palette w i ∘ v) (f i)): ContinuousOn
    (fun i=> θ.finalReading M α w (v i) (∏ j∈ Q.parts,f j i)) U:= by
   apply Displays.observes M.basis _ (spectate Z (α w)) (Displays.times ?_ (Displays.prod hf (fun t ht=> other_palettes h w (hv ht))) (displays h hv' hv))
   intro t ht; refine Set.disjoint_left.mpr (fun z hz he=>?_); obtain ⟨i,hi,hh⟩:= Set.mem_iUnion₂.mp hz; obtain ⟨j,rfl⟩:=he; have heL:= h.border w (v t) (hv ht) j (⟨i,hi⟩:Q.parts) _ hh; rw [sub_self,norm_zero] at heL; exact heL.not_gt h.pos
lemma lit : Lit r (θ.polls M α):= by
   constructor; exact anchored θ M α; intro V _ v U w hU hv hw t ht; apply ContinuousOn.congr (final_plot (α:=α) (M:=M) h w hv hw ht) (fun x hx'=> θ.voted M α w (v x) (fun i=> t i x))

variable {x: ℕ→ E} {w:ℕ→ W} {T':ℕ→ℝ} {φ : Filter ℕ} [φ.NeBot] (he : ∀ i,x i∈ r.stage (w i))(ht : Tendsto T' φ atTop)
include he ht
omit h he [Fintype J] [φ.NeBot] in
lemma apart_price (γ:ℝ) (hg:0<γ) {f g: ℕ→ E4}(hh : ∀ i, γ ≤ ‖f i-g i‖) : Intervals φ T' 0 (sole ∘ f) (sole ∘ g) := by
   apply from_gap (RateIs.swap (RateIs.const ht zero_lt_one) neg_zero.symm) ht γ hg (Eventually.of_forall fun i=> le_trans (show γ*1 ≤ γ from (mul_one γ).le) (hh i))
omit [φ.NeBot] in
lemma haloFine : Fine M φ T' (pack (fun i=> θ.values (w i) (x i))) 0 0 (fun i=>θ.haloWord M (w i) (x i)) := by
   let p(j:J)(i:ℕ):= θ.values (w i) (x i) j; let V(j:J): Set (ℕ→ E4):={p j}; let f(j:J)(i:ℕ):= insertField M.basis (p j i) (d j) (θ.labels j (w i) (x i))
   have hp(j:J):Fine M φ T' (V j) 0 0 (f j) := Fine.field ht (Set.mem_singleton _) ((RateLE.absBound _ ht (Eventually.of_forall fun i=> θ.bounds.choose_spec j _ _ (he i))).mono (by simp))
   have hh:((Finset.univ : Finset J):Set J).Pairwise (fun i j=> Cross φ T' 0 (V i) (V j)):= fun i _ j _ hi X hx y hy=> by rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]; exact apart_price ht δ h.pos (fun t=> h.apart (w t) (x t) (he t) (Set.mem_univ i) (Set.mem_univ j) hi)
   apply Fine.germ (Fine.admits (A':=pack (fun i=> θ.values (w i) (x i))) (Fine.product ht (p:=Finset.univ) (a:=fun _=>0) (s:=0) (fun i _=> hp i) hh) (by simp) ?_) ?_
   · exact Set.iUnion₂_subset fun i _=> singleton_subset_iff.mpr (Set.mem_range_self _)
   exact Eventually.of_forall (fun i=> Finset.prod_apply ..)

omit [Fintype J] [φ.NeBot] in
lemma nearby_players : (Q.parts : Set GN).Pairwise fun i j=> Cross φ T' 0 (r.avenue i w x) (r.avenue j w x):= by
   rintro i hi j hj he' f ⟨f,rfl⟩ g ⟨g,rfl⟩; exact apart_price ht δ h.pos fun t=> h.sober (⟨i,hi⟩:Q.parts) ⟨j,hj⟩ (fun h=> he' (congr_arg Subtype.val h)) _ _ (he t) _ (Set.mem_range_self f) _ (Set.mem_range_self g)
omit [Fintype J] [φ.NeBot] in
lemma borderAvenue : Cross φ T' 0 (⋃ i∈ Q.parts, r.avenue i w x) (pack (fun t=> θ.values (w t) (x t))):= by
  rintro f hf y ⟨z,rfl⟩; obtain ⟨i,hi,g,rfl⟩:= Set.mem_iUnion₂.mp hf; exact apart_price ht δ h.pos (fun t=> h.border (w t) (x t) (he t) z (⟨i,hi⟩:Q.parts) _ (Set.mem_range_self g))
lemma final_counts (A : Services C F S)(t : GN→ ℕ→ Expression Z.sector.derivatives) (c : GN→ℝ)
    (hh : ∀ i∈ Q.parts, Funds Z M φ T' (r.avenue i w x) 0 (c i) (t i)) : RateLE φ T' (fun i=> θ.finalReading M α (w i) (x i) (∏ j∈Q.parts,t j i)) (Q.parts.sum c) := by
   have hh':Funds Z M φ T' (⋃ i∈Q.parts,r.avenue i w x) 0 (Q.parts.sum c) (fun i=> ∏ j∈Q.parts,t j i):= Funds.ident (Funds.product ht zero_le_one hh (nearby_players h he ht)) (Eventually.of_forall (fun i=> Finset.prod_apply ..))
   have hf : View Z M φ T' _ ((fun i=> ∏ j∈Q.parts,t j i) * (fun i=> θ.haloWord M (w i) (x i))):= hh'.tests ht A le_rfl le_rfl zero_le_one (borderAvenue h he ht) (haloFine h he ht); rw [add_zero] at hf; exact hf (fun i=> α (w i))
end Backdrop

variable {r} {φ : Filter ℕ}{T : ℕ→ℝ}{v : ℝ}
lemma habitat0 (i : Q.parts) {w : ℕ→W}{x : ℕ→E} (hh : ∀ t,x t∈r.stage (w t))(hT : Tendsto T φ atTop)(he : RateIs φ T (r.R i.val ∘ w) (-v)) : Habitat φ T v (fun j=> r.oculus (w j) i.val (x j)) (r.avenue i.val w x) := by
   rintro f ⟨f,rfl⟩; exact from_span he hT r.reserve (Eventually.of_forall fun j=> (r.oculus_extent (w j) (x j) i f).trans (( (show ‖(normalOn P i.val).starProjection (x j)‖ ≤ r.R i.val (w j)*r.reserve from r.proportions i _ (hh j)).trans_eq (mul_comm ..))))
lemma layer_coarsen (h : Services C F S) (M : Devices Z.sector.derivatives)(i : Q.parts) (w : ℕ→W)(x : ℕ→E) (hh : ∀ t,x t∈r.stage (w t))(hT : Ride r.diameter φ T w) {t : ℕ→ Expression Z.sector.derivatives}{c : ℝ} (ht:r.booked Z M c φ T w x i.val t) [φ.NeBot] : Funds Z M φ T (r.avenue i.val w x) 0 c t:=by
   obtain ⟨v,hv,he⟩:= hT.entries (r.register i.val); exact (ht v ⟨hv,he⟩).coarsen hT.height h (habitat0 i hh hT.height he) (r.along_paths i w x) hv.1 hv.2 le_rfl
namespace Backdrop
variable [Fintype J]
variable {δ : ℝ} {θ : Backdrop S r d}{α : W→ Viewers Z} {M : Devices Z.sector.derivatives}
lemma hierarchy_cost (hθ : θ.Eligible δ)(A : Services C F S): Loan Z M r 1 (θ.polls M α):= by
    refine ⟨lit hθ,Bill.one,?_⟩; intro φ _ T w x c hp hc he _ e hh; have hc:= RateEqual hc (RateIs.const hp.height one_pos); subst c; rw [zero_add]; refine RateLE.congr (final_counts (α:=α) hθ he hp.height A e _ (fun i hi=> layer_coarsen (r:=r) A M ⟨i,hi⟩ w x he hp (hh i hi))) (Eventually.of_forall fun i=> (θ.voted M α _ (x i) (fun j=> e j i)).symm)
end Backdrop
end YM.Contacts.Solstice
