import YM.Contacts.Solstice.Windows
/-!
# Common core formula on overlaps, recovering ordinary functions

Keep positions and tests in the same ambient plane containing the total norms of these groups
for both local recipes; tag collectors need care on words since the requested output response may
have no meaning outside individual tests. But the untagged expressions already agree on those
opportunities, **before** taking integrals. Y's relative operations obey the punctured recipe
independent of further cut placements. Equations that put together punctured products during
one step while allowing all other parallel pairs/groups choices can use `System.refines` and
`System.departure`, `System.onPatch`. The direct comparison here applies to whole memberships
also when the patches are not subordinate to one another.

No assertion that the raw point stabilizers agree as tuples of germs on supports; all equalities
in terms of action on mask-tests. For instance Taylor tests throughout other disjoint groups are
in the same integrated tensor.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory TensorProduct
variable {E W W' I I' J : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {G: Gauge}{C : Family G}{F : Extraction.Order}{S: Table C.book}{Z : Final C F S}
variable {k : ℕ}{g : Normal.Group k} (P:E→ₗᵢ[ℝ] Points k) {Q R : Pieces g}
local notation "GN" => Normal.Group k

structure GroupsTest (P:E→ₗᵢ[ℝ] Points k) (Q : Pieces g)(o : Points k)(U : Set E) : Prop where
   full i (h : i∈ Q.parts) : plane i≤ LinearMap.range P.toLinearMap
   alongside i (h : i∈Q.parts) : Collapsed i o
   separate : ∀ x∈U,∀ i∈ Q.parts,∀ j∈Q.parts,i≠j → ∀ a∈i,∀ b∈j,(P x+o) a ≠ (P x+o) b

variable {A : Type}[CommRing A][Algebra ℂ A]
variable (Y:System E A k) (s:ℝ)
lemma crosses_true (T : Pieces g) (ht : T≤ Q)(h : ¬ T ≤ R) {o : Points k}{p : SmoothTests E}
  (hx : ∀ i∈Q.parts, plane i ≤ LinearMap.range P.toLinearMap) (hx' : ∀ i∈Q.parts,Collapsed i o)
  (hm : ∀ x∈ tsupport p.val,∀ i∈ R.parts,∀ j∈R.parts,i≠j → ∀ a∈i,∀ b∈j,(P x+o) a≠(P x+o) b) : parcel (Y.cumulant P s) T * instructionScore E A (mask p)=0:=by
   obtain ⟨l,hl,i,hi,j,hj,he,a,ha,b,hb,ha',hb'⟩:= crossing h; obtain ⟨f,hf,hk⟩:= ht hl; rw [parcel,split_last _ hl _ ((Y.compatible P s).stands T),mul_assoc, all_off (K:=normalOn P l) (?_) (Y.translatesOrigin P s l),mul_zero]; intro x hxL hw
   apply hm x hw i hi j hj he.symm a ha' b hb'; simp only [PiLp.add_apply]; rw [(collapsed_iff ..).1 (hx' f hf) a (hk ha) b (hk hb), (collapsed_iff ..).1 ( (local_collapse ((plane_le hk).trans (hx f hf)) x).2 ((normalOn P l).starProjection_apply_eq_zero_iff.mpr hxL)) a ha b hb]

/-- untagged overlap value. use on any common placement where linear reader meaningful. -/
lemma coincides {p : SmoothTests E}{o : Points k} (hQ : GroupsTest P Q o (tsupport p.val))(hR : GroupsTest P R o (tsupport p.val)) :
   parcel (Y.full P s) Q * instructionScore E A (mask p)= parcel (Y.full P s) R * instructionScore E A (mask p):=by
    unfold System.full; rw [← full_expands (Y.cumulant P s) Q (Y.compatible P s), ← full_expands (Y.cumulant P s) R (Y.compatible P s), Finset.sum_mul, Finset.sum_mul]; let f:= Finset.univ.filter (fun x:Pieces g=>x≤Q∧x≤R)
    trans ∑ x∈f, parcel (Y.cumulant P s) x * instructionScore E A (mask p)
    · symm; apply Finset.sum_subset (fun x hx=>Finset.mem_filter.mpr ⟨Finset.mem_univ x,(Finset.mem_filter.mp hx).2.1⟩); intro x hx hw
      have he: x≤ Q:= (Finset.mem_filter.mp hx).2; exact crosses_true P Y s x he (fun hh=>hw (Finset.mem_filter.mpr ⟨Finset.mem_univ x,he,hh⟩)) hQ.full hQ.alongside hR.separate
    apply Finset.sum_subset (fun x hx=>Finset.mem_filter.mpr ⟨Finset.mem_univ x,(Finset.mem_filter.mp hx).2.2⟩); intro x hx hw; have he:x≤R:= (Finset.mem_filter.mp hx).2; exact crosses_true P Y s x he (fun hh=> hw (Finset.mem_filter.mpr ⟨Finset.mem_univ x,hh,he⟩)) hR.full hR.alongside hQ.separate
lemma overlap_action {p : SmoothTests E}{o : Points k} (hQ : GroupsTest P Q o (tsupport p.val))(hR : GroupsTest P R o (tsupport p.val)) (x:E): action x p (parcel (Y.full P s) Q) = action x p (parcel (Y.full P s) R) := by
    let K:=coincides P Y s hQ hR; let t: SmoothTests E:= ⟨fun _=>1, (contDiff_const (c:=(1:ℂ)): ContDiff ℝ ∞ ((fun _=>1):E→ℂ))⟩; have he:=congrArg (action x t) K; rw [takeRight,takeRight,show mask p t=p from Subtype.ext (funext (fun x=>mul_one _))] at he; exact he
lemma top_parcel (g : GN) (h : g.Nonempty) : parcel (Y.full P s) (root g)= Y.full P s g:= by unfold parcel; rw [one_set _ rfl h,Ordered.product_one]
omit [FiniteDimensional ℝ E] in
lemma top_groups {o : Points k}(v : Set E)(h : plane g ≤ LinearMap.range P.toLinearMap) (he : Collapsed g o) : GroupsTest P (root g) o v:= ⟨fun _ hi=>(plane_le ((root g).le hi)).trans h,fun _ hi=> he.subgroups ((root g).le hi), fun _ _ _ hi _ hj hh _ _=> (hh ((Finset.mem_singleton.mp ( (Finpartition.parts_top_subset g) hi)).trans (Finset.mem_singleton.mp ((Finpartition.parts_top_subset g) hj)).symm)).elim⟩

section Files
variable {A' : Type} (Y' : System E (Grammar A') k) (t:ℝ)
lemma cleared_events (Q : Pieces g) : retag E eraseTags (Y'.election P t (festive k) Q)= parcel (Y'.full P t) Q:= by
   rw [System.standard P t Y' (festive k) Q (fun i _=> rfl),System.coupled,System.forest, parcel, retag_product]; unfold parcel; refine Ordered.eq_product fun i hi=> ?_; rw [show retag E eraseTags (retag E (tag i) _)=_ from reconnect (I:=GN) (E:=E) (A:=A') i eraseTags (AlgHom.id ..) (erase_tags i) _]; exact reshape_id _
lemma cleared_action (p : SmoothTests E)(x:E) : eraseTags (action x p (Y'.election P t (festive k) Q))= action x p (parcel (Y'.full P t) Q) := by rw [← cleared_events,retags,action_reshape]; rfl
end Files
variable {P}
-- sufficient to compare strict extended even when not in the top-level detector collar.
lemma onstage (r : Route P Q I W) (w : W) {p:SmoothTests E}(hx : tsupport p.val⊆r.stage w){δ:ℝ}(hp:0<δ)(hh : Sober r δ) : GroupsTest P Q (r.offset w) (tsupport p.val):= by
  refine ⟨r.displaysNormals,r.aligned w,fun x hx' i hi j hj he a ha b hb hw=>?_⟩; let V:= r.actualAt w x
  have ht (i) (hi:i∈Q.parts)(a:Fin k)(ha:a∈i) : V a∈ r.palette w i x:= ⟨⟨{a},Finset.singleton_subset_iff.mpr ha,Finset.singleton_nonempty _⟩,centroid_single _ a⟩
  have he:=hh (⟨i,hi⟩:Q.parts) ⟨j,hj⟩ (fun h=> he (congr_arg Subtype.val h)) w x (hx hx') (V a) (ht i hi a ha) (V b) (ht j hj b hb); rw [show V a= V b from hw,sub_self,norm_zero] at he; exact he.not_gt hp

variable (M : Devices Z.sector.derivatives){d:Fin k→ℕ}
def localImage (P:E→ₗᵢ[ℝ] Points k) (Q : Pieces g)(o:Points k)(t:ℝ) (T: Cells S d) (p:SmoothTests E)(x:E): Expression Z.sector.derivatives:= action x p (parcel ((waySystem P M o d T).full P t) Q)

lemma image_route (r : Route P Q I W) {d' : J→ℕ} [Fintype J] (θ : Backdrop S r d') (T : W→ Cells S d) (α : W→ Viewers Z)(w:W)(p:SmoothTests E)(x:E): θ.finalReading M α w x (localImage M P Q (r.offset w) (r.length w) (T w) p x)= r.windings M (θ.polls M α) T (festive k) w p x:= by
   have h:= cleared_action (Q:=Q) P (r.components M T w) (r.length w) p x; exact congrArg (θ.finalReading M α w x) h.symm
lemma top_image {r : Route P Q I W}(H : g.Nonempty) {w:W} (T : W→ Cells S d)(f : SmoothTests E){δ : ℝ}(hd:0<δ)(ht : Sober r δ)(hv : tsupport f.val⊆ r.stage w)(h : plane g ≤ LinearMap.range P.toLinearMap)(he : Collapsed g (r.offset w))(x:E): action x f ((r.components M T w).full P (r.length w) g)= localImage M P Q (r.offset w) (r.length w) (T w) f x:= by rw [← top_parcel _ _ _ _ H]; exact overlap_action P (waySystem P M _ _ _) _ (top_groups _ _ h he) (onstage _ _ hv hd ht) x -- ambiguous underscores implicit opts?

-- all singleton parts already: agreement independent of choices Y on any remaining proposals everywhere.
local notation "𝔈" => Expression Z.sector.derivatives
private def incl (E A:Type)[NormedAddCommGroup E][NormedSpace ℝ E][CommRing A][Algebra ℂ A] : (E→A)→+* Score E A:= (Algebra.TensorProduct.includeLeft : (E→ A) →ₐ[ℂ] Score E A).toRingHom
lemma at_singles (T:System E A k)(h : ∀ i∈Q.parts,i.card≤1)(t : ℝ) : parcel (T.full P t) Q=(∏ j∈ g,T.field j) ⊗ₜ[ℂ] (1:Optical E):= by
   let f(i:GN):= ∏ j∈ i,T.field j; have he: ∏ j∈ Q.parts, f j= ∏ j∈g,T.field j:= (Finset.prod_biUnion (s:=Q.parts) (t:=id) Q.disjoint).symm.trans (?_) -- implement
   swap; · congr; exact Q.biUnion_parts
   unfold parcel; have hh(i:GN)(hi:i∈Q.parts) : T.full P t i = incl E A (f i):= by obtain ⟨k,rfl⟩:= alone_in h hi; rw [System.full_single]; unfold f; rw [Finset.prod_singleton]; rfl
   rw [eq_product hh, ← show incl E A (Ordered.product Q.parts f)=Ordered.product Q.parts (fun i=>incl E A (f i)) from Ordered.mapped _ f _, Ordered.product_true,he]; rfl
end YM.Contacts.Solstice
