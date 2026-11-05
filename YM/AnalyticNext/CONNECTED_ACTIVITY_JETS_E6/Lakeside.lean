import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Erosion
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lagoon
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rasura
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Turns

/-!
# Gated sampling of a weak atom at the derivative evaluation point

All gauge paths chosen once in *estimates*. `V` itself need not be in one
chart. The receptive `u` still must match wherever measured. Smaller halo
(< radiusB) permits using this jointly. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Frond
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Scroll Strokes Quill Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {V : Config G c} {U : Config G f}
variable {s : ℝ} {P : Teller G} {L : Side} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {j : ℕ}
open Brush

/-- Require U match on ≤7B/8 (so available from a B protector).
No far κ usage. `L` post hull. -/
private lemma concentration (H : Room P S T s) (o : Spot c f) (k : S.Choices) (z : Site c→G.El)
    (x : ZipP G c f) (a : Directions G f) (d : ℕ) (hd : 7*radiusB s /8≤d)
    (he : AgreeNear id (lead S o) d (gauge z V) (increment 1 x.1))
    (ht : AgreeNear S.ratio.parent (lead S o) d U (increment (replica S.ratio V) a))
    (hv : ∀ p : Bond f, separation (lead S o) (atEdge S p) ≤ d → spinRow S z a p=x.2 p) :
    squarepot T s k U V a o=ivy T s k o x := by
  let b:= lead S o; let G':= constantGauge z S.ratio; let P':=gauge G' U; let V':=gauge z V; let q:=S.prediction U k
  let w:=increment 1 x.1; let u:= shaft S x; let B:=radiusB s
  have hp := H.sight
  have hl:= SectorMeasure.funds_branch H.accepted
  obtain ⟨W,K,hP,-⟩ := H.accepted.feeds
  have hx : AgreeNear S.ratio.parent b d P' u := by
    intro i hi
    have hf : gauge G' (increment (replica S.ratio V) a) i=increment (replica S.ratio V') (spinRow S z a) i := by
      rw [← copied _ S.patch.odd_side]; unfold Lattice.gauge; simp only [increment,spinRow,exp_adjoint]
      change G' i.1*_*_=G' i.1*_* (G' i.1)⁻¹*(G' i.1*_*_); unfold G'; group
    rw [show P' i=gauge G' (increment (replica S.ratio V) a) i by unfold P' Lattice.gauge; rw [ht i hi],hf];
    unfold u shaft increment; rw [hv i hi,replica_near he i hi]; rfl
  unfold squarepot ivy
  rw [← winds z U V H.accepted s o k true, rivers H o k k (he.shrink (by rw [separation_self]; omega)) (hx.shrink (by change separation b b+_≤_; rw [separation_self]; omega)) ?_ true]
  swap
  · intro i hi; exact prediction_near_eq hl _ _ k i (hx.shrink (by simp only [id_eq] at hi; unfold b; omega))
  refine congr_arg₂ (·-·) rfl (Finset.sum_congr rfl fun i hi=> ?_)
  change ‖freely _ _ _ _ _+_‖^2/2=‖freely _ _ _ _ i+_‖^2/2
  have hf : focus S i=b := by rw [cost_is_here i,(parent_iff ..).1 hi]
  let R:=till s; let p:= he.shrink (q':=focus S i) (D':=B/4) (by rw [hf]; change separation b b+B/4≤d; unfold B; rw [separation_self]; omega)
  rw [← G.norm_adjoint (z (focus S i)),map_add, ← peony z H.accepted, ← under T hP]
  rw [show straightened T (till s) V' (spinRow S z a) i=straightened T R w x.snd i from ?_]
  · unfold freely baseStroke; rw [entry_stencil H _ _ _ _ k i (replica_near p) p, shoreVisa H i p]
  refine short_near T hl _ _ _ _ _ i (B/4) ?_ p ?_
  · unfold B; have hz:=H.frame; unfold till; omega
  intro j hj; apply hv j; change separation (focus S i) _≤_ at hj; rw [hf] at hj; unfold b at hj; omega

lemma earth (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) {Q : ℝ→ℝ}
    (h : Rate G L (-(1/2)) Q) (hp : ∀ᶠ x in atTop,0≤Q x) :
    ∃ F : ℝ→ℝ, Rate G L (-(3/2)) F ∧ ∀ᶠ s : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T →
    ∀ (k:S.Choices) (o:Spot c f) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (V : E→Config G c)
      (U:E→Config G f) (a:E→Directions G f) (x:E), Mode V x j (Q s) →
       let d:= 7*radiusB s/8
       Clean (V x) s (lead S o) (d+1) → (∀ p:Bond f, distAt S p (lead S o)≤d→ Brush j (Q s) 1 (fun i=> a i p) x) →
         (∀ᶠ v in 𝓝 x, AgreeNear S.ratio.parent (lead S o) d (U v) (increment (replica S.ratio (V v)) (a v))) →
         Brush j (F s) 1 (fun i=>squarepot T s k (U i) (V i) (a i) o) x := by
  obtain ⟨Z,hZ,hk⟩ := base_ray P L j h hp
  let f s:= Z s+Q s; let p s:= f s+f s; have hF : Rate G L (-(1/2)) f:=hZ.add h; have hM := hF.add hF
  obtain ⟨A,F,hA,hB,hP⟩:= evokes P L D hD j hM (by filter_upwards [hp,hk] with s hs he; exact add_nonneg (add_nonneg he.1 hs) (add_nonneg he.1 hs))
  refine ⟨_,parseRate j hA hM (by norm_num) (show Rate G L (- -(1/2)) A by rw [neg_neg]; exact hB),?_⟩
  filter_upwards [hp,hk,hP, room G P L] with s Hp H Hx HT c f' S T hD hs k o E _ _ V U a x hV d he ha hv
  obtain ⟨z,b,h₁,h₂⟩:= H.2 _ _ S T hs E V x d _ hV (by unfold d; omega) he; let y:=lead S o
  let c' i (p : Bond f'):= if distAt S p y ≤ d then spinRow S z (a i) p else 0
  have hh : Brush j (Q s) 1 c' x := by
    refine Brush.fold zero_le_one Hp (fun i=>?_)
    change Brush j (Q s) 1 (fun j=>c' j i) x; dsimp only [c']; split_ifs
    next ht =>
      have hk := (ha i ht).report (G.adjoint (z (atEdge S i))).toContinuousLinearMap (v:=1)
        (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v=> le_of_eq (by change ‖G.adjoint _ _‖= _; rw [G.norm_adjoint,one_mul])))
      rw [one_mul] at hk; exact hk
    exact (certified zero_le_one (0:G.Color)).climb (by rwa [norm_zero]) le_rfl
  let f' i := (b i,c' i)
  have ht : Brush j (p s) 1 f' x := Brush.pair (h₁.climb (le_add_of_nonneg_right Hp) le_rfl) (hh.climb (le_add_of_nonneg_left H.1) le_rfl)
  have hu := scaled ht (Hx _ _ S T hD hs k o _ ht.bound)
  apply (hu.trim).shimmy
  filter_upwards [h₂,hv] with i he hv
  exact concentration (HT _ _ _ _ hs) o k z _ (a i) d le_rfl he hv (fun p hp => Eq.symm (if_pos hp))
end YM.ConnectedActivityE6.Blaze.Frond
