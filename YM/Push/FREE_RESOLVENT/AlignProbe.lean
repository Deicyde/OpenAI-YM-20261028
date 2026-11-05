import YM.Push.FREE_RESOLVENT.Views

/-!
# Genuine Q jet comparisons

Price a single finite patch before varying volume. Covers include every frame
argument, along corresponding displaced patches and connectors. `Align`
always means the actual U,V axes coincide. At the flat field (where we take
Taylor coefficients here) tags not required to match: the unique optimizing
branches apply *on a neighborhood for each test*. In particular results work
on ANY actual shared tag specification; no likelihood manipulation, no trying
to differentiate across switches. Compare kinematic square with no holes only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine.View
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open Work.F08 Lifted
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c f' c' : Side} {S : StepData c f} {P : Patch} {K : KernelChoices}
variable {h : f.val=c.val*P.L.val} {h' : f'.val=c'.val*P.L.val}


def haze (P : Patch) := Finset.univ.sup fun i : P.Points => size i.val
def cross (P : Patch) := Finset.univ.sup fun i : P.Points => Finset.univ.sup fun j : P.Points =>
  Finset.univ.sup fun k : Lattice.Order => (route i.val j.val k).length

def reach (P : Patch) := haze P+cross P+P.L.val

def Watch (S : StepData c f) (k : S.Choices) (p : pair G c f) :=
  (∀ x, S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) (unwrapped S p))) ∧
  ∀ e, S.patch.usesBest S.kernel (S.connector (unwrapped S p) k.1 e)

lemma watches (S : StepData c f) (k : S.Choices) (hb : S.patch.Branches S.kernel G) :
    ∀ᶠ p : pair G c f in 𝓝 0, Watch S k p := by
  -- use actual represent/log chart identification on this neighborhood. No uniform radius asserted/needed for jets.
  let L (x : pair G c f) : Dir G f := fun i => G.plog (G.mat (unwrapped S x (i.1,axisEquiv.symm i.2)))
  have hz : unwrapped S (0 : pair G c f)=1 := (white _).trans (back_flat ..)
  have ht : ∀ e : Edge (Site f), Tendsto (fun p : pair G c f => unwrapped S p e) (𝓝 0) (𝓝 1) := fun e => by
    have h : ContinuousAt (fun p => unwrapped S p e) (0 : pair G c f) :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (active_smooth e).continuous.continuousAt.tendsto
    convert! h.tendsto; rw [hz]; rfl
  have hv : Tendsto L (𝓝 0) (𝓝 0) := tendsto_pi_nhds.mpr fun i => by
    have he := G.plog_diff.continuousAt.tendsto; rw [G.plog_one] at he
    exact he.comp ((G.continuous_mat.tendsto 1).comp (ht _))
  have hf : ∀ᶠ x in 𝓝 0, ∀ e : Edge (Site f), G.lieExp (G.plog (G.mat (unwrapped S x e)))=unwrapped S x e :=
    eventually_all.mpr fun e => (ht e).eventually G.plog_right
  have h1 : ∀ᶠ x in 𝓝 (0 : Dir G f), ∀ y : Site c, S.patch.usesMin S.kernel (expandAt (S.ratio.embed y) (represent x)) :=
    eventually_all.mpr fun y => Push.threshold S y
  have h2 : ∀ᶠ x in 𝓝 (0 : Dir G f), ∀ e : Edge (Site c), S.patch.usesBest S.kernel (S.connector (represent x) k.1 e) := by
    refine eventually_all.mpr fun e => ?_
    have he : ContinuousAt (Push.deck (G:=G) S e k.1) 0 := continuousAt_pi.mpr fun i =>
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (Push.builds S hb _ k.1 i).continuousAt.tendsto
    apply he.tendsto.eventually (S.patch.best_open.mem_nhds ?_)
    apply lt_of_le_of_lt ((S.patch.bond_min _).choose_spec 1)
    simpa [Patch.bondCost, Push.deck_zero S hb _ k.1] using S.kernel.predictor_cut_pos
  filter_upwards [hv.eventually h1,hv.eventually h2,hf] with p hp hq hP
  rw [Watch,← show represent (L p)=unwrapped S p from ?_]; exact ⟨hp,hq⟩
  ext1 i; rw [represent_link]; unfold L; rw [← coord_map, axisEquiv.symm_apply_apply]; exact hP i

variable {o : Site c} {o' : Site c'} {R : ℕ} {p : pair G c f} {p' : pair G c' f'}
variable (hc : 1<c.val) (hc' : 1<c'.val)

lemma ground (S : StepData c f) (o : Site c) (z : Cover) (x : Cover) :
    wrap f x+S.ratio.embed (addr o z)=bottom S o (z+carry (0:Site S.patch.L) x) (arrives (0:Site S.patch.L) x) := by
  rw [add_comm,← bottom_root, bottom_adv]

lemma frame_cost (P : Patch) (a b : P.Points) (k : Lattice.Order) (z : Cover) :
    size (z+carry (0:Site P.L) a.val)+(route a.val b.val k).length ≤ size z+View.reach P := by
  have he : size (z+carry (0:Site P.L) a.val) ≤ size z+haze P := (size_add ..).trans (Nat.add_le_add_left
    ((carry_size ..).trans (Finset.le_sup (f:=fun i : P.Points => size i.val) (Finset.mem_univ a))) _)
  have hh : (route a.val b.val k).length ≤ cross P :=
    (Finset.le_sup (f:=fun j => (route a.val b.val j).length) (Finset.mem_univ k)).trans <|
      (Finset.le_sup (f:=fun i : P.Points => Finset.univ.sup fun j : Lattice.Order => (route a.val i.val j).length) (Finset.mem_univ b)).trans <|
        (Finset.le_sup (f:=fun x : P.Points => Finset.univ.sup fun i : P.Points =>
          Finset.univ.sup fun j : Lattice.Order => (route x.val i.val j).length) (Finset.mem_univ a))
  unfold reach; omega

variable {k : (data h K).Choices} {k' : (data h' K).Choices}

include hc hc'
lemma closeFrame (z : Cover) (hb : P.Branches K G) (H : Reads p p' h h' K o o' R)
    (hx : size z+reach P ≤ R) (hp : Watch _ k p) (hp' : Watch _ k' p') :
    (data h K).frames (unwrapped (data h K) p) k.1 (addr o z)=(data h' K).frames (unwrapped (data h' K) p') k'.1 (addr o' z) := by
  let U := expandAt ((data h K).ratio.embed (addr o z)) (unwrapped (data h K) p)
  let V := expandAt ((data h' K).ratio.embed (addr o' z)) (unwrapped (data h' K) p')
  have he (a b : P.Points) (k : Lattice.Order) : travel U a.val (route a.val b.val k)=travel V a.val (route a.val b.val k) := by
    unfold U V; rw [travel_at,travel_at, ground,ground]
    exact H.march hc hc' (z+carry (0:Site P.L) a.val) _ _ ((frame_cost P a b k z).trans hx)
  have hh (w : P.Frame G) : P.score U w=P.score V w := by simp only [Patch.score,Patch.average,Patch.via,he]
  have hw (X : P.Frame G) (h : P.minimizing U X) : P.minimizing V X := ⟨h.1,fun A ha => by rw [← hh, ← hh]; exact h.2 A ha⟩
  have hu : P.usesMin K U := hp.1 (addr o z)
  have hv : P.usesMin K V := hp'.1 (addr o' z)
  change P.frame K U _ = P.frame K V _
  simp only [Patch.frame, if_pos hu,if_pos hv]
  exact (hb.frame_unique V hv).unique (hw _ (P.min_exists U).choose_spec) (P.min_exists V).choose_spec

lemma prognosis (z : Cover) (hb : P.Branches K G) (H : Reads p p' h h' K o o' R)
    (hx : size z+reach P+1 ≤ R) (hp : Watch _ k p) (hp' : Watch _ k' p') (i : Axis) :
    (data h K).prediction (unwrapped (data h K) p) k (addr o z,i)=(data h' K).prediction (unwrapped (data h' K) p') k' (addr o' z,i) := by
  have he (t : Site c) : addr t z+step i=addr t (z+step i) := by simp [addr,add_assoc]
  have he' : addr o' z+step i=addr o' (z+step i) := by simp [addr,add_assoc]
  let X := (data h K).connector (unwrapped (data h K) p) k.1 (addr o z,i)
  let X' := (data h' K).connector (unwrapped (data h' K) p') k'.1 (addr o' z,i)
  have hh : X=X' := by
    funext w
    unfold X X' StepData.connector
    have hz : size (z+step i) ≤ size z+1 := (size_add ..).trans (Nat.add_le_add_left (by
      simp [size,apply_ite Int.natAbs]) _)
    rw [travel_at,travel_at]
    simp only [he, he']; rw [closeFrame hc hc' z hb H (by omega) hp hp', closeFrame hc hc' (z+step i) hb H (by omega) hp hp',ground,ground]
    congr 2
    have ht : size (z+carry (0:Site P.L) w.val) ≤ size z+haze P :=
      (size_add ..).trans (Nat.add_le_add_left ((carry_size ..).trans (Finset.le_sup (f:=fun i : P.Points => size i.val) (Finset.mem_univ w))) _)
    exact H.march hc hc' (z+carry (0:Site P.L) w.val) _ (List.replicate P.L.val (posDir i)) (by rw [List.length_replicate]; unfold reach at hx; omega)
  have hq : P.usesBest K X := hp.2 _
  change P.predict K X _ = P.predict K X' _
  rw [← hh]; simp only [Patch.predict,hq,↓reduceIte]

/-- Member `PAC 1` includes global rotation action with backward site shift
for a negative positive-row representative. Prove equality of the oriented
prediction first. V_0 multiplied and inverted on the same channel. -/
lemma rotor (s : Signed) (z : Cover) (w : PAC G 1) (hb : P.Branches K G) (H : Reads p p' h h' K o o' R)
    (hx : size z+reach P+2 ≤ R) (hp : Watch _ k p) (hp' : Watch _ k' p') :
    pull s 0 ((data h K).prediction (unwrapped (data h K) p) k)
      (which ((coarseHere s o z w).1,w.1))=
    pull s 0 ((data h' K).prediction (unwrapped (data h' K) p') k')
      (which ((coarseHere s o' z w).1,w.1)) := by
  unfold which pull
  simp only
  rw [show affine s 0 (coarseHere s o z w).1 = _ from coarse_here s o z w, show affine s 0 (coarseHere s o' z w).1 = _ from coarse_here s o' z w]
  cases hs : Step.rotate (posDir (axisEquiv.symm w.1)) s with
  | mk i b =>
    cases b
    · exact prognosis hc hc' z hb H (by omega) hp hp' i
    simp only [Step.read,Step.used,↓reduceIte]
    rw [show addr o z-step i=addr o (z-step i) by unfold addr; rw [map_sub,wrap_step]; abel,
        show addr o' z-step i=addr o' (z-step i) by unfold addr; rw [map_sub,wrap_step]; abel]
    have he : size (z-step i) ≤ size z+1 := by
      rw [sub_eq_add_neg]; apply (size_add ..).trans; rw [size_neg]; simp [size,apply_ite Int.natAbs]
    rw [prognosis hc hc' (z-step i) hb H (by omega) hp hp' i]

lemma responseView (s : Signed) (z : Cover) (w : PAC G 1) (hb : P.Branches K G) (H : Reads p p' h h' K o o' R)
    (hx : size z+reach P+2 ≤ R) (hp : Watch _ k p) (hp' : Watch _ k' p') (hf : Watch _ k (p.1,0)) (hf' : Watch _ k' (p'.1,0)) :
    gaugeQ (data h K) s k p (coarseHere s o z w) = gaugeQ (data h' K) s k' p' (coarseHere s o' z w) := by
  have he := rotor hc hc' s z w hb H hx hp hp'
  have hh := rotor hc hc' s z w hb H.blank hx hf hf'
  rw [white,white] at hh
  exact congr_arg (fun v : G.El => G.projectColor (G.mat v) w.2) (congr_arg₂ _ he (congr_arg (fun v : G.El => v⁻¹) hh))
end YM.FreeResolvent.Affine.View
