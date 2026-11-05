import YM.Push.FREE_RESOLVENT.JetWindows
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gap

set_option warningAsError false

/-!
# Authentic block predictors over a common patch

Copy to a sufficiently large *single reference period* (obtain higher
mixed chart jets there). This proof adapts the fixed-L one-derivative-on-a-chart
comparison's `connect` (private, GAUSSIAN_SECTOR_CHANGE/Block) -- same
cover lemmas for the actual k frame and Q. The projection is independent of V,
U, chart and of the derivatives taken; records the support as well. Coordinates
not inspected in this predictor are blank ONLY in this inspection lemma, not in
the precision or volume.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance.Press
open Function Filter Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open YM.Push.SectorMeasure YM.Push YM.Next.Fluctuations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

section locality

variable (P : Patch) (o : Axis)

-- No particular geometric efficiency needed for this fixed-patch receipt.
private def frameSites : Finset Cover := univ.biUnion fun x : P.Points => univ.biUnion
  fun y : P.Points => univ.biUnion fun l : Lattice.Order => (visits x.val (route x.val y.val l)).toFinset

private def alongBond := List.replicate P.L.val (posDir o)
private def bondShift : Cover := centerRoot P (step o)

private def predSites := (frameSites P ∪ (frameSites P).image (· + bondShift P o)) ∪
  univ.biUnion (fun x : P.Points => (visits x.val (alongBond P o)).toFinset)

private lemma frame_eq (K : KernelChoices) (hb : P.Branches K G)
    (U W : CoverConfig G) (h : ∀ i : Edge Cover, i.1 ∈ frameSites P → U i = W i)
    (t : P.FrameTag) : P.frame K U t = P.frame K W t := by
  have he (x y : P.Points) (l : Lattice.Order) : travel U x.val (route x.val y.val l) =
      travel W x.val (route x.val y.val l) := by
    apply travel_local _ _ U W
    exact fun i hi _ => h i (mem_biUnion.mpr ⟨x,mem_univ x, mem_biUnion.mpr ⟨y,mem_univ y,
      mem_biUnion.mpr ⟨l,mem_univ l,List.mem_toFinset.mpr hi⟩⟩⟩)
  have hax (x : P.FrameTag) : P.axial U x = P.axial W x := funext fun i => he x.1 i x.2
  have hv (f : P.Frame G) : P.via f U = P.via f W := by funext x y l; rw [via, via, he]
  have hs : P.score U = P.score W := by funext r; simp only [score,hv]
  have hm : P.usesMin K U ↔ P.usesMin K W := by simp only [usesMin,hax,hv]
  unfold Patch.frame
  by_cases hh : P.usesMin K W
  · rw [if_pos hh, if_pos (hm.mpr hh)]
    have h' : P.minimizing W (P.selected U) := by
      simp only [minimizing, ← hs]
      exact (P.min_exists U).choose_spec
    exact (hb.frame_unique W hh).unique h' (P.min_exists W).choose_spec
  · rw [if_neg hh, if_neg (fun h => hh (hm.mp h)), hax]

-- Make the different evaluation origins into explicit finite-cover reads.
private def predictionAt (K : KernelChoices) (U : CoverConfig G) (l r : P.FrameTag) (j : P.Points) :=
  P.predict K (fun x => P.frame K U l x * travel U x.val (alongBond P o) *
    (P.frame K (translate (bondShift P o) U) r x)⁻¹) j

private lemma predAt_eq (K : KernelChoices) (hb : P.Branches K G) (U W : CoverConfig G)
    (h : ∀ i : Edge Cover, i.1 ∈ predSites P o → U i = W i)
    (l r : P.FrameTag) (j : P.Points) : predictionAt P o K U l r j = predictionAt P o K W l r j := by
  have he : P.frame K U l = P.frame K W l := frame_eq P K hb U W
    (fun i hi => h i (mem_union_left _ (mem_union_left _ hi))) l
  let y := bondShift P o
  have hh : P.frame K (translate y U) r = P.frame K (translate y W) r := frame_eq P K hb _ _ (by
    intro i hi; unfold Lattice.translate; apply h
    exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hi))) r
  have hu (x : P.Points) : travel U x.val (alongBond P o) = travel W x.val (alongBond P o) :=
    travel_local _ _ U W fun i hi _ => h i <| mem_union_right _ (mem_biUnion.mpr
      ⟨x,mem_univ x,List.mem_toFinset.mpr hi⟩)
  unfold y at hh
  simp only [predictionAt, he, hh, hu]

private lemma reads_at (U : Config G f) (k : S.Choices) (q : Site c) (i : Axis) :
    S.prediction U k (q,i) = predictionAt S.patch i S.kernel (expandAt (S.ratio.embed q) U)
      (k.1 q) (k.1 (q+step i)) (k.2 (q,i)) := by
  have he := levels S q U (step i)
  rw [plank, wrap_step, add_comm] at he
  unfold predictionAt StepData.prediction StepData.connector StepData.frames bondShift alongBond; rw [he]

private lemma transReach {i : Axis} {x : Cover} (hx : x∈predSites S.patch i) : (route 0 x 1).length ≤ predReach S.patch := by
  unfold predReach
  exact le_trans (le_sup (f:=fun x => (route 0 x 1).length) hx) (le_sup (f:=fun i =>
    (predSites S.patch i).sup (fun x => (route 0 x 1).length)) (mem_univ i))

private lemma onto {i : Axis} {x : Cover} (hx : x∈predSites S.patch i) (q : Site c) :
    separation q (S.ratio.parent (wrap f x + S.ratio.embed q)) ≤ predReach S.patch := by
  let w := route 0 x 1
  let s := S.ratio.embed q
  have hh : stop s w = wrap f x + s := by simpa only [map_zero, add_zero, add_comm] using Work.E03.stop_route s 0 x
  rw [← hh]
  apply le_trans ?_ (transReach hx)
  nth_rewrite 1 [← S.ratio.embed_parent q]
  exact Work.E03.sep_walk _ (Work.E03.parent_step S) _ w

end locality
section prices
variable (P : Patch) (K : KernelChoices) (G : Gauge)

private lemma reference_exists : ∃ c₀ : Side, 1 < c₀.val ∧
    ∀ i : Axis, ∀ x ∈ predSites P i, lift (wrap (c₀*P.L) x) = x := by
  let M := univ.sup (fun i : Axis => (predSites P i).sup (fun x => univ.sup (fun a : Axis => (x a).natAbs)))
  let c₀ : Side := ⟨2*M+2, by omega⟩
  refine ⟨c₀, by change 1 < 2*M+2; omega,fun i x hx => lift_eq_iff.mpr ⟨rfl,fun a => ?_⟩⟩
  have hv : (x a).natAbs ≤ M := le_trans (le_sup (s:=univ) (f:=fun a => (x a).natAbs) (mem_univ a))
    (le_trans (le_sup (s:=predSites P i) (f:=fun x => univ.sup (fun a : Axis => (x a).natAbs)) hx)
      (le_sup (s:=univ) (f:=fun i => (predSites P i).sup (fun x => univ.sup (fun a : Axis => (x a).natAbs))) (mem_univ i)))
  have ht : 2*M < (c₀*P.L).val := lt_of_lt_of_le (b:=c₀.val) (by change _ < 2*M+2; omega)
    (by exact le_mul_of_one_le_right (Nat.zero_le _) P.L.property)
  omega


/-- Take a finite common reference frame for all charts needed in an actual
predictor. Blanks chosen fixed one on this test; no period-uniform direction
price has yet been used. -/
lemma impression (h : P.Branches K G) : ∃ c₀ : Side, 1 < c₀.val ∧
    ∀ {c f : Side} (hv : f.val=c.val*P.L.val),
      let S : StepData c f := ⟨P,K,hv⟩; let T : StepData c₀ (c₀*P.L) := ⟨P,K,rfl⟩
      ∀ (x : Site c) (i : Axis) (k : S.Choices), ∃ (k₀ : T.Choices)
        (Q : Bond (c₀ * P.L) → Bond f) (J : Bond (c₀*P.L) → Bool),
        (∀ e, J e=true → separation x (S.ratio.parent (Q e).1) ≤ predReach P) ∧
        ∀ U : Config G f, S.prediction U k (x,i) = T.prediction (fun e => if J e then U (Q e) else 1) k₀ (0,i) := by
  obtain ⟨c₀,hc,hu⟩ := reference_exists P
  refine ⟨c₀,hc,?_⟩
  intro c f hv S T x i k
  haveI : Fact (1 < c₀.val) := ⟨hc⟩
  have ha : Lattice.step i ≠ (0:Site c₀) := by
    intro he
    have h : (1 : ZMod c₀.val) = 0 := by simpa using congr_fun he i
    exact one_ne_zero h
  let k₀ : T.Choices := (fun y => if y=0 then k.1 x else k.1 (x+Lattice.step i), fun _ => k.2 (x,i))
  let s := S.ratio.embed x; let s' := T.ratio.embed 0
  let B := c₀*P.L
  let X (y : Site B) := wrap f (lift (y-s'))+s
  let J (u : Bond B) := decide (lift (u.1-s') ∈ predSites P i)
  let Q (u : Bond B) : Bond f := (X u.1, u.2)
  let F (U : Config G f) : Config G B := fun v => if J v then U (Q v) else 1
  have read (U : Config G f) (v : Cover) (p : Axis) (h : v∈predSites P i) : expandAt s' (F U) (v,p) = expandAt s U (v,p) := by
    unfold expandAt F
    have hx : J (wrap B v+s',p) = true := by apply decide_eq_true; change lift (wrap B v+s'-s')∈_; rwa [add_sub_cancel_right,hu i v h]
    rw [if_pos hx]; unfold Q X; rw [show ((wrap B v+s',p):Bond B).1-s'=wrap B v by simp,hu i v h]
  refine ⟨k₀,Q,J, ?_, fun U => ?_⟩
  · exact fun e he => onto (S:=S) (of_decide_eq_true he) x
  rw [reads_at, reads_at]
  have ht : k₀.1 (0+Lattice.step i)=k.1 (x+Lattice.step i) := by dsimp only [k₀]; rw [zero_add, if_neg ha]
  change predictionAt P i K _ _ _ _ = predictionAt P i K _ _ _ _
  rw [ht, show k₀.1 0=k.1 x from if_pos rfl]; apply predAt_eq P i K h
  exact fun z hz => (read U z.1 z.2 hz).symm
end prices
end YM.AnalyticBridge.Covariance.Press
