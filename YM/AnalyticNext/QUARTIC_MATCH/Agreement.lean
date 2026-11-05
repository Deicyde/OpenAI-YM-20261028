import YM.AnalyticNext.QUARTIC_MATCH.Multiples
import YM.AnalyticNext.QUARTIC_MATCH.Residual
import YM.Work.B04


/-!
# Functoriality of the actual value on admission and repetitions

No equality of frozen likelihood measures assumed; this is classical germ data on
every permitted tag/forest. May use different comparison bounds after repetitions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Sheets
open Matrix Lattice RG Wilson Tree Precision Exterior Bid Filter Function Topology Joint
open Work.F04 Work.F05
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable (P : Patch) (K : KernelChoices) {G : Gauge} {c d : Side} (h : c.val∣d.val)

def spinUp (b : Deck h) : Vertical G d (d*P.L) →L[ℝ] Vertical G d (d*P.L) :=
    rephase (S:=stepAt P K d) 1 b.val

def cycle (b : Deck h) : Dir G d × Vertical G d (d*P.L) →L[ℝ] Dir G d × Vertical G d (d*P.L) :=
    (shifts 1 b.val).prodMap (spinUp P K h b)

section verticalShift

lemma spin_fst (b : Deck h) (v : Vertical G d (d*P.L)) (i : Body 1 (d*P.L)) :
    (spinUp P K h b v).1 i = v.1 (i.1 + (embedDeck P K h b).val,i.2) :=
    Joint.shift_one_apply ..
lemma spin_snd (b : Deck h) (v : Vertical G d (d*P.L)) (i : Site d) :
    (spinUp P K h b v).2 i = v.2 (i+b.val) := by
  change v.2 (affine 1 b.val i)=_
  simp [affine]
lemma spin_once (b y : Deck h) (v : Vertical G d (d*P.L)) :
    spinUp P K h b (spinUp P K h y v) = spinUp P K h (b+y) v := by
  apply Prod.ext
  · funext i; rw [spin_fst,spin_fst,spin_fst, show (embedDeck P K h (b+y)).val=(embedDeck P K h b).val+
      (embedDeck P K h y).val from (stepAt P K d).ratio.root.map_add _ _]; simp [add_assoc]
  funext i; simp only [spin_snd, AddSubgroup.coe_add,add_assoc]
lemma necklace (b : Deck h) (v : Dir G c × Vertical G c (c*P.L)) :
    cycle P K h b (rideAlong P h v) = rideAlong P h v := by
  apply Prod.ext
  · funext i
    change (shifts 1 b.val (reuses h v.1)) i=_
    rw [shift_one_apply]; change v.1 (project h _,i.2)=v.1 (project h _,i.2)
    rw [map_add, show project h b.val=0 from b.property,add_zero]
  change spinUp _ _ _ b (ride P h v.2) = _
  apply Prod.ext
  · funext i
    rw [spin_fst]; change v.2.1 (project _ _,i.2)=v.2.1 (project _ _,i.2)
    rw [map_add,show project (within P h) (embedDeck P K h b).val=0 from (embedDeck P K h b).property,add_zero]
  funext i; rw [spin_snd]
  change v.2.2 (project _ _) = v.2.2 (project _ _)
  rw [map_add,show project _ _=0 from b.property,add_zero]
lemma periodic_vertical (v : Vertical G d (d*P.L)) (hv : ∀ b : Deck h, spinUp P K h b v=v) : v ∈ Set.range (ride P h) := by
  refine ⟨(fun x => v.1 (pin (within P h) x.1,x.2),v.2 ∘ pin h),?_⟩
  apply Prod.ext
  · funext i; let F (j : Site (d*P.L)) := v.1 (j,i.2)
    refine congr_fun (periodic (within P h) F ?_) i.1
    intro y hy x
    obtain ⟨j,hj⟩ := embedDeck_onto P K h ⟨y,hy⟩
    have hb : F (x+(embedDeck P K h j).val)=F x := by rw [← show (spinUp P K h j v).1 (x,i.2)=F (x+_) from spin_fst ..,hv]
    rwa [hj] at hb
  refine periodic h v.2 ?_
  intro u hu x
  rw [← spin_snd P K h (b:=⟨u,hu⟩),hv]

lemma earnings [Fintype ↥(Deck h)] (v : Vertical G d (d*P.L)) :
    (∑ b : ↥(Deck h), spinUp P K h b v) ∈ Set.range (ride P h) := by
  refine periodic_vertical P K h _ (fun i => ?_)
  simp_rw [map_sum,spin_once]
  exact Equiv.sum_comp (Equiv.addLeft i) fun x => spinUp P K h x v
end verticalShift

variable {p : Clip} {W : PathData G}
variable {T : Forest (stepAt P K c).ratio} {B : Forest (stepAt P K d).ratio}
    {b : Dir G c → AxisChart G T} {u : Dir G d → AxisChart G B}
    {σ C Λ : ℝ}

section equivariance
variable (hb : P.Branches K G) (hW : W.Bounds p σ C Λ)
include hb hW

lemma cycle_law (B : Forest (stepAt P K d).ratio) (k : (stepAt P K d).Choices) (y : Deck h) :
    let F := Joint.action (stepAt P K d) k p W
    F ∘ cycle P K h y =ᶠ[𝓝 0] F := by
  intro F
  let S := stepAt P K d
  let t := S.withinChoice 1 y.val k
  have he : F ∘ cycle P K h y = Joint.action _ t p W :=
    funext fun x => (commutes (S:=stepAt P K d) p W hb 1 y.val k x)
  have hh : Tendsto (fun z : Dir G d × Vertical G d (d*P.L) => (z.1,slice B z)) (𝓝 0) (𝓝 0) := by
    have ht := (slice_jet (G:=G) B).continuousAt.tendsto
    rw [slice_zero] at ht
    exact (continuous_fst.tendsto _).prodMk_nhds ht
  rw [he]
  exact (Joint.reduce B hb hW t).trans (((tested_germ (S:=stepAt P K d) hb B _ _ t k).comp_tendsto hh).trans (Joint.reduce B hb hW k).symm)

lemma station_paid (hu : Critical B p W u) (t : (stepAt P K d).Choices) :
    let F := Joint.action _ t p W
    ∀ᶠ z in 𝓝 (0 : Dir G c × Vertical G c (c*P.L)), ∀ i : Deck h,
      vert F (rideAlong P h z)=vert F (rideAlong P h z) ∘L spinUp P K h i := by
  classical
  intro F; apply eventually_all.mpr; intro i
  let L := rideAlong (G:=G) P h
  let V := cycle P K h i (G:=G)
  have ht : Tendsto L (𝓝 0) (𝓝 0) := by simpa only [map_zero] using L.continuous.tendsto 0
  filter_upwards [ht.eventually (Filter.EventuallyEq.fderiv (𝕜:=ℝ) (cycle_law P K h hb hW B t i)),
    ht.eventually ((root_born hb hW hu t).eventually (by simp))] with z hz hx
  have he : V (L z)= L z := necklace ..
  have H : DifferentiableAt ℝ F (V (L z)) := he.symm ▸ (show ContDiffAt ℝ ω F (L z) from hx).differentiableAt (by simp)
  change fderiv ℝ (F ∘ V) (L z)=_ at hz
  rw [fderiv_comp (L z) H V.differentiableAt,V.fderiv,he] at hz
  apply ContinuousLinearMap.ext; intro v
  have hx : V (0,v) = (0,spinUp P K h i v) := Prod.ext (shifts 1 i.val (G:=G) |>.map_zero) rfl
  change fderiv ℝ F _ (0,v) = fderiv ℝ F _ (0,spinUp P K h i v)
  rw [← hx]; exact DFunLike.congr_fun hz.symm (0,v)

/-- Vanishing upstairs, despite possible terms using identified locations in
torus evaluations. Doesn't transport Hessian eigenvalues or radius. -/
theorem pays_vert (hb' : Critical T p W b) (hu : Critical B p W u) (k : (stepAt P K c).Choices) :
    let V := Joint.action _ k p W
    let A := Joint.action _ (mimic P K h k) p W
    ∀ᶠ x in 𝓝 0, vert V x=0 → vert A (rideAlong P h x)=0 := by
  classical
  letI := Fintype.ofFinite (Deck h)
  intro V A
  let L := rideAlong P h (G:=G)
  have he : A ∘ L=(mult h:ℝ) • V := funext fun x => action_copy P K h k p W x
  have hx := root_born hb hW hb' k
  have hy := root_born hb hW hu (mimic P K h k)
  have ht : Tendsto L (𝓝 0) (𝓝 0) := by simpa only [map_zero] using L.continuous.tendsto 0
  filter_upwards [hx.eventually (by simp),ht.eventually (hy.eventually (by simp)),station_paid P K h hb hW hu (mimic P K h k)]
    with z hF hH hS hv
  have hf : DifferentiableAt ℝ V z := hF.differentiableAt (by simp)
  have hH := (show ContDiffAt ℝ ω A (L z) from hH).differentiableAt (by simp)
  let D := vert A (L z)
  have hs (i : (Vertical G c (c*P.L))) : D (ride P h i)=0 := by
    have hb : (fderiv ℝ A (L z)) ∘L L = (mult h:ℝ) • fderiv ℝ V z := by
      have ht := fderiv_comp z hH (L.differentiableAt)
      rwa [L.fderiv, he, fderiv_const_smul hf,eq_comm] at ht
    have hw : D (ride P h i) = (mult h:ℝ) • vert V z i := by
      have hx : L (0,i)=(0,ride P h i) := Prod.ext ((reuses h (G:=G) (k:=1)).map_zero) rfl
      change fderiv ℝ A _ (0,ride P h i) = _; rw [← hx]; exact DFunLike.congr_fun hb (0,i)
    rw [hw,hv,_root_.zero_apply,smul_zero]
  apply ContinuousLinearMap.ext; intro v
  have hY i : D (spinUp P K h i v)=D v := DFunLike.congr_fun (hS i).symm v
  obtain ⟨w,hw⟩ := earnings P K h v
  have ha : ∑ i : ↥(Deck h), D (spinUp P K h i v) = 0 := by rw [← map_sum, ← hw,hs]
  simp_rw [hY] at ha
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ha
  exact (mul_eq_zero.mp ha).resolve_left (by positivity)
end equivariance

variable {M : Bed} {η : ℝ}

/-- The real germ on projected fields. Detect all orders on precisely these
physical lifts; no ancestor path regenerated. -/
theorem covers_value (hp : P.Branches K G) (hW : W.Bounds p σ C Λ)
    (hb : Critical T p W b) (hu : Critical B p W u) (hm : Comptroller B M p W)
    (he : 0 < η) (hη : PriceGap B p W η) (k : (stepAt P K c).Choices) (t : (stepAt P K d).Choices) :
    Joint.value B t p W u ∘ reuses h =ᶠ[𝓝 0] (mult h:ℝ) • Joint.value T k p W b := by
  let s := mimic P K h k
  let Z := Joint.action _ s p W
  let F := arc (plant T ∘ arc b)
  obtain ⟨ha,hj,hJ⟩ := Joint.joints hp hW hb k
  have ht : Tendsto F (𝓝 0) (𝓝 0) := by
    have hx := hj.arc_smooth.continuousAt.tendsto
    simpa only [show F 0=0 from Prod.ext rfl ha] using (show Tendsto F _ (𝓝 (F 0)) from hx)
  let L := reuses (k:=1) (G:=G) h
  let U := rideAlong (G:=G) P h
  have hU : Tendsto U (𝓝 0) (𝓝 0) := by simpa only [map_zero] using U.continuous.tendsto 0
  have hL : Tendsto L (𝓝 0) (𝓝 0) := by simpa only [map_zero] using L.continuous.tendsto 0
  filter_upwards [hJ,hj.station, ht.eventually (pays_vert P K h hp hW hb hu k), ht.eventually
    (hU.eventually (Joint.recognizes hp hW hu s M hm he hη)), hL.eventually ((crit_home hu).eventually (tested_germ hp B p W t s))]
    with x hx hy hp hh hv
  have hw : Z (U (F x)) = Joint.value B s p W u (L x) := hh (hp hy)
  exact hv.trans (hw.symm.trans ((action_copy P K h k p W (F x)).trans (congr_arg ((mult h:ℝ)*·) hx)))

/-- Wilson base/corrections already evaluate correctly on all sheets. -/
theorem peak_lift (p : Clip) (W : PathData G) : (Residual.wilsonAt-Residual.baseAt (c:=d) p W) ∘ reuses h =
    (mult h:ℝ) • (Residual.wilsonAt - Residual.baseAt (c:=c) p W) := by
  funext u
  simp only [Function.comp_apply, Pi.sub_apply, Residual.wilsonAt, Residual.baseAt, ← represented, wilson_copy,
    main_copy, Pi.smul_apply, smul_eq_mul,nsmul_eq_mul]; ring
end YM.AnalyticNext.QuarticMatch.Sheets
