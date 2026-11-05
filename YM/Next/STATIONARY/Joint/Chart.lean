import YM.Analytic.Frame
import YM.Next.STATIONARY.Lift.Ward



set_option autoImplicit false
/-!
`native_frame_stationary` applies without assuming vertical criticality,
regularity or Hessian sign. The germ it produces is the one the branch test
really consumes; in particular it can be used for every tag at once. We
record the counting Hessian with its p0 **square** normalization. These are
fixed step, fixed period assertions.
-/
noncomputable section
namespace YM.Stationary
open Filter Function Lattice RG Wilson Precision Tree Matrix Pressure Push Analytic
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} (S : StepData c f) (y : Site c)

section
variable (P : RG.Patch)

def readFrame (i : P.Points) : P.FrameCoordinates G →L[ℝ] G.Color := LinearMap.toContinuousLinearMap {
  toFun q := if h : i=P.center then 0 else WithLp.toLp 2 fun j => q (⟨i,h⟩,j)
  map_add' a b := by split <;> simp
                         ; rfl
  map_smul' t x := by split <;> simp
                         ; rfl }

lemma read_frame (i : P.Points) (x : P.FrameCoordinates G) :
    P.frameFromCoordinates G x i = G.lieExp (readFrame P i x) := by
  unfold Patch.frameFromCoordinates
  by_cases H : i=P.center <;> simp [readFrame,H]

def pairFrame (a b : P.FrameCoordinates G) : ℝ :=
  Patch.average fun i : P.Points => Patch.average fun j : P.Points =>
    inner ℝ (readFrame P i a - readFrame P j a) (readFrame P i b - readFrame P j b)

lemma pair_pos (a : P.FrameCoordinates G) (H : a≠0) : 0 < pairFrame P a a := by
  classical
  have hex : ∃ i : {i : P.Points // i ≠ P.center}, readFrame P i.val a ≠ 0 := by
    by_contra! he
    apply H
    ext ⟨i,j⟩
    have hy := congr_arg (fun z : G.Color => z j) (he i)
    simpa [readFrame,i.property] using hy
  obtain ⟨i, hi⟩ := hex
  unfold pairFrame Patch.average
  have hn : 0 < (Fintype.card P.Points : ℝ) := by exact_mod_cast Fintype.card_pos
  simp_rw [real_inner_self_eq_norm_sq]
  refine mul_pos (by positivity) (Finset.sum_pos' (fun i _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩)
  refine mul_pos (by positivity) (Finset.sum_pos' (fun i _ => by positivity) ⟨P.center, Finset.mem_univ _,?_⟩)
  have Hc : readFrame P P.center a=0 := by simp [readFrame]
  rw [Hc,sub_zero]; exact pow_pos (norm_pos_iff.mpr hi) _
end

theorem frame_jet : ContDiffAt ℝ ω (nativeFrameScore (G:=G) S y) 0 := by
  let P := S.patch
  unfold nativeFrameScore Patch.score Patch.average
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _ => ContDiffAt.mul contDiffAt_const
    (ContDiffAt.sum fun j _ => ContDiffAt.mul contDiffAt_const
      (ContDiffAt.sum fun k _ => Work.F03.price_smooth (A := fun z : In G f × P.FrameCoordinates G => S.patch.via (S.patch.frameFromCoordinates G z.2) (Push.product S y z.1) i j k) ?_)))
  have ht (v : P.Points) : ContDiffAt ℝ ω (fun p : In G f × P.FrameCoordinates G => G.mat (P.frameFromCoordinates G p.2 v)) 0 := by
    simp_rw [read_frame]
    have he : ContDiffAt ℝ ω (fun p : In G f × P.FrameCoordinates G => readFrame P v p.2) 0 := ((readFrame P v).contDiff.contDiffAt.comp (f:=Prod.snd) _ contDiffAt_snd)
    exact G.exp_jet.contDiffAt.comp (f:=fun p : In G f × P.FrameCoordinates G => readFrame P v p.2) (x:=0) he
  simp only [Patch.via,G.mat_mul,G.mat_inv,product,travel_at]
  refine ContDiffAt.mul ((ht i).mul ?_) ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (ht j))
  exact (Push.writes (G:=G) (route i.val j.val k) (atPoint S y i)).comp (f:=Prod.fst) (0: In G f × S.patch.FrameCoordinates G) contDiffAt_fst

theorem frame_flat :
    let F := fun q : S.patch.FrameCoordinates G => nativeFrameScore S y (0,q)
    F 0=0 ∧ fderiv ℝ F 0=0 ∧ ∀ v w, iteratedFDeriv ℝ 2 F 0 ![v,w] = pairFrame S.patch v w := by
  intro F
  have hh : ContDiffAt ℝ ω F 0 := (frame_jet S y).comp (f:=fun q => (0,q)) _
    (contDiffAt_const.prodMk contDiffAt_id)
  refine Work.F03.hessian_of_limit (hh.of_le le_top) (fun q => ?_) ?_ ?_
  · let P := S.patch
    let A (i : P.Points) := readFrame P i q
    have hp (i : P.Points) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • A i))) (G.colorMat (A i)) 0 := by
      have hx : HasDerivAt (fun t : ℝ => t • A i) (A i) 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const (A i)
      have he : HasFDerivAt (fun x => G.mat (G.lieExp x)) G.colorMat.toContinuousLinearMap ((0 : ℝ) • A i) := by
        rw [zero_smul]; exact G.expDiff_zero
      exact he.comp_hasDerivAt 0 hx
    unfold F pairFrame nativeFrameScore Patch.score Patch.average
    simp_rw [mul_div_assoc,Finset.sum_div,Patch.via,product_zero,Pressure.one,mul_one,read_frame,map_smul]
    -- cancel counts from the innermost mean
    have hx := Fintype.card_pos (α:=Lattice.Order)
    have hu : (Fintype.card Lattice.Order : ℝ) ≠ 0 := by positivity
    simp_rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul, mul_div_assoc, inv_mul_cancel_left₀ hu, Finset.sum_div]
    refine Tendsto.const_mul _ (tendsto_finsetSum _ (fun i _ => Tendsto.const_mul _ (tendsto_finsetSum _ (fun j _ => ?_))))
    rw [real_inner_self_eq_norm_sq]
    apply Work.F03.price_limit (G := G) (V:=fun t => G.lieExp (t • A i) * (G.lieExp (t • A j))⁻¹)
    · simp
    simp_rw [G.mat_mul, G.mat_inv]
    convert! (hp i).mul (hp j).star using 1
    simp [Gauge.colorMat_skew, sub_eq_add_neg, A,P]
  · intro a b x; simp only [pairFrame, map_add]
    unfold Patch.average
    simp_rw [show ∀ a b c d : G.Color, a+b-(c+d)=a-c+(b-d) from fun a b c d => by abel,
      inner_add_left,Finset.sum_add_distrib,mul_add]
    rw [Finset.sum_add_distrib,mul_add]
  · intro a b; unfold pairFrame; conv_lhs => arg 1; intro i; arg 1; intro j; rw [real_inner_comm]

section reading
variable (h : S.patch.Branches S.kernel G)
include h

private theorem tagGerm (B : In G f → S.patch.FrameCoordinates G) (hx : B 0=0)
    (hu : AnalyticAt ℝ B 0) (hb : ∀ᶠ a in 𝓝 0, HasFDerivAt (fun q => nativeFrameScore S y (a,q)) (0 : S.patch.FrameCoordinates G →L[ℝ] ℝ) (B a))
    (t : S.SitesChoice) :
    ∀ᶠ a in 𝓝 0, S.frames (represent a) t y = S.patch.frameFromCoordinates G (B a) := by
  let P := S.patch
  let W (a : In G f) : P.FrameCoordinates G := WithLp.toLp 2 fun i =>
    G.plog (Push.hats S y t a i.1.val) i.2
  have heW : W 0 = 0 := by ext ⟨i,j⟩; simp [W, Push.hats_zero S y t (h:=h)]
  have ht (i : P.Points) : ContinuousAt (fun a : In G f => Push.hats S y t a i) 0 :=
    Push.hat_cont S y t i (h:=h)
  have hw : Tendsto W (𝓝 0) (𝓝 0) := by
    rw [← heW]
    change ContinuousAt W 0
    refine (PiLp.continuous_toLp 2 _).continuousAt.comp (f:=fun a i => ((W a) i)) (continuousAt_pi.mpr fun i => ?_)
    refine (PiLp.continuous_apply (β:=fun _ : G.ColorIndex => ℝ) 2 i.2).continuousAt.comp (?_ : ContinuousAt (fun a => G.plog (Push.hats S y t a i.1.val)) (0:In G f))
    refine ContinuousAt.comp (g:=G.plog) ?_ (ht i.1.val)
    rw [Push.hats_zero S y t (h:=h)]
    exact G.plog_diff.continuousAt
  have he : ∀ᶠ a : In G f in 𝓝 0, S.frames (represent a) t y = S.patch.frameFromCoordinates G (W a) := by
    refine eventually_all.mpr (?_) |>.mono (fun _ hp => funext hp)
    intro i
    by_cases hv : i=P.center
    · subst i; filter_upwards [Push.roots S y t (G:=G)] with a ha
      rw [Patch.frameFromCoordinates_center]
      exact G.mat_injective (ha.trans G.mat_one.symm)
    let R (a : In G f) := S.frames (represent a) t y i
    have ha : R 0=1 := G.mat_injective ((Push.hats_zero S y t i (h:=h)).trans G.mat_one.symm)
    have hy : Tendsto R (𝓝 0) (𝓝 1) := by
      rw [← ha]; exact (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (ht i)
    filter_upwards [hy.eventually G.plog_right] with a hi
    rw [Patch.frameFromCoordinates, dif_neg hv]; exact hi.symm
  have hc : ContDiffAt ℝ ω (fun z : In G f × P.FrameCoordinates G => nativeFrameScore S y z) 0 := frame_jet S y
  have hg : ∀ v : P.FrameCoordinates G, Work.F05.bend (fun q => nativeFrameScore S y (0,q)) 0 v v = 0 → v = 0 := by
    intro v he; rw [Work.F05.bend_apply, (frame_flat S y).2.2] at he
    exact Classical.byContradiction (fun hv => (pair_pos P v hv).ne' he)
  have hf : Tendsto B (𝓝 0) (𝓝 0) := hx ▸ hu.continuousAt.tendsto
  have hk : ∀ᶠ a in 𝓝 0, fderiv ℝ (fun q => nativeFrameScore S y (a,q)) (W a) = 0 := by
    filter_upwards [Push.threshold S y (G:=G), he,
      (tendsto_id.prodMk_nhds hw).eventually (hc.eventually (by simp))] with a ha he hh
    apply IsLocalMin.fderiv_eq_zero
    refine Filter.Eventually.of_forall fun q => ?_
    change S.patch.score _ (S.patch.frameFromCoordinates G (W a)) ≤ _
    rw [← he]
    change S.patch.score _ (S.patch.frame S.kernel (product S y a) _) ≤ _
    rw [Patch.frame, if_pos ha]; exact (P.min_exists (product S y a)).choose_spec.2 _ (Patch.frameFromCoordinates_center ..)
  apply (he.and (Work.F05.station_unique (F:=fun a q => nativeFrameScore S y (a,q)) hc hg hw hf hk (hb.mono (fun _ he => he.fderiv)))).mono
  exact fun a he => he.1.trans (congr_arg _ he.2)

/-- The fixed-period graph from `nativeFrameScore` is the one in every
connector reading the same physical tag. -/
theorem frame_germ :
    ∃ B : In G f → S.patch.FrameCoordinates G, B 0=0 ∧ AnalyticAt ℝ B 0 ∧
      (∀ᶠ a in 𝓝 0, HasFDerivAt (fun q => nativeFrameScore S y (a,q)) (0 : S.patch.FrameCoordinates G →L[ℝ] ℝ) (B a)) ∧
      ∀ᶠ a in 𝓝 0, ∀ t, S.frames (represent a) t y=S.patch.frameFromCoordinates G (B a) := by
  have hh := frame_jet S y (G:=G)
  have ha : ContDiffAt ℝ ω (fun q : S.patch.FrameCoordinates G => nativeFrameScore S y (0,q)) 0 :=
    hh.comp (f:=fun q => (0,q)) _ (contDiffAt_const.prodMk contDiffAt_id)
  have hv := (ha.differentiableAt (by simp)).hasFDerivAt
  rw [(frame_flat S y).2.1] at hv
  obtain ⟨B,H,H',_,ht⟩ := native_frame_stationary S y 0 hh.analyticAt hv fun v ht => by
    rw [(frame_flat S y).2.2]; exact pair_pos S.patch v ht
  exact ⟨B,H,H',ht,eventually_all.mpr (tagGerm S y h B H H' ht)⟩
end reading
end YM.Stationary
end

/-!
# Real joint frame-tangent space. Coordinates in physical counting basis

Left variation means Exp increment ON LEFT. Using exponential/additive
`Point` of fields at trivialization (not changing base) only for kernels
and jets. In this file charts for rooted and centered variables use the
same type; rooted vs centered specified in the users. Norm here is Pi/sup
(not the tangent ℓ² with counting basis that prices a determinant).
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators
variable {G : Gauge} {c f n : Side}

-- make component reads/spins explicit
abbrev Coats (G : Gauge) (n : Side) := Site n → G.El

def gaugeColor : BaseSites G n ≃L[ℝ] (Site n → G.Color) := (arm _ _ _).trans <| LinearEquiv.toContinuousLinearEquiv {
  toFun a x := a (x,vac)
  invFun a x := a x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv a := by funext ⟨x,i⟩; change a (x,vac)=_; rw [vac_only i]
  right_inv _ := rfl }

def edgeColor : Link G n ≃L[ℝ] (Edge (Site n) → G.Color) := (arm _ _ _).trans <| LinearEquiv.toContinuousLinearEquiv {
  toFun a x := a (x.1,coord x.2)
  invFun a x := a (x.1,axisEquiv.symm x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv a := by funext ⟨x,i⟩; change a (x,axisEquiv (axisEquiv.symm i))=_; rw [Equiv.apply_symm_apply]
  right_inv a := by funext ⟨x,i⟩; change a (x,axisEquiv.symm (axisEquiv i))=_; rw [Equiv.symm_apply_apply] }

lemma switch_color (b : BaseSites G n) (x) : switchSite b x=G.lieExp (gaugeColor b x) := rfl
lemma input_color (b : Link G n) (e : Edge (Site n)) : input G n b e=G.lieExp (edgeColor b e) := encode_link ..

def plogC (G : Gauge) (x : G.El) := G.plog (G.mat x)
@[simp] lemma plogC_one : plogC G 1=0 := G.plog_one

def frameLog (U : Coats G n) := gaugeColor.symm (fun i => plogC G (U i))
@[simp] lemma frameLog_one : frameLog (1 : Coats G n)=0 := by simp only [frameLog,Pi.one_apply,plogC_one]; exact gaugeColor.symm.map_zero
lemma switch_frameLog : ∀ᶠ x : Coats G n in 𝓝 1, switchSite (frameLog x) = x := by
  suffices he : ∀ᶠ x : Coats G n in 𝓝 1, ∀ i : Site n, switchSite (frameLog x) i=x i from he.mono (fun _ hx => funext hx)
  refine eventually_all.mpr fun i => ?_
  simp only [switch_color,frameLog,gaugeColor.apply_symm_apply]
  exact ((continuous_apply i).tendsto (1:Coats G n)).eventually G.plog_right
lemma frameLog_switch : ∀ᶠ x : BaseSites G n in 𝓝 0, frameLog (switchSite x) = x := by
  have h (i : Site n) : ∀ᶠ x : BaseSites G n in 𝓝 0, plogC G (switchSite x i)=gaugeColor x i := by
    have he : Tendsto (fun x : BaseSites G n => gaugeColor x i) (𝓝 0) (𝓝 0) := by simpa only [map_zero,Pi.zero_apply] using (show Continuous (fun x : BaseSites G n => gaugeColor x i) from by fun_prop).tendsto 0
    exact he.eventually G.plog_left
  filter_upwards [eventually_all.mpr h] with x hx
  exact gaugeColor.injective (by rw [frameLog,gaugeColor.apply_symm_apply]; exact funext hx)

abbrev Joint (G : Gauge) (c f : Side) := Config G f × Coats G c
abbrev Vault (G : Gauge) (c f : Side) := Link G f × BaseSites G c
abbrev Point (G : Gauge) (c f : Side) := Link G c × Vault G c f

def extend (X : Vault G c f) : Joint G c f := (input G f X.1,switchSite X.2)
def retract (U : Joint G c f) : Vault G c f := (content U.1,frameLog U.2)
@[simp] lemma extend_zero : extend (0:Vault G c f)=1 := by simp [extend]
@[simp] lemma retract_one : retract (1:Joint G c f)=0 := by simp [retract]
@[fun_prop] lemma extend_cont : Continuous (extend : Vault G c f → Joint G c f) :=
  (input_cont.comp continuous_fst).prodMk (switch_cont.comp continuous_snd)
lemma extend_retract : ∀ᶠ x : Joint G c f in 𝓝 1, extend (retract x) = x := by
  filter_upwards [(continuous_fst.tendsto (1:Joint G c f)).eventually content_encodes,(continuous_snd.tendsto (1:Joint G c f)).eventually switch_frameLog] with x hx hy
  exact Prod.ext hx hy
lemma retract_extend : ∀ᶠ x : Vault G c f in 𝓝 0, retract (extend x)=x := by
  filter_upwards [(continuous_fst.tendsto (0:Vault G c f)).eventually input_encodes,(continuous_snd.tendsto (0:Vault G c f)).eventually frameLog_switch] with x hx hy
  exact Prod.ext hx hy

-- true group analytic family (no Lie-group manifold layer used).
section origin
variable {ι X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {x : X} {w : X → Y}

def Army (u : X → ι → G.El) (x : X) := ∀ i, ContDiffAt ℝ ω (fun z => G.mat (u z i)) x
def Thaw (f : X → Joint G c n) (x : X) := Army (fun z => (f z).1) x ∧ Army (fun z => (f z).2) x

namespace Army
variable {u v : X → ι → G.El}
lemma cont (h : Army u x) : ContinuousAt u x := continuousAt_pi.mpr fun i =>
  (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (h i).continuousAt
lemma mul (h : Army u x) (k : Army v x) : Army (fun z => u z * v z) x := fun i => (h i).mul (k i)
lemma inv (h : Army u x) : Army (fun z => (u z)⁻¹) x := fun i =>
  (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp (f:=fun a => G.mat (u a i)) _ (h i)
lemma comp {g : Y → ι → G.El} (h : Army g (w x)) (k : ContDiffAt ℝ ω w x) : Army (g ∘ w) x := fun i => (h i).comp x k
lemma park (u : ι → G.El) (x : X) : Army (fun _ => u) x := fun _ => contDiffAt_const
lemma powL {v : X → Link G n} (h : ContDiffAt ℝ ω v x) : Army (fun z => input G n (v z)) x := by
  intro i; simp_rw [input_color]
  exact G.exp_jet.contDiffAt.comp (g:=fun a => G.mat (G.lieExp a)) (f:=fun z => edgeColor (v z) i) _ (((contDiffAt_apply ℝ G.Color i _).comp (f:=fun z => edgeColor (v z)) _ (edgeColor.contDiff.contDiffAt.comp _ h)))
lemma powG {v : X → BaseSites G n} (h : ContDiffAt ℝ ω v x) : Army (fun z => switchSite (v z)) x := by
  intro i
  exact G.exp_jet.contDiffAt.comp (g:=fun a => G.mat (G.lieExp a)) (f:=fun z => gaugeColor (v z) i) _ (((contDiffAt_apply ℝ G.Color i _).comp (f:=fun z => gaugeColor (v z)) _ (gaugeColor.contDiff.contDiffAt.comp _ h)))
lemma slant {k : X → Coats G n} {V : X → Config G n} (h : Army k x) (hv : Army V x) : Army (fun z => Lattice.gauge (k z) (V z)) x :=
    fun i => ((h i.1).mul (hv i)).mul (h.inv (i.1+step i.2))
lemma logG {V : X → Coats G n} (h : Army V x) (hp : V x=1) : ContDiffAt ℝ ω (fun z => frameLog (V z)) x := by
  refine gaugeColor.symm.contDiff.contDiffAt.comp (f:=fun z i => plogC G (V z i)) _ (contDiffAt_pi.mpr fun i => ?_)
  refine ContDiffAt.comp (g:=G.plog) _ ?_ (h i)
  rw [hp,Pi.one_apply,G.mat_one]; exact G.plog_diff
lemma logL {V : X → Config G n} (h : Army V x) (hp : V x=1) : ContDiffAt ℝ ω (fun z => content (V z)) x :=
  (content_analytic hp fun i => (h i).analyticAt).contDiffAt
end Army
namespace Thaw
variable {U V : X → Joint G c n}
lemma cont (h : Thaw U x) : ContinuousAt U x := h.1.cont.prodMk h.2.cont
lemma mul (h : Thaw U x) (k : Thaw V x) : Thaw (fun z => U z * V z) x := ⟨h.1.mul k.1,h.2.mul k.2⟩

lemma fixed (v : Joint G c n) (x : X) : Thaw (fun _ => v) x := ⟨Army.park v.1 x,Army.park v.2 x⟩
lemma through {v : X → Vault G c n} (h : ContDiffAt ℝ ω v x) : Thaw (fun z => extend (v z)) x := ⟨Army.powL h.fst,Army.powG h.snd⟩
lemma log (h : Thaw U x) (p : U x=1) : ContDiffAt ℝ ω (fun z => retract (U z)) x :=
    (h.1.logL (by rw [p]; rfl)).prodMk (h.2.logG (by rw [p]; rfl))
lemma comp {g : Y → Joint G c n} (h : Thaw g (w x)) (k : ContDiffAt ℝ ω w x) : Thaw (g ∘ w) x := ⟨h.1.comp k,h.2.comp k⟩
end Thaw
end origin

end YM.Stationary
end

/-!
# Joint fine field and added coarse frame. Rooted action. `recruit` for a
centered frame with actual G.focus of weighted matrix mean; this uses same
period/tag even when frame points wrap. No claim of gauge invariance for
that coordinate centering; stationarity & offshell assertions use transported
tangents as needed. Centered h is cap⁻¹ times the rooted h, so to read in
these centered frame slots we use Φˢ cap⁻¹ for Φ.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators
variable {G : Gauge} {c f n : Side}

variable (S : StepData c f)

section root

def hatPoint (x : Site f) : S.patch.Points := ⟨Lattice.lift (S.ratio.residue x), by
  have he := S.ratio.half_box S.patch.odd_side (S.ratio.residue x)
  have hx : S.ratio.count.val/2 ≤ S.patch.radius := (Nat.div_le_self ..).trans
    (Nat.le_mul_of_pos_left S.patch.L.val (by omega))
  rw [box_test] at he
  unfold Patch.sites
  rw [box_test]; refine ⟨?_,?_⟩
  · intro i; exact le_trans (neg_le_neg (by exact_mod_cast hx)) (he.1 i)
  intro i; exact (he.2 i).trans (by exact_mod_cast hx)⟩
lemma point_hat (x : Site f) : atPoint S (S.ratio.parent x) (hatPoint S x) = x := (add_comm ..).trans (S.ratio.unpack_at x)

end root
section action

def wages (k : Coats G f) (u : Coats G c) (U : Joint G c f) : Joint G c f :=
    (Lattice.gauge k U.1,fun i => u i * U.2 i * (k (S.ratio.embed i))⁻¹)

lemma wage_comp (k h : Coats G f) (x y : Coats G c) (U : Joint G c f) : wages S k x (wages S h y U) = wages S (k*h) (x*y) U := by
  ext a <;> simp [wages,Lattice.gauge,mul_assoc]
@[simp] lemma wages_zero (U : Joint G c f) : wages S 1 1 U=U := by ext a <;> simp [wages,Lattice.gauge]

variable (t : S.Choices)

def ribbon (U : Joint G c f) : Config G c := Lattice.gauge U.2 (S.prediction U.1 t)
def shield (U : Joint G c f) : Coats G f := fun x => U.2 (S.ratio.parent x) * S.frames U.1 t.1 (S.ratio.parent x) (hatPoint S x)
def tickets (V Z : Config G c) : ℝ := S.kernel.penalty * ∑ e, G.price (V e * (Z e)⁻¹)
def muster (p : Clip) (R : PathData G) (V : Config G c) (U : Joint G c f) : ℝ := mainTerm p R U.1 + tickets S V (ribbon S t U)

variable (h : S.patch.Branches S.kernel G) (U : Joint G c f) (u : Coats G c) (k : Coats G f)
include h

lemma ribbons : ribbon S t (wages S k u U)=Lattice.gauge u (ribbon S t U) := by
  funext ⟨x,i⟩; simp only [ribbon,wages,Lattice.gauge,StepData.prediction]
  rw [S.updateGauged h k U.1 t.1 (x,i), (S.patch.bond_gauge (h:=h) ..).2]
  group

lemma shields : shield S t (wages S k u U) = fun i => u (S.ratio.parent i)*shield S t U i * (k i)⁻¹ := by
  funext i; simp only [shield,wages,StepData.frames]
  rw [expandAt_gauge, (S.patch.frame_gauged h ..).2,Patch.changed]
  rw [show S.patch.center.val=0 from rfl,map_zero,zero_add,show wrap f _ + _ = i from point_hat S i]; group
lemma root_wages (p : Clip) (R : PathData G) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (V : Config G c) :
    muster S t p R (Lattice.gauge u V) (wages S k u U)=muster S t p R V U := by
  simp only [muster,ribbons S t h]
  simp only [wages,Work.F05.mainTerm_gauge hp]
  congr 1
  unfold tickets; apply congr_arg; refine Finset.sum_congr rfl fun i _ => ?_
  rw [← G.price_conj (u i.1) (V i * (ribbon S t U i)⁻¹)]
  unfold Lattice.gauge; apply congr_arg; group
end action
section centering
variable (t : S.Choices)

def prospect (T : Config G f) (x : Site c) : G.Mat := ∑ i,S.patch.weight i • G.mat (S.frames T t.1 x i)
def bears (T : Config G f) : Coats G c := fun i => G.focus (prospect S t T i)

def enroll (U : Joint G c f) : Joint G c f := (U.1,U.2 * (bears S t U.1)⁻¹) -- to rooted
def recruit (U : Joint G c f) : Joint G c f := (U.1,U.2 * bears S t U.1) -- to centered

lemma enroll_recruit (U : Joint G c f) : enroll S t (recruit S t U)=U := by simp [recruit,enroll]

def merit (p : Clip) (R : PathData G) (x : Point G c f) : ℝ :=
    muster S t p R (input _ _ x.1) (enroll S t (Stationary.extend x.2))

variable (h : S.patch.Branches S.kernel G)
include h
lemma prospect_zero (x : Site c) : prospect S t (1:Config G f) x=1 := by
  unfold prospect; rw [← link_one]
  have he v : G.mat (S.frames (represent (0:Push.In G f)) t.1 x v) = 1 := Push.hats_zero S x t.1 v (h:=h)
  simp_rw [he, ← Finset.sum_smul,S.patch.weight_sum,one_smul]
lemma bear_zero : bears S t (1: Config G f)=1 := by
  funext i; rw [bears, prospect_zero S t h]; exact (mem_of_mem_nhds G.nearest_is_focus 1 (fun i => by simp)).symm
lemma ribbon_zero : ribbon S t (1: Joint G c f) = 1 := by
  funext i; change (1:G.El)*_*(1:G.El)⁻¹=1; simp [Push.settled S h]

lemma enroll_zero : enroll S t (1:Joint G c f)=1 := by simp [enroll,bear_zero S t h]
lemma recruit_zero : recruit S t (1:Joint G c f)=1 := by simp [recruit,bear_zero S t h]
end centering
end YM.Stationary
end

/-! # Generate analytic fixed-mesh covariant arrays for calculating actual jets. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f}

section regalia
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}
  {T : X → Config G f} {U : X → Joint G c f}

lemma Thaw.wages (S : StepData c f) {k : X → Coats G f} {l : X → Coats G c} (he : Thaw U x) (hk : Army k x) (hl : Army l x) :
    Thaw (fun z => Stationary.wages S (k z) (l z) (U z)) x := ⟨hk.slant he.1,
      fun i => ((hl i).mul (he.2 i)).mul (hk.inv _)⟩

attribute [local instance] Gauge.frobInner
lemma matrix_price_jet {A : X → G.El} (he : ContDiffAt ℝ ω (fun x => G.mat (A x)) x) :
    ContDiffAt ℝ ω (fun x => G.price (A x)) x := by
  have he (x : X) : G.price (A x) = ‖G.mat (A x) - 1‖ ^ 2 / G.colorScale ^ 2 / 2 := by
    rw [← div_pow]; change _ = G.chord _ ^ 2 / 2; rw [G.chord_price]; ring
  rename_i h
  simp_rw [he]
  exact (((contDiff_norm_sq ℝ).contDiffAt.comp x (h.sub contDiffAt_const)).div_const _).div_const _

variable (h : S.patch.Branches S.kernel G) (t : S.Choices)
include h

/-- Consume actual scores to bind rooted branches. Does not require
    the family to have coherence over multiples of a period. -/
lemma Army.frame (p : Army T x) (u : T x=1) (i : Site c) : Army (fun z => S.frames (T z) t.1 i) x := by
  obtain ⟨B,hb,H,_,ht⟩ := frame_germ S i h
  let L := fun y => arm G f 1 (content (T y))
  have he : L x=0 := by simp [u,L]
  have hi : ContDiffAt ℝ ω L x := (arm _ _ _).contDiff.contDiffAt.comp _ (p.logL u)
  have hd : ContDiffAt ℝ ω (B ∘ L) x := by
    apply ContDiffAt.comp (g:=B) _ ?_ hi
    rw [he]; exact H.contDiffAt
  intro j
  have hh : ContDiffAt ℝ ω (fun y => G.mat (G.lieExp (readFrame S.patch j ((B ∘ L) y)))) x :=
    G.exp_jet.contDiffAt.comp (f:=fun y => readFrame S.patch j ((B ∘ L) y)) (g:=fun a => G.mat (G.lieExp a)) _ ((readFrame S.patch j).contDiff.contDiffAt.comp _ hd)
  refine hh.congr_of_eventuallyEq ?_
  filter_upwards [(show Tendsto L _ (𝓝 0) from he ▸ hi.continuousAt.tendsto).eventually ht,
    (show Tendsto T _ (𝓝 1) from u ▸ p.cont.tendsto).eventually content_encodes] with y hy hv
  rw [Function.comp_apply, ← read_frame, ← hy t.1, show represent (L y)=_ from hv]

lemma Army.bear (p : Army T x) (u : T x=1) : Army (fun z => bears S t (T z)) x := by
  intro i
  let F y := prospect S t (T y) i
  have hf : ContDiffAt ℝ ω F x := ContDiffAt.sum fun j _ => (p.frame h t u i j).const_smul _
  have hp : ContDiffAt ℝ ω (fun u => G.mat (G.focus u)) (F x) := by
    rw [show F x=1 by simp [F,u,prospect_zero S t h]]; exact G.focus_diff
  exact hp.comp (f:=F) _ hf

lemma Army.pred (p : Army T x) (u : T x=1) : Army (fun z => S.prediction (T z) t) x := by
  let L := fun y => arm G f 1 (content (T y))
  have he : L x=0 := by simp [L,u]
  have hi : ContDiffAt ℝ ω L x := (arm _ _ _).contDiff.contDiffAt.comp _ (p.logL u)
  intro i
  have hv : ContDiffAt ℝ ω (fun v => G.mat (S.prediction (represent v) t i)) (L x) := he.symm ▸ Push.prediction_cont S h i t
  refine (hv.comp _ hi).congr_of_eventuallyEq ?_
  filter_upwards [(show Tendsto T _ (𝓝 1) from u ▸ p.cont.tendsto).eventually content_encodes] with y hy
  dsimp only [Function.comp_apply]; rw [show represent (L y)=_ from hy]

lemma Thaw.to_cap (p : Thaw U x) (he : (U x).1=1) : Thaw (fun z => enroll S t (U z)) x :=
    ⟨p.1,p.2.mul (p.1.bear h t he).inv⟩
lemma Thaw.from_cap (p : Thaw U x) (he : (U x).1=1) : Thaw (fun z => recruit S t (U z)) x :=
    ⟨p.1,p.2.mul (p.1.bear h t he)⟩
lemma Thaw.shields (p : Thaw U x) (he : (U x).1=1) : Army (fun z => shield S t (U z)) x := fun _ =>
  (p.2 _).mul (p.1.frame h t he _ _)
lemma Thaw.ribbons (p : Thaw U x) (he : (U x).1=1) : Army (fun z => ribbon S t (U z)) x :=
    p.2.slant (p.1.pred h t he)

lemma Thaw.earn (p : Thaw U x) (he : (U x).1=1) {V : X → Config G c} (hv : Army V x) {q : Clip} {R : PathData G} {σ A Λ : ℝ}
    [FiniteDimensional ℝ X] (hp : R.Bounds q σ A Λ) : ContDiffAt ℝ ω (fun z => muster S t q R (V z) (U z)) x := by
  have hF := (Work.F02.answer _ _ _ _ _ _ hp).crown x _ _ he p.1
  unfold muster tickets; refine ContDiffAt.add hF (ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _ => matrix_price_jet (?_)))
  exact (hv _).mul ((p.ribbons h t he).inv i)

end regalia
lemma merit_diff (h : S.patch.Branches S.kernel G) (t : S.Choices) {p : Clip} {R : PathData G} {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) :
    ContDiffAt ℝ ω (merit S t p R) 0 :=
  ((Thaw.through (v:=Prod.snd) (contDiffAt_snd (p:=(0:Point G c f)))).to_cap h t (by simp [Stationary.extend])).earn h t (by simp [enroll,Stationary.extend]) (Army.powL contDiffAt_fst) hp
end YM.Stationary
end
