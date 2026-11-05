import YM.AnalyticNext.QUARTIC_MATCH.Joint
import YM.Bid.Drops
import YM.Work.B06

/-!
# Symmetries of the stationary value in the actual step

Don't presume `rho` transforms globally, or require a relabeling selects the same forest.
Compare on the true stationary germs. Translations on the torus, including roots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Filter Function Matrix Precision RG Lattice Exterior Tree Bid Wilson
open Work.F03 Work.F04 Work.F05 Topology
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}
namespace Joint
variable {n c f : Side} {S : StepData c f} {W : PathData G}

section orient

/-- Signed and translated pull, as an actual linear map in the log convention. -/
def shifts (s : Signed) (b : Site n) : Dir G n →L[ℝ] Dir G n :=
  ContinuousLinearMap.pi fun i =>
    let e := (posDir (axisEquiv.symm i.2)).rotate s
    let j := e.used (affine s b i.1)
    if e.neg then -ContinuousLinearMap.proj (j.1,coord j.2) else ContinuousLinearMap.proj (j.1,coord j.2)

lemma rep_shifts (s : Signed) (b : Site n) (a : Dir G n) : represent (shifts s b a)=pull s b (represent a) := by
  funext e
  simp only [shifts,pull,Step.read,represent_link,ContinuousLinearMap.pi_apply,
    show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _]
  split
  · exact exp_neg_color _
  rfl

@[simp] lemma shift_one_apply (b : Site n) (a : Dir G n) (i : Body 1 n) :
    shifts 1 b a i = a (i.1+b,i.2) := by
  rcases i with ⟨z,j⟩; obtain ⟨j,rfl⟩ := axisEquiv.surjective j
  simp [shifts,affine,posDir,Step.used]
  rw [show axisEquiv.symm (coord j) = j from axisEquiv.symm_apply_apply _]

def records (U : Config G n) : Dir G n := fun i => G.plog (G.mat (U (i.1,axisEquiv.symm i.2)))

lemma rec_end : ∀ᶠ z : Dir G n in 𝓝 0, records (represent z) = z := by
  have he (i : Body 1 n) : ∀ᶠ z : Dir G n in 𝓝 0,
      G.plog (G.mat (G.lieExp (z i))) = z i := ((continuous_apply i).tendsto (0:Dir G n)).eventually G.plog_left
  filter_upwards [eventually_all.mpr he] with z hz
  funext i; unfold records
  rw [represent_link, show coord (axisEquiv.symm i.2)=i.2 from axisEquiv.apply_symm_apply _]; exact hz _

/-- Onto for the linear reorientation tested using the exponential chart. -/
theorem shifts_onto (s : Signed) (b : Site n) : Surjective (shifts (G:=G) s b) := by
  let T := shifts (G:=G) s b
  let r := s⁻¹
  let y := -s⁻¹.act b
  let U := shifts (G:=G) r y
  have he : (T ∘L U) = ContinuousLinearMap.id ℝ (Dir G n) := by
    have ht : Tendsto (T ∘L U) (𝓝 0) (𝓝 0) := by simpa only [map_zero] using (T ∘L U).continuous.tendsto 0
    have hh : (T ∘L U) =ᶠ[𝓝 0] (id : Dir G n → Dir G n) := by
      filter_upwards [ht.eventually rec_end, rec_end (G:=G) (n:=n)] with z hz hy
      rw [← hz]
      change records (represent (T (U z)))= _
      unfold T U r y; rw [rep_shifts,rep_shifts,pull_pull]; simpa [affine, add_comm] using hy
    simpa using hh.fderiv_eq (𝕜:=ℝ)
  intro v
  exact ⟨U v,DFunLike.congr_fun he v⟩

lemma pullGauge (t : Spin G n) (U : Config G n) (s : Signed) (b : Site n) :
    pull s b (Lattice.gauge t U) = Lattice.gauge (t ∘ affine s b) (pull s b U) := by
  funext ⟨x,i⟩
  change ((posDir i).rotate s).read (Lattice.gauge t U) (affine s b x) = _
  rw [Step.gauge_read]
  simp only [Lattice.gauge, Step.vec_rotate, Step.vec_pos,pull, affine, Signed.act_add,Function.comp_apply]
  rw [add_right_comm]

lemma translate_by (s : Signed) (b : Site n) (U : Config G n) :
    pull s b U = translate ((s⁻¹).act b) (pull s 0 U) := by
  rw [← pull_one,pull_pull]; simp [affine]

lemma uncut_translate {m : ℕ} (A : ℕ → Atom G m) (b : Site n) (U : Config G n) :
    uncut A (translate b U)=uncut A U := by
  have he (x : Site n) : expandAt x (translate b U)=expandAt (x+b) U := by
    funext _; simp [expandAt,translate, add_assoc]
  have hx (x : Site n) i : (A i).unmasked (translate b U) x = (A i).unmasked U (x+b) := by
    simp_rw [Atom.unmasked,RG.Slot.atSite,he]
  simp_rw [uncut, hx]; exact Equiv.sum_comp (Equiv.addRight b) (fun x => ∑' i, (A i).unmasked U x)
lemma quadratic_translate (p : Clip) (W : PathData G) (b : Site n) (U : Config G n) :
    quadratic p W (translate b U)=quadratic p W U := by
  have he (x : Site n) : expandAt x (translate b U) = expandAt (x+b) U := by funext _; simp [expandAt,translate,add_assoc]
  unfold quadratic
  conv_rhs => rw [← Equiv.sum_comp (Equiv.prodCongr (Equiv.addRight b) (Equiv.refl PlaqAxes))]
  refine Finset.sum_congr rfl ?_; rintro ⟨x,i⟩ _
  change p.direct * _ + ‖W.ell (translate b U) (x,i)‖^2/2 =
    p.direct * G.price (faceValue U (x+b,i)) + ‖W.ell U (x+b,i)‖^2/2
  have ha : faceValue (translate b U) (x,i) = faceValue U (x+b,i) := by
    rw [← pull_one]; unfold faceValue; rw [travel_pull]; simp [affine,square]
  rw [ha]; simp_rw [PathData.ell, PathData.ellTerms, RG.Slot.atSite, he]

lemma main_pull (p : Clip) (W : PathData G) (s : Signed) (b : Site n) (U : Config G n) :
    mainTerm p W (pull s b U) = mainTerm p W U := by
  unfold mainTerm Patch.average; apply congr_arg
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft s)]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only; rw [pull_pull]
  rw [translate_by (s*i) (affine s b 0),quadratic_translate, uncut_translate, uncut_translate]; rfl

lemma energy_channel (s : Signed) (b : Site n) (k : KernelChoices) (V Y : Config G n) :
    groupEnergy k (pull s b V) (pull s b Y) = groupEnergy k V Y := by
  unfold groupEnergy; apply congr_arg
  conv_rhs => rw [← Equiv.sum_comp (StepData.sendBonds s b)]
  refine Finset.sum_congr rfl ?_; rintro ⟨x,i⟩ _
  unfold pull Step.read; split
  · have he (u v : G.El) : G.price (u⁻¹*(v⁻¹)⁻¹)=G.price (u*v⁻¹) := by
      rw [← G.price_inv (u*v⁻¹), show (u*v⁻¹)⁻¹ = u * (u⁻¹*(v⁻¹)⁻¹) * u⁻¹ by group, G.price_conj]
    rw [he]; rfl
  rfl

/-- Includes negative orientations. -/
lemma field_channel (p : Clip) (W : PathData G) (h : S.patch.Branches S.kernel G)
    (V : Config G c) (U : Config G f) (k : Spin G c) (s : Signed) (b : Site c) (t : S.Choices) :
    fieldAction S t p W (pull s b V) (pull s (S.ratio.embed b) U) (k ∘ affine s b) =
        fieldAction S (S.withinChoice s b t) p W V U k := by
  rw [fieldAction, S.prediction_channel h s b,← pullGauge, main_pull,energy_channel]; rfl

/-- We also need to translate the vertical frame at all the coarse sites. -/
def rephase (s : Signed) (b : Site c) : Vertical G c f →L[ℝ] Vertical G c f :=
    ((shifts s (S.ratio.embed b)) ∘L ContinuousLinearMap.fst _ _ _).prod
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (affine s b i) ∘L ContinuousLinearMap.snd _ _ _)

lemma rephase_surjective (s : Signed) (b : Site c) : Surjective (rephase (S:=S) (G:=G) s b) := by
  rintro ⟨u,v⟩
  obtain ⟨w,hw⟩ := shifts_onto s (S.ratio.embed b) u
  let φ := (StepData.sendSites s b)
  refine ⟨(w,v ∘ φ.symm), Prod.ext hw <| funext fun i => ?_⟩
  exact congr_arg v (φ.symm_apply_apply i)

lemma commutes (p : Clip) (W : PathData G) (h : S.patch.Branches S.kernel G)
    (s : Signed) (b : Site c) (t : S.Choices) (x : Dir G c × Vertical G c f) :
    action S t p W (shifts s b x.1,rephase (S:=S) s b x.2) = action S (S.withinChoice s b t) p W x := by
  unfold action
  change fieldAction S t p W (represent _) (represent (shifts s _ _)) (power x.2.2 ∘ affine s b)=_
  rw [rep_shifts, rep_shifts]
  exact field_channel p W h ..
end orient

abbrev value (T : Forest S.ratio) (k : S.Choices) (p : Clip) (W : PathData G) (b : Dir G c → AxisChart G T) :=
    uncurry (tested T k p W) ∘ arc b

section curves
variable {T : Forest S.ratio} {B : Bed} {p : Clip} {b : Dir G c → AxisChart G T}
    {σ C Λ η : ℝ}
variable (h : S.patch.Branches S.kernel G) (hW : W.Bounds p σ C Λ) (hb : Critical T p W b)
    (hc : Comptroller T B p W) (hp : 0 < η) (hh : PriceGap T p W η)
include h hW hb hc hp hh

/-- Generalized parameter E, so can use analytic changes in B, on both sides,
which need NOT be invertible. W/p and branch kept. Need genuine submersion in
vertical coordinates. -/
theorem transfigures {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k t : S.Choices)
    (F L : E → Dir G c) (V : E × Vertical G c f → Vertical G c f)
    (hF : ContDiffAt ℝ ω F 0) (hL : ContDiffAt ℝ ω L 0) (hV : ContDiffAt ℝ ω V 0)
    (hf : F 0=0) (hl : L 0=0) (hv : V 0=0)
    (hu : ∀ᶠ z in 𝓝 0, action S k p W (F z.1,z.2) = action S t p W (L z.1,V z))
    (hS : ∀ᶠ z in 𝓝 0, Surjective (vMap V z)) :
    value T k p W b ∘ F =ᶠ[𝓝 0] value T t p W b ∘ L := by
  let U := plant T ∘ arc b
  obtain ⟨h1,h2,h3⟩ := joints h hW hb k
  let Y (z : E × Vertical G c f) := (F z.1,z.2)
  let M := action S k p W ∘ Y
  let J := action S t p W
  have ht : Tendsto F (𝓝 0) (𝓝 0) := by simpa only [hf] using hF.continuousAt.tendsto
  have hB : Tendsto (arc (U ∘ F)) (𝓝 0) (𝓝 0) := by
    have e : Tendsto U (𝓝 0) (𝓝 0) := by simpa only [h1] using h2.path.continuousAt.tendsto
    exact tendsto_id.prodMk_nhds (e.comp ht)
  have he := vert_pull (P:=M) (Q:=J) (L:=L) hV hL hu (show ContDiffAt ℝ ω J _ from by
    rw [hl,hv]; exact root_born h hW hb t)
  have hr := vert_pull (P:=M) (L:=F) (Q:=action S k p W) (p:=Prod.snd) contDiffAt_snd hF
    EventuallyEq.rfl (show ContDiffAt ℝ ω _ _ from by rw [hf]; exact root_born h hW hb k)
  let N (z : E × Vertical G c f) := (L z.1,V z)
  have hN : Tendsto N (𝓝 0) (𝓝 0) := by
    have h₀ := ((hL.comp (f:=Prod.fst) 0 contDiffAt_fst).prodMk hV).continuousAt.tendsto
    simpa only [show N 0=0 from Prod.ext hl hv] using (show Tendsto N _ (𝓝 (N 0)) from h₀)
  have hx := recognizes h hW hb t B hc hp hh
  filter_upwards [ht.eventually h3,ht.eventually h2.station,hB.eventually hS,hB.eventually hr,
    hB.eventually he,hB.eventually hu,hB.eventually (hN.eventually hx)] with x hx hY ha ht' hk hc' hg
  let z := arc (U ∘ F) x
  have hs : vert M z=0 := by
    apply ht'.trans; change (vert (action S k p W) ((F x),U (F x))) ∘L _=0
    change vert (action S k p W) (F x,U (F x))=0 at hY; rw [hY,ContinuousLinearMap.zero_comp]
  have hw : vert J (L x, V z)=0 := by
    apply ContinuousLinearMap.ext; intro i; obtain ⟨j,rfl⟩ := (show Surjective (vMap V z) from ha) i
    exact DFunLike.congr_fun (hk.symm.trans hs) j
  exact hx.symm.trans (hc'.trans (hg hw))

/-- Physical orientation and translation invariant real value germ at every
stamped step. Use on *that* W and *that* stationary proposal. -/
theorem oriented (s : Signed) (y : Site c) (k : S.Choices) :
    value T k p W b ∘ shifts s y =ᶠ[𝓝 0] value T k p W b := by
  let t := S.withinChoice s y k
  let V := rephase (S:=S) (G:=G) s y
  let P := V ∘L ContinuousLinearMap.snd ℝ (Dir G c) (Vertical G c f)
  have he := transfigures h hW hb hc hp hh t k id (shifts s y) P
    contDiffAt_id (shifts s y).contDiff.contDiffAt P.contDiff.contDiffAt rfl (map_zero _) (map_zero _)
    (Eventually.of_forall fun z => (commutes p W h s y k z).symm) (Eventually.of_forall fun z => by
      have hx : vMap (⇑P) z=V := by
        apply ContinuousLinearMap.ext; intro b; rw [vMap,P.fderiv]; rfl
      rw [hx]; exact rephase_surjective s y)
  have hh : S.patch.Branches S.kernel G := h
  exact he.symm.trans ((tested_germ hh T _ _ t k).comp_tendsto (crit_home hb))
end curves
end Joint
end YM.AnalyticNext.QuarticMatch
