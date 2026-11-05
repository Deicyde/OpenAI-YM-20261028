import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.LocalJet
import YM.Work.F05.Jacobian


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Actual branch derivative on small fields in local stencil

Threshold post-L, periodic sizes arbitrary. Copy some private cover
lemmas here from Next/FLUCTUATIONS/Prediction, sharing *same*
predReach (D-cut rule/geometric eligibility uses that stencil). For the
branch and analytic proof itself use the accepted producers for log pastes
(`Push.prediction_cont` at one period, authentic branches).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.LocalJet.Block
open Function Filter Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open YM.Push.SectorMeasure YM.Push YM.Next.Fluctuations YM.Next.SectorChange.Motion
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Metric

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

lemma transReach {i : Axis} {x : Cover} (hx : x∈predSites S.patch i) : (route 0 x 1).length ≤ predReach S.patch := by
  unfold predReach
  exact le_trans (le_sup (f:=fun x => (route 0 x 1).length) hx) (le_sup (f:=fun i =>
    (predSites S.patch i).sup (fun x => (route 0 x 1).length)) (mem_univ i))

lemma onto {i : Axis} {x : Cover} (hx : x∈predSites S.patch i) (q : Site c) :
    separation q (S.ratio.parent (wrap f x + S.ratio.embed q)) ≤ predReach S.patch := by
  let w := route 0 x 1
  let s := S.ratio.embed q
  have hh : stop s w = wrap f x + s := by simpa only [map_zero, add_zero, add_comm] using Work.E03.stop_route s 0 x
  rw [← hh]
  apply le_trans ?_ (transReach hx)
  nth_rewrite 1 [← S.ratio.embed_parent q]
  exact Work.E03.sep_walk _ (Work.E03.parent_step S) _ w

end locality

/-- Smooth near zero in both log *and* left increment. Uses plog only
there, then keep left increments even at other fields. -/
private def steam (u a : Directions G f) := increment (increment 1 u) a

private lemma steam_mat {e : Bond f} : ContDiff ℝ ω (fun z : Directions G f × Directions G f => G.mat (steam z.1 z.2 e)) := by
  have hi : ContDiff ℝ ω (fun z : Directions G f × Directions G f => G.mat (G.lieExp (z.1 e))) :=
    G.exp_jet.comp ((contDiff_apply ℝ G.Color e).comp contDiff_fst)
  have hh : ContDiff ℝ ω (fun z : Directions G f × Directions G f => G.mat (G.lieExp (z.2 e))) :=
    G.exp_jet.comp ((contDiff_apply ℝ G.Color e).comp contDiff_snd)
  unfold steam increment; simp only [Pi.one_apply,mul_one,G.mat_mul]; exact hh.mul hi

private def steamLog (z : Directions G f × Directions G f) := Flat.labels fun e => G.plog (G.mat (steam z.1 z.2 e))

private lemma steam_rep : (represent (n:=f) (G:=G) ∘ steamLog) =ᶠ[𝓝 (0:Directions G f × Directions G f)] uncurry steam := by
  have ht (e : Bond f) :
      ∀ᶠ z : Directions G f × Directions G f in 𝓝 0,G.lieExp (G.plog (G.mat (steam z.1 z.2 e))) = steam z.1 z.2 e := by
    have he : Tendsto (fun z : Directions G f × Directions G f => steam z.1 z.2 e) (𝓝 0) (𝓝 1) := by
      refine (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr ?_
      have hw := (steam_mat (G:=G) (e:=e)).continuous.tendsto (0:Directions G f × Directions G f)
      simp only [Prod.fst_zero,Prod.snd_zero] at hw
      rw [show steam 0 (0:Directions G f) e=1 by rw [steam,increment_zero,increment_zero]; rfl] at hw
      exact hw
    exact he.eventually G.plog_right
  filter_upwards [Filter.eventually_all.mpr ht] with z hz
  funext i
  simp only [Function.comp_apply,represent,steamLog,Flat.collected,increment, hz,one_mul,mul_one,Pi.one_apply,uncurry]

set_option maxHeartbeats 150000 in
private lemma steam_smooth : ContDiffAt ℝ ω steamLog (0:Directions G f × Directions G f) := by
  unfold steamLog Flat.labels
  apply contDiffAt_pi.mpr; refine fun i => ?_
  let b : Bond f := (i.1,axisEquiv.symm i.2)
  let z0 := (0:Directions G f × Directions G f)
  let P := fun z : Directions G f × Directions G f => G.mat (steam z.1 z.2 b)
  have hm : P z0=(1:G.Mat) := by simp only [P,z0,steam,Prod.fst_zero,Prod.snd_zero,increment_zero,Pi.one_apply,G.mat_one]
  have ht : ContDiffAt ℝ ω P z0 := (steam_mat (G:=G) (e:=b)).contDiffAt
  exact (show ContDiffAt ℝ ω G.plog (P z0) from hm.symm ▸ G.plog_diff).comp (f:=P) z0 ht

private def basic (k : S.Choices) (b : Bond c) (p : Directions G f × Directions G f) :=
    G.mat (out (increment 1 p.1) k b p.2)

set_option maxHeartbeats 150000 in
private lemma predictor_smooth {k : S.Choices} (hS : S.patch.Branches S.kernel G) (b : Bond c) :
    ContDiffAt ℝ ω (basic (G:=G) k b) 0 := by
  let X := Directions G f × Directions G f
  let F (x : X) := G.mat (S.prediction (steam x.1 x.2) k b)
  have he : ContDiffAt ℝ ω F 0 := by
    have hh := prediction_cont S hS b k
    have ht : steamLog (0 : X)=0 := by
      funext i
      change G.plog (G.mat (steam 0 (0:Directions G f) (i.1,axisEquiv.symm i.2)))=_
      simp [steam,increment_zero]
    rw [← ht] at hh
    refine (hh.comp (0:X) (f:=steamLog) steam_smooth).congr_of_eventuallyEq ?_
    filter_upwards [steam_rep (G:=G) (f:=f)] with z hz
    exact congr_arg (fun U : Config G f => G.mat (S.prediction U k b)) hz.symm
  let L := fun z : X => ((z.1,(0:Directions G f)):X)
  have hp : ContDiffAt ℝ ω (fun z : X => F (L z)) 0 := by
    apply ContDiffAt.comp (g:=F) (f:=L) _ _ (contDiffAt_fst.prodMk contDiffAt_const)
    exact he
  have hw : ContDiffAt ℝ ω (fun z => F z * star (F (L z))) 0 := he.mul
    ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp (f:=fun z=>F (L z)) 0 hp)
  suffices e : basic (G:=G) k b = fun z => F z * star (F (L z)) from e.symm ▸ hw
  funext a; unfold F L basic out steam
  rw [G.mat_mul,G.mat_inv]
  dsimp only; rw [increment_zero]

private def pair (k : S.Choices) (b : Bond c) (v : Directions G f × Directions G f) :=
  bTest (increment 1 v.1) k b v.2

private lemma pair_plot {k : S.Choices} (hS : S.patch.Branches S.kernel G) (b : Bond c) :
    ContDiffAt ℝ ω (pair (G:=G) k b) 0 := Fluctuations.curvature_diff_mat _ _ (predictor_smooth hS b)

/-- fderiv in actual increment (second arg). -/
private lemma probe_cont {k : S.Choices} (hS : S.patch.Branches S.kernel G) (b : Bond c) :
    ContinuousAt (fun u => fderiv ℝ (fun a => pair k b (u,a)) 0) (0:Directions G f) :=
  (ContDiffAt.fderiv (f:=fun u a => pair k b (u,a)) (g:=fun _ : Directions G f => (0 : Directions G f))
    (m:=ω) (n:=ω) (pair_plot hS b) contDiffAt_const (by simp)).continuousAt

/-- Conditional Taylor gate at one fixed-volume. H mat version for Q interpretation. -/
private lemma solo {k : S.Choices} (hS : S.patch.Branches S.kernel G) (i : Bond c) {ε : ℝ} (he : 0<ε) :
    ∃ B r : ℝ, 0 < B ∧ 0 < r ∧ ∀ u : Directions G f, ‖u‖ ≤ r →
      let U := increment 1 u; let L:=fderiv ℝ (bTest U k i) 0
      ContDiffAt ℝ ω (fun a => G.mat (out U k i a)) 0 ∧ ContDiffAt ℝ ω (bTest U k i) 0 ∧
        ‖L-fderiv ℝ (bTest 1 k i) 0‖ ≤ ε ∧ ‖L‖ ≤ B := by
  let F (u : Directions G f) := fun a => pair k i (u,a)
  let L (u : Directions G f) := fderiv ℝ (F u) 0
  let B := ε+‖L 0‖
  have hx {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {g : Directions G f × Directions G f → H}
      (h : ContDiffAt ℝ ω g 0) : ∀ᶠ u : Directions G f in 𝓝 0, ContDiffAt ℝ ω (fun a : Directions G f => g (u,a)) 0 := by
    have hv : Tendsto (fun a : Directions G f => (a,(0:Directions G f))) (𝓝 0) (𝓝 ((0:Directions G f × Directions G f))) :=
      tendsto_id.prodMk_nhds tendsto_const_nhds
    filter_upwards [hv.eventually (h.eventually (n:=ω) (by simp))] with u hu
    exact hu.comp _ (contDiffAt_const.prodMk contDiffAt_id)
  have hl : ∀ᶠ u : Directions G f in 𝓝 0, ContDiffAt ℝ ω (fun a => basic k i (u,a)) 0 ∧ ContDiffAt ℝ ω (F u) 0 ∧ ‖L u-L 0‖ ≤ ε := by
    filter_upwards [hx (pair_plot hS (k:=k) i),hx (predictor_smooth (k:=k) hS i),
      (probe_cont (k:=k) hS i).eventually (ball_mem_nhds (L 0) he)] with u h₁ h₂ h₃
    exact ⟨h₂,h₁, (by simpa only [mem_ball,dist_eq_norm] using (Metric.mem_ball.mp h₃).le)⟩
  obtain ⟨r,hr,Hr⟩ := nhds_basis_closedBall.eventually_iff.mp hl
  refine ⟨B,r,by unfold B; positivity,hr,?_⟩
  intro u hu W M
  obtain ⟨hl,h,hP⟩ := Hr (x:=u) (mem_closedBall.mpr (by simpa using hu))
  have ht : L 0=fderiv ℝ (bTest (1:Config G f) k i) 0 := by unfold L F pair; simp only [increment_zero]
  exact ⟨hl,h,by rw [← ht]; exact hP,(show ‖L u‖ ≤ ‖L u-L 0‖+‖L 0‖ by simpa only [sub_add_cancel] using norm_add_le (L u-L 0) (L 0)).trans (add_le_add_left hP _)⟩

private lemma simultaneous (S : StepData c f) (hS : S.patch.Branches S.kernel G) {ε : ℝ} (he : 0<ε) :
    ∃ B r : ℝ, 0 < B ∧ 0 < r ∧ ∀ u : Directions G f, ‖u‖ ≤ r →
      ∀ (k:S.Choices) (i:Bond c), let U := increment 1 u; let L:=fderiv ℝ (bTest U k i) 0
      ContDiffAt ℝ ω (fun a => G.mat (out U k i a)) 0 ∧ ContDiffAt ℝ ω (bTest U k i) 0 ∧
        ‖L-fderiv ℝ (bTest 1 k i) 0‖ ≤ ε ∧ ‖L‖ ≤ B := by
  choose B r hB hr H using fun ki : S.Choices × Bond c => solo (k:=ki.1) hS ki.2 he
  let A := 1+∑ i, B i
  let m := (univ.image r).min' (univ_nonempty.image r)
  have hm : m ∈ univ.image r := min'_mem _ _
  refine ⟨A,m, by unfold A; exact add_pos_of_pos_of_nonneg (by norm_num) (sum_nonneg fun i _ => (hB _).le),
    ?_,?_⟩
  · obtain ⟨i,-,hi⟩ := mem_image.mp hm
    exact hi ▸ hr i
  intro u hu k i; let j := (k,i)
  obtain ⟨h,h',h1,h2⟩ := H j u (hu.trans (min'_le _ _ (mem_image_of_mem _ (mem_univ j))))
  have hx : B j ≤ ∑ i,B i := single_le_sum (f:=B) (fun i _ => (hB i).le) (mem_univ j)
  exact ⟨h,h',h1,h2.trans (hx.trans (by unfold A; linarith))⟩

section transplant
variable (P : Patch) (K : KernelChoices)

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


private lemma connect (h : P.Branches K G) (hv : f.val=c.val*P.L.val) {c₀ : Side} (hc : 1 < c₀.val)
    (hu : ∀ i : Axis, ∀ x ∈ predSites P i, lift (wrap (c₀*P.L) x) = x) (x : Site c) (i : Axis)
    (k : (⟨P,K,hv⟩ : StepData c f).Choices) (U : Config G f) {C δ : ℝ} (hC : 0<C) (hδ : 0<δ)
    (gate : ∀ u : G.El, G.chord u ≤ δ → G.lieExp (G.plog (G.mat u)) = u ∧ ‖G.plog (G.mat u)‖ ≤ C*G.chord u)
    (y : ℝ) (hy : 0≤y) (hy' : y≤δ) :
    let S : StepData c f := ⟨P,K,hv⟩
    (∀ e : Bond f, separation x (S.ratio.parent e.1) ≤ predReach S.patch → G.chord (U e) ≤ y) →
    let S' : StepData c₀ (c₀*P.L) := ⟨P,K,rfl⟩
    ∃ k' : S'.Choices, ∃ (u' : Directions G (c₀*P.L)) (L : Directions G f →L[ℝ] Directions G (c₀*P.L)),
      ‖u'‖ ≤ C*y ∧ (∀ a, ‖L a‖ ≤ settle S x (predReach S.patch) a) ∧
      ∀ a, out U k (x,i) a = out (increment 1 u') k' (0,i) (L a) ∧
        out (1:Config G f) k (x,i) a = out 1 k' (0,i) (L a) := by
  intro S H S'
  haveI : Fact (1 < c₀.val) := ⟨hc⟩
  have ha : Lattice.step i ≠ (0:Site c₀) := by
    intro he
    have h : (1 : ZMod c₀.val) = 0 := by simpa using congr_fun he i
    exact one_ne_zero h
  let k₀ : S'.Choices := (fun y => if y=0 then k.1 x else k.1 (x+Lattice.step i), fun _ => k.2 (x,i))
  let s := S.ratio.embed x; let s' := S'.ratio.embed 0
  let B := c₀*P.L
  let X (y : Site B) := wrap f (lift (y-s'))+s
  let D (u : Bond B) : Prop := lift (u.1-s') ∈ predSites P i
  let Q (u : Bond B) : Bond f := (X u.1, u.2)
  let T (U : Config G f) : Config G B := fun v => if D v then U (Q v) else 1
  let L : Directions G f →L[ℝ] Directions G B := (LinearMap.pi fun b : Bond B => if D b then (LinearMap.proj (Q b) : Directions G f →ₗ[ℝ] _) else 0).toContinuousLinearMap
  let u : Directions G B := fun b => G.plog (G.mat (T U b))
  have L_eq (a : Directions G f) (e : Bond B) : L a e = if D e then a (Q e) else 0 := by
    change (if D e then (LinearMap.proj (Q e) : Directions G f →ₗ[ℝ] G.Color) else 0) a=_; split <;> rfl
  have read (U : Config G f) (v : Cover) (p : Axis) (h : v∈predSites P i) : expandAt s' (T U) (v,p) = expandAt s U (v,p) := by
    unfold expandAt T
    have hx : D (wrap B v+s',p) := by change lift (wrap B v+s'-s')∈_; rwa [add_sub_cancel_right,hu i v h]
    rw [if_pos hx]; unfold Q X; rw [show ((wrap B v+s',p):Bond B).1-s'=wrap B v by simp,hu i v h]
  have hsize (p : Bond B) (hp : D p) : separation x (S.ratio.parent (Q p).1) ≤ predReach P :=
    onto (S:=S) hp x
  have htu (p) : G.chord (T U p) ≤ y := by
    unfold T; split
    next h => exact H _ (hsize p h)
    next h => simpa using hy
  have hn (p) := gate (T U p) ((htu _).trans hy')
  have hxU : T U=increment 1 u := by funext i; unfold increment u; rw [(hn i).1]; simp
  have lake (U : Config G f) (a : Directions G f) : increment (T U) (L a)=T (increment U a) := by
    funext e; unfold T increment; rw [L_eq]; split
    next h => simp [h]
    next h => simp [h]
  have he (U : Config G f) : S.prediction U k (x,i) = S'.prediction (T U) k₀ (0,i) := by
    rw [reads_at, reads_at]
    have ht : k₀.1 (0+Lattice.step i)=k.1 (x+Lattice.step i) := by dsimp only [k₀]; rw [zero_add, if_neg ha]
    change predictionAt P i K _ _ _ _ = predictionAt P i K _ _ _ _
    rw [ht, show k₀.1 0=k.1 x from if_pos rfl]
    apply predAt_eq P i K h
    exact fun z hz => (read U z.1 z.2 hz).symm
  have hi (U : Config G f) (a) : out U k (x,i) a = out (T U) k₀ (0,i) (L a) := by
    unfold out; rw [he U,he (increment U a), lake]
  refine ⟨k₀,u,L,?_,?_,fun a => ⟨hxU ▸ hi U a,?_⟩⟩
  · exact (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le hy)).mpr fun p => ((hn p).2).trans (mul_le_mul_of_nonneg_left (htu p) hC.le)
  · intro a
    refine (pi_norm_le_iff_of_nonneg (settle_nonneg ..)).mpr fun p => ?_
    rw [L_eq]; split
    next hp => exact settle_pays _ _ _ _ (hsize p hp)
    next hp => rw [norm_zero]; exact settle_nonneg ..
  have h1 : T (1:Config G f)=1 := by funext i; unfold T; split <;> rfl
  rw [hi 1,h1]

/-- Actual at any period and one actual k. Estimate on fderiv of
rooted Q uses local direction count at this period. Includes analytic
on the **mat** version; compare the left-trivialized group differential
before using on noise. No claim on likelihood differentiation. -/
theorem block_comparison (G : Gauge) (P : Patch) (K : KernelChoices) (h : P.Branches K G) {ε : ℝ} (he : 0<ε) :
    ∃ B δ : ℝ, 0<B ∧ 0<δ ∧ ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ k : S.Choices, ∀ (U : Config G f) (i : Bond c),
      (∀ e : Bond f, separation i.1 (S.ratio.parent e.1) ≤ predReach P → G.chord (U e) ≤ δ) →
      let L:=fderiv ℝ (bTest U k i) 0
      ContDiffAt ℝ ω (fun a => G.mat (out U k i a)) 0 ∧ ContDiffAt ℝ ω (bTest U k i) 0 ∧
      ∀ a : Directions G f, ‖L a‖ ≤ B * settle S i.1 (predReach P) a ∧
        ‖L a - fderiv ℝ (bTest 1 k i) 0 a‖ ≤ ε * settle S i.1 (predReach P) a := by
  obtain ⟨c',hc',Hf⟩ := reference_exists P
  let S' : StepData c' (c'*P.L) := ⟨P,K,rfl⟩
  obtain ⟨B,r,hB,hr,H⟩ := simultaneous S' h he
  obtain ⟨C,δ,hC,hδ,H'⟩ := log_chart_cost G
  let x := min δ (r / C)
  have hx : 0<x := lt_min hδ (div_pos hr hC)
  refine ⟨B,x,hB,hx,?_⟩
  rintro c f ⟨P₀,K₀,e⟩ hP hK k U i hf
  change P₀=P at hP; change K₀=K at hK; subst P₀ K₀
  let S : StepData c f := ⟨P,K,e⟩
  obtain ⟨k',u,T,ht,hL,hl⟩ := connect P K h e hc' Hf i.1 i.2 k U hC hδ H' x hx.le (min_le_left ..) hf
  intro L
  let b : Bond c' := (0,i.2)
  let B' : S'.Choices → Directions G (c'*P.L) → Directions G (c'*P.L) → G.Color := fun k a y => bTest (increment 1 a) k b y
  have heq : bTest U k i=B' k' u ∘ T := funext fun a => congr_arg G.curvature (hl a).1
  have hmeq : (fun a => G.mat (out U k i a))=(fun y => G.mat (out (increment (1:Config G (c'*P.L)) u) k' b y)) ∘ T :=
    funext fun a => congr_arg G.mat (hl a).1
  have h0eq : bTest (1:Config G f) k i=B' k' 0 ∘ T := funext fun a => by
    unfold bTest B'; rw [increment_zero]; exact congr_arg G.curvature (hl a).2
  obtain ⟨hv,hu,hN,hJ⟩ := H u (ht.trans (by
    rw [mul_comm]; exact (le_div_iff₀ hC).1 (min_le_right ..))) k' b
  have hp := (H 0 (by rw [norm_zero]; exact hr.le) k' b).2.1
  have hM : T 0=0 := T.map_zero
  rw [← hM] at hv hu hp
  refine ⟨?_,heq ▸ hu.comp _ T.contDiff.contDiffAt,fun a => ?_⟩
  · rw [hmeq]
    -- hM only change site, not RHS
    -- type
    exact hv.comp (f:=T) _ T.contDiff.contDiffAt
  unfold L; rw [heq,h0eq,fderiv_comp _ (hu.differentiableAt (by simp)) T.differentiableAt,
    fderiv_comp (g:=B' k' 0) (f:=T) (𝕜:=ℝ) (0:Directions G f) (by simpa only [hM,B',hM] using hp.differentiableAt (by simp)) T.differentiableAt]
  simp only [hM,T.fderiv,ContinuousLinearMap.comp_apply]
  constructor
  · exact ((fderiv ℝ (B' k' u) 0).le_opNorm _).trans (mul_le_mul hJ (hL _) (norm_nonneg _) hB.le)
  change ‖(fderiv ℝ (B' k' u) 0 - fderiv ℝ (B' k' 0) 0) (T a)‖ ≤ _
  apply ((fderiv ℝ (B' k' u) 0 - fderiv ℝ (B' k' 0) 0).le_opNorm _).trans
  have hb : B' k' 0=bTest (1:Config G (c'*P.L)) k' b := by unfold B'; rw [increment_zero]
  rw [hb]; exact mul_le_mul hN (hL a) (norm_nonneg _) he.le

end transplant
end YM.Next.SectorChange.LocalJet.Block
