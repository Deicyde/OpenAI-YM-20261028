import YM.PREC.Implicit
import YM.Pressure.Seeds

/-!
# Frame branch real smooth germ at trivial. Fixed period here. Project
nearest matrix to avoid choices at Lie complement. All site-frame histories
near trivial ignored coherently. Not uniform Gram cluster widths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push
open Function Filter Lattice RG Wilson Precision Pressure Gauge Branch Exterior
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators NNReal
attribute [local instance] Gauge.frobInner

variable {n : Side} {G : Gauge}

lemma stroll {U : fieldDir G n 1 → Config G n} (h : ∀ i, ContDiffAt ℝ ω (fun v => G.mat (U v i)) 0) (p : Walk) (x : Site n) :
    ContDiffAt ℝ ω (fun v => G.mat (travel (U v) x p)) 0 := by
  induction p generalizing x with
  | nil => exact contDiffAt_const
  | cons i l ih =>
    simp only [travel, mat_mul]; apply ContDiffAt.mul _ (ih _)
    unfold Step.read; split; next he => simp only [mat_inv]; exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (h _)
    exact h _

lemma writes (p : Walk) (x : Site n) : ContDiffAt ℝ ω (fun v => G.mat (travel (represent v) x p)) 0 := stroll
    (fun i => by
      unfold represent increment collect; simp only [Pi.one_apply,mul_one]
      exact G.exp_jet.contDiffAt.comp _ (contDiffAt_apply _ _ _ _)) p x

@[simp] lemma stroll_zero (p : Walk) (x : Site n) : travel (represent (0 : fieldDir G n 1)) x p=1 := by
  induction p generalizing x with
  | nil => rfl
  | cons i l ih => rw [travel,ih]; simp [Step.read]

section any
variable {n X : Type} [Fintype n] (a : n → ℝ → X) [NormedAddCommGroup X] [NormedSpace ℝ X] (t : ℝ) (d : n → X)
lemma avg_rate (h : ∀ i,HasDerivAt (a i) (d i) t) : HasDerivAt (fun x => avg fun i => a i x) (avg d) t := by
  apply HasDerivAt.const_smul
  exact HasDerivAt.fun_sum (fun i _ => h i)
end any

lemma focused {U : ℝ → G.Mat} (d : G.Mat) (h : HasDerivAt U d 0) (he : U 0=1) :
    HasDerivAt (fun x => G.mat (G.focus (U x))) (G.lie.starProjection d) 0 := by
  have hv : HasFDerivAt (fun x => G.mat (G.focus x)) G.lie.starProjection (U 0) := by rw [he]; exact G.focus_deriv.hasFDerivAt
  exact hv.comp_hasDerivAt 0 h

variable {c f : Side} (S : StepData c f)
abbrev In (G : Gauge) (f : Side) := fieldDir G f 1

section frame
variable (y : Site c) (t : S.SitesChoice)

def product (v : In G f) := expandAt (S.ratio.embed y) (represent v)
def hats (v : In G f) (i : S.patch.Points) := G.mat (S.frames (represent v) t y i)

def cloud (p : In G f × (S.patch.Points → G.Mat)) (i : S.patch.Points) := avg fun r : S.patch.Points => avg fun o : Lattice.Order =>
    p.2 r * star (G.mat (travel (product S y p.1) i.val (route i.val r.val o)))

lemma product_cont : Continuous fun v : In G f => product S y v := by
  unfold product expandAt represent collect increment; fun_prop

lemma product_zero : product S y (0 : In G f)=1 := by funext i; simp only [product,link_one]; rfl

def plant (q : In G f × (S.patch.Points → G.Mat)) (i : S.patch.Points) :=
    if i=S.patch.center then q.2 i - 1 else q.2 i - G.mat (G.focus (cloud S y q i))

variable {h : S.patch.Branches S.kernel G}

lemma picks : S.patch.usesMin S.kernel (product S y (0 : In G f)) := by
  intro k l x v
  simp only [product_zero,Patch.via,Patch.axial,Pressure.one,mul_one, inv_one,chord_one]; exact S.kernel.frame_cut_pos

lemma threshold : ∀ᶠ v : In G f in 𝓝 0,S.patch.usesMin S.kernel (product S y v) := (product_cont S y).continuousAt.tendsto.eventually
  (S.patch.min_open.mem_nhds (picks S y (G:=G)))
include h

lemma hats_zero (i : S.patch.Points) : hats S y t (0 : In G f) i=1 := by
  let U := product S y (0 : In G f)
  have hs : S.patch.selected U=1 := (h.frame_unique U (picks S y (G:=G))).unique (S.patch.min_exists U).choose_spec
    (show S.patch.minimizing U 1 from ⟨rfl,fun i _ => by
      have he : S.patch.score U 1=0 := by simp [Patch.score, Patch.average,Patch.via,U,product_zero,Pressure.one]
      rw [he]; unfold Patch.score Patch.average
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => (G.price_range _).1))) ⟩)
  change G.mat (S.patch.frame S.kernel U _ i)=_
  rw [Patch.frame, if_pos (picks S y (G:=G)),hs]; simp

lemma hat_cont (i : S.patch.Points) : ContinuousAt (fun v : In G f => hats S y t v i) 0 := by
  let m := product S y (G:=G)
  have he : ContinuousAt S.patch.selected (m 0) := (S.patch.selected_cont h).continuousAt (S.patch.min_open.mem_nhds (picks S y (G:=G)))
  apply (G.continuous_mat.continuousAt.comp (show ContinuousAt (fun v => S.patch.selected (m v) i) 0 from
    (continuous_apply i).continuousAt.comp (he.comp (product_cont S y).continuousAt))).congr
  filter_upwards [threshold S y (G:=G)] with v hv
  change G.mat _=G.mat (S.patch.frame _ (product S y v) _ i)
  rw [Patch.frame, if_pos hv]

omit h in
lemma roots : ∀ᶠ v : In G f in 𝓝 0,hats S y t v S.patch.center=1 := by
  filter_upwards [threshold S y (G:=G)] with v hv
  change G.mat (S.patch.frame _ (product S y v) _ _)=_
  rw [Patch.frame,if_pos hv,show S.patch.selected _ _=1 from (S.patch.min_exists (product S y v)).choose_spec.1]
  exact mat_one _

lemma cloud_zero (i : S.patch.Points) : cloud S y (0, hats S y t (0 : In G f)) i=1 := by simp only [cloud,hats_zero S y t (h:=h), product_zero,Pressure.one,G.mat_one,star_one,mul_one,avg_const]

omit h in
lemma cloud_form (i : S.patch.Points) (b) : ContDiffAt ℝ ω (fun p : In G f × _ => cloud S y p i) (0,b) := by
  unfold cloud Branch.avg
  apply ContDiffAt.const_smul; apply ContDiffAt.sum; intro j _; apply ContDiffAt.const_smul; apply ContDiffAt.sum
  intro l _; refine ((contDiffAt_apply ℝ G.Mat j _).comp ((0:In G f),b) contDiffAt_snd).mul ?_
  simp_rw [product,travel_at]
  have hb : ContDiffAt ℝ ω (fun p : In G f × _ => G.mat (travel (represent p.1) (atPoint S y i) (route i.val j.val l))) (0,b) := (writes (G:=G) (route i.val j.val l) (atPoint S y i)).comp (f:=Prod.fst) ((0:In G f),b) (contDiffAt_fst (p:=((0:In G f),b)))
  exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp ((0:In G f),b) hb

lemma stars (i) : ∀ᶠ v : In G f in 𝓝 0, hats S y t v i = G.mat (G.focus (cloud S y (v,hats S y t v) i)) := by
  have ht : ContinuousAt (hats S y t (G:=G)) 0 := continuousAt_pi.mpr (hat_cont S y t (h:=h))
  have he := (cloud_form S y (G:=G) i (hats S y t 0)).continuousAt.tendsto
  rw [cloud_zero S y t (h:=h)] at he
  filter_upwards [threshold S y, (he.comp (tendsto_id.prodMk_nhds ht.tendsto)).eventually G.nearest_is_focus] with v hv hq
  unfold hats; congr 1; apply hq _
  let U := product S y v
  let H (i : S.patch.Points) := S.patch.frame S.kernel U (t y) i
  have hg := Road.strips S.patch _ U hv (t y) (fun _ => 1)
  rw [show (Lattice.gauge (fun _ => (1:G.El)) U)=U from funext fun i => by simp [Lattice.gauge]] at hg
  have hs : G.Nearest (H i) ((Road.pairs S.patch U).feedback H i) := Pairs.self_consistent _ (by simpa only [inv_one,mul_one,H, U] using hg) _
  convert! hs using 1

lemma scheme (i : S.patch.Points) : ContDiffAt ℝ ω (fun v : In G f => hats S y t v i) 0 := by
  let a := hats S y t (G:=G)
  let F := uncurry (fun x u => plant S y (x,u)) (α:=In G f)
  have hk : ContDiffAt ℝ ω F (0,a 0) := by
    refine contDiffAt_pi.mpr fun v => ?_
    unfold F uncurry plant
    dsimp only
    split
    · exact ((contDiffAt_apply ℝ G.Mat v _).comp ((0:In G f),a 0) contDiffAt_snd).sub contDiffAt_const
    apply ((contDiffAt_apply ℝ G.Mat v _).comp ((0:In G f),a 0) contDiffAt_snd).sub
    have hh : ContDiffAt ℝ ω (fun x => G.mat (G.focus x)) (cloud S y (0,a 0) v)  :=
      by rw [show cloud _ _ _ _=1 from cloud_zero S y t (h:=h) _]; exact G.focus_diff
    exact hh.comp (f:=fun p => cloud S y p v) ((0:In G f),a 0) (cloud_form S y v (a 0))
  have hx : ∀ᶠ x : In G f in 𝓝 0,F (x,a x)=0 := by
    filter_upwards [roots S y t (G:=G), eventually_all.mpr (stars S y t (h:=h))] with x hx hh
    funext i; change plant _ _ _ _=_; unfold plant; split
    next hi => rw [hi]; simp [a,hx]
    exact sub_eq_zero.mpr (hh i)
  refine (contDiffAt_apply ℝ G.Mat i _).comp 0 (authored a F 0 hx (continuousAt_pi.mpr fun i => hat_cont S y t (h:=h) i) hk fun u H => ?_)
  let P := ((0:In G f),a 0)
  let p (x : ℝ) := ((0:In G f),a 0+x • u)
  have hp : p 0=P := by simp [P,p]
  have hg : HasDerivAt p (0,u) 0 := by
    have hx : HasDerivAt (fun x : ℝ => x • u) u 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const u
    have hg : HasDerivAt (fun x : ℝ => a 0+x • u) u 0 := hx.const_add _
    exact (hasDerivAt_const (0:ℝ) 0).prodMk hg
  have hP := hk.differentiableAt (by simp) |>.hasFDerivAt
  rw [show (0,a 0)=p 0 from hp.symm] at hP
  have hF := hP.comp_hasDerivAt 0 hg; rw [hp, H] at hF
  let Q := Branch.avg u
  let AA := G.lie.starProjection Q
  have hu (j) : HasDerivAt (fun x => (p x).2 j) (u j) 0 := ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : S.patch.Points => G.Mat) j) ∘L (ContinuousLinearMap.snd ℝ (In G f) _)).hasFDerivAt.comp_hasDerivAt _ hg
  have hv (j) : HasDerivAt (fun x => F (p x) j) 0 0 := by
    simpa only [map_zero] using! (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : S.patch.Points => G.Mat) j).hasFDerivAt.comp_hasDerivAt _ hF
  have he (j) : u j=if j=S.patch.center then 0 else AA := by
    have hi := hv j
    change HasDerivAt (fun x => if j=S.patch.center then (p x).2 j-1 else _) 0 0 at hi
    split <;> rename_i HJ
    · simp only [if_pos HJ] at hi
      exact ((hu j).sub_const _).unique hi
    simp only [if_neg HJ] at hi
    have hb : HasDerivAt (fun x => cloud S y (p x) j) Q 0 := by
      simp only [cloud,p,product_zero,Pressure.one,G.mat_one,star_one,mul_one,avg_const]
      exact avg_rate _ _ _ hu
    have hh := focused Q hb (by rw [hp]; exact cloud_zero S y t (h:=h) _)
    exact sub_eq_zero.mp (((hu j).sub hh).unique hi)
  have hn : 0<(Fintype.card S.patch.Points : ℝ):=by exact_mod_cast Fintype.card_pos
  have hv0 : AA=0 := by
    have eq : Q = (Fintype.card S.patch.Points : ℝ)⁻¹ • (((Fintype.card S.patch.Points : ℝ)-1) • AA) := by
      unfold Q avg; congr 1
      calc
        _ = ∑ j : S.patch.Points,(AA - if j=S.patch.center then AA else 0) := Finset.sum_congr rfl fun i _ => by rw [he i]; split <;> simp
        _ = _ := by simp [Finset.sum_sub_distrib,sub_smul , - nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
    have hy : (Fintype.card S.patch.Points:ℝ) • AA=((Fintype.card S.patch.Points:ℝ)-1) • AA := by
      have hg : G.lie.starProjection AA=AA := G.lie.starProjection_eq_self_iff.mpr (G.lie.starProjection_apply_mem _)
      conv_lhs => arg 2; unfold AA; rw [eq]; simp only [map_smul,hg]
      rw [smul_inv_smul₀ hn.ne']
    rw [sub_smul,one_smul] at hy; grind
  funext i; rw [he,hv0]; simp
end frame
end YM.Push
