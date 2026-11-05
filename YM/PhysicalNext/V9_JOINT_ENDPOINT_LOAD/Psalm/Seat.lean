import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Confirmed
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Sonata

/-! # Unmasked forecast on the *actually tested* bare region in an ambient
sector. Constants chosen so the argument fits the displacement chart at a
funded link, not L times (or the diameter of X times) that chart. No
holding unrelated Y stakes to obtain this; take any assignments on frozen
slots and even in the neighboring stationary germs. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure WardBin.Lies Planned.AtomRegular.Foliage
   AnalyticBridge.LocalGaussianLaws GaugeRoute Heir
open AnalyticBridge.SectorAffine (Offset.mean)
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {k : S.Choices} {I : Type}
    {X : Support f} {Y : Support c} {P B : BudgetPoint} {Pt : Teller G} {n j l : ℕ} {x u : ℝ} {q : Chi} {d : ℝ} {V W : Config G c}
    {o p : Site c} {g : Site c → G.El} {C : Libretto G n} {D : Record}

abbrev vocal (T : Tube G S) (x : ℝ) (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (q : Chi) (d : ℝ) (U : Config G f) (W : Config G c) :=
    tape (Offset.mean T x k A F q d (Folio.leaf A F x U) W)

lemma center_rot (T : Tube G S) (g : Site c → G.El) (h : Pt.Funds S T) (e : Active A x F) (U : Config G f) :
    G.adjoint (g (S.ratio.parent e.val.val.1)) (vocal T x k A F q d U W e) = vocal T x k A F q d (gauge (g ∘ S.ratio.parent) U) (gauge g W) e := by
  unfold vocal; rw [(carry_model (A:=A) (F:=F) g W U h).1,ascent_read]; rfl

variable (h : Plays C D P B Pt T x) (a : Museum F x A X Y I) (hV : Healthy P.threshold Y V)
include a h
lemma solstice (hy : Museum.Station Y x o) (hg : Canvas P o (reach x) V g n C.C) (e : Active A x F) (hp : separation o (S.ratio.parent e.val.val.1) ≤ 7*(1+radiusB x)) :
    ∀ᶠ W : Config G c in 𝓝 V, ∀ U : Config G f, G.adjoint (g (S.ratio.parent e.val.val.1)) (vocal T x k A F q d U W e) = Signal T F x k (crop o (reach x) g W) e.val.val :=
  hg.seen.mono (fun _ he U => (center_rot T g h.bulletin.priced e U).trans (a.near_forecast h.bulletin hy _ he e hp _))

omit a h
abbrev voiceCost (C : Libretto G n) := C.M*C.C*2 + C.C*2 + 1
lemma voiceCost_one (C : Libretto G n) : 1 ≤ voiceCost C := by have := C.matins; have := C.C_one; unfold voiceCost; nlinarith
lemma release_tension (h : Rehearsed C D P B S.patch.L x) :
    let v := loom P (reach x) C.C
    D.Q*(temp x+v)*v ≤ B.threshold := by
  intro v; have he := h.tensions.quartic; have h1 := C.web.cost; have h0 := Work.E04.temp_nonneg x; have := D.majorant
  have hh := P.threshold_pos; have := C.C_one; have hv : 0≤v := by unfold v loom; positivity
  apply le_trans (b:=C.web.scale*(D.Q*(temp x+v))^2)
  · calc
      _ ≤ (D.Q*(temp x+v))^2 := by rw [sq]; gcongr; nlinarith only [hv,h0,D.majorant]
      _ ≤ _ := le_mul_of_one_le_left (by positivity) h1
  linarith only [he,B.threshold_pos]

include a h hV
lemma vocal_bound (e : Active A x F) (hy : halo (reach x+1) {S.ratio.parent e.val.val.1} ⊆ Y) (U : Config G f) : ‖vocal T x k A F q d U V e‖ ≤ voiceCost C * B.threshold := by
  let i := e.val.val; let o := S.ratio.parent i.1
  have hy' := (Corona.halo_mono (Nat.le_succ _) (Finset.Subset.refl _)).trans hy
  obtain ⟨g,hg⟩ := primed hV hy (roomy h.space) C.Z (by have := h.rehearsed.test; have := P.order_ge; omega) h.rehearsed.wire
  rw [← G.norm_adjoint (u:=g o), (solstice (k:=k) h a hy' hg e (le_trans (separation_self _).le (Nat.zero_le _))).self_of_nhds U]
  let v := crop o (reach x) g V; let S0 := Signal T F x k v
  have hh : ‖S0-treeMap T F v‖ ≤ B.threshold := ((h.harps F k).zeroth_charge (by have := h.rehearsed.test; have := P.order_ge; omega)
    (hg.paid C.C_one) h.rehearsed.tensions.allows.le).trans (release_tension h.rehearsed)
  have hP := P.threshold_pos; have hC := C.C_one
  have hc := (h.stages F).stage v i i.1 (mul_nonneg (by positivity) hP.le) (hg.visible hC h.rehearsed.powers)
  rw [spine_self,mul_one] at hc
  have hd : ‖carriedCopy S v i‖ ≤ C.C*P.threshold := by
    change ‖linearCopy S.ratio v i‖ ≤ _; unfold linearCopy; split
    · rw [norm_zero]; positivity
    simpa only [o,i,spine_self,mul_one] using (hg.visible hC (Nat.le_refl P.power) (o,i.2))
  have he : ‖S0 i‖ ≤ ‖(S0-treeMap T F v) i‖ + ‖woody T F v i‖ + ‖carriedCopy S v i‖ := by
    have h := congr_fun (DFunLike.congr_fun (woody_eq T F) v) i; change _ = treeMap T F v i + carriedCopy S v i at h
    calc
      _ = ‖(S0-treeMap T F v) i + woody T F v i - carriedCopy S v i‖ := by congr 1; rw [h,Pi.sub_apply]; abel
      _ ≤ _ := (norm_sub_le ..).trans (add_le_add_left (norm_add_le ..) _)
  change ‖S0 i‖ ≤ _; have h₁ : P.threshold ≤ 2*B.threshold := h.rehearsed.temp_eq.symm ▸ h.rehearsed.tensions.coarse
  have hm := C.matins
  unfold voiceCost; nlinarith only [he,(norm_le_pi_norm _ i).trans hh,hc,hd,mul_le_mul_of_nonneg_left h₁ (by positivity : 0≤C.M*C.C+C.C)]

omit a h hV
lemma chart_continuousAt {E : Type*} [TopologicalSpace E] (f : Config G c → E) (h : ContinuousAt (f ∘ increment V) 0) : ContinuousAt f V := by
  let L (t : Config G c) (e : Edge (Site c)) := G.plog (G.mat (t e*(V e)⁻¹))
  obtain ⟨(hx : L V=0), (hh : ContinuousAt L V), he⟩ := WardBin.exp_local V id V rfl (fun i => (continuous_apply i).continuousAt)
  exact ContinuousAt.congr_of_eventuallyEq ((show ContinuousAt (f ∘ increment V) (L V) from hx.symm ▸ h).comp hh) (he.mono fun y hy => congr_arg f hy.symm)

private lemma unrotate (g : G.El) (a : G.Color) : G.adjoint g⁻¹ (G.adjoint g a) = a := by
  rw [← G.adjoint_mul,inv_mul_cancel]; simp

include a h hV
lemma vocal_cont (e : Active A x F) (hy : halo (reach x+1) {S.ratio.parent e.val.val.1} ⊆ Y) (U : Config G c → Config G f) : ContinuousAt (fun W => vocal T x k A F q d (U W) W e) V := by
  let i := e.val.val; let o := S.ratio.parent i.1
  have hy' := (Corona.halo_mono (Nat.le_succ _) (Finset.Subset.refl _)).trans hy
  obtain ⟨g,hg⟩ := primed hV hy (roomy h.space) C.Z (by have := h.rehearsed.test; have := P.order_ge; omega) h.rehearsed.wire
  let f W := Signal T F x k (crop o (reach x) g W)
  have he : ContinuousAt f V := ((h.harps F k).uniform _ ((hg.paid C.C_one).trans h.rehearsed.tensions.allows.le)).smooth.continuousAt.comp (chart_continuousAt _ hg.germ.continuousAt)
  refine ContinuousAt.congr_of_eventuallyEq ((G.adjoint (g o)⁻¹).toContinuousLinearMap.continuous.continuousAt.comp ((continuous_apply i).continuousAt.comp he)) ?_
  filter_upwards [solstice (k:=k) (d:=d) (q:=q) h a hy' hg e (le_trans (separation_self _).le (Nat.zero_le _))] with W hw
  change _ = G.adjoint _ (f W i); unfold f; rw [← hw (U W)]; exact (unrotate ..).symm

omit a h hV
include a h

end YM.PhysicalNext.JointLoad.Psalm
