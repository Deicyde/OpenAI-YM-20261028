import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Gauged
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Corners


/-! Exact gauge transport through the *unmasked* local mean and E's
relative field. The tree and every extra likelihood/seed choice remain in
the same system; NOT a transformation to a changed physical sector.
No smoothness assumed for unspecified behavior of unselected or off-branch
predictors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Tree Next Next.SectorChange Next.SectorChange.Rows Wisps
    Precision Next.Fluctuations Exterior Bloch Bid AnalyticBridge.LocalGaussianLaws Push.SectorMeasure
    Tube ColorBook AnalyticBridge.SectorAffine.Offset GaugeRoute Matrix
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {o : Site f} {p : Site c} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {x : ℝ} {X : Support f} {Y : Support c} {V W : Config G c} {k : S.Choices} {P : Teller G} {T : Tube G S} {q : Chi} {d u : ℝ}

abbrev ascent {I : Type} [Fintype I] [DecidableEq I] (g : I → G.El) := ColorBook.onPage (Equiv.refl I) (tagColor (fun i => adBody (g i)))
lemma ascent_read {I : Type} [Fintype I] [DecidableEq I] (g : I → G.El) (z : Prices G I) :
    tape (ascent g *ᵥ z)=pivot g (tape z) := by rw [← (tape.symm_apply_apply z),ascent, ColorBook.onPage_read,MeasurableEquiv.apply_symm_apply,MeasurableEquiv.apply_symm_apply]; rfl

private lemma bare_stacks (T : Tube G S) (V : Config G c) (z : Site c → G.El) (h : S.patch.Branches S.kernel G) (x : ℝ) (k : S.Choices) :
    fixedBase T x (gauge z V) k=pivot (rowAt S z) (fixedBase T x V k) := by
  let r := Stores.till x
  funext ⟨s,j⟩
  let v := pull s (0:Site c) V; let q := z ∘ s.act; let W := gauge q v
  have h1 : pull s 0 (Lattice.gauge z V)=W := by rw [Work.F05.pull_gauge_zero]; unfold W; congr! 1; funext; simp [q,affine]
  have h0 : facade S s (Lattice.gauge z V) 0=Lattice.gauge (q ∘ S.ratio.parent) (facade S s V 0) := by
    rw [fixed_facade,fixed_facade,← AnalyticBridge.SectorAffine.Identity.top_copy,← AnalyticBridge.SectorAffine.Identity.top_copy,h1,← copied S.ratio S.patch.odd_side]; rfl
  have hb j : T.Xn r W j=G.adjoint (q j.1.1) (T.Xn r v j) := plotted_flow ..
  cases j
  next j =>
    change T.Xf r _ _ - Pressure.zip (T.Φ r _) (T.Xn r _) _=G.adjoint (q (S.ratio.parent j.1.1)) (_ - _)
    rw [h0,h1,Tube.Xf,plotted_flow,map_sub]; apply congr_arg₂ _ rfl
    unfold Pressure.zip; rw [map_sum]; exact Finset.sum_congr rfl fun t _ => by rw [hb]; exact leap_flow ..
  next j =>
    change Z S _ _ _ - Pressure.zip (T.Φ' r _) (T.Xn r _) _=G.adjoint (q j.1) (_ - _)
    rw [h1,aim S z V k h,map_sub]; apply congr_arg₂ _ (z_turn G v _ _ _)
    unfold Pressure.zip; rw [map_sum]; exact Finset.sum_congr rfl fun t _ => by rw [hb]; exact lane_flow ..

variable (z' : Site c→G.El)
private lemma carry_f0 (V : Config G c) (U : Config G f) (ht : S.patch.Branches S.kernel G) :
    f0 T x A F k (gauge z' V) q d (Folio.leaf A F x (gauge (z' ∘ S.ratio.parent) U)) =
      ascent (rowAt S z') *ᵥ f0 T x A F k V q d (Folio.leaf A F x U) := by
  let Y := Folio.leaf A F x U
  have he : Folio.leaf A F x (gauge (z' ∘ S.ratio.parent) U) = sendFrozen S z' x A F Y := rfl
  unfold f0; rw [he,fired S z' V x A F,ascent,onPage_read,(GaugeRoute.template S T z' V x k ht _).2,bare_stacks T V z' ht x k,← map_add,bands]; rfl

lemma carry_model (V : Config G c) (U : Config G f) (h : P.Funds S T) :
    let L := ascent (columnAt S z' x A F); let Y := gauge (z' ∘ S.ratio.parent) U; let W := gauge z' V
    AnalyticBridge.SectorAffine.Offset.mean T x k A F q d (Folio.leaf A F x Y) W = L *ᵥ AnalyticBridge.SectorAffine.Offset.mean T x k A F q d (Folio.leaf A F x U) V ∧
    fog A F T x W k=Density.skim L (fog A F T x V k) := by
  intro L Y W
  have hs : S.patch.Branches S.kernel G := h.knobs ▸ h.kernel
  obtain ⟨m,n,hm,-⟩ := h.feeds
  let t := shots S x
  let D V := Rows.move T x V k t A F
  let p U V := f0 T x A F k V q d (Folio.leaf A F x U)
  let R := fun i => adBody (columnAt S z' x A F i)
  obtain ⟨ha,hb⟩ := ColorBook.weaves (Equiv.refl _) R (Equiv.refl _) (fun i => adBody (rowAt S z' i)) (D V) (D W) (p Y W) (p U V)
    (pushed S T z' V x A F k hm hs t) (congr_arg _ (carry_f0 (A:=A) (F:=F) (T:=T) z' V U hs))
  let T0 (i : Active A x F) : Set (Active A x F) := {j | Assembly.rel S .endpoint (radiusB x) i.val.val j.val.val}
  have hL : ColorBook.sheet (k:=G.ColorIndex) T0=panels A F := rfl
  obtain ⟨_,h1,h2,_⟩ := ColorBook.moves _ R (Rows.gram T x V k t A F) (Rows.gram T x W k t A F) _ _ T0 T0 0 rfl ha hb
  simp_rw [hL,pane_zero] at h1 h2
  exact ⟨h2,h1⟩

namespace Museum
variable {I : Type} (M : Museum F x A X Y I) [Fintype I] [DecidableEq I] (h : P.Funds S T)

abbrev badge (i : I) := z' (S.ratio.parent (M.address i).1)
abbrev toned := ascent (M.badge z')

include h
lemma twilight_gauge (V : Config G c) : M.twilight k T (gauge z' V) = Density.skim (M.toned z') (M.twilight k T V) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  have hh := (carry_model (x:=x) (q:=Chi.canonical) (d:=0) (A:=A) (F:=F) (k:=k) z' V 1 h).2
  unfold twilight; rw [hh,submatrix_apply]
  change Density.skim (onPage _ _) _ (M.seat i,a) (M.seat j,b)=_
  rw [skim_read,toned,ascent,skim_read]; rfl

lemma ascend (i : I) (V : Config G c) (U : Config G f) (w : Prices G I) : M.deposited k T q d u (gauge z' V) (gauge (z' ∘ S.ratio.parent) U) (M.toned z' *ᵥ w) (M.seat i) =
    G.adjoint (M.badge z' i) (M.deposited k T q d u V U w (M.seat i)) := by
  unfold deposited toned; rw [(carry_model (A:=A) (x:=x) (F:=F) z' V U h).1,ascent_read, M.seat.injective.extend_apply,ascent_read,M.seat.injective.extend_apply,map_add,map_smul]; rfl

lemma received_gauge (V : Config G c) (U : Config G f) (w : Prices G I) :
    Agrees (inspected X) (M.received k T q d u (gauge z' V) (gauge (z' ∘ S.ratio.parent) U) (M.toned z' *ᵥ w)) (gauge (z' ∘ S.ratio.parent) (M.received k T q d u V U w)) := by
  intro i hi he; unfold received physical SectorChange.returned thaw Lattice.gauge
  by_cases H : i∈F.trunks
  · rw [show F.drape _ i=_ from F.on_tree _ ⟨i,H⟩,show F.drape _ i=_ from F.on_tree _ ⟨i,H⟩]
    dsimp only [Function.comp_apply]; rw [F.trunk_internal H]; simp
  let a : Active A x F := ⟨⟨i,H⟩,M.admits hi he⟩
  obtain ⟨j,hj⟩ := M.covers a hi he
  change F.drape _ a.val.val = _ * F.drape _ a.val.val * _
  rw [F.off_tree, F.off_tree,freeze_regular,freeze_regular]; unfold release
  rw [show M.deposited k T q d u _ _ _ a=G.adjoint _ (M.deposited k T q d u V U w a) from hj ▸ M.ascend z' h j V U w]
  change _ * replica S.ratio (gauge z' V) i = _
  rw [← copied S.ratio S.patch.odd_side]; unfold Lattice.gauge
  have hU (z : G.El) (v : G.Color) : G.lieExp (G.adjoint z v) = z*G.lieExp v*z⁻¹ := by
    apply G.mat_injective; rw [G.mat_lieExp,G.mat_adjoint,G.exp_conjugate,G.mat_mul,G.mat_mul, G.mat_lieExp]; rfl
  rw [hU, show M.badge z' j=(z' ∘ S.ratio.parent) i.1 by simp [badge,address,hj,a]]; change (_*_*_⁻¹)*(z' _ * _ * (z' _)⁻¹)=_; unfold Function.comp; group; rfl
end Museum
end YM.PhysicalNext.JointLoad.Heir
