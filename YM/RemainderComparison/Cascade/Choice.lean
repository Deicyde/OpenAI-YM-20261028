import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Pane
import YM.MergeProof.TeamLocal
import YM.RemainderComparison.Cascade.Tone
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Team
variable (M : Team R) (X : Coat T F) (k:Finset ℕ)
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation
open Packets Art Silica Poll Pond
variable {X':Coat T F} {H: Support c} {I : Finset (Tubular f G)} {Z : Support c} {k k' : Finset ℕ} {l : ℕ}
    {u v : Air f G} (p:Molecule S)
def grove (W a:ℝ) (Ñ:ChartRatio G)(l:ℕ):= if Ac.Spark (areas R T l X.B) p∧ troupe T R l X.B p then likely (fun i=> M.cinema ((preps X (roster p)).taggedL i) p W a Ñ l (podium S G (ground R T l X.B p) X.B)) else 0
def picture (W a:ℝ) (Ñ:ChartRatio G) (l:ℕ):=∫ z,M.grove (X.rinse z) p W a Ñ l ∂(MeasureTheory.Measure.pi fun _:Site c=>G.probHaar)
variable (ht:Intake P T X.x R) (hs:Room P S T X.x) (hp:ShellAccess S G X.x W X.width C) (hN:LocalRatio Ñ) (hl:500≤l)
include ht
include hp hN in
lemma groveB : Measurable fun y=> M.grove (vary X y) p W a Ñ l:=by
  classical
  let Z(v):= vary X v; let H:= ground R T l X.B p
  change Measurable fun y=> if Ac.Spark (areas R T l X.B) p∧ troupe T R l X.B p then likely (fun i => M.cinema ((preps (Z y) (roster p)).taggedL i) p W a Ñ l (podium S G H X.B)) else 0
  split_ifs
  · refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _=>?_)
    let Y:=(preps X (roster p)).taggedL i
    exact M.page Y p ht hp hN
  exact measurable_const
include hs hl in
lemma groveL : LocalOn (ground R T l X.B p) (fun V:Config G c=> M.grove (vary X V) p W a Ñ l):=by
  intro V U hu; let s:=ground R T l X.B p; unfold grove
  change (if Ac.Spark (areas R T l X.B) p∧ troupe T R l X.B p then likely _ else (0:ℝ))= (if Ac.Spark (areas R T l X.B) p∧ troupe T R l X.B p then likely _ else (0:ℝ)); split
  next he=>
    apply congr_arg likely; funext k
    exact M.synchronizeLK ((preps (vary X V) (roster p)).taggedL k) p ht (hp:=Finset.Subset.refl _) hs (show Village _ ((preps (vary X U) (roster p)).taggedL k) s from ⟨rfl,rfl,rfl,fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,hu⟩) hl
  next => rfl
include hp hN hs hl in
lemma tailSpin : Measurable (fun V=> M.picture (vary X V) p W a Ñ l) ∧ LocalOn (ground R T l X.B p) (fun V=> M.picture (vary X V) p W a Ñ l)∧ GaugeInvariant (fun V=> M.picture (vary X V) p W a Ñ l):=by
  let Y:=MeasureTheory.Measure.pi fun _:Site c=>G.probHaar
  have hf : Measurable (fun a : Config G c × (Site c → G.El)=> gauge a.2 a.1):=by unfold Lattice.gauge; fun_prop
  refine ⟨(((M.groveB (a:=a) (l:=l) X p ht hp hN).comp hf).stronglyMeasurable.integral_prod_right' (ν:=Y)).measurable,?_,?_⟩
  · intro V U hu; unfold picture; apply integral_congr_ae; filter_upwards with z
    exact M.groveL X p ht hs hl (gauge z V) (gauge z U) (fun i hi hj=>by unfold Lattice.gauge; rw [hu i hi hj])
  intro z V
  let f:= MeasurableEquiv.piCongrRight (fun i=> MeasurableEquiv.mulRight (z i))
  have hp : MeasurePreserving f Y Y := measurePreserving_pi _ _ (fun i : Site c=> measurePreserving_mul_right G.probHaar (z i))
  unfold picture; dsimp only; rw [← hp.integral_comp' (fun z=>M.grove ((vary X V).rinse z) p W a Ñ l)]
  apply integral_congr_ae; filter_upwards with u; have ht : gauge u (gauge z V) = gauge (f u) V := by
    funext i; unfold Lattice.gauge; change _= (u _*z _)* V _* (u _*z _)⁻¹; group
  unfold vary rinse; simp_rw [ht]
omit ht
-- no changed appointment.C for anal bank
variable (H : Cash W x μ L Q o C T R) {v d b C' B A r: ℝ} {j k : ℕ}{χ:Chi}{Ξ:Utopia H j v d r C' χ} (hΘ:Oboe H j v B k A b Ξ)
    (hX:X.x=x) (hv:X.width=o.K) (he:X.χ=χ) (h:(roster p).flags=∅) (hy:Healthy (Pressure.temp x) (H.unionP p) X.V)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V : E→Config G c} {y:E}
include hX hy h
lemma casin (q: S.Choices)(U V:Config G c)(hq:Agrees (H.unionP p) U V):
    let I:=podium S G (H.unionP p) (radiusB x)
    M.cinema (vary ((planted X p).taggedL q) U) p W a Ñ Q.halo I=M.cinema ((preps (vary X V) (roster p)).taggedL q) p W a Ñ Q.halo I:=by
  intro I; let A:=vary ((planted X p).taggedL q) U; let A':=(preps (vary X V) (roster p)).taggedL q
  have hv : Village A A' (H.unionP p):=by
    refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,hq⟩
    intro i hi; have he : i∉RG.flags (Pressure.temp X.x) X.V:=by rw [hX]; exact Finset.disjoint_left.mp hy hi
    unfold A A' vary taggedL planted preps place; simp [h,he]
  unfold I; rw [← show A.B=radiusB x from congr_arg radiusB hX]; apply M.synchronizeLK A p (show Intake P T A.x R from hX.symm ▸ H.laws.intake) (l:=Q.halo) _ (show Room P S T A.x from hX.symm ▸ H.laws.data.room) hv Q.buys
  change ground R T Q.halo (radiusB X.x) p⊆ _; rw [hX]; exact Subset.refl _
include hv
omit hy in
lemma pictured : M.bloom X W o.a Q.table Q.halo p=masked (Pressure.temp x) (H.unionP p) (fun V=> M.grove (vary X V) p W o.a Q.table Q.halo) X.V:=by
  let V:= H.unionP p; have ht:ground R T Q.halo X.B p=V:=by unfold Coat.B; rw [hX]; rfl
  have hB : X.B=radiusB x:=congr_arg radiusB hX
  by_cases hh: Healthy (Pressure.temp x) V X.V
  · rw [masked_eq _ _ _ _ hh,bloom]; unfold grove; simp_rw [show vary X X.V=X from rfl]
    split
    next hy=>
      rw [if_pos ⟨hy.1,hy.2.1⟩,ht,hB] -- X.B
      apply congr_arg likely; funext k; let K:= (planted X p).taggedL k
      let I:=podium S G V (radiusB x)
      have hf : M.cinema K p W o.a Q.table Q.halo I=M.tithe K (Matter.own p) W o.a Q.table Q.halo p:=by
        have H':Cash W K.x μ L Q o C T R:= hX.symm ▸ H -- careful simp.R
        unfold I; rw [← hB]; apply M.selfish K p H' hv (planted_valid X p) V
        · change Healthy (Pressure.temp X.x) (ground R T Q.halo X.B p) X.V; rw [ht,hX]; exact hh
        exact ht.le
      exact hf.symm.trans (M.casin X p H hX h hh k X.V X.V (fun _ _ _=>rfl))
    next hy=>
      rw [if_neg]; rintro ⟨h₁,h₂⟩; apply hy
      have hf : RG.flags (Pressure.temp X.x) X.V ∩ ground R T Q.halo X.B p=(roster p).flags:=by rw [ht,hX,h]; exact Finset.disjoint_iff_inter_eq_empty.mp (show Disjoint _ _ from hh.symm)
      exact ⟨h₁,h₂,hf⟩
  rw [masked_ne _ _ _ _ hh,bloom,if_neg]
  intro hp; apply hh
  unfold Healthy; rw [← hX,← ht]
  apply Disjoint.symm; exact Finset.disjoint_iff_inter_eq_empty.mpr (hp.2.2.trans h)
include he hΘ
lemma gathers (hq:Mode V y j v) (hx: V y=X.V) : ∀ᶠ z in 𝓝 y, ∀ M:Team R, M.picture (vary X (V z)) p W o.a Q.table Q.halo=M.grove (vary X (V z)) p W o.a Q.table Q.halo:=by
  let K:=planted X p; let Y q z:=vary (K.taggedL q) (V z); let Z(t:E):= vary X (V t)
  have hf q: ∀ᶠ t in 𝓝 y,Stained.Hue (Y q t):=Stained.eventual_hue (hΘ.flow F (K.taggedL q) hX he hv (planted_valid X p) E V y hx hq)
    (H.laws.data.localP F (K.taggedL q) hX hv (planted_valid X p)).sails
  filter_upwards [eventually_all.mpr hf] with y hh M
  let L (z:Coat T F):= M.grove z p W o.a Q.table Q.halo
  have hF z: L ((Z y).rinse z)=L (Z y):=by
    unfold L grove; rw [show ((Z y).rinse z).B=X.B from rfl,show (Z y).B=X.B from rfl,show X.B=radiusB x from congr_arg radiusB hX]
    split
    next hQ =>
      apply congr_arg likely; funext q; let I:=podium S G (H.unionP p) (radiusB x); let b X:= M.cinema (F:=F) (T:=T) X p W o.a Q.table Q.halo I
      have hpz : b ((preps (vary X (gauge z (V y))) (roster p)).taggedL q)=b ((Y q y).rinse z) := (M.casin X p H hX h hy q _ _ (show Agrees _ (gauge z (V y)) (gauge z (V y)) from fun i _ _=> rfl)).symm
      have hpc : b (Y q y)= b ((preps (vary X (V y)) (roster p)).taggedL q):= M.casin X p H hX h hy q _ _ (show Agrees _ (V y) (V y) from fun i _ _=> rfl)
      change b _=b _; refine hpz.trans ((?_ : b ((Y q y).rinse z)=b (Y q y)).trans hpc); have ht:=H.laws.data; unfold b I; rw [← chargedU];
      apply M.coastal (Y q y) p (show Intake P T (Y q y).x R from hX.symm ▸ H.laws.intake) (show ShellAccess S G (Y q y).x W (Y q y).width o.γ from (by change ShellAccess S G X.x W X.width o.γ; rw [hX,hv]; exact H.laws.data.access)) _ z Q.table_exists _ _ (hh q)
      · apply mul_pos o.large; unfold Coat.t; change 0<Pressure.fiery G X.x _; rw [hX]; exact H.laws.data.room.fiery
      unfold Coat.t; change 4*_ *Pressure.fiery G X.x _ < _; rw [hX,ht.funds.length_eq]; exact H.laws.data.covers
    next => rfl
  change (∫ z,L ((Z y).rinse z) ∂_)=L _; simp_rw [hF]; simp; rfl
lemma arc (hq:Mode V y j v) (hx: V y=X.V) : ∀ᶠ z in 𝓝 y, M.picture (vary X (V z)) p W o.a Q.table Q.halo=M.grove (vary X (V z)) p W o.a Q.table Q.halo:=(Team.gathers X p H hΘ hX hv he h hy hq hx).mono fun _ hi=> hi M
end Team
end YM.PhysicalNext.Repeat.Lotus
