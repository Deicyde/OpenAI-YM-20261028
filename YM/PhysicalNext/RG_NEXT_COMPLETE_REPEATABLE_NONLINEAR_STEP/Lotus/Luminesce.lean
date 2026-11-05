import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Tonic
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
namespace Leaf
variable (M : Leaf R) (X : Coat T F) (k:Finset ℕ)
variable (X' : Coat T F) {p : Molecule S} {l' k' : Finset ℕ} {Z : Support c} {u v : Air f G}
lemma concur (A:Borough X X' Z u v k k' R)(he: Room P S T X.x) (hl:500≤m) (hp: ground R T m X.B p⊆ Z)
    (hT : Intake P T X.x R) : M.premium X W a Ñ k m u p=M.premium X' W a Ñ k' m v p:=by
  unfold premium; split
  next ha=>
    have hv : areas R T m X.B (M.turn.badge S)⊆ Z := (subset_biUnion_of_mem _ ha).trans hp
    have hZ : Footprint.enlargement S.ratio m X.B (RG.inspected M.crest)⊆ Z:= by rw [M.turn.badge_area] at hv; exact hv
    have hx : M.ingredient (X.input _)=M.ingredient (X'.input _) := M.specific _ _ (A.inherits he (l:=m) (by omega) _ hZ)
    have hh : ∀ i∈ areas R T 0 X.B (M.turn.badge S),Cleanroom Z (30*X.B) i:=by
      intro i hi j hj; rw [M.turn.badge_area] at hi; obtain ⟨x,h,p⟩:= halo_spec.mp hi
      apply hZ; refine halo_spec.mpr ⟨x,h,(separation_triangle x i j).trans ?_⟩; rw [zero_mul] at p
      exact le_trans (add_le_add p hj) ((zero_add _).trans_le (Nat.mul_le_mul_right X.B (by omega)))
    unfold paidU fond; rw [← A.B, A.enforces he _ hh, hx]; exact congr_arg (_ * ·) (Finset.prod_congr rfl (fun i hi=> A.complete he hl i ((show areas R T m X.B i⊆ _ from subset_biUnion_of_mem _ (mem_of_mem_erase hi)).trans hp) hT _ _ _))
  rfl
variable (H:Cash W X.x μ L Q o C T R)(hk:X.width=o.K)(ht:X.manifest)
include H hk
lemma coni (ht:X.manifest) (hq:X'.manifest)(hv:Village X X' (H.unionP p)) (hg :∀ i: Site f,S.ratio.parent i∈ H.unionP p → (i∈Contract.covered R k ↔ i∈Contract.covered R k')):
    M.tithe X k W o.a Q.table Q.halo p=M.tithe X' k' W o.a Q.table Q.halo p:=by
  have hh:X'.x=X.x:=hv.weather.symm
  -- H tip via explicit compatibility
  unfold tithe; rw [integral_prod _ (M.tip X k H hk ht p|>.2.1),integral_prod _ (M.tip X' k' (show Cash W X'.x μ L Q o C T R from hh.symm ▸ H) (hv.width ▸ hk) hq p|>.2.1)]
  apply integral_congr_ae; filter_upwards with y; let I:=podium S G (H.unionP p) X.B
  have hpX: X.relating.PosDef := (H.laws.data.localP F X rfl hk ht).sails.fullC
  have hp: X'.relating.PosDef:= (H.laws.data.localP F X' hh (hv.width ▸ hk) hq).sails.fullC
  have hb:circuit I X.relating=circuit I X'.relating:=by ext i j; exact hv.same_cov H.laws.data.room j.val j.2 i.val
  have hM : MeasurePreserving (swim I) X'.dice (arch I X.relating) := by rw [arch,hb]; exact orbit hp.posSemidef I
  let f (u:Air f G) := M.into X W o.a Q.table k Q.halo p (y,u)
  let f' (u:Air _ G) := M.into X' W o.a Q.table k' Q.halo p (y,u)
  have ht':Measurable f:= (M.tip X k H hk ht p|>.1.meas).comp (measurable_const.prodMk measurable_id)
  have hg':Measurable f':= (M.tip X' k' (show Cash W X'.x μ L Q o C T R from hh.symm ▸ H) (hv.width ▸ hk) hq p|>.1.meas).comp (measurable_const.prodMk measurable_id)
  have hc(u v)(hx: swim I u=swim I v): f u=f' v:= M.concur (X.wrapY y) k (X'.wrapY y) ⟨hv.wrap y y (fun _ _=>rfl),(observe I).mp hx,hg⟩ H.laws.data.room Q.buys (Finset.Subset.refl _) H.laws.intake
  rw [Pond.gathered (spill I) (spill_m I) (show MeasurePreserving (swim I) X.dice (arch I X.relating) from orbit hpX.posSemidef I) (settled I) (f:=f) (fun u v h=> (hc u v h).trans (hc v v rfl).symm) ht', Pond.gathered (spill I) (spill_m I) hM (settled I) (f:=f') (fun u v h=> (hc u u rfl).symm.trans (hc u v h)) hg']
  exact integral_congr_ae (Eventually.of_forall fun z=>hc _ _ rfl)
end Leaf
end YM.PhysicalNext.Repeat.Lotus
