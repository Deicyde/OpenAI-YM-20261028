import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymSeason
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Pitcher
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Garden
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels

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
open Horticulture
variable {F':Forest S.ratio}
variable (X' : Coat T F') {p : Molecule S} {l' k' : Finset ℕ} {Z : Support c} {u v : Air f G}
lemma lands (A:Clump X X' Z u v k k' R)(he: Room P S T X.x) (hl:500 ≤ m) (hp: ground R T m X.B p⊆ Z)
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
variable (s : Molecule S) (hK : X.width=o.K) (hK' : X'.width=o.K) (hy : X'.x=X.x) (hv : X.V=X'.V) (hc:X.χ=X'.χ) (H : Cash W X.x μ L Q o C T R) (hw : ∀ i:Site f,S.ratio.parent i∈ H.unionP s → F.up i=F'.up i)
include M hK hK' hv hc hy H hw
lemma paths (ho : X.seeds=X'.seeds) (hk : X.k=X'.k) (hm : X.manifest) (hm' : X'.manifest) (l : Finset ℕ) :
    M.tithe X l W o.a Q.table Q.halo s=M.tithe X' l W o.a Q.table Q.halo s := by
  have hM {F' : Forest S.ratio} (Z : Coat T F') (hx : Z.x=X.x)(ht: Z.width=o.K) : Measurable (M.into Z W o.a Q.table l Q.halo s) := M.crystall Z l (hx.symm ▸ H.laws.intake) (by rw [hx,ht]; exact H.laws.data.access) Q.table_exists ..
  unfold tithe; rw [integral_prod _ (M.tip X l H hK hm s|>.2.1),integral_prod _ (M.tip X' l (show Cash W X'.x μ L Q o C T R from hy.symm ▸ H) hK' hm' s|>.2.1)]
  rw [← Pond.reception (Horticulture.reserve (S:=S) G F) _ ((hM X rfl hK).stronglyMeasurable.integral_prod_right' (ν:=X.dice)).measurable,
    ← Pond.reception (Horticulture.reserve (S:=S) G F') _ ((hM X' hy hK').stronglyMeasurable.integral_prod_right' (ν:=X'.dice)).measurable]
  apply integral_congr_ae; filter_upwards with u
  let I:= podium S G (H.unionP s) X.B; let Xa:= X.wrapY (bridge (S:=S) F u); let Yf:=X'.wrapY (bridge (S:=S) F' u)
  have he: Crop Xa Yf (H.unionP s) := ⟨hy.symm,hK.trans hK'.symm,hc,fun _ _=> ho ▸ Iff.rfl, foreclose hw u,
    fun i _=> (congr_fun (congr_arg Prod.fst hk) i), fun i _=> (congr_fun (congr_arg Prod.snd hk) i), fun i _ _=> congr_fun hv i⟩
  have hp : Room P S T Xa.x := H.laws.data.room
  have ht := Pond.orbit (H.laws.data.localP F X rfl hK hm).sails.fullC.posSemidef I
  have ht' := Pond.orbit (H.laws.data.localP F' X' hy hK' hm').sails.fullC.posSemidef I
  let g (w:Air f G):=M.premium Xa W o.a Q.table l Q.halo w s
  let y (w:Air f G):=M.premium Yf W o.a Q.table l Q.halo w s
  have hJ (p q) (h : swim I p=swim I q) : g p=y q := by
    have hh : Clump Xa Yf (H.unionP s) p q l l R := ⟨he,(observe I).1 h,fun _ _=> Iff.rfl⟩
    exact M.lands Xa l Yf hh hp Q.buys (Finset.Subset.refl _) H.laws.intake
  change (∫ w,g w ∂X.dice)=∫ w,y w ∂X'.dice
  have hg : Measurable g := by
    change Measurable (fun z=> M.into X W o.a Q.table l Q.halo s (bridge (S:=S) F u,z))
    exact (hM X rfl hK).comp (measurable_const.prodMk measurable_id)
  have hm : Measurable y := by
    change Measurable (fun z=>M.into X' W o.a Q.table l Q.halo s (bridge (S:=S) F' u,z))
    exact (hM X' hy hK').comp (measurable_const.prodMk measurable_id)
  have hC : circuit I X.relating=circuit I X'.relating := by
    ext i j
    exact he.same_cov hp (j:Tubular f G) j.property (i:Tubular f G)
  have hY : MeasurePreserving (swim I) X'.dice (arch I X.relating) := by unfold arch; rw [hC]; exact ht'
  calc
    _ = ∫ i,g (spill I i) ∂arch I X.relating := gathered _ (spill_m I) (show MeasurePreserving (swim I) X.dice (arch I X.relating) from ht) (settled I)
          (fun p q h=> (hJ p q h).trans (hJ q q rfl).symm) hg
    _ = ∫ i,y (spill I i) ∂arch I X.relating := integral_congr_ae (ae_of_all _ fun i=> hJ _ _ (show swim I (spill I i)=_ from rfl))
    _ = _ := (Pond.gathered (spill I) (spill_m I) hY (settled I) (f:=y)
          (fun p q h=> (hJ p p rfl).symm.trans (hJ p q h)) hm).symm

-- average includes tree Gram inverses, no changing Φ
private lemma meanLK (he:X.seeds=X'.seeds) (hp:X.manifest)(ha:X'.manifest): M.steep X k W o.a Q.table Q.halo s=M.steep X' k W o.a Q.table Q.halo s:=by
  unfold steep; apply congr_arg likely; funext v
  exact M.paths (X.taggedL v) (X'.taggedL v) s hK hK' hy hv hc H hw he rfl hp ha k
private lemma meanPlant : M.steep (planted X s) (own s) W o.a Q.table Q.halo s=M.steep (planted X' s) (own s) W o.a Q.table Q.halo s:=by
  let a:=planted X s; let a':=planted X' s
  have he:a.seeds=a'.seeds:=by unfold a a' planted preps; dsimp only;rw [hv,hy]
  exact meanLK M a (own s) a' s hK hK' hy hv hc H hw he (planted_valid X _) (planted_valid X' _)
lemma sailV : M.bloom X W o.a Q.table Q.halo s=M.bloom X' W o.a Q.table Q.halo s:=by
  unfold bloom
  have he: standsIn X R Q.halo s↔ standsIn X' R Q.halo s:= by unfold standsIn claimed Coat.B; rw [hv,hy]
  exact if_congr he (meanPlant M X X' s hK hK' hy hv hc H hw) rfl
end Leaf
end YM.PhysicalNext.Repeat.Lotus
