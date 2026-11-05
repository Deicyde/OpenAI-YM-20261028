import YM.RG08.Vale.Shovel
/-!
# Costed ordinary section legs; analytic probes at full stencils
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Tall
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{p m c: Side}{R:ℝ}{D d e j r n i k t:ℕ} {τ:ℕ}
variable (Z : Finset Cover){F: Labels.Frame G d} {T : SectionData F} {V : BoardU D R G}
private abbrev chair (G:Gauge)(Z:Finset Cover) := Spot Z × G.ColorIndex
private def way (v:chair G Z) : Fare G := ((Place.first v.1).val,coord (Place.beam v.1),v.2)
private def maplegs (v:Fin r→ chair G Z) := way Z∘ v
private def read_at (i : chair G Z) : Place.Dev Z G:=Pi.single i.1 (WithLp.toLp 2 (Pi.single i.2 1))
lemma salonEq (z:Link G m)(x:Site m): ∀ y : Spot Z,
    (∑ i: chair G Z, z (x+wrap m (way Z i).1,(way Z i).2) • read_at Z i) y=arm G m 1 z (wrap m (Place.first y).val+x,coord (Place.beam y)) := by
  intro y; rw [Fintype.sum_prod_type,Finset.sum_apply,sum_eq_single y]; swap
  · intro b _ hb; rw [Finset.sum_apply]; apply sum_eq_zero; intro i _; unfold read_at; simp [Ne.symm hb]
  swap; · simp
  rw [Finset.sum_apply]; ext k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,read_at,Pi.smul_apply,Pi.single_eq_same, PiLp.smul_apply,WithLp.ofLp_toLp,Pi.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,sum_ite_eq,mem_univ,if_true]
  rw [arm_apply,add_comm (wrap m _)]; rfl
-- restriction actual period links read
def salon (G:Gauge)(i:Site m) : Link G m→L[ℝ] Place.Dev Z G:=
  (ContinuousLinearMap.pi fun p:Spot Z=>ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>G.Color) (wrap m (Place.first p).val+i, coord (Place.beam p))).comp (arm G m 1).toContinuousLinearMap
lemma salon_pa (i:Site m)(x:Link G m): salon Z G i x= ∑ j:chair G Z,x (i+wrap m (way Z j).1,(way Z j).2) • read_at Z j := Eq.symm (funext (salonEq Z x i))
lemma slants (T:SectionData F)(v:F.Coeff)(p:Site m) (x : Link G m): (T.places v p) (input G m x)=slant T v (salon T.stencil G p x) := by
  apply T.cylinder_local; intro i h1 h2; let v:Place.Spot T.stencil:=⟨(⟨i.1,h1⟩,i.2),h2⟩
  have hp := Place.pore_site (salon T.stencil G p x) v
  exact (encode_link x _ _).trans hp.symm
private def drive (H : Tensor.T (Place.Dev Z G) ℝ r) (b:Fin r→chair G Z) := H (read_at Z ∘ b)
-- sym for canonical stencil

def stock (H : Tensor.T (Place.Dev Z G) ℝ r) : Shale (Loc G 1) r := sew (pool (drive Z H) (maplegs Z))
lemma stock_tidied (H : Tensor.T (Place.Dev Z G) ℝ r) : Tidy (stock Z H) := Tidy.sewn (pens_for.mpr (Summable.of_finite.hasSum.tsum_fiberwise _).summable)
lemma stock_paid (H : Tensor.T (Place.Dev Z G) ℝ r)(w:ℝ) (h:0≤w): ∃ A,Lit (stock Z H) w A := by
  let a:= drive Z H; let m:=maplegs Z (G:=G) (r:=r)
  let f i:= ling w (m i)*‖a i‖
  have he : Quire.Ink (ling w ∘ m) a (∑' i,f i):= ⟨fun i=>mul_nonneg (ling_pos w _).le (norm_nonneg _),Summable.of_finite,le_rfl⟩
  exact ⟨_,stitching (he.pour m (ling_one h))⟩
lemma stocks (H : Tensor.T (Place.Dev Z G) ℝ r)(p:Site m) (x: Link G m) : rootSong (stock Z H) m p x=Tensor.diagonal H (salon Z G p x) := by
  let G':= drive Z H; let S : Summable G':=Summable.of_finite -- Prop, change let
  let M:= maplegs Z (G:=G) (r:=r)
  have he:Pens (pool G' M):=pens_for.mpr (S.hasSum.tsum_fiberwise _).summable
  unfold stock; rw [sew_diagonal he]; change stitch (tub G' M) m p (fun _=> x)= _
  rw [st_tub _ _ (pens_for.mpr S),tsum_fintype]; unfold Tensor.diagonal; rw [salon_pa]
  rw [H.map_sum (fun _ i=> x (p+wrap m (way Z i).1,(way Z i).2) • read_at Z i)]
  refine sum_congr rfl fun i _=>?_ ; rw [H.map_smul_univ _ (fun a=> read_at Z (i a)),smul_eq_mul]; exact mul_comm ..
@[simp] lemma stock_zero (G:Gauge) (r:ℕ): stock Z (0:Tensor.T (Place.Dev Z G) ℝ r)=0 := by
  apply (stock_tidied ..).uniquely (Tidy.zero ..); intro m; rw [root_zero]; exact funext fun v=> (stocks ..).trans rfl
lemma salon_scenery (Z: Finset Cover): ∀ᶠ i:ℕ in atTop,salon Z G (0:Site (boards i)) ∘ studio G d (boards i)=Film.localLane (S:=Z) := by
  filter_upwards [eventually_all.mpr (fun i:Spot Z=> Next.Free.eventually_unfold boards board_end (Place.first i).val)] with i hi
  funext a k; ext1 l
  let m:=boards i; let j: Link G m:= studio G d m a
  change arm G m 1 j (_,coord (Place.beam k)) l= _; rw [add_zero, arm_apply,← coord_map]; unfold j studio screenR heap; dsimp only [Function.comp_apply]; simp only [hi k, axisEquiv.symm_apply_apply]; rfl
lemma stock_lank (H : Tensor.T (Place.Dev Z G) ℝ r): Polished (stock Z H) := scarlet (stock_paid Z H 1 zero_le_one).choose_spec one_pos
-- read agrees with full multigraded pieces
set_option maxHeartbeats 400000 in
lemma stock_leads (H : Tensor.T (Place.Dev Z G) ℝ r): amount (stock Z H) d j=iteratedFDeriv ℝ j (Tensor.diagonal H ∘ Film.localLane) 0 := by
  ext1 x; symm; apply tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds (movie (stock_tidied ..) (stock_lank Z H) x)
  filter_upwards [salon_scenery Z (G:=G) (d:=d)] with i h
  let m:=boards i
  have he: rootSong (stock Z H) m 0=Tensor.diagonal H ∘ salon Z G (0:Site m):= funext fun i=> stocks ..
  rw [show rootSong (stock Z H) _ _ ∘ studio G d (boards i)= Tensor.diagonal H ∘Film.localLane from by rw [he,Function.comp_assoc,h]]
end YM.RG08.Vale
