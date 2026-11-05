import YM.WilsonBulk.Broadcast.GalleryRain

/-!
# Implement noise joint and Haar kernels, supply Tac attributes
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Audience Exterior Wilson
open Work.F08 RG Sheet Pert.Bulk Atelier
variable {c f L : Side} {G : Gauge} {P : Patch} {S : StepData c f} {K : KernelChoices}
attribute [local instance] Gauge.frobInner

lemma rung_price (he : S.patch.Branches S.kernel G) (i : Site c) (j : Axis) (t : S.Choices) :
    ∀ᶠ x : ReadingV G c f in 𝓝 0, S.prediction (signal G f (upper _ _ x)) t (i,j)=looming j (tackle S G i x) := by
  let T:= tackle S G i; let U:=signal G f ∘ upper (Pennant G f) (Pennant G c); let Y (z) := expandAt (S.ratio.embed i) (U z); let Z:=rainU S.patch G ∘ T
  have hU : Army U 0 := signal_force (upper (Pennant G f) (Pennant G c)).contDiff.contDiffAt
  have heq : U 0=1:= by unfold U; rw [Function.comp_apply,map_zero,signal_zero]
  have hY : Y 0=1:= by ext1 x; simp only [Y,expandAt,heq, Pi.one_apply]
  have hZ : Z 0=1:= by unfold Z; rw [Function.comp_apply,map_zero,rain_birth]
  have hv : Army Z 0:= (show Army (rainU S.patch G) (T 0) from T.map_zero.symm ▸ rain_Ω).comp (w:=T) T.contDiff.contDiffAt
  filter_upwards [centered_wire S t he hU heq i j,centered_wire S t he hU heq (i+step j) j, plaza_agree (U:=Y) he (fun k=> hU _) hY hv hZ (Eventually.of_forall fun x u hu j=> (rung_match i u j x hu).symm)] with x ⟨hp,hp'⟩ ⟨hc,hC⟩ ⟨ht,hg⟩
  rw [hp,hc,← house_moves] at hp'; change (entryCap S.patch (Y x))⁻¹*_ *entryCap S.patch (hall _ (Y x) _) = _ at hp'
  calc _ = entryCap S.patch (Y x)*victoryBox S.patch (Y x) j*(entryCap S.patch (hall S.patch (Y x) j))⁻¹ := by rw [← hp']; unfold U; dsimp only [Function.comp_apply]; group
       _ = _ := by
          rw [(hg j).1]; unfold looming entryCap entryHat; rw [ht,(hg j).2]; rfl -- sum occurrence

lemma patchiness (he : S.patch.Branches S.kernel G) (t : S.Choices) : canonWeight G S t=ᶠ[𝓝 0] plantSector (stake S.patch G) (splatter S.patch G S.kernel.penalty) c ∘ rung S G := by
  filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>rung_price he i j t))] with x hx
  unfold canonWeight plantSector; simp only [noiseTaylor,Function.comp_apply,Fintype.sum_prod_type,hx,Finset.sum_apply,Finset.mul_sum, splatter]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by rw [show rainV S.patch G (socket (ladder (stake S.patch G) i) (rung S G x)) _= _ from rung_rain i j x]; rfl

abbrev noisePart (P : Patch) (K : KernelChoices) (G : Gauge) := later (chapters 2 (stake P G) (splatter P G K.penalty))
abbrev parade (G : Gauge) (g : Ratio c f) := promenade (Cloth G) (Cloth G) g
lemma jury_noise (he : S.patch.Branches S.kernel G) (t : S.Choices) : jury (parade G S.ratio).symm (volumeTape (issue c (noisePart S.patch S.kernel G)))=advanceP _ (gossip G S t) := by
  erw [later_decal (stake S.patch G) _ c (splattered he _), jury_advance,jury_zoom,jury_zoom]
  have hp : ContDiffAt ℝ ω (plantSector (stake S.patch G) (splatter S.patch G S.kernel.penalty) c) 0:= cont_diff_sum _ _ (fun i _=> let T:=socket (ladder (stake S.patch G) i); (show ContDiffAt ℝ ω _ (T 0) from T.map_zero.symm ▸ splattered he _).comp _ T.contDiff.contDiffAt)
  unfold gossip; rw [ink_of (patchiness he t)]; congr 3 -- ?
  exact (ink_rename (parade G S.ratio).symm _ hp).symm

-- plant Haar
variable {J : ChartRatio G}
def swipe (G : Gauge) (i : Cloth G) : Market (Cloth G) := (0,i)
def tariffJ (J : ChartRatio G) (x : Tabletop (Cloth G)) := ∑ i:Axis,Real.log (J.J (priceScreen (fun k=>(coord i,k)) x))
abbrev curtainHair (J : ChartRatio G) := later (chapters 0 (swipe G) (tariffJ J))
lemma hair_jet (hj : LocalRatio J) : ContDiffAt ℝ ω (tariffJ J) 0 := by
  unfold tariffJ; refine ContDiffAt.sum fun i _=>?_ ; let V:= priceScreen (fun j:G.ColorIndex=>(coord i,j))
  exact ((show ContDiffAt ℝ ω J.J (V 0) by rw [map_zero]; exact hj.germ _ (Metric.mem_ball_self hj.patch)).comp 0 V.contDiff.contDiffAt).log (by rw [Function.comp_apply,map_zero,hj.anchored]; exact one_ne_zero)
lemma veil_bill (n : Side) (J : ChartRatio G) : realCost n J=plantSector (swipe G) (tariffJ J) n := by
  ext1 x; simp only [realCost,plantSector,Finset.sum_apply,Function.comp_apply,tariffJ,Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _=> ?_; congr 2; ext j; rw [traces_at]
  change x _= x (rolls z _ (wrap n 0,(coord i,j))); simp only [rolls_apply, map_zero,zero_add]; rfl
lemma veil_cash (c f : Side) (hj : LocalRatio J) : mountain (Pennant G f) (Pennant G c) (volumeTape (issue f (curtainHair J)))=haarTape c f J := by
  let u:= upper (Pennant G f) (Pennant G c)
  rw [chapters_simple _ _ f (hair_jet hj), ← veil_bill, advance_empty _ (ink_root (cost_zero hj))]
  rw [mountain,← upper_code]; exact (ink_comp (F:=u) (cost_jet hj) u.contDiff.contDiffAt u.map_zero).symm
end YM.WilsonBulk.Parapet
