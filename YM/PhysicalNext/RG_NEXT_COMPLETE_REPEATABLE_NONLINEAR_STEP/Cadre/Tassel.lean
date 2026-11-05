import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Embroidery
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Toll


/-! # Regular script for second unforced log. Keeps repeats. No Hessian subtraction yet!

Anchor on UNION site; pays factor exp surplus at endpoint, doesn't move
 each genealogy to fresh center. Keep honest clustered labels.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained Gas Ursell
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

def leaflet (H : Cash W s μ L Q o C T R) (χ : Chi) (V : Config G c) (p : H.ThinP) := likely fun i : Greenbelt.Reserve S=>
    fringe (prism T s χ o.K V (Greenbelt.allot i)) W o.a p.val R Q.table Q.halo
def stream (H : Cash W s μ L Q o C T R) (χ : Chi) (V : Config G c) (p : Clusters H.ThinP) := Gas.term H.seam (leaflet H χ V) p

namespace Captain
variable (N : Captain H j C' d v Y A b r B q k χ)
variable (p : Clusters H.ThinP)
open Greenbelt

lemma avgBrush {A : Type} [Fintype A] [Nonempty A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : A→ E→ℝ) (D : ℝ) (x : E) (he : ∀ i, Brush j D 1 (V i) x) :
    Brush j D 1 (fun v=> likely (fun i=> V i v)) x := by
  let a:ℝ:= (Fintype.card A:ℝ)⁻¹; have hz := (Brush.spree univ V (fun _=> D) (by norm_num) (fun i _=> he i)).smul a
  have ht : 0≤a := by unfold a; positivity
  simp only [Real.norm_of_nonneg ht, sum_const,nsmul_eq_mul,smul_eq_mul,card_univ] at hz
  rw [show a*((Fintype.card A:ℝ)*D)=D by simp [a]] at hz; exact hz

lemma arrived (p : H.ThinP) : Measurable (fun V=>leaflet H χ V p) ∧ LocalOn (H.smallAt p) (fun V=>leaflet H χ V p) ∧
    GaugeInvariant (fun V=>leaflet H χ V p) := by
  let X i := prism T s χ o.K 1 (Greenbelt.allot (S:=S) i); let f i V:=fringe (vary (X i) V) W o.a p.val R Q.table Q.halo
  have he i := Stained.seam (H:=H) (X:=X i) p.val rfl rfl
  change Measurable (fun V=> likely (fun i=> f i V)) ∧ LocalOn (H.smallAt p) (fun V=>likely (fun i=> f i V)) ∧ GaugeInvariant (fun V=> likely (fun i=> f i V))
  refine ⟨measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> (he i).1),fun U V h=>congr_arg likely (funext fun i=> (he i).2 U V h),
    fun z V=>?_⟩
  exact congr_arg likely (funext fun i=> frieze (X i) W o.a p.val R Q.table Q.halo z V)
lemma collective (p : H.ThinP) (V : Config G c) : H.entriesPool χ V p=masked (Pressure.temp s) (H.smallAt p) (fun V=>leaflet H χ V p) V ∧
    (Healthy (Pressure.temp s) (H.smallAt p) V → Ore V (fun U=> leaflet H χ U p) v (B*N.conduit.meant p.val k) j) := by
  letI : Nonempty (Tree.Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  let X i := prism T s χ o.K 1 (Greenbelt.allot (S:=S) i); let f i V:=fringe (vary (X i) V) W o.a p.val R Q.table Q.halo
  have he i := N.sextant (X:=X i) p.val rfl rfl rfl p.2.2 V
  let P:= Healthy (Pressure.temp s) (H.smallAt p) V
  let g i:=H.entries (vary (X i) V) p
  change likely g=_ ∧ _
  by_cases hp : P
  · refine ⟨Eq.trans ?_ (masked_eq _ _ _ _ hp).symm,fun _ T A C t U x ht hv=>?_⟩
    · exact congr_arg likely (funext fun i=> (he i|>.1).trans (masked_eq _ _ _ _ hp))
    change Brush _ _ _ (fun y=> likely (fun i=> f i (U y))) _
    apply avgBrush; intro i; exact (he i|>.2 hp) T U x ht hv
  have hv i : g i=0:= (he i|>.1).trans (masked_ne _ _ _ _ hp)
  exact ⟨(Eq.trans (congr_arg likely (funext hv)) (likely_constant (A:=Greenbelt.Reserve S) 0)).trans (masked_ne _ _ _ _ hp).symm, fun he=> (hp he).elim⟩
include N
lemma permitAverage :
    let Z:= unionOf H.smallAt p.snd
    let L V:= stream H χ V p
    LocalOn Z L ∧ Measurable L ∧ GaugeInvariant L ∧ (fun V=> H.trainedPool χ V p)=masked (Pressure.temp s) Z L ∧
      ∀ V,Healthy (Pressure.temp s) Z V → Ore V L v (N.design p) j := by
  intro Z L
  let f k V:= leaflet H χ V (p.snd k)
  let Y' i:= H.smallAt (p.snd i)
  have hx i:= N.collective (p.2 i); have he i:= arrived (H:=H) (χ:=χ) (p.2 i)
  let e := coefficient H.seam p.2
  let a:ℝ := e /(p.1+1).factorial
  have hv V : L V= a • ∏ i,f i V := by unfold L a stream Gas.term f e; simp [smul_eq_mul]; ring
  have hg i : Y' i ⊆ Z:= subset_biUnion_of_mem (H.smallAt ∘ p.2) (mem_univ _)
  let t:= Pressure.temp s; let g V:= H.trainedPool χ V p
  have hT V : g V=a*∏ i,masked t (Y' i) (f i) V := by
    unfold g Cash.trainedPool Gas.term; simp_rw [(fun i=> show H.entriesPool χ V (p.2 i)=_ from ((hx i) V).1)]
    unfold a e f t Y' Cash.smallAt; ring
  refine ⟨fun U V hu=>?_,?_,fun z V=> ?_,funext fun V=> ?_,fun V h E _ _ _ U x hz hu=> ?_⟩
  · rw [hv,hv]; exact congr_arg _ (prod_congr rfl fun i _=> (he i).2.1 U V (agrees_mono hu (Finset.coe_subset.mpr (hg i))))
  · rw [show L=_ from funext hv]; exact measurable_const.mul (Finset.measurable_fun_prod _ fun i _=> (he i).1)
  · rw [hv,hv]; exact congr_arg _ (prod_congr rfl fun i _=> (he i).2.2 z V)
  · by_cases hh : Healthy t Z V
    · rw [show H.trainedPool _ V p=g V from rfl,hT]; simp_rw [show Pressure.temp s=t from rfl]
      rw [RG.masked_eq _ _ _ _ hh,hv]; exact congr_arg _ (prod_congr rfl (fun i _=>RG.masked_eq _ _ _ _ (Finset.disjoint_of_subset_left (hg i) hh)))
    rw [show H.trainedPool _ V p=g V from rfl,hT,RG.masked_ne _ _ _ _ hh]; obtain ⟨x,hr,hF⟩:= Finset.not_disjoint_iff.mp hh
    obtain ⟨i,hP,hi⟩:= Finset.mem_biUnion.mp hr; rw [Finset.prod_eq_zero hP (RG.masked_ne _ _ _ _ (Finset.not_disjoint_iff.mpr ⟨x,(show x∈ Y' i from hi),hF⟩)),mul_zero]
  let g i:= B*N.conduit.meant (p.snd i).val k
  have hh := Brush.all_prod univ (fun i t=> f i (U t)) g (fun _=>1) (fun i _=> ((hx i V).2 (Finset.disjoint_of_subset_left (hg i) h)) E U x hz hu)
  simp_rw [Function.comp_def,hv]; apply (hh.trim.smul a).climb _ le_rfl
  simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin,mul_one]
  unfold design clusters stone; change ‖a‖*((∏ i,g i)*(1+((p.fst+1:ℕ):ℝ))^j) ≤ |e| *(∏ i,2^j*g i)/_
  conv_rhs => rw [prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_option,Fintype.card_fin]
  have he : (1+((p.fst+1:ℕ):ℝ))^j ≤ (2^j : ℝ)^(p.fst+1) := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]; gcongr; rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=p.fst+1)
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (show 0≤∏ i,g i from Finset.prod_nonneg
    fun i _=> mul_nonneg N.balance (N.conduit.meant_nonneg k _))) (norm_nonneg a)).trans_eq
  unfold a; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (by positivity : 0 ≤ ((p.1+1).factorial:ℝ))]; ring

lemma gloryBudget (U : BudgetPoint) (hu : U.threshold=Pressure.temp s) (hf : U.order≤j) :
    let Z:= reachability (H:=H) p
    let L V:= stream H χ V p
    (fun V=> H.trainedPool χ V p)=masked U.threshold Z L ∧ U.Regular Z L ∧
      ∀ m, U.power ≤ m → ∀ x∈Z,U.supBounds x Z L (markΦ N p m) := by
  intro Z L; obtain ⟨hx,hY,hF,hz,h⟩:= N.permitAverage p
  have hL V (hh : Healthy U.threshold Z V) : Ore V L v (N.design p) j:= h V (hu ▸ hh)
  have hh (V) (ht : Healthy U.threshold Z V) : ContDiffAt ℝ (↑U.order) (L ∘ increment V) 0 := (charted (hL V ht) N.position).of_le (Nat.cast_le.mpr hf)
  have ha : Sailor G U.threshold q j := ⟨fun c _ hb => N.weigh.stroke c _ (hb.trans (hu.trans_le N.talent))⟩
  refine ⟨(by rw [hu]; exact hz),⟨hx,hY,hF,hh,fun V hV A l hl=> left_has A hl (hh V hV)⟩,fun m hm x hv=>?_⟩
  let D := radiusB s; let b:ℝ := coverNumber D Z; let Y':= shiftG s*(1+b)
  have ht : 0≤ b := Nat.cast_nonneg _
  have hi : 1≤Y' := one_le_mul_of_one_le_of_one_le (by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB s)]) (le_add_of_nonneg_right ht)
  refine ⟨mul_nonneg (pow_nonneg (zero_le_one.trans hi) _) (pvc N p),fun V hV l hl hq=>?_⟩
  apply (costsD (g:=L) hx ha N.income x _ N.near (hL V hV) (Y:=Y') ?_ hi l (hl.trans hf) hq).trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hi (Nat.mul_le_mul_right j hm)) (pvc N p)))
  intro y hy; have hf : (separation y x:ℝ) ≤ b*(4*(D:ℝ)+2)+2*(D:ℝ) := by unfold b; exact_mod_cast Corona.extent Z D hy hv
  unfold Y' shiftG; change _≤ 4*(2*(D:ℝ)+1)*(1+b); nlinarith [Nat.cast_nonneg (α:=ℝ) D]
end Captain
end YM.ConnectedActivityE6.Blaze.March
