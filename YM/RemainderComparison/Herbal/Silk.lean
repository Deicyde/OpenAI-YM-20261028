import YM.RemainderComparison.Herbal.Mead
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Herbal
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D W A v u d e t a c' B':ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type}
variable {T : Tube G S} {F : Forest S.ratio} {Θ : ChartRatio G} {k': S.Choices} (ρ:Bid.Dir G c→AxisChart G F) (B:BudgetPoint) (β:ℝ)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Yx"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
local notation "D'"=> wick G L d t
variable {x:Positions (Uniform.Primary c G)} {K:KernelChoices} {O:Teller G}
variable {X Y:Config G f→ℝ}
lemma merge (hp:Sect X t j k Z C)(hy:Sect Y t j k Z A): Sect (fun x=>X x+Y x) t j k Z (C+A):=by
   refine ⟨⟨fun E _ _ U h y hy'=> (hp.tall E U h y hy').gathering (hy.tall E U h y hy'), fun E _ _ U h=>?_⟩,
     fun i j=>congr_arg₂ (·+·) (hp.vigor i j) (hy.vigor i j),hp.localM.add hy.localM, fun U h=>?_⟩
   · obtain ⟨hX,h₁⟩:= hp.mode E U h; obtain ⟨hY,h₂⟩:=hy.mode E U h
     refine ⟨hX.add hY,fun i hi hy=>?_⟩
     change ‖iteratedFDeriv ℝ i ((X ∘ U) + (Y ∘ U)) 0‖ = 0 -- edit precedence
     rw [iteratedFDeriv_add_apply (hX.of_le (by exact_mod_cast hi)) (hY.of_le (by exact_mod_cast hi)), norm_eq_zero.mp (h₁ i hi hy), norm_eq_zero.mp (h₂ i hi hy),add_zero,norm_zero]
   rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (hp.value U h) (hy.value U h))
lemma grow (hp:Sect X t j k Z C) (a:ℝ) : Sect (fun x=>a*X x) t j k Z (‖a‖*C):=by
   refine ⟨⟨fun E _ _ U h y hy'=> (hp.tall E U h y hy').smul a, fun E _ _ U h=>?_⟩,
     fun i j=>congr_arg (a*·) (hp.vigor i j),measurable_const.mul hp.localM, fun U h=>?_⟩
   · obtain ⟨hX,h₁⟩:= hp.mode E U h
     refine ⟨hX.const_smul a,fun i hi hy=>?_⟩
     change ‖iteratedFDeriv ℝ i (a • (X ∘ U)) 0‖ = 0
     rw [iteratedFDeriv_const_smul_apply (hX.of_le (by exact_mod_cast hi)), norm_eq_zero.mp (h₁ i hi hy), smul_zero,norm_zero]
   rw [norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (hp.value U h) (norm_nonneg _)
lemma array (s:Finset ι)(X:ι→ Config G f→ℝ)(p:ι→ℝ)(hp:∀ i∈s,Sect (X i) t j k Z (p i)): Sect (fun x=>∑ i∈s,X i x) t j k Z (∑ i∈s,p i):=by
   induction s using Finset.induction_on with
   | empty=>
     simp only [Finset.sum_empty]; refine ⟨⟨fun E _ _ U h y hy'=>?_, fun E _ _ U h=>?_⟩,fun _ _=>rfl,measurable_const,fun U h=>by rw [norm_zero,zero_mul]⟩
     · exact (Brush.certified zero_le_one (0:ℝ)).climb (norm_zero.le) le_rfl
     exact ⟨contDiffAt_const,fun i hi hy'=> le_antisymm ((Brush.offer.mp ((Brush.certified (x:=0) (k:=k) zero_le_one (0:ℝ)|>.climb (norm_zero.le) le_rfl))).inside i hi) (norm_nonneg _)⟩
   | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact merge (hp _ (mem_insert_self ..)) (ih fun i hi=> hp _ (mem_insert_of_mem hi))
section kin
variable (R:PathData G)(p:Clip)(h:R.Bounds p σ C W) (s:Signed) (i: Face (Per f)) (U:Config G f)

def turn (i:Face (Per f))(U:Config G f):=let V:=pull s 0 U;p.direct*G.price (faceValue V i)+‖R.ell V i‖^2/2
lemma rill : 0≤ turn R p s i U:=by unfold turn; exact add_nonneg (mul_nonneg p.quadratic_pos.le (G.price_range _).1) (div_nonneg (sq_nonneg _) (by norm_num))
lemma still_turn : turn R p s i (1:Config G f)=0:=by
   have hp:pull s 0 (1:Config G f)=1:= by funext i; simp [pull,Lattice.Step.read]
   have hx (i:Face (Per f)):faceValue (1:Config G f) i=1:=by simp [faceValue,square,travel]
   have ht (j:Slot) (x:Site f): j.atSite (1:Config G f) x=0:=by rw [Work.F03.atSite_path,hx,G.curvature_unit,map_zero]
   unfold turn; simp [hp,hx,PathData.ell, PathData.ellTerms,ht]

include h
lemma worthwhile : 0≤ C:= (tsum_nonneg (h.rows (Classical.arbitrary _)).1).trans (h.rows _).2.2
lemma uponU (hv:flags B.threshold U=∅): ‖turn R p s i U‖≤(p.direct+C^2)*B.threshold^2:=by
   let V:= pull s 0 U; have hC:=worthwhile R p h -- edit
   have hp (i:Face (Per f)):= Pane.lucid B V (Pane.tranquility U hv s 0) i; have hg:G.price (faceValue V i)≤ B.threshold^2/2:= price_of_chord _ (hp i) -- edit
   let q k:=|(R.row i.2 k).1| * Real.exp (σ*(R.row i.2 k).2.length)
   have he j: ‖R.ellTerms i j V‖ ≤ q j*B.threshold:= by
      let L':= (R.row i.2 j).2; change ‖(R.row i.2 j).1 • L'.atSite V i.1‖ ≤ _; rw [norm_smul,Work.F03.atSite_path,G.norm_adjoint]
      apply mul_le_mul _ ((G.curvature_norm _).trans (hp _)) (norm_nonneg _) (h.rows i.2|>.1 _)
      exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (Nat.cast_nonneg _)))
   have hF : ‖R.ell V i‖≤C*B.threshold:= by
      have hc:= (h.rows i.2).2.1.mul_right B.threshold; have hv':= hc.of_nonneg_of_le (fun _=>norm_nonneg _) he
      refine (norm_tsum_le_tsum_norm hv').trans ((hv'.tsum_le_tsum he hc).trans ?_); rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right (h.rows i.2).2.2 B.threshold_pos.le
   rw [Real.norm_of_nonneg (rill ..)]; unfold turn
   simp only []; apply le_trans (add_le_add (mul_le_mul_of_nonneg_left hg p.quadratic_pos.le) (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hF _) (by norm_num)))
   have h:=p.quadratic_pos
   rw [mul_pow,add_mul]; gcongr <;> nlinarith only [sq_nonneg B.threshold, mul_nonneg h.le (sq_nonneg B.threshold),mul_nonneg (sq_nonneg C) (sq_nonneg B.threshold)] -- edit
omit h
def legPrice (G:Gauge)(k:ℕ)(Z σ:ℝ) := pathCentury k Z σ* |Work.F02.slotConst G| *‖Work.F02.colorReal G‖ where
    pathCentury k Z σ:= composeCost k ((1+2^k / Work.F02.radius σ)^k) Z
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E] {A':E→ Config G f}
-- A' shadows notation
lemma wages (hp:Uniform.Inputs A' k Z) (x:E)(hx:‖x‖<1) (hσ:0<σ)(b:Slot)(y:Site f) : Allows k (fun z=> b.atSite (pull s 0 (A' z)) y) x (legPrice G k Z σ*Real.exp (σ*b.length)) :=by
   let T z:= Work.F02.physical (pull s 0 (A' z)); have hh := (pulled hp s); have he:Allows k T x Z:=allows_ambient (U:=fun z=>pull s 0 (A' z)) fun i=>hh.2.2 i x hx.le
   have hS := allows_real_of_entire k (Work.F02.slotExt_contDiff b y) (x:=T x) (Work.F02.radius_pos hσ) (fun z hz=>
       (Work.F02.slotExt_bound (pull s 0 (A' x)) hσ z (ball_subset_closedBall hz) b y).trans (mul_le_mul_of_nonneg_right (le_abs_self (Work.F02.slotConst G)) (Real.exp_pos _).le))
   have hF z : Work.F02.colorReal G (Work.F02.slotExt b y (T z))= b.atSite (pull s 0 (A' z)) y:=by unfold T; rw [Work.F02.slotExt_physical,Work.F02.colorReal_up]
   simp_rw [← hF]; apply ((hS.comp he).linear (Work.F02.colorReal G) le_rfl).mono; unfold legPrice legPrice.pathCentury composeCost; apply le_of_eq; ring

include h
lemma honor (hp:Inputs A' k Z)(x:E)(hx:‖x‖<1):Brush k (C*legPrice G k Z σ) 1 (fun z=> R.ell (pull s 0 (A' z)) i) x:=by
   let v:= legPrice G k Z σ; have hv:0 ≤ v:=by have hz:=Work.F02.radius_pos h.width; have ht:=hp.2.1; unfold v legPrice legPrice.pathCentury composeCost; positivity
   let U i':=|(R.row i.2 i').1| * Real.exp (σ*(R.row i.2 i').2.length)
   let A'' (i':ℕ)(z:E):=R.ellTerms i i' (pull s 0 (A' z)); have he:= h.rows i.2
   have hz : SumBudget (fun i=> U i*v) (C*v):= ⟨fun i=>mul_nonneg (he.1 _) hv,he.2.1.mul_right _,by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right he.2.2 hv⟩
   refine dons (u:=A'') isOpen_ball (convex_ball _ _).isPreconnected hz (fun i' y hy=>?_) x (mem_ball_zero_iff.mpr hx)
   unfold U; rw [mul_assoc, mul_comm (Real.exp _)] ; exact (wages s hp y (mem_ball_zero_iff.mp hy) h.width ..).smul _

def staple (G:Gauge)(σ C Z W:ℝ)(p:Clip)(k:ℕ):ℝ:= |p.direct| * Uniform.priceCost G (travelCost G k 4 Z) + Lantern.clump k (C*legPrice G k Z σ) W
-- optional comp budget purchased fixed before manually possible.
omit h
lemma considerable (G:Gauge)(σ C Z:ℝ)(k:ℕ) : ∃ A>0, ∀ x∈closedBall (0:G.Color) (C*legPrice G k Z σ), Brush k A 1 (fun z:G.Color=>‖z‖^2/2) x :=
    Brush.compact (s:=closedBall _ _) (isCompact_closedBall _ _) (fun _ _=> ((contDiff_norm_sq (𝕜:=ℝ)).div_const (2:ℝ)).contDiffAt)
include h
variable (hW:∀ x∈closedBall (0:G.Color) (C*legPrice G k Z σ), Brush k A 1 (fun z:G.Color=>‖z‖^2/2) x)
local notation "Γ"=> staple G σ C Z A p k
include hW
lemma authorized (hp:Inputs A' k Z)(x:E)(hx:‖x‖<1): Brush k Γ 1 ((turn R p s i) ∘ A') x:=by
   let A z:=pull s 0 (A' z); have he:= honor R p h s i hp x hx; have hv:= pulled hp s
   have hg:Allows k (fun z=>p.direct * G.price (faceValue (A z) i)) x (|p.direct| *Uniform.priceCost G (travelCost G k 4 Z)):=
      (Allows.price (f:=fun z=>faceValue (A z) i) (travel_jets (U:=A) (fun j=>hv.2.2 j x hx.le) (w:=square _ _) i.1 (a:=4) (by simp [square]))).smul _
   exact (Brush.offer.mpr ⟨hg.analytic.of_le le_top,hg.norm_le⟩).gathering (composite he (hW _ (mem_closedBall_zero_iff.mpr he.bound))) -- colorm
lemma authorize : Sect (turn R p s i) B.threshold 2 k Z (|Γ| + (p.direct+C^2)):=by
   have he : Γ ≤ |Γ| + (p.direct+C^2):= (le_abs_self _).trans (le_add_of_nonneg_right (add_nonneg p.quadratic_pos.le (sq_nonneg _)))
   refine ⟨⟨fun E _ _ U hU y hy=> (authorized R p h s i hW hU y hy).climb he le_rfl, fun E _ _ U hU=>?_⟩, fun m t=>?_,?_,fun U hV=>(uponU B R p h s i U hV).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg _)) (sq_nonneg B.threshold))⟩
   · refine ⟨(authorized R p h s i hW hU 0 (by simp)).smooth,fun j hj hk=>?_⟩
     let V:= (turn R p s i) ∘ U; have hp : V 0=0:=by unfold V; rw [Function.comp_apply,hU.1,still_turn] -- edit
     unfold normJ; interval_cases j <;> change ‖iteratedFDeriv ℝ _ V 0‖=0
     · rw [norm_iteratedFDeriv_zero,hp,norm_zero]
     have hv:IsLocalMin V 0:= Eventually.of_forall fun z=> hp.le.trans (rill ..)
     rw [norm_iteratedFDeriv_one,hv.fderiv_eq_zero,norm_zero]
   · unfold turn; simp only [Work.F05.pull_gauge_zero,face_gauge, G.price_conj, Work.F05.ell_gauge h,G.norm_adjoint]
   have h':Measurable (pull s (0:Site f) (K:=G.El)):= by fun_prop
   unfold turn; apply Measurable.add
   · apply Continuous.measurable; apply continuous_const.mul; unfold faceValue; fun_prop
   exact ((((R.ell_meas i p σ C W h).comp h').norm).pow_const _).div_const _
open Oriented
def center (U:Config G f):= averaged fun s=> ∑ i:Face (Per f), turn R p s i U
lemma velour :
    Sect (center R p (f:=f)) B.threshold 2 k Z (Fintype.card (Face (Per f))*(|Γ| + (p.direct+C^2))) := by
   have hp (s:Signed) := array Finset.univ (turn R p s (f:=f)) (fun _=> (|Γ| + (p.direct+C^2))) (fun i _=> authorize B R p h s i hW)
   let m := (Fintype.card Signed:ℝ); have hm : 0< m:= Nat.cast_pos.mpr Fintype.card_pos
   simp_rw [Finset.sum_const,card_univ,nsmul_eq_mul] at hp
   have he:= array (Finset.univ:Finset Signed) (fun s U=>∑ i:Face (Per f), turn R p s i U) (fun _=>Fintype.card (Face (Per f))*(|Γ| + (p.direct+C^2))) (fun s _=> hp s)
   have ht:= grow he m⁻¹
   rw [Finset.sum_const,nsmul_eq_mul,card_univ, Real.norm_of_nonneg (inv_pos.mpr hm).le, inv_mul_cancel_left₀ hm.ne'] at ht; exact ht
end kin
end YM.RemainderComparison.Herbal
