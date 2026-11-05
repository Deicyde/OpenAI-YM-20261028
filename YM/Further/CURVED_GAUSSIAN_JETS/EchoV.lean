import YM.Further.CURVED_GAUSSIAN_JETS.DirectV
import YM.Further.CURVED_GAUSSIAN_JETS.EchoGauge
import YM.Further.CURVED_GAUSSIAN_JETS.Nozzle
import YM.Further.CURVED_GAUSSIAN_JETS.Weights
import YM.Work.A14

/-!
# Native price for the derivative of the common-tag noise slopes

One actual positive-orientation evaluation per bond (not a prescription
which evaluates a tangent on a differently-oriented representative).
Differentiating the raw branch, no extension by zero due to geometry.
Even when the a coefficient is zero by lack of local directions, the
branch itself needn't have nonnegative probabilities or uniform jets there!
Nothing here authorizes multiplying by such a switch and differentiating.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum Pockets Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure Shape Next.Fluctuations
open Green (wt)
open FlatTree (wheel)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {f c n : Side} {S : StepData c f} {F : Forest S.ratio} {V : Config G c} {k j : ℕ} {K D δ A r : ℝ} (H : Finset F.Free)
    (hk : ExpReceipt G (k+1) K) (hD : LogReceipt G D δ) (hF : FocusReceipt G k A r)

def raw (l : S.Choices) (V : Config G c) (j : ℕ) (p : Bond c) (x : joint G c f j) := S.prediction (twoStep S.ratio V j x) l p

def drive (G : Gauge) (P : Patch) (T : KernelChoices) (k : ℕ) (K D δ r : ℝ) := min 1 (predictionRadius P G T k K (fullCost G (k+1) K) D δ r)
include hk hD hF in
lemma drive_pos (P : Patch) (T : KernelChoices) (he : 2 ≤ k) : 0 < drive G P T k K D δ r := by
  let S : StepData 1 P.L := ⟨P,T,by simp⟩
  exact lt_min zero_lt_one (prediction_radius_pos S (cruise_input S.ratio (1: Site P.L → G.El) hk (j:=0) (Nat.zero_le _)) he hk hD hF)

def rawCost (G : Gauge) (P : Patch) (k : ℕ) (K A : ℝ) := let C := composeCost k (composeCost k A (connectorCost P G k K (fullCost G (k+1) K))) 1
  2^k*(2^k*matSize G*C)*matSize G

include hk hD hF in
lemma raw_pay (ht : 2≤k) (hj : j≤k+1) {h : Site f → G.El} {z : Dir G f} (hz : ‖z‖ < drive G S.patch S.kernel k K D δ r) (hS : S.patch.Branches S.kernel G)
    (l : S.Choices) (y : Bond c) (he : AgreeNear S.ratio.parent y.1 (predReach S.patch) (gauge h (replica S.ratio V)) (represent z)) :
    Allows k (fun x=> G.mat (raw l V j y x)) 0 (rawCost G S.patch k K A) := by
  let left := (h (S.ratio.embed y.1))⁻¹; let right := h (S.ratio.embed (y.1+Lattice.step y.2)); let u := fun x : joint G c f j=> S.prediction (cruise S.ratio h j (x,z)) l y
  have hx : raw l V j y = fun x=> left * u x * right := funext (cruise_back h V y l hS he)
  rw [hx]
  have heq := prediction_pay S (cruise_input S.ratio h hk hj) ht hk hD hF (0,z) (by simpa [Prod.norm_def] using hz.trans_le (min_le_right ..)) l y
  have hz := allows_const (n:=k) (0:joint G c f j) (hz.le.trans (min_le_left ..))
  let v x := G.mat (S.prediction (cruise S.ratio h j x) l y)
  have hf := heq.comp (g:=v) (f:=fun x=>(x,z)) ((linear_fare (ContinuousLinearMap.id ℝ _) (fun _=>le_rfl) (by simp : ‖(0:joint G c f j)‖ ≤ (1:ℝ))).pair hz)
  exact ((allows_const 0 (mat_size left).le).times (f:=fun _ => left) (g:=u) hf).times (f:=fun x=>left * u x) (g:=fun _=>right) (allows_const 0 (mat_size right).le)

def dropCost (G : Gauge) (k : ℕ) (C : ℝ) := let m {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y) := ‖L‖
  m (X:=G.Mat) (Y:=G.Color) G.projectColor.toContinuousLinearMap * (2^k*C*composeCost k C 1)

lemma nozzle_tap (b : Bits H G) (x : Slab G c j) {l : S.Choices} {y : Bond c}
    (h : DifferentiableAt ℝ (fun u=> G.mat (raw l V j y u)) (x,0)) :
    tap (insertTest H (Pi.single b 1)) (fun q=> G.projectColor (G.mat (raw l V j y q * (raw l V j y (q.1,0))⁻¹))) x =
      nozzle H (replica S.ratio (chug j V x)) l y (Pi.single b 1) := by
  let U := replica S.ratio (chug j V x); let a := raw l V j y (x,0)
  have ha : a = S.prediction U l y := by unfold a raw twoStep U; dsimp only; rw [Work.G07.at_zero_increment]
  let f (u : Directions G f) := G.mat (raw l V j y (x,u))
  have hf : DifferentiableAt ℝ f 0 := h.comp 0 (f:=fun u=>(x,u)) (by fun_prop)
  let L := G.projectColor.toContinuousLinearMap ∘L ((ContinuousLinearMap.mul ℝ G.Mat).flip (G.mat a⁻¹))
  have he := L.hasFDerivAt.comp 0 hf.hasFDerivAt; unfold tap; simp_rw [G.mat_mul]
  change fderiv ℝ (L ∘ f) 0 _ = nozzle H U l y _
  rw [he.fderiv,nozzle,← ha]; change L _ = L _; congr 1
  exact (tap_read f (insertTest H) hf (Pi.single b 1)).symm

lemma fluid_pay (b : Bits H G) {l : S.Choices} {i : Shape.Page G c 1} {C : ℝ}
    (h : Allows (k+1) (fun u=> G.mat (raw l V j ((wheel c).symm i.1) u)) 0 C) :
    Allows k ((fun u=> fluid H (replica S.ratio u) l i b) ∘ chug j V) 0 (dropCost G (k+1) C) := by
  let R := raw l V j ((wheel c).symm i.1); let F := fun q : joint G c f j=> (q.1,(0:Directions G f))
  let T := ContinuousLinearMap.fst ℝ (Slab G c j) (Directions G f)
  have he : Allows (k+1) F 0 1 := (linear_fare T (fun x=>show ‖x.1‖ ≤ _ from le_max_left ..) (by simp)).pair (allows_const _ (by simp))
  have ht := (h.times (f:=R) (g:=fun q=>(R (F q))⁻¹) ((h.comp (f:=F) (g:=fun u=>G.mat (R u)) he).inverse (f:=R ∘ F))).linear G.projectColor.toContinuousLinearMap le_rfl
  apply Allows.germ (allows_proj (tap_pay (insertTest H (Pi.single b 1)) ht (insertTest_short H b)) i.2)
  have hh : Tendsto (fun x : Slab G c j => (x,(0:Directions G f))) (𝓝 0) (𝓝 0) := (continuous_id.prodMk continuous_const).tendsto (0:Slab G c j)
  refine (hh.eventually (h.analytic.eventually (by simp))).mono fun x hx=>?_
  exact congr_arg (fun v : G.Color=>v.ofLp i.2) (nozzle_tap H b x (hx.differentiableAt (by simp)))

lemma fluid_dead (l : S.Choices) (hS : S.patch.Branches S.kernel G) (i : Shape.Page G c 1) (j : Bits H G) (he : ¬Shape.visits H ((wheel c).symm i.1) j.1) (u : Config G c) : fluid H (replica S.ratio u) l i j = 0 := by
  let U := replica S.ratio u
  by_cases hx : DifferentiableAt ℝ (fun x=> G.mat (Shape.readBond H U l ((wheel c).symm i.1) x)) 0
  · exact fluid_range H U l hS i j hx he
  dsimp only [U] at hx
  unfold fluid; rw [row_unit, nozzle]; erw [fderiv_zero_of_not_differentiableAt hx]
  change (G.projectColor ((0:G.Mat) * _)).ofLp i.2=0; rw [Matrix.zero_mul,map_zero]; rfl

lemma fluid_reads (l : S.Choices) (hS : S.patch.Branches S.kernel G) (i : Shape.Page G c 1) (j : Bits H G) : Numerical S.ratio.embed (coarseSite S i) ((1+predReach S.patch)*S.ratio.count.val) (fun u=>fluid H (replica S.ratio u) l i j) := by
  intro u v he
  let U := replica S.ratio u; let V := replica S.ratio v; let b := (wheel c).symm i.1
  have hx : AgreeNear S.ratio.parent b.1 (predReach S.patch) U V := by
    intro j hj; unfold U V replica; split; rfl
    refine he _ ((Next.Free.scaled_root S.ratio b.1 _).trans ?_)
    dsimp only [Prod.fst]; rw [mul_comm]; exact Nat.mul_le_mul_right _ (hj.trans (by omega : predReach S.patch ≤ 1+predReach S.patch))
  have hQ := prediction_near_eq hS U V l b hx
  have Hq : Shape.readBond H U l b=Shape.readBond H V l b := by
    funext x; apply prediction_near_eq hS; intro b hb; rw [Shape.restore,Shape.restore,increment,increment,hx b hb]
  change fluid H U l i j = fluid H V l i j
  simp only [fluid,row_unit,b,nozzle,hQ,Hq]
lemma visits_dist (i : Shape.Page G c 1) (j : Bits H G) (he : Shape.visits H ((wheel c).symm i.1) j.1) : separation (coarseSite S i) (keySite H j) ≤ (1+predReach S.patch)*S.ratio.count.val := by
  have hm := Next.Free.scaled_root S.ratio i.1.1 (S.ratio.parent (keySite H j)); have hx := Corona.near S.ratio (keySite H j)
  rw [separation_comm] at hx; unfold coarseSite
  apply (separation_triangle _ (S.ratio.embed (S.ratio.parent (keySite H j))) _).trans
  rw [add_mul,one_mul,mul_comm (predReach _)]
  have hj : separation i.1.1 (S.ratio.parent (keySite H j)) ≤ predReach S.patch := he
  have h := hm.trans (Nat.mul_le_mul_left _ hj); omega

theorem fluid_items (G : Gauge) (P : Patch) (T : KernelChoices) (k p : ℕ) {w : ℝ} (hw : 0<w) : ∃ C δ : ℝ, 0<C ∧ 0<δ ∧ ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=T → Paid S G → ∀ (F : Forest S.ratio) (H : Finset F.Free) (o : Site f) (V : Config G c) {t s : ℝ}, 0 ≤ t → 0 ≤ s → s ≤ δ → Covered H s V → ∀ l : S.Choices, Items S.ratio o (coarseSite S) (keySite H) w t p k V (fun u=>Shape.fluid H (replica S.ratio u) l) C := by
  let m := k+2
  obtain ⟨K,hK,h⟩ := exp_receipt G (m+1)
  obtain ⟨D,δ,hD⟩ := log_receipt G
  obtain ⟨A,r,hA,hF⟩ := focus_receipt G m
  obtain ⟨M,s,hM,hs,hE⟩ := Pockets.patchGauge P G
  let d := drive G P T m K D δ r; have hd : 0<d := drive_pos h hD hF P T (by omega)
  let C := max 1 (dropCost G m (rawCost G P m K A)); have hC : 0<C := zero_lt_one.trans_le (le_max_left ..)
  let R := (1+predReach P)*P.L.val
  refine ⟨Real.exp (w*(R:ℝ)) * (C*(1+(R:ℝ))^(p*k)), min s ((d/2)/M), by positivity,lt_min hs (by positivity),fun S hp hT hS F H o V t τ ht hr hr' hv l i j=>?_⟩
  let b := (wheel _).symm i.1; let U := replica S.ratio V
  by_cases he : Shape.visits H b j.1; swap
  · exact sticker_zero (funext (fluid_dead H l hS.1.1 i j he)) ht (by positivity)
  obtain ⟨g,z,hz,hg⟩ := hE S hp (hp ▸ hS.2) hr (hr'.trans (min_le_left ..)) _ V (hp ▸ weak_of_visits H hv he)
  have hq : R=(1+predReach S.patch)*S.ratio.count.val := by unfold R; rw [←hp]; rfl
  refine sticker_local (hq ▸ visits_dist H i j he) hw.le ht (hq ▸ fluid_reads H l hS.1.1 i j) fun j' hj=>?_
  have hg : AgreeNear S.ratio.parent _ (predReach S.patch) (Lattice.gauge g U) (represent z) := hg.shrink (by rw [separation_self,zero_add,hp]; unfold Pockets.reach; omega)
  have hz : ‖z‖ < drive G S.patch S.kernel m K D δ r := by rw [hp,hT]; change ‖z‖ < d; linarith only [hz,hd,(le_div_iff₀ hM).mp (hr'.trans (min_le_right ..))]
  have hb := raw_pay h hD hF (show 2≤m by omega) (hj.trans (by omega) : j'≤m+1) hz hS.1.1 l b hg
  have hx := fluid_pay (k:=k+1) (j:=j') H j (i:=i) hb
  exact (hx.order hj).mono (hp ▸ (le_max_right 1 _))
end YM.Further.CurvedGaussianJets.ChangeV
