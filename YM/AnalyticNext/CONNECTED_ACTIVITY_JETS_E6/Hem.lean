import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Marchers

/-!
# Shape budgets for angular sup marks and genuine `Regular`

 Absolute merged marks separate. Pays at anchored P compatible with
 old History threshold and new generation etc, but no Taylor vanishing claim!
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets  Silica Poll Pond  Eider  Hues Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

lemma charted {V : Config G c} {g : Config G c → ℝ} (p : Ore V g v B j) (hv : 0<v) :
    ContDiffAt ℝ (↑j) (fun a : Directions G c=> g (increment V a)) 0 := by
  obtain ⟨u,hu,h⟩:= expCost G j 1
  let a:=1+j.factorial*u; have ha : 0<a := by unfold a; positivity
  let d:= v/(2*a); have hd : 0<d:= by unfold d; positivity
  let L := d • ContinuousLinearMap.id ℝ (Directions G c)
  have hL : ‖L‖ ≤ 1*d := by unfold L; rw [norm_smul,one_mul,Real.norm_of_nonneg hd.le]; exact mul_le_of_le_one_right hd.le ContinuousLinearMap.norm_id_le
  have hh := fromLogL L (x:=0) (linearB L (u:=1) (d:=d) (by simp) hL hd.le) 1 zero_lt_one h (by intro i; simp only [map_zero, Pi.zero_apply]; simp) V
  have he : (1+(j.factorial:ℝ)*u)*((1+1)*d)=v := by change a*_ =_; unfold d; field_simp; ring
  rw [he] at hh
  let f Z := g (increment V (L Z))
  have hp : ContDiffAt ℝ (↑j) f 0 := (p (Directions G c) (fun a=> increment V (L a)) 0 (by rw [map_zero]; exact Work.G07.at_zero_increment V) hh).smooth
  let M := d⁻¹ • ContinuousLinearMap.id ℝ (Directions G c)
  rw [show (fun a : Directions G c=> g (increment V a))=f ∘ M from funext fun _=> by simp [f,M,L,smul_smul,hd.ne']]; exact ((show ContDiffAt ℝ (↑j) f (M 0) from by rw [map_zero]; exact hp)).comp (0:Directions G c) (f:=M) M.contDiff.contDiffAt

variable {Z : Support c} {g : Config G c→ℝ}
lemma stays (h : LocalOn Z g) (l : List (Directions G c)) (W : Directions G c → Directions G c)
    (he : ∀ i∈l,∀ j : Bond c, j.1∈Z→W i j=i j) :
    ∀ V U, Agrees Z V U → leftDerivs g l V=leftDerivs g (l.map W) U := by
  induction l with
  | nil => exact h
  | cons i l ih =>
    intro V U hv
    refine congr_arg (fun f=>deriv f 0) (funext fun (t:ℝ)=> show leftDerivs g l (increment V (t • i))=_ from ih
      (fun i hi=>he _ (List.mem_cons_of_mem _ hi)) _ (increment U (t • W i)) (fun j hj hk=>?_))
    unfold increment; simp only [hv j hj hk,Pi.smul_apply,he i (by simp) j hj]

structure Sailor (G : Gauge) (t C : ℝ) (j : ℕ) : Prop where
  stroke : ∀ (c:Side) (A: Directions G c), ‖A‖≤t → ∀ (E: Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → Config G c) (x:E) (d:ℝ),
    Mode f x j d → Mode (fun i:E × ℝ=> increment (f i.1) (i.2 • A)) (x,0) j (C+d)

lemma costsD (h : LocalOn Z g) {p : BudgetPoint} {U : Config G c}
    (N : Sailor G p.threshold C j) (hq : 0≤ C) (y : Site c) (B : ℝ) (hp : j*C ≤ v) (hv : Ore U g v B j)
    (hx : ∀ x∈Z, 1+ (separation x y:ℝ)≤Y) (ht : 1≤Y) :
    ∀ l: List (Directions G c), l.length ≤ j → (∀ i∈l,p.dirBound y i) → ‖leftDerivs g l U‖ ≤ Y^(p.power*j)* B := by
  intro l hl hU
  let t := Y^p.power; have ht' : 1≤t:= one_le_pow₀ ht; have hu := zero_lt_one.trans_le ht'
  let f (a: Directions G c) (e:Bond c) := if e.1∈Z then a e else 0
  let l' := l.map f; let Z':List (Directions G c):= l'.map (fun i=> t⁻¹ • i)
  have hh : l'=Z'.map (fun i=>t • i) := by
    unfold Z'; simp only [List.map_map]; simp only [Function.comp_def,smul_smul,mul_inv_cancel₀ hu.ne',one_smul]; exact congr_fun List.map_id_fun.symm l'
  have hi := stays h l f (fun i hi j hj=> if_pos hj) U U (fun _ _ _=>rfl); rw [hi]; change ‖leftDerivs g l' U‖ ≤ _
  have hZ i (hi:i∈Z') : ‖i‖≤p.threshold := by
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hi; obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hz
    rw [norm_smul,norm_inv,Real.norm_of_nonneg hu.le]; have he : ‖f k‖≤p.threshold*t := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg p.threshold_pos.le hu.le)).2; intro e; unfold f; split
      next hx' => exact (hU k hk e).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hx _ hx') _) p.threshold_pos.le)
      rw [norm_zero]; exact mul_nonneg p.threshold_pos.le hu.le
    rw [mul_comm]; apply (mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hu.le)).trans_eq; field_simp
  let W (_:ℝ):= U; have hz : Mode W 0 j 0:= ⟨le_rfl,fun i=> a_oneB G (U i) le_rfl⟩
  have ht : Z'.length=l.length:= by simp [Z',l']
  have he : Brush 0 B 1 ((leftDerivs g Z') ∘ W) 0 := explorers hv hz rfl (N.stroke c) Z'
    (by rw [zero_add,ht]; exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hq).trans hp) hZ (by omega)
  rw [hh,expands,norm_smul,Real.norm_of_nonneg (by positivity : 0≤ t^Z'.length)]
  rw [pow_mul]; exact mul_le_mul (pow_le_pow_right₀ ht' (ht ▸ hl)) he.bound (norm_nonneg _) (pow_nonneg hu.le _)

lemma shaped (M : Molecule S) (hf : Ac.Spark H.supportP M) : (coverNumber (radiusB s) (H.unionP M):ℝ) ≤ H.shapeW M := by
  let b:= radiusB s
  have hp : (coverNumber b (H.unionP M):ℝ) ≤ ∑ i∈M,(coverNumber b (H.supportP i):ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast Ac.cover H.supportP b hf
  refine hp.trans (Finset.sum_le_sum (fun i hi=> ?_))
  exact le_add_of_nonneg_right (show 0≤Mixed.lengths S H.faresP (ConnectedActivityE6.lengths T R) i from by
    rcases i with i|i; exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _)

def shiftG (s : ℝ) := 4*(2*(radiusB s:ℝ)+1)

end YM.ConnectedActivityE6.Blaze.March
