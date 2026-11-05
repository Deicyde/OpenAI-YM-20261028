import YM.MergeProof.Garden

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
local notation "sx"=> radiusB x
open Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
variable (rA:ι→ℝ)
local notation "X'"=> swing Q L μ R.beta x C

variable (hR:Plot M Y rA) {e d B:ℝ} {j k : ℕ} (hB: Bikes Q L μ x a e B j k)
set_option quotPrecheck false
include hR
local notation "p₀"=> fun i:Y.ThinP=> tune M Y rA 0 k i.val
local notation "p₁"=> fun i:Y.ThickP=> tune M Y rA 1 0 i.val
local notation "P₀"=> pledgeA L Q μ x B j k
local notation "P₁"=> Charity.daisD Q L μ x k
local notation "VQ" => pledgeQ L Q μ x B j k
local notation "E0" => Q.mark L μ x
local notation "ρ"=> sailUp Q L x

def song (i:Y.fragrances)(U: Config G c) (t:ℝ)(u:Finset ι):=Y.trainedMill (color M Y χ U (ways rA t u)) i
-- Burn, same polls (even bad). No changing L or masks between these estimates.
def fete (i:Y.Chainbook)(U:Config G c) (t:ℝ) (u:Finset ι):=Y.smilesMill U (color M Y χ U (ways rA t u)) i
def lace (k : ℕ)(i:Y.fragrances):= clusters Y.seam (fun i:Y.ThinP=> tune M Y rA 0 k i.val) i.2
def bold (k : ℕ)(i:Y.Chainbook):ℝ:= if Y.Fresh i∧ Ac.Spark Y.bookFoot i.1 then manyW (grade Y.seam (fun i:Y.ThinP=>tune M Y rA 0 k i.val) p₁) i else 0
open Switch
lemma fair (i:Y.fragrances)(k:ℕ): Paid (song M Y χ rA i) (lace M Y rA k i):=by
  let C: ℝ:=↑((i.1+1).factorial)
  let c:= coefficient Y.seam i.2/C
  have h: lace M Y rA k i= ‖c‖ *∏ j:Option (Fin i.1), tune M Y rA 0 k ((i.2 j).val):= by
    unfold lace c C clusters; rw [Real.norm_eq_abs,abs_div, abs_of_nonneg (by positivity:0≤ (↑((i.1+1).factorial):ℝ))]; ring
  rw [h]; refine Paid.congr ((Paid.prod univ (fun j:Option (Fin i.1)=> vote M Y χ rA (i.2 j).val) _ (fun j _=> aca M Y χ rA hR _ k)).smul c) ?_
  intro U x hx; ext i'; unfold song Cash.trainedMill Gas.term; simp_rw [Pi.smul_apply,Finset.prod_apply,smul_eq_mul]; unfold c C; ring_nf; rfl
lemma awake (i:Y.Chapter)(k:ℕ): Paid (fun U t (u:Finset ι)=>Y.cologneMill (color M Y χ U (ways rA t u)) i) (grade Y.seam (fun i:Y.ThinP=>tune M Y rA 0 k i.val) p₁ i) := by
  rcases i with i|i
  · exact ack M Y χ rA hR i
  exact (fair M Y χ rA hR i k).neg
lemma fairs (i:Y.Chainbook)(k:ℕ): Paid (fete M Y χ rA i) (bold M Y rA k i):=by
  unfold bold; split
  next hi =>
    let c:= grade Y.seam (fun i:Y.ThinP=>tune M Y rA 0 k i.val) p₁
    let f j U (t:ℝ)(u:Finset ι):=Y.cologneMill (color M Y χ U (ways rA t u)) j
    let F (j: ↥i.1) := (((↑((i.2 j + 1).factorial):ℝ)⁻¹) • (f j.val) ^ (i.2 j+1)) -- Sigma? check
    let G := ∏ j,F j
    have hp : Paid G (manyW c i):= Paid.prod univ F _ fun j _=> by
      convert! ((awake M Y χ rA hR j.val k).pow (i.2 j+1)).smul _ using 1
      simp [div_eq_mul_inv,mul_comm,c]
    refine Paid.congr (Paid.gate (X:={U| Y.statesPool U i}) hp) ?_
    intro U x _; ext p
    by_cases h:Y.statesPool U i
    · rw [Set.indicator_of_mem (show U∈_ from h)]; unfold fete Cash.smilesMill; rw [if_pos ⟨hi.1,hi.2,h⟩]; unfold G manyW F; simp [f,div_eq_mul_inv,mul_comm]
    rw [Set.indicator_of_notMem (show U∉{U|Y.statesPool U i} from h)]; exact (if_neg (show ¬(_∧ _∧Y.statesPool U i) from fun he=>h he.2.2)).symm --
  next h=> refine Paid.congr paidZero (fun U x hx=>?_); ext i; exact (if_neg (show ¬(Y.Fresh _ ∧ Ac.Spark _ _ ∧ _) from fun y=> h ⟨y.1,y.2.1⟩)).symm
variable (hb:0≤B)
include hB hb χ
lemma lucent : Ac.Hit (fun i:Y.fragrances=>Y.bookFoot (.inr i)) (radiusB x) (lace M Y rA k) (a+e) (P₀*(1-ρ)⁻¹):=by
  intro i; have hz := log_hit_tail Y.seam Y.smallAt (radiusB x) Y.testS (Palette.field M Y χ rA hR hB hb|>.1) (add_nonneg hB.posts hB.allow.le) 0 i
  simp only [Nat.zero_le,pow_zero,mul_one,true_and] at hz
  convert! hz using 2
lemma bright : Ac.Hit Y.library (radiusB x) (bold M Y rA k) a (Real.exp (-E0)*(2*VQ)):=by
  intro i
  obtain ⟨h1,h2,hk,hv,hφ⟩:= Palette.field M Y χ rA hR hB hb
  have ht:= OmitClusters.restore Y.seam Y.smallAt Y.largeAt p₀ p₁ (radiusB x) (fun i=> (aca M Y χ rA hR i k).rocket) (fun i=> (ack M Y χ rA hR i).rocket)
    (fun i=>i.2.1) (fun i=>i.2.1) (by norm_num: (1:ℝ)≤2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2<1) hk hB.posts hB.allow Y.testS h1 h2 hφ hv hB.gains hB.heat (by norm_num : (1:ℝ)/2<1) i 0
  have hu:=show ( ((2:ℝ)^ (0:ℕ))⁻¹ * Real.exp (-E0))*(VQ*(1-1/2)⁻¹)= Real.exp (-E0)*(2*VQ) from by ring
  dsimp only at ht; rw [hu] at ht; refine budget_mono ht (fun i' => ?_) fun m=>?_
  · split; exact mul_nonneg (Paid.rocket (fairs M Y χ rA hR i' k)) (Real.exp_pos _).le; exact le_rfl
  split
  next h=>
    unfold bold; split
    next hz => rw [if_pos ⟨Y.regains m hz.2 hz.1,Nat.zero_le _⟩,Multiple.connected, if_pos ⟨hz.2,h⟩]; exact (mul_comm ..).le
    rw [zero_mul]; exact ht.1 _
  next=> exact ht.1 _
end YM.Merge.Palette
