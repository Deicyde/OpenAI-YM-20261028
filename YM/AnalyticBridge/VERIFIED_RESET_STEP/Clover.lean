import YM.AnalyticBridge.VERIFIED_RESET_STEP.Calculus
import YM.Push.STRESS_FLUX.Clover
import YM.Push.STRESS_FLUX.Low
import YM.UVNext.PRICED_KERNELS.MaskE


/-! Based clover values, physical t-gain in *all* the ordered derivatives,
using only a single healthy anchor. No shrinking-indicator identity claimed
for free. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG StressFlux UVNext.PricedKernels Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Support n}

namespace Square
lemma touched_here (o : Site n) (a b : Step) (h : a.dir < b.dir) : o ∈ touched (atFace o a b,⟨(a.dir,b.dir),h⟩) := by
  rcases a with ⟨i,_|_⟩ <;> rcases b with ⟨j,_|_⟩ <;> simp [touched,square,visits,atFace, Step.vec, posDir,negDir] <;> abel_nf <;> tauto
lemma nearby (o : Site n) (a b : Step) {x : Site n} (h : x ∈ visits o (oriented a b)) : separation o x ≤ 2 := by
  have h1 := oneStep_le o a; have h2 := oneStep_le (o+a.vec) b; have h3 := oneStep_le o b
  have hx := separation_triangle o (o+a.vec) (o+a.vec+b.vec)
  simp only [oriented,visits,List.mem_cons,List.not_mem_nil,or_false,Step.vec_rev] at h
  rcases h with rfl|rfl|rfl|rfl|rfl
  · simp
  · omega
  · omega
  · rw [show o+a.vec+b.vec+-a.vec = o+b.vec by abel]; omega
  rw [show o+a.vec+b.vec+-a.vec+-b.vec = o by abel]; simp
lemma near_face (o : Site n) (a b : Step) : separation (atFace o a b) o ≤ 2 := by
  have h1 := oneStep_le o a; have h2 := oneStep_le (o+a.vec) b; have h3 := oneStep_le o b
  have hx := separation_triangle o (o+a.vec) (o+a.vec+b.vec)
  rw [separation_comm]; unfold atFace; split_ifs <;> (try simp only [add_zero,separation_self]) <;> omega
lemma small {o : Site n} {V : Config G n} (a b : Step) (h : a.dir < b.dir) (hv : Healthy p.threshold {o} V) :
    G.chord (travel V o (oriented a b)) ≤ p.threshold := by
  rw [price_shift_pos G.chord V G.chord_inv (fun k g => G.chord_conj g k) a b o]
  by_contra! he
  exact Finset.disjoint_left.mp hv (Finset.mem_singleton_self _) ((flags_spec ..).mpr ⟨_,touched_here o a b h,he⟩)
end Square

lemma projector_stamp (u : G.El) : Wages.projector G (G.mat u - 1) = G.curvature u := by
  rw [map_sub,show Wages.projector G (1:G.Mat) = G.curvature (1:G.El) from rfl,G.curvature_unit, sub_zero]; rfl

def colorBill (G : Gauge) (L P k : ℕ) := G.colorScale⁻¹ * feeWalk G L P k

lemma curvature_bill (p : BudgetPoint) (o : Site n) (l : Walk) (Z : Config G n → Prop) (hz : ∀ U, Z U → G.chord (travel U o l) ≤ p.threshold) :
    Bill p o Z (colorBill G l.length p.power p.order * p.threshold) fun U => G.curvature (travel U o l) := by
  simp_rw [← projector_stamp,colorBill,mul_assoc]
  have he := word_fund o l p Z hz
  exact ⟨he.smooth.postcomp _, mul_nonneg (inv_nonneg.mpr G.colorScale_pos.le) he.nonneg, fun a ha hd U hu => by
    rw [one_pow,mul_one]
    change ‖leftDerivs (fun U => Wages.projector G (wordStamp o l U)) a U‖ ≤ _
    have ht : leftDerivs (fun U => Wages.projector G (wordStamp o l U)) a U = _ := congr_fun (Work.G07.left_linear he.smooth (Wages.projector G) ha) U
    rw [ht]
    exact (Wages.norm_projector G _).trans (mul_le_mul_of_nonneg_left (bill.norm he a ha hd U hu) (inv_nonneg.mpr G.colorScale_pos.le))⟩

def petals (U : Config G n) (o : Site n) : Flux G := fun b => clover U o b.val.1 b.val.2
lemma petals_moves (U : Config G n) (o : Site n) (s : Signed) (b : Site n) : petals (pull s b U) o = reframe (petals U (affine s b o)) s := by
  ext1 ⟨⟨i,j⟩,he⟩
  rw [petals,clover_pull]; congr 1
  rcases lt_or_gt_of_ne (s.perm.injective.ne (show i < j from he).ne) with h|h
  · simp [orderedDir,h,not_lt_of_gt h,petals]
  simp only [orderedDir,h,not_lt_of_gt h,↓reduceDIte, zero_sub, petals]
  rw [clover_swap U (affine s b o) (s.perm i) (s.perm j)]
lemma petals_gauge (t : Site n → G.El) (U : Config G n) (o : Site n) (b : PlaqAxes) :
    petals (Lattice.gauge t U) o b = G.adjoint (t o) (petals U o b) := clover_gauge ..
@[fun_prop] lemma petals_cont (o : Site n) (b : PlaqAxes) : Continuous fun U : Config G n => petals U o b := by unfold petals clover stencil; fun_prop
lemma petals_reads (o : Site n) (b : PlaqAxes) : LocalOn (halo 2 {o}) fun U : Config G n => petals U o b := by
  intro U V h
  have hl (a b : Step) : plate U o a b = plate V o a b := congrArg G.curvature (travel_local o (oriented a b) _ _
    (agrees_mono h (fun x hx => show x ∈ halo 2 {o} from halo_spec.mpr ⟨_,Finset.mem_singleton_self _, Square.nearby o a b hx⟩)))
  simp [petals, clover,stencil,hl]

lemma unitTravel {R : Type*} [AddCommGroup R] [One R] (G : Gauge) (o : Four R) (l : Walk) : travel (1 : Links R G.El) o l = 1 := by
  induction l generalizing o <;> simp_all [travel,Step.read]
@[simp] lemma petals_one (o : Site n) : petals (1:Config G n) o = 0 := by
  funext b; change _ = 0; simp [petals,clover,stencil,plate, unitTravel, Gauge.curvature_unit]
lemma petals_bill (p : BudgetPoint) (o : Site n) (b : PlaqAxes) : Bill p o (Healthy p.threshold {o})
    (colorBill G 4 p.power p.order * p.threshold) fun U : Config G n => petals U o b := by
  have h (i j : Step) (hi : i.dir < j.dir) : Bill p o (Healthy p.threshold {o}) (colorBill G 4 p.power p.order * p.threshold)
      fun U : Config G n => plate U o i j := curvature_bill p o (oriented i j) _ fun _ hv => Square.small i j hi hv
  have he i (hi : i.dir = b.val.1) := Bill.sub (h i (posDir b.val.2) (hi.symm ▸ b.property)) (h i (negDir b.val.2) (hi.symm ▸ b.property))
  refine Bill.le (Bill.scale 4⁻¹ (Bill.sub (he (posDir b.val.1) rfl) (he (negDir b.val.1) rfl))) ?_
  norm_num; linarith

def pairBill (G : Gauge) (p : BudgetPoint) := pairingCost G.Color p.order * colorBill G 4 p.power p.order ^2
lemma pair_nonneg (G : Gauge) (p : BudgetPoint) : 0 ≤ pairBill G p := mul_nonneg (pairing_nonneg ..) (sq_nonneg _)
lemma pair_paid (p : BudgetPoint) (o : Site n) (a b : PlaqAxes) :
    Bill p o (Healthy p.threshold {o}) (pairBill G p * p.threshold ^ 2) fun U : Config G n => inner ℝ (petals U o a) (petals U o b) := by
  apply Bill.le (Bill.pair (petals_bill p o a) (petals_bill p o b)); unfold pairBill; apply le_of_eq; ring

def counter (q : PlaqAxes → PlaqAxes → ℝ) (o : Site n) : Pot G n := fun U => quad q (petals U o) (petals U o) / 2
lemma counter_bill (o : Site n) (q : PlaqAxes → PlaqAxes → ℝ) (p : BudgetPoint) : Bill p o (Healthy p.threshold {o})
    ((2:ℝ)⁻¹ * ∑ a, ∑ b, |q a b| * (pairBill G p * p.threshold ^ 2)) (counter (G:=G) q o) := by
  unfold counter quad
  simp_rw [div_eq_inv_mul]; simpa using! Bill.mul_left 2⁻¹ (Bill.sum Finset.univ (fun i _ => Bill.sum Finset.univ fun j _ => Bill.mul_left (q i j) (pair_paid (G:=G) p o i j)))
lemma counter_regular (o : Site n) (q : PlaqAxes → PlaqAxes → ℝ) (p : BudgetPoint) : p.Regular (halo 2 {o}) (counter q o (G:=G)) := by
  apply reg_bill (counter_bill o q p)
  · unfold counter quad; fun_prop
  · intro U V h; simp only [counter,quad,petals_reads o _ U V h]
  intro t U; simp only [counter,quad,petals_gauge,inner_adjoint]
lemma counter_sub (q q' : PlaqAxes → PlaqAxes → ℝ) (o : Site n) :
    counter q o - counter q' o (G:=G) = counter (q-q') o := by
  funext U; simp [counter,quad,sub_mul,Finset.sum_sub_distrib,sub_div]
end YM.AnalyticBridge.VerifiedReset
