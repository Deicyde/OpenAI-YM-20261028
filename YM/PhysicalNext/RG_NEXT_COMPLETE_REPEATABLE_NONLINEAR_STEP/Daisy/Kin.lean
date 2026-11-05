import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Berries
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Broom

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "za'" => za M H (n:=n)
variable {t Y₁ g z c₁ v₁ b₁ κ' e:ℝ}
variable (h: Herd H N.conduit A B n)
def pond0 (i : H.Chainbook):= if H.Fresh i∧ Ac.Spark H.bookFoot i.1 then manyW (grade H.seam (zoe M H N) (za M H (n:=n))) i else 0
def oval (i:Clusters H.ThinP) := clusters H.seam (zoe M H N) i.2
lemma oval_pos (i:Clusters H.ThinP) : 0≤oval M H N i:=clusters_nonneg _ (rises M H N) _ -- check syntax
lemma grade_pos (i:H.Chapter) : 0≤grade H.seam (zoe M H N) (za M H (n:=n)) i:=by
  rcases i with i|i; exact rides M H n i; exact oval_pos M H N i
lemma pond_pos (i:H.Chainbook) : 0≤pond0 M H N i:=by
  unfold pond0; split
  next h=> exact Finset.prod_nonneg fun i _ => div_nonneg (pow_nonneg (grade_pos M H N i.val) _) (by positivity)
  exact le_rfl

include h
lemma roosts (V:Config G c)(t:ℝ)(ht:|t| * d0 ≤1)(i:H.fragrances) : Est (oval M H N i) d0 t (fun p=> H.trainedMill (color M H χ V p) i):= by
  exact Est.logCharge H.seam (zoe M H N) (fun p=> H.entriesMill (color M H χ V p)) ((dew M H).2.1) (fun i=> warm M H h V t ht i) i
lemma inSun (V: Config G c)(t:ℝ)(ht:|t| * d0 ≤1)(i:H.Chainbook): Est (pond0 M H N i) d0 t (fun t=> H.smilesMill V (color M H χ V t) i):=by
  unfold Cash.smilesMill pond0; split_ifs with hp h' h'
  -- test order (Fresh first)
  · refine Est.copies (fun t=>H.cologneMill (color M H χ V t)) _ ((dew M H).2.1) ?_ i; rintro (i|i)
    · exact cold M H χ V t ht i
    change Est (oval M H N i) _ _ (fun t=> -( H.trainedMill (color M H χ V t) i))
    simpa only [neg_one_mul,abs_neg, abs_one, one_mul] using! ((roosts M H N h V t ht i).rescale (-1))
  · exact Est.nil _ _ _ _ (dew M H|>.2.1) (by rw [abs_zero]; exact Finset.prod_nonneg fun i _=> div_nonneg (pow_nonneg (grade_pos M H N i.val) _) (by positivity))
  · exact (hp ⟨h'.1,h'.2.1⟩).elim
  exact Est.nil _ _ _ _ (dew M H|>.2.1) (abs_zero.le)
omit h
-- ratio terms positivity.Structures
structure Plating (α t q' c₁ u κ' e : ℝ) : Prop where
  first : Ready H.smallAt (radiusB x) (zoe M H N) (α+e) t b₁ q' -- implicit b₁ variable hidden in structure parameter
  second : Ac.Hit H.largeAt (radiusB x) (za M H (n:=n)) (α+e) c₁
  κ0 : 0≤κ'
  live : 0≤α
  post : 0<e
  income : 0<u
  price : u ≤ 1/2
  earns : (2*Real.exp κ'*(1-(1/2:ℝ))⁻¹)*c₁ + 2*(1-(1/2:ℝ))⁻¹*(t*(1-q')⁻¹) ≤ u
  charm : degreePrice (radiusB x) u e ≤ 1/2
variable (k : Plating (b₁:=b₁) M H N a t g c₁ u κ' e)
-- new Schedule Needed before selecting radius.LANE.
include k
lemma reserveK : Ac.Hit H.library (radiusB x) (pond0 M H N) a (Real.exp (-κ')*(2*u)):=by
  intro i; have ht:= OmitClusters.restore H.seam H.smallAt H.largeAt (zoe M H N) za' (radiusB x) (rises M H N) (rides M H n)
    (fun i=>i.2.1) (fun i=>i.2.1) (by norm_num: (1:ℝ)≤2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2<1) k.κ0 k.live k.post H.testS k.first k.second k.earns k.income k.price k.charm (by norm_num : (1:ℝ)/2<1) i 0
  have hu:=show ( ((2:ℝ)^ (0:ℕ))⁻¹ * Real.exp (-κ'))*(u*(1-1/2)⁻¹)= Real.exp (-κ')*(2*u) from by ring
  dsimp only at ht; rw [hu] at ht; refine budget_mono ht (fun i' => ?_) fun m=>?_ 
  · split; exact mul_nonneg (pond_pos M H N i') (Real.exp_pos _).le; exact le_rfl
  split
  next h=>
    unfold pond0; split
    next hz => rw [if_pos ⟨H.regains m hz.2 hz.1,Nat.zero_le _⟩,Multiple.connected, if_pos ⟨hz.2,h⟩]; exact (mul_comm ..).le
    rw [zero_mul]; exact ht.1 _
  next=> exact ht.1 _
omit k in
lemma everyoneN {i:Type*}(X : i→ Support c)(f':i→ℝ)(hf:∀ i,0≤f' i)(hb: Ac.Hit X (radiusB x) f' a g)(he:∀i,f' i≠0→ (X i).Nonempty)(ha:0≤a): Summable f':=by
  have hp := AbsoluteSums.Product.everyone_ne _ _ hf he hb; refine Summable.of_nonneg_of_le hf ?_ hp.2.1
  intro i; exact le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))


lemma ticks (m : ℕ) : Ac.Hit (fun i:Clusters H.ThinP=>H.bookFoot (.inr i)) (radiusB x)
    (fun i=> if m ≤ i.1 then oval M H N i else 0) (a+e) (t*g^m *(1-g)⁻¹) :=by
  intro i
  have hz := log_hit_tail H.seam H.smallAt (radiusB x) H.testS k.first (add_nonneg k.live k.post.le) m i
  convert! hz using 2
  rename_i z
  by_cases hp:m ≤ z.1 <;> by_cases hs:i∈ unionOf H.smallAt z.2 <;> simp only [*,Trees.currency,not_false_eq_true,true_and, if_neg] <;> simp [show H.bookFoot (.inr z)=_ from (rfl: H.bookFoot _=unionOf H.smallAt z.2), hs,oval] -- edit
end Charity
end YM.PhysicalNext.Repeat.Daisy
