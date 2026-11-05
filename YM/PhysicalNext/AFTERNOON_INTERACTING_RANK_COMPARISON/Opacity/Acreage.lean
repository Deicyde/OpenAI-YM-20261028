import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Grid
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Vegetal
import YM.Push.RELAY_MARK.Budget
/-!
# Vary all registrations. Real variant earnings at the Wares cost
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Grid
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew Pot Marker Milk
    Local Next.SectorChange.Rows Gaussian Schur Wisps Next.Rank Next.Rank.Value Next.Rank.Flux Vale Display.Docking
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ENNReal
variable {c f : Side} {G : Gauge} {S : StepData c f} {x W t q Κ r l c₀ χ Δ H₀ e : ℝ} {A : Stores S} {v : Dyed G S} {P : Teller G} {F : Forest S.ratio}
variable (H : Draft v P x W) (M : Plate v x W) (O : Orchard S)
local notation "Z"=> Vale.amount H M O
local notation "T"=>sprouting H M O
local notation "K"=>Sprigs H M O
local notation "B"=>v.bp.B
private lemma scales (r : ℝ) (hr : 1≤r) (l : ℝ) (hl : 1≤l) (z : K):
    (T z).infl r l ≤ l * r^z.val.toLeft.card := by
  unfold Zest.infl
  have he:1 ≤ r^z.val.toLeft.card:= one_le_pow₀ hr
  split
  next hh=>
    have hk : 0<z.val.toLeft.card:= by
      obtain ⟨i,hi⟩:=hh
      obtain ⟨j|j,hj,hp⟩:=mem_biUnion.mp (show i∈cardGoal Z z.val from hi)
      · exact card_pos.mpr ⟨j,mem_toLeft.mpr hj⟩
      exact False.elim ((notMem_empty i) (show i∈ (∅ : Support c) from (blankFlags (S:=S)) ▸ (show i∈(store S ∅).flags from hp)))
    obtain ⟨w,h⟩:= Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [h,pow_succ]; have h' : 1≤r^w:= one_le_pow₀ hr; rw [← mul_assoc]; apply le_mul_of_one_le_left (zero_le_one.trans hr); nlinarith only [mul_le_mul hl h' zero_le_one (zero_le_one.trans hl)]
  exact le_mul_of_one_le_right (zero_le_one.trans hl) he

structure Pupil (v : Dyed G S) (x W q vK : ℝ) : Prop where
  fee : 0≤q
  floor : 0<vK
  credit : ∀ (p:Pilot G S x), Matched p → Pours (palette v.things p.key p.park p.tag x p.view .endpoint) (front p.key p.park) (front p.key p.park) 0 vK
  dust : ∀ (p:Pilot G S x) (i : Fleck S), Matched p → Toned (2*radiusB x) (toes S i) p.y.2 q → v.sock W i p=0

def coast (G : Gauge) (q vK : ℝ) (L : Patch) (x : ℝ) := Real.exp (1/4 - damp G vK L (radiusB x) * q^2)
def chargeStep (D : Patch) (q : ℝ) {x : ℝ} (v : Rung S x→ℝ) (b : Glade c→ℝ) : Herbs S x→ℝ := Sum.elim v (Sum.elim (fun _=> q* Jewels.attrition D) b)
variable (J : Rung S x→ℝ) (N : Glade c→ℝ) (h : ∀ i,0≤J i) (hx : ∀ i,0≤N i)
    (hp : ∀ i (p : Pilot G S x),Matched p→ r*|atomP W v M (Sum.inl i) p|≤J i) (hr : 1≤r) (hl : 1≤l)
    (hM : ∀ i (p : Pilot G S x), Matched p→ |Real.exp (M.aux i p)-1|≤ N i)
    (hu : Pupil v x W q Κ)
local notation "w"=> coast G q Κ S.patch x
local notation "fee"=> chargeStep S.patch t J N
include h hx in
private lemma prices_nn (ht :0≤t) (i:Herbs S x): 0≤ fee i := by rcases i with i|i|i; exact h _; exact mul_nonneg ht (Jewels.attrition_nn _); exact hx i
include hu h hx hp hr hl hM
lemma invested (ht : w≤t) (i : K): (T i).Wares v.things r l (l*∏ j∈i.val, fee j) := by
  let E:=i.val.toLeft; let g:Herbs S x→ℝ:= chargeStep S.patch 1 (fun i=> J i/r) N
  have hℓ:0 ≤ l:= zero_le_one.trans hl; have hf : 0 < r:= zero_lt_one.trans_le hr; have hS:0≤ t:= (Real.exp_pos _).le.trans ht
  have hg j : 0≤g j:= prices_nn _ N (fun i=>div_nonneg (h i) hf.le) hx zero_le_one j
  let f:= ∏ j∈i.val, g j; have hf':0≤f:= Finset.prod_nonneg fun j _=> hg j
  refine ⟨mul_nonneg hℓ (Finset.prod_nonneg fun j _=> prices_nn J N h hx hS j),fun V A _ he k=> ?_⟩ -- order
  have hA:Positioned x A V:= he ▸ position ..
  let p(y:RoomView A x k.wood G):Pilot G S x:= ⟨A,k.wood,k.tag,V,y⟩
  let Q:= i.val.toRight.toLeft
  let v₀:= palette v.things A k.wood k.tag x V .endpoint
  have hP:= H.enrolled.fogged A k.wood V k.tag hA
  let y:RoomView A x k.wood G:= (1,0)
  have hv:= hu.credit (p y) hA
  obtain ⟨L,ZZ,HZ⟩:= fill_room v₀ (x:=x) hP hv hu.floor hu.fee f hf' Q
  refine ⟨L,?_,fun y=>?_⟩
  · apply (mul_le_mul (scales H M O r hr l hl i) (ZZ.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le ht _) hf')) (Tilt.fractional L) (show 0≤l*_ from by positivity)).trans_eq
    let q:= (Q.card:ℕ)
    rw [mul_assoc]; apply congr_arg
    have ht (s : Finset (Herbs S x)): r^s.toLeft.card * ((∏ j∈s,g j) * t^s.toRight.toLeft.card)=∏ j∈s,fee j:= by
      let A:=s.toLeft;let F:=s.toRight.toLeft; let C:=s.toRight.toRight
      have hh : s = A.disjSum (F.disjSum C):= by unfold A F C; rw [Finset.toLeft_disjSum_toRight,Finset.toLeft_disjSum_toRight]
      change r^A.card*((∏ j∈s,g j)*t^F.card)=∏ j∈s,fee j; rw [hh]; simp only [prod_disjSum]
      have hx: r^A.card * (∏ j∈A,g (Sum.inl j)) = ∏ j∈A,J j := by rw [← Finset.prod_const, ← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro j _; change r*(J j/r)=_; field_simp
      have hz: t^F.card*(∏ j∈F,g (Sum.inr (.inl j)))=∏ j∈ F,fee (Sum.inr (.inl j)):= by rw [← Finset.prod_const, ← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro j _; change t*(1*_)= _; rw [one_mul]; rfl
      change _= (∏ j∈A,J j)* (_* ∏ j∈ C,g (.inr (.inr j))); rw [← hx,← hz]; ring
    exact ht i.val
  let ZZ(y:RoomView A x k.wood G) := ∏ j∈i.val,atomP W v M j (p y)
  rw [contracts,Complex.norm_real,Real.norm_eq_abs]; change |ZZ y| ≤ Tilt.banner L y.2
  by_cases hh: ZZ y≠0
  · apply le_trans (b:=f) ?_ (HZ y.2 ?_)
    · unfold ZZ f; rw [abs_prod]; apply prod_le_prod (fun i _=> abs_nonneg _); rintro (j|j|j) hj
      · apply (le_div_iff₀ hf).mpr; rw [mul_comm]; exact hp j (p y) hA
      · exact (v.little_sock W H.enrolled.produced.branched j (p y)).trans (le_of_eq (one_mul _).symm)
      exact hM j _ hA
    intro j hj h; exact (prod_ne_zero_iff.mp hh _ (mem_toRight.mp (mem_toLeft.mp hj))) (hu.dust (p y) j hA h)
  rw [not_not.mp hh,abs_zero]; exact Tilt.lamps_up L y.2 hP
omit hu h hx hp hr hl hM in
private lemma payments {ι ψ : Type} [Fintype ψ] [Fintype ι] {g : ι→ℝ} {X : ι→ Support c} {b : BudgetPoint} {m l : ℝ} (d : ψ→ Finset ι) (η : ℝ) (ht : ∀ i,0≤g i) (ha : 0≤η) (hℓ : 0≤l) (hr : Risible b.B m) (hk : Ac.Hit X b.B g (η+1) m) (hh : Injective d) (hu : ∀ i:ψ,Ac.Spark X (d i)):
    let V (i:ψ):= (d i).biUnion X
    Hits V (fun i=>l*∏ j∈d i,g j) b η (l*(Real.exp m-1)):= by
  intro V i
  let U := Ac.roots X b.B g η i
  have haP := Ac.forest X _ ha ht hk hr.grain hr.day i
  let t' := univ.filter fun j:ψ=> i∈V j
  have hz : (∑ i∈t',U (d i)) ≤ Real.exp m-1:= by
    rw [← show ∑ j∈ Finset.image d t', U j=∑ i∈ t',U (d i) from Finset.sum_image hh.injOn]; exact budget_sum haP _
  apply le_trans _ (mul_le_mul_of_nonneg_left hz hℓ)
  rw [Finset.mul_sum]; unfold strike
  apply le_of_eq
  refine Finset.sum_congr (Finset.ext fun i=> by simp only [t',mem_filter]) (fun j hj=>?_)
  unfold U Ac.roots
  rw [if_pos (show Ac.Spark _ _∧ _ from ⟨hu j,(mem_filter.mp hj).2⟩)]; unfold alarm V; ring
lemma grants (ht : w≤t) (hm : Ac.Hit (scarf (S:=S) (x:=x)) B fee (e+1) H₀) (ha : 0 ≤ e) (hb : Risible B H₀) :
    ∃ z, (∀ i:K, (T i).Wares v.things r l (z i)) ∧ Hits (fun i:K => (T i).zone) z v.bp e (l*(Real.exp H₀-1)):= by
  exact ⟨_,invested H M O J N h hx hp hr hl hM hu ht,payments (X:=scarf) (fun i:K=>i.val) e (fun i=> prices_nn J N h hx (lt_of_lt_of_le (Real.exp_pos _) ht).le i) ha (zero_le_one.trans hl) hb hm Subtype.val_injective (fun i=> i.property.1)⟩
end YM.PhysicalNext.InteractingRank.Pump.Grid
