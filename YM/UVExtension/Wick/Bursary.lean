import YM.UVExtension.Wick.Strip

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {x y γ W μ δ e : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R}
def stalk (Q:YM.ConnectedActivityE6.Target G P) {γ : ℝ} (h : Q.rate≤γ) (hγ : γ<0) : YM.ConnectedActivityE6.Target G P :=
    {Q with rate:=γ, start:=Q.start.trans_le h, stop:=hγ}
def chimney (A : Stores S) (b : ℝ) (G : Gauge) (L : Side) (x : ℝ) := Real.exp (b*Delay.bill G L x^5*A.shares)
lemma trunkfit (G : Gauge) (L : Side) : ∃ b:ℝ, 0≤b∧∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T:Tube G S) (F : Forest S.ratio) (X:Coat T F), X.x=x → S.patch.L=L →∀ (p: Stores S) (y : ℝ) z, z∈aisle (betaF G x L) → ‖warmth X (z.re) z p y‖≤ Wick.chimney p b G L x := by
  obtain ⟨C,hC,hP⟩:= Census.width_bound G L 10 2
  let t : ℝ:= (Itinerary.density L:ℝ)*C; let d : ℝ:= Fintype.card G.ColorIndex; let b:=t*d/2; have hb:0 ≤ b := by unfold b t d; positivity
  refine ⟨b,hb,?_⟩
  filter_upwards [aisles G L 1 zero_lt_one, Delay.shift_pos G L] with x hx ht c f S T F X hX hL p y z hz
  rw [warmth_size X z _ _ (breath ht hz)]; have hh:= hx c f S ∅ _ hL hz; let I:=X.pens p; let q:= Delay.bill G L x; have hp:1≤q:=Delay.bill_ge ..
  have hY :(I.card:ℝ) ≤ t*q^4*p.shares:= by
    have hy := (Finset.card_le_card (filter_subset (fun i=>i∉F.trunks) (visit p (10*X.B)))).trans (touch_price S (10*X.B) p)
    rw [hL] at hy; change I.card≤ p.shares*_ *Itinerary.density L at hy
    rw [show X.B=radiusB x from congr_arg _ hX] at hy
    apply (Nat.cast_le (α:=ℝ)|>.2 hy).trans
    push_cast; unfold t q
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hP x) (Nat.cast_nonneg (α:=ℝ) p.shares)) (Nat.cast_nonneg (α:=ℝ) (Itinerary.density L))).trans_eq (by ring)
  apply Real.exp_monotone; unfold amber; change I.card*d/2 * _≤ b*q^5*p.shares
  have hv := mul_le_mul_of_nonneg_right hY (show 0≤d from Nat.cast_nonneg _)
  calc
    _ ≤ (I.card:ℝ)*d/2:= mul_le_of_le_one_right (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num)) hh.2.1
    _ ≤ _ := ((div_le_div_of_nonneg_right hv (by norm_num : (0:ℝ)≤2))).trans (le_trans (le_of_eq (by unfold b; ring : t*q^4*(p.shares:ℝ)*d/2=b*q^4*p.shares)) (by gcongr; omega))
lemma growfit (b c : ℝ) (p : Stores S) : Wick.chimney p b G L x * steamP S (Q.costs L μ u x c) p=steamP S (Q.costs L μ u x (c+b)) p := by
  unfold Wick.chimney steamP Target.costs Buy.quote Packets.income; dsimp only; rw [one_mul,one_mul,← Real.exp_add]; congr 1; ring
section sum
variable {c : Side} {ι K : Type} [Fintype K] {X : ι → Support c} {w z : ι → ℝ} {d : ι → ℕ} {b : ℕ}
lemma sales_plus (h : Sales b a e X w d v) (hk : Sales b a e X z d u) : Sales b a e X (fun i=> w i+z i) d (v+u) := by
  refine ⟨fun i=> add_nonneg (h.nonneg i) (hk.nonneg i),fun i=>?_⟩; convert budget_plus (h.hit i) (hk.hit i) using 2 with x; unfold tariff; split <;> ring
omit [Fintype K] in
lemma sales_total {w : K→ι→ℝ} {u : K→ℝ} (H : Finset K) (hp : ∀ i∈H,Sales b a e X (w i) d (u i)) : Sales b a e X (fun x=> ∑ i∈H,w i x) d (∑ i∈H,u i):= by
  induction H using Finset.induction_on with
  | empty =>
    simp only [sum_empty]; refine ⟨fun i=>le_rfl,fun x=>?_⟩; simp [tariff, SumBudget]
  | insert i H h hh => simp_rw [Finset.sum_insert h]; exact sales_plus (hp i (mem_insert_self ..)) (hh fun i hi=> hp i (mem_insert_of_mem hi))
end sum
variable {ι : Type} [Fintype ι]
-- combined weak Account. Amplitude chosen post actual Roll but η reserve before L. NOT pre-sum per volume.

/-- generic combinations of optional tolls. `Combined` uses relaxed scalar power but
    no new incoming width requirements. -/
lemma indulgent (P : Teller G) (L : Side) (Q : YM.ConnectedActivityE6.Target G P) (γ e t:ℝ)
    (C : ℕ) (h : 0<e) (he : e + Q.rate < γ) :
    ∀ᶠ x in atTop, ∀ (c f : Side) (S:StepData c f) (T:Tube G S) (R:Rep G f) (Z : Type) [Fintype Z],
    Fintype.card Z=C → let B:=radiusB x; let Δ:=betaF G x L^e; let X:= footprints T R Q.halo B; let u:Alphabet c f→ℕ:= Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)
    ∀ w (v:Z→Alphabet c f→ℝ), Sales B Q.relative Q.ε X w u (Q.goal L x) → (∀ i, Sales B Q.relative Q.ε X (v i) u (Q.goal L x)) →
      Sales B Q.relative Q.ε X (fun i=> |t| *(2*w i+Δ*∑ j,v j i)) u (betaF G x L^γ) := by
  have h : Rate G L (e+Q.rate) (fun x=> |t| *(2* Q.goal L x+betaF G x L^e * (↑C * Q.goal L x))) := by
    exact ((((Rate.power (a:=Q.rate)|>.mul_left 2).weaken (le_add_of_nonneg_left h.le)).add (Rate.power.mul (Rate.power.mul_left _))).mul_left _)
  filter_upwards [h γ he, Delay.shift_pos G L] with x hx hD c f S T R Z _ hC B Δ X u w v hp hv
  have hQ:0≤Δ:= by unfold Δ; positivity
  have hW:= sales_total univ (fun i _=> hv i)
  rw [sum_const,card_univ,hC,nsmul_eq_mul] at hW
  have h := sales_plus (hp.shift (z:=fun i=>2*w i) (by norm_num : (0:ℝ) ≤2) (fun i=> mul_nonneg (by norm_num) (hp.nonneg i)) (fun _=>le_rfl))
    (hW.shift hQ (fun i=>mul_nonneg hQ (hW.nonneg i)) (fun _=>le_rfl))
  exact (h.shift (abs_nonneg _) (fun i=>mul_nonneg (abs_nonneg _) (h.nonneg i)) (fun _=>le_rfl)).raise ((le_abs_self _).trans hx)

section emission
variable (H : Cash W x μ L Q o a T R) (V : ι → Juice G f)

def platK {A : Type*} (f:A→ℝ) (g:ι→ A→ℝ) (D : ℝ) (i:A) := 2*f i+D*∑ j,g j i
variable (hv:R.beta=β.re) (V' : ∀ j:ι,Cash W x μ L Q o a T (chunk R (V j) R.beta))
variable {B : ℝ}
variable (v : ι→ℂ) (ht : ∀ i, ‖v i‖ ≤B) (z : Air f G) {X}
include ht hv
lemma draws (hβ:‖β‖ / β.re≤2) (hp:X.x=x) (hm:X.width=o.K) (h:X.manifest) (i : LogIndex c f) (hB :0≤B) :
    ‖logRay X R V o.a Q.table z β v i‖ ≤ platK H.w (fun j=> (V' j).w) B i := by
  have he : 0<R.beta:=H.laws.intake.positive
  let L p:= platK H.w (fun j=> (V' j).w) B p
  rw [(loftR X V R (a:=o.a) 0 1 β he v i|>.1)]; split
  next hx =>
    apply (norm_sum_le ..).trans
    apply le_trans _ (le_add_of_nonneg_left (show 0≤2*H.w i from mul_nonneg (by norm_num) (H.fares.nonneg (.inr (.inl i)))))
    rw [mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; rw [norm_mul]; exact mul_le_mul (ht j) (by rw [Complex.norm_real]; exact ((V' j).quotes _ X hp hm h|>.2.1 i _).1) (norm_nonneg _) hB
  next hx =>
    rw [show flight R R.beta=R from rfl,norm_mul,Complex.norm_real]
    apply le_trans _ (le_add_of_nonneg_right (mul_nonneg hB (Finset.sum_nonneg fun j (_:j∈(Finset.univ:Finset ι))=> show 0≤(V' j).w i from (V' j).fares.nonneg (.inr (.inl i)))))
    refine mul_le_mul ?_ ((H.quotes _ X hp hm h|>.2.1 i _).1) (norm_nonneg _) (by norm_num)
    split
    · rw [norm_div,Complex.norm_real,Real.norm_of_nonneg he.le,hv]; exact hβ
    rw [norm_one]; norm_num
end emission
end YM.UVExtension.Wick
