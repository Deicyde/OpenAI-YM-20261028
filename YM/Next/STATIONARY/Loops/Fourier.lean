import YM.Next.STATIONARY.Loops.Syntax


set_option autoImplicit false
/-!
# Lattice memory of the continuous Fourier zero mode

`shop m F` evaluates on EACH new lattice spacing. `stock` (product
normalized additive Haar of `1`-period circle, hence \\int d^4k/(2π)^4`) will feed
stationarity/delay coherence. Exponential bill requires common strip but
not uniform growth assumptions beyond its prechosen cap. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β γ : Type} {m : Side} {q p r : Momentum} {σ A : ℝ}

def shop (m : Side) (F : Momentum→ℂ) := (cents m:ℂ)⁻¹ * ∑ p : Site m,F (mon p)
def stock (F : Momentum→ℂ) := Laurent.market F 0 0

lemma shop_sub (f g : Momentum→ℂ) : shop m (f-g)=shop m f-shop m g := by simp [shop,sum_sub_distrib,mul_sub]

lemma mode_on (m : Side) (x : Cover) : shop m (fun p => mode p x) = if wrap m x=0 then 1 else 0 := by
  unfold shop; simp_rw [← cell_wrap, cell_duality _ (wrap m x)]; split; next h => rw [h]; simp [cents,cell, side_ne]
  next h => rw [sum_cell h,mul_zero]

lemma winds_size (x : Cover) (h : wrap m x=0) (he : x≠0) : m.val ≤ Laurent.size x := by
  obtain ⟨a,k⟩ := cover_of_eq 0 x (by rw [map_zero,h])
  have hx : a≠0 := fun H => he (by rw [k,H,nsmul_zero,add_zero])
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
  have ha : m.val ≤ (x i).natAbs := by
    rw [k,zero_add]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]; exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hi)
  exact ha.trans (Finset.single_le_sum (fun i _ => Nat.zero_le ((x i).natAbs)) (Finset.mem_univ i))

section grid
variable {ι : Type} {f : ι→Momentum→ℂ}
lemma shop_sum (F : Momentum→ℂ) (h : ∀ p : Site m, HasSum (fun i => f i (mon p)) (F (mon p))) : HasSum (fun i => shop m (f i)) (shop m F) := by
  have he (A : Finset (Site m)) : HasSum (fun i => ∑ p∈A, f i (mon p)) (∑ p∈A,F (mon p)) := by
    induction A using Finset.induction with
    | empty => simp
    | insert i l hi IH => simpa only [Finset.sum_insert hi] using (h i).add IH
  exact (he Finset.univ).mul_left _

-- tail near period condition explicitly any coarse wrap
lemma wrap_bill (g : ι→ℂ) (b : ι→Cover) {m : Side} (F : Momentum→ℂ) (σ A : ℝ) (hσ : 0 ≤ σ) (hp : SumBudget (fun i => Real.exp (σ* Laurent.size (b i))*‖g i‖) A)
    (he : ∀ p : Site m,HasSum (fun i => mode (mon p) (b i)*g i) (F (mon p))) :
    ‖shop m F - ∑' i, (if b i=0 then g i else 0)‖ ≤ A * Real.exp (-σ*(m.val:ℝ)) := by
  let H := fun i => if b i=0 then g i else 0
  let Q (i : ι) := shop m (fun p => mode p (b i)*g i)
  have hQ := shop_sum (f:=fun i p => mode p (b i)*g i) F he
  have hm : Summable (fun i => ‖g i‖) := by
    refine hp.2.1.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_)
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
  have hH : Summable H := by
    apply Summable.of_norm
    refine hm.of_nonneg_of_le (fun i => norm_nonneg (H i)) (fun i => ?_); unfold H; split <;> simp
  let t := Real.exp (-σ*m.val)
  let P (i : ι) := Real.exp (σ*Laurent.size (b i))*‖g i‖
  have he (i) : ‖Q i-H i‖ ≤ t*P i := by
    have hv : Q i=g i * shop m (fun p => mode p (b i)) := by unfold Q shop; rw [← Finset.sum_mul]; ring
    rw [hv, mode_on]
    by_cases h : b i=0
    · rw [h,map_zero,if_pos rfl]; simp only [H,h,↓reduceIte,mul_one,sub_self,norm_zero]; unfold t P; positivity
    rw [show H i=0 from if_neg h,sub_zero]
    split
    next H =>
      rw [mul_one, show t*P i=Real.exp (-σ*m.val+σ*Laurent.size (b i))*‖g i‖ by unfold P t; rw [Real.exp_add,mul_assoc]]; apply le_mul_of_one_le_left (norm_nonneg _); apply Real.one_le_exp
      have he : (m.val:ℝ)≤(Laurent.size (b i):ℝ) := by exact_mod_cast winds_size _ H h
      nlinarith
    next H => rw [mul_zero,norm_zero]; unfold t P; positivity
  have HH := hp.2.1.mul_left t
  have hz := HH.of_nonneg_of_le (fun i => norm_nonneg _) he
  change ‖_ - ∑' i, H i‖ ≤ _
  rw [← hQ.tsum_eq]
  change ‖(∑' i,Q i)-(∑' i,H i)‖ ≤ _
  rw [← Summable.tsum_sub (show Summable Q from hQ.summable) hH]
  apply ((norm_tsum_le_tsum_norm hz).trans (hz.tsum_le_tsum he HH)).trans; rw [tsum_mul_left, mul_comm A]
  exact mul_le_mul_of_nonneg_left hp.2.2 (Real.exp_pos _).le
end grid

def royalty (σ A : ℝ) := A*(2*((1+σ/4)/(σ/4)))^(Fintype.card Axis)
lemma Firm.tryout {F : Momentum→ℂ} (h : Firm σ A F) (m : Side) :
    ‖shop m F-stock F‖ ≤ royalty σ A*Real.exp (-(σ/4)*m.val) := by
  have hs := h.width_pos
  have hK := Vane.issues h.1 h.2 (σ/4) (σ/4) (by positivity) (by positivity) (by linarith)
  let g := Laurent.market F 0
  have he (p : Site m) : HasSum (fun x => Laurent.mode (mon p) x * g x) (F (mon p)) := by
    have hx := h.in_range (real_frequency p)
    rw [← h.1.paints h.2 _ hx]; exact (hK.series (mon p) (by
      have hx := Work.F07.realStrip _ (by positivity : 0 < σ/4) (real_frequency p)
      exact fun i => (hx i).le)).2.1.of_norm.hasSum
  convert wrap_bill g id F (σ/4) (royalty σ A) (by positivity) hK he using 3
  simp [stock,g]

lemma mesh_tend (m : ℕ → Side) (hm : Tendsto (fun i => (m i).val) atTop atTop) {σ C : ℝ} (hσ : 0 < σ) :
    Tendsto (fun i => C * Real.exp (-σ*(m i).val)) atTop (𝓝 0) := by
  have H := (Filter.tendsto_const_mul_atBot_of_neg (r:=-σ) (by linarith)).2 (tendsto_natCast_atTop_atTop.comp hm : Tendsto _ _ (atTop : Filter ℝ))
  have h := (Real.tendsto_exp_atBot.comp H).const_mul C
  simpa [Function.comp_def] using h
lemma retail_iter {w : ℕ → ℂ} {u : ℂ} (m : ℕ→Side) (hm : Tendsto (fun i => (m i).val) atTop atTop) {σ A : ℝ} (hp : 0<σ)
    (h : ∀ i, ‖w i-u‖ ≤ A * Real.exp (-σ*(m i).val)) : Tendsto w atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]; exact squeeze_zero (fun _ => norm_nonneg _) h (mesh_tend _ hm hp)
lemma Firm.retail (m : ℕ→Side) (hm : Tendsto (fun i => (m i).val) atTop atTop) {F : Momentum → ℂ} (h : Firm σ A F) :
    Tendsto (fun i => shop (m i) F) atTop (𝓝 (stock F)) := retail_iter _ hm (div_pos h.width_pos (by norm_num : 0<(4:ℝ))) (fun i => h.tryout _)

end YM.Stationary
end

/-!
# Integral limits have analytic strips.

Project a joint periodic strip in `Phase (α ⊕ Axis)` to α via orthogonality;
sup bound by testing contour real average. Needed also if pointwise derivative
outcomes at finite volume only have local analyticity; the filmed quadratic
uses this independent *auxiliary translation-invariant strip*, which allows
quantitative estimates uniformly in those periods. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators
variable {α : Type} [Fintype α] {p : Phase α} {q : Momentum} {σ η A : ℝ}

-- Coarse k characters tied to mesh via the cells. `Album` packs
-- incoming and external phase
abbrev Album (α : Type) := α ⊕ Axis
def starTrack (f : Phase α → Momentum → ℂ) (p : Phase (Album α)) := f (p ∘ Sum.inl) (p ∘ Sum.inr)
def grip (a : Shift α) : Shift (Album α) := Sum.elim a 0
lemma grip_width {f : Shift (Album α)→ℂ} (he : Width σ A f) : Width σ A (fun a => f (grip a)) := by
  have hx (a : Shift α) : Laurent.size (grip a)=Laurent.size a := by
    unfold Laurent.size; rw [Fintype.sum_sum_type]; simp [grip]
  let P := fun z : Shift (Album α) => Real.exp (σ*Laurent.size z)*‖f z‖
  have hi : Injective (grip (α:=α)) := fun x y h => funext fun i => congr_fun h (.inl i)
  have hy : Summable (fun z => P (grip z)) := (show Summable P from he.2.1).comp_injective hi
  have htc : (∑' z : Shift α,P (grip z))≤A :=
    (Summable.tsum_le_tsum_of_inj (g:=P) grip hi (fun i _ => he.1 i) (fun i => le_rfl) hy (show Summable P from he.2.1)).trans he.2.2
  have H : SumBudget (fun z => P (grip z)) A := ⟨fun _ => he.1 _,hy,htc⟩
  simpa only [Width,P,hx] using H
lemma stock_take (F : Phase α→Momentum→ℂ) (h : Firm σ A (starTrack F)) {p : Phase α} (hp : p∈ strip σ) : Firm σ A (F p) := by
  let f (a : Momentum) := Sum.elim p a
  have hh : Differentiable ℂ f := by
    apply differentiable_pi.mpr; intro j; rcases j with x|x
    exact differentiable_const _
    exact differentiable_apply _
  have hx : F p=starTrack F ∘ f := rfl
  rw [hx]
  refine h.comp f hh h.width_pos (fun p hp' i => Sum.recOn (motive:=fun i => |(f p i).im|<σ) i hp hp') fun p v => ?_
  refine ⟨Sum.elim 0 v,?_⟩; funext i; rcases i with i|i <;> simp [f,reciprocal]

def walent : ℕ→Side := fun i => ⟨i+1,by positivity⟩
lemma walentes : Tendsto (fun i => (walent i).val) atTop atTop := by
  exact tendsto_atTop.2 fun b => by filter_upwards [eventually_ge_atTop b] with i hi; change b ≤ i+1; omega

section choice
variable (F : Phase α→Momentum→ℂ) (h : Firm σ A (starTrack F))
include h
lemma fireworks {b : ℝ} (hb : 0<b) (hx : b<σ) : Firm b A (fun p => stock (F p)) := by
  have hσ : 0<σ := h.width_pos
  let f := Laurent.market (starTrack F) 0
  let K := A*(2*((1+(σ-b)/2)/((σ-b)/2)))^(Fintype.card (Album α))
  have he : Width b K f := (h.1.issues h.2 b ((σ-b)/2) hb.le (by linarith) (by linarith))
  let g a := f (grip a)
  have hg : Firm b K (Laurent.read g) := Firm.of_series (grip_width he) hb
  have hh (p : Phase α) (hp : p∈strip b) : stock (F p)=Laurent.read g p := by
    let J x := mode p ((x : Shift (Album α)) ∘ Sum.inl)*f x
    let R x : Cover := (x : Shift (Album α)) ∘ Sum.inr
    have hx' : p ∈ strip σ := fun i => (hp i).trans hx
    have ht := Firm.retail walent walentes (stock_take F h hx')
    have hm : SumBudget (fun x => Real.exp (b*Laurent.size (R x))*‖J x‖) K := by
      have hu (x : Shift (Album α)) : Real.exp (b*Laurent.size (R x))*‖J x‖ ≤ Real.exp (b*Laurent.size x)*‖f x‖ := by
        have hs : Laurent.size x=Laurent.size (x ∘ Sum.inl)+Laurent.size (R x) := by unfold Laurent.size; rw [Fintype.sum_sum_type]; rfl
        unfold J; rw [norm_mul,hs,Nat.cast_add,mul_add,Real.exp_add,mul_comm (Real.exp (b* Laurent.size (x ∘ Sum.inl))),mul_assoc]; gcongr
        exact reward _ _ _ fun i => (hp i).le
      have h0 x : 0 ≤ Real.exp (b* Laurent.size (R x))*‖J x‖ := by positivity
      exact ⟨h0,he.2.1.of_nonneg_of_le h0 hu, ((he.2.1.of_nonneg_of_le h0 hu).tsum_le_tsum hu he.2.1).trans he.2.2⟩
    have hc (i : ℕ) : ‖shop (walent i) (F p)-∑' v, (if R v=0 then J v else 0)‖ ≤ K*Real.exp (-b*(walent i).val) := by
      refine wrap_bill J R (F p) _ _ hb.le hm fun a => ?_
      let k := mon a
      let q := Sum.elim p k
      have hy : q∈ strip b := fun i => Sum.recOn (motive:=fun i => |(q i).im|<b) i hp (Work.F07.realStrip _ hb (real_frequency a))
      have hw : F p k=Laurent.read f q := (h.1.paints h.2 q (fun i => (hy i).trans hx)).symm
      have hv : HasSum (fun x => mode q x * f x) (Laurent.read f q) := (he.series q (fun i => (hy i).le)).2.1.of_norm.hasSum
      rw [show F p (mon a) = _ from hw]
      convert hv using 1; funext z
      simp only [J,R,mode]; rw [Fintype.sum_sum_type,mul_add,Complex.exp_add]; simp only [q, k, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]; ring
    refine (tendsto_nhds_unique ht (retail_iter _ walentes hb hc)).trans ?_
    let j (v : Shift (Album α)) : ℂ := if R v=0 then J v else 0
    have hi : Injective (grip (α:=α)) := fun x y h => funext fun i => congr_fun h (.inl i)
    have hx : Set.EqOn j 0 (Set.range grip)ᶜ := by
      intro i hi; unfold j; split <;> rename_i he; swap; rfl
      apply False.elim; apply hi
      exact ⟨i ∘ Sum.inl, funext fun x => by cases x with
        | inl a => rfl
        | inr a => exact congr_fun he.symm a⟩
    change (∑' i,j i)=_
    rw [show (∑' v,j v)=_ from (hi.tsum_eq (f:=j) ?_).symm]
    · apply tsum_congr; intro i; unfold j; rw [if_pos (show R (grip i)=0 from rfl)]; rfl
    intro x hp; by_contra h; exact hp (hx h)
  refine ⟨⟨hb,fun p hp => (hg.1.hol _ hp).congr_of_eventuallyEq (by filter_upwards [(Work.F07.stripOpen b).mem_nhds hp] with p hx; exact hh p hx), fun i hi u => ?_⟩,
    fun i hi => ?_⟩
  · rw [hh (i+reciprocal u) (fun j => by simpa [reciprocal] using (hi j)),hh _ hi,hg.1.reset i hi u]
  have hv := stock_take F h (p:=i) (fun j => (hi j).trans hx)
  exact market_cap hv.1 (hv.in_range (by simp)) 0 A hv.2
end choice
end YM.Stationary
end

/-!
# Trace arcs and per-cell calibrated bill for quadratic. Here no curvature
emission, comparison asserts exponential only on EXACT external momentum
mesh (with the strip *uniform for the models* supplied). -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {G : Gauge} {ι α β γ : Type} {m : Side} {q p r : Momentum} {σ η A : ℝ}

section arcs
variable (p q : Momentum)
lemma negResident {p : Momentum} (h : p∈strip σ) : -p ∈ strip σ := fun i => by simpa using h i
lemma canvas {p q : Momentum} (hx : p∈strip σ) (he : q∈strip η) : p+q∈strip (σ+η) := fun i =>
  (show |((p+q) i).im|≤_ from abs_add_le ((p i).im) ((q i).im)).trans_lt (add_lt_add (hx i) (he i))
lemma duo (h : 0<σ) (hp : p ∈ strip (σ/2)) (hq : q∈ strip (σ/2)) : Boulevard σ (-p) p q := by
  have hr : p∈ strip σ := fun i => (hp i).trans (by linarith)
  have he : q∈ strip σ := fun i => (hq i).trans (by linarith)
  have H := canvas hq hp; have H' := canvas hq (negResident hp); rw [add_halves] at H H'
  exact ⟨⟨negResident hr,he,H'⟩,⟨hr,he,H⟩,by simpa⟩

structure Highlights (σ : ℝ) [Fintype α] (f : Phase α → Momentum→ℂ) : Prop where
  eligible {p : Phase α} {q : Momentum} : p∈strip σ→ q∈strip σ → DifferentiableAt ℂ (uncurry f) (p,q)
  rolls {p p' : Phase α} {q q' : Momentum} (hp : rolls p p') (hq : rolls q q') : p∈strip σ → q∈strip σ → f p q=f p' q'
-- needs Fintype α for topology
lemma highlights [Fintype α] {f : Phase α→Momentum→ℂ} (h : Highlights σ f) (hp : 0<σ) (he : ∀ p∈ strip σ, ∀ q∈strip σ, ‖f p q‖ ≤ A) : Firm σ A (starTrack f) := by
  refine ⟨⟨hp,fun i hi => ?_, fun i hi u => ?_⟩,fun i hi => he _ (fun j=> hi (.inl j)) _ (fun j=> hi (.inr j))⟩
  · let G := fun z : Phase (Album α) => (z ∘ Sum.inl,z ∘ Sum.inr)
    refine (h.eligible (p:=G i|>.1) (q:=G i|>.2) (fun j => hi (.inl j)) (fun j => hi (.inr j))).comp (f:=G) _ ?_
    exact (DifferentiableAt.prodMk (differentiableAt_pi.mpr (fun j => differentiableAt_apply (Sum.inl j) _)) (differentiableAt_pi.mpr (fun j => differentiableAt_apply (Sum.inr j) _)))
  apply Eq.symm; refine h.rolls ?_ ?_ (fun j => hi (.inl j)) (fun j => hi (.inr j))
  · exact ⟨u ∘ Sum.inl,rfl⟩
  exact ⟨u ∘ Sum.inr,rfl⟩
end arcs

variable [Fintype α] [DecidableEq α]

namespace Film
def framePay (F : Film ι α α) (i j : ι) (p q r : Momentum) := F.coupon (r+(p+q)) * F.arch i j p q r -
    (((F.coupon (r+(p+q))*F.spot i p (r+q))*F.coupon (r+q))*F.spot j q r)

def figure (F : Film ι α α) (i j : ι) (p q : Momentum) := (F.framePay i j (-p) p q).trace
end Film
namespace Play
lemma pose {F : Film ι α α} (h : Play F σ) (hp : ∀ p∈strip σ, IsUnit (F.tab p).det) (i j) : Stagehand σ (F.framePay i j) := by
  refine ⟨fun w => ?_,fun h1 h2 h3 w => ?_⟩
  · rename_i p q r
    let z := (p,q,r)
    let X := Momentum × Momentum × Momentum
    let f : X → Momentum := Prod.fst; let g : X→ Momentum := fun a => a.2.1; let m : X → Momentum := fun a => a.2.2
    have hf : DifferentiableAt ℂ f z := differentiableAt_fst
    have hg : DifferentiableAt ℂ g z := differentiableAt_fst.comp z differentiableAt_snd
    have hm : DifferentiableAt ℂ m z := differentiableAt_snd.comp z differentiableAt_snd
    have ht : Poster σ F.coupon := (h.back hp).tab
    have H := ht.go (x:=z) w.total (hm.add (hf.add hg)); have J := ht.go (x:=z) w.second.added (hm.add hg)
    exact BillD.less (H.bond ((h.arch i j).shape w)) (((H.bond ((h.spot i).go w.proceed hf (hm.add hg))).bond J).bond ((h.spot j).go w.second hg hm))
  simp only [Film.framePay,Film.coupon,h.tab.shifts (h3.plus (h1.plus h2)) w.total,h.tab.shifts (h3.plus h2) w.second.added,(h.arch i j).shifts h1 h2 h3 w,(h.spot i).shifts h1 (h3.plus h2) w.proceed,(h.spot j).shifts h2 h3 w.second]

lemma estate {F : Film ι α α} (h : Play F σ) (hσ : 0<σ) (hp : ∀ p∈ strip σ, IsUnit (F.tab p).det) (i j) : Highlights (σ/2) (F.figure i j) := by
  let a := F.framePay i j
  have y := h.pose hp i j
  refine ⟨fun he hr => ?_,fun h1 h2 he hw => ?_⟩
  · rename_i p q
    exact BillD.collects (y.go (p:=fun z : Momentum × Momentum => -z.1) (q:=Prod.fst) (r:=Prod.snd) (x:=(p,q)) (duo _ _ hσ he hr) (by fun_prop) (by fun_prop) (by fun_prop))
  exact congr_arg trace (y.shifts h1.neg h1 h2 (duo _ _ hσ he hw))
end Play

variable [Fintype ι] [DecidableEq ι]

namespace Ticket
variable {F : Film ι α α} {U : OperatorF ι m α α}
lemma receipt (h : Ticket F U) (hx : IsUnit (U 0).det) (a b : Site m) (p q : Momentum) (hp : rolls (mon a) p) (hq : rolls (mon b) q) (i j) :
    beat (fun z => Real.log (U z).det) 0 2 ![relay a i,relay b j]= if a+b=0 then ∑ r : Site m,(F.framePay i j p q (mon r)).trace else 0 := by
  let X := (cardM U)⁻¹
  have ht : Jaunt X F.coupon 0 := h.tab.backway (cash_safe hx)
  have hh := ht.join (h.arch i j a b p q hp hq) (hp.combine hq) (add_zero _)
  have hp' := Jaunt0 (ht.join (h.spot i a p hp) hp (add_zero _)) ht
  let W := ((X*seat U (relay a i))*X)*seat U (relay b j)
  have hq' : Jaunt W (fun r => ((F.coupon (r+(p+q))*F.spot i p (r+q))*F.coupon (r+q))*F.spot j q r) (a+b) := by
    convert hp'.join (h.spot j b q hq) hq (add_comm b a) using 1
    funext r; simp only [add_assoc r, add_comm q]
  rw [trace_scrim h.finance hx]; change _-W.trace=_; rw [← trace_sub,sub_eq_add_neg]; exact (hh.plus hq'.backside).accounting
end Ticket
end YM.Stationary
end

/-! Taylor comparison with the Wilson shape, before the stationary operation -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius RealInnerProductSpace
variable {G : Gauge} {m : Side} {σ A : ℝ}

-- APS strip and rays; even if written using negative momentum, no anti-hol assumption
lemma anti_ancestral {α : Type} [Fintype α] {f : Phase α → ℂ} (hf : Firm σ A f) : Firm σ A (fun x => f (-x)) := by
  refine hf.comp (fun i => -i) (by fun_prop) hf.width_pos (fun i h j => ?_) (fun p x => ⟨-x,?_⟩)
  · simpa using h j
  ext; simp [reciprocal]; ring

lemma pair_firm {f : Momentum → ℂ} (hf : Firm σ A f) : Firm σ A (fun p => f (axisPair p)) := by
  refine hf.comp axisPair ?_ hf.width_pos (fun p hp i => hp _) (fun p x => ⟨x ∘ stick 0,rfl⟩)
  rw [differentiable_pi]; intro i; unfold axisPair projected; simp only [Function.comp_apply]; fun_prop

private lemma common_symbol (hσ : 0 < σ) (i j) : Firm σ (4*(Real.exp σ+1)) (fun p : Momentum => symbol 1 p i j) := strip_symbol (Embedding.refl Axis) hσ i j
lemma price_step_metric {R : FaceRow} (hσ : 0 < σ) (hr : R.strip σ A) (i j) : Firm σ A (fun p : Momentum => R.read p i j) :=
    Firm.of_series (R.constant_strip hr i j) hσ

def bedCharge (σ A : ℝ) := (Fintype.card (TypeFace 2):ℝ)*(Fintype.card (TypeFace 2) * ((4*(Real.exp σ+1))*A))*(4*(Real.exp σ+1))
lemma bedCharge_nonneg (h : 0 ≤ A) : 0 ≤ bedCharge σ A := by unfold bedCharge; positivity
lemma bed_price {B : FaceRow} (hs : 0<σ) (h : B.strip σ A) (i j) : Firm σ (bedCharge σ A)
    (fun p : Momentum => dcross B p i j) := by
  unfold dcross
  simp_rw [Matrix.mul_apply,Matrix.transpose_apply]
  have hh (k : TypeFace 2) := Firm.sum Finset.univ _ _ hs (fun x _ => ((anti_ancestral (common_symbol hs x i)).mul
    (price_step_metric hs h x k)))
  have he := Firm.sum Finset.univ _ _ hs fun x _ => (hh x).mul (common_symbol hs x j)
  convert he using 1
  unfold bedCharge; simp; ring
lemma slots_cost {B : FaceRow} (hs : 0 < σ) (h : B.strip σ A) (i : Ink G 2) b : Firm σ (bedCharge σ A) (slots B G i b) := by
  have hA := (bed_price hs h (b 0) (b 1)).budget_nonneg
  unfold slots; split
  · exact (((Firm.const hs (1/2:ℂ)).mul (pair_firm (bed_price hs h _ _))).mono hs le_rfl
      (mul_le_of_le_one_left hA (by norm_num)))
  exact (Firm.zero hs).mono hs le_rfl hA

lemma rays_total {α β : Type} [Fintype α] [Fintype β] {s : ℕ} {f : β → Corn α → ℂ} (h : ∀ i, Rays s (f i)) : Rays s (fun x => ∑ i,f i x) := fun p => Asymptotics.IsBigO.sum (fun i _ => h i p)

lemma bed_gain {K : ℕ} (B D : FaceRow) (h : ∀ x y, Rays K (fun p : Corn Axis => B.read (axes p) x y-D.read (axes p) x y))
    (b i : TypeFace 1) : Rays (1+K+1) (fun p : Corn Axis => dcross B (axes p) b i - dcross D (axes p) b i) := by
  have he (p : Momentum) : dcross B p b i-dcross D p b i = (((symbol 1 (-p)).transpose*(B.read p-D.read p))*symbol 1 p) b i := by
    rw [Matrix.mul_sub,Matrix.sub_mul]; rfl
  simp_rw [he,Matrix.mul_apply,Matrix.transpose_apply,Matrix.sub_apply]; apply rays_total
  intro d; refine (Rays.mul ?_ (ray_symbol (Embedding.refl Axis) d i))
  apply rays_total
  intro e; refine Rays.mul ?_ (h e d)
  intro p
  have hy := ray_symbol (Embedding.refl Axis) e b (-p)
  simp_rw [smul_neg,axes_flip] at hy; exact hy

lemma bed_rays {B : FaceRow} (hs : 0 < σ) (h : B.strip σ A) (x : Ink G 2) b : Rays 2 (slots B G x b ∘ axes) := by
  unfold slots; split
  · intro p
    have h0 : (fun i j => fun x : Cover => (0:ℝ))= (0:FaceRow) := rfl
    have hv u v : Rays 0 (fun p : Corn Axis => B.read (axes p) u v-(0:FaceRow).read (axes p) u v) := by
      have he p : (0:FaceRow).read p u v=0 := by simp [Row.read,Laurent.read]
      simp_rw [he,sub_zero]; exact rays_zero ((price_step_metric hs h u v).analytic_real 0)
    have hh p : dcross (0:FaceRow) p=0 := by
      unfold dcross
      rw [show (0:FaceRow).read p=0 by ext i j; simp [Row.read,Laurent.read]]; simp
    have hk := bed_gain _ _ hv (b 0) (b 1) (p ∘ stick 0)
    simp_rw [hh,Matrix.zero_apply,sub_zero] at hk; exact hk.const_mul_left _
  intro p; exact isBigO_zero ..

-- Wilson record explicitly

def leader : FaceRow := fun x y v => if v=0 then (1 : Matrix (TypeFace 2) (TypeFace 2) ℝ) x y else 0
lemma leader_safe : Row.safe leader := by
  intro i j
  apply summable_of_ne_finset_zero (s:={0}); intro z hz; unfold leader; split <;> simp_all
lemma leader_pay (σ : ℝ) : Row.strip leader σ 1 := by
  intro i j
  unfold Width leader
  by_cases H : i=j
  · simp only [Matrix.one_apply,H,ite_true]
    refine ⟨fun _ => by positivity,(summable_of_ne_finset_zero (s:={0}) ?_),?_⟩
    · intro b hb; simp_all
    rw [tsum_eq_single (0:Cover)]; all_goals simp_all [Laurent.size]
  simp only [Matrix.one_apply, if_neg H,ite_self,norm_zero,mul_zero]
  exact ⟨fun _ => le_rfl, summable_zero, by simp⟩
@[simp] lemma leader_step (m : Side) : Row.acts leader m=1 := by
  ext ⟨x,i⟩ ⟨y,j⟩
  rw [Row.acts,Matrix.of_apply,tsum_eq_single (0:Cover)]
  · by_cases h : x=y <;> simp [leader,Matrix.one_apply, *,eq_comm]
  intro z hz; simp [leader,hz]
@[simp] lemma leader_const (p : Momentum) : Row.read leader p=1 := by
  ext i j
  rw [Row.read,Matrix.of_apply,Laurent.read,tsum_eq_single (0:Cover)]
  · by_cases h : i=j <;> simp [leader,h, Matrix.one_apply]
  intro z hz; simp [leader,hz]
lemma outright (G : Gauge) (m : Side) : WilsonQ G m 0=0 ∧ fderiv ℝ (WilsonQ G m) 0=0 ∧ Recorded (slots leader G) (WilsonQ G m) 0 := by
  let Q (x y : Link G m) := ∑ i, parts G 1 (arm G m 1 x) i ⬝ᵥ (Precision.K (Row.acts leader m)*ᵥ parts G 1 (arm G m 1 y) i)
  have he (x y : Link G m) : Q x y=∑ j : Face (Per m), inner ℝ (Work.F03.faceCurl j (arm G m 1 x)) (Work.F03.faceCurl j (arm _ _ _ y)) := by
    unfold Q; rw [Precision.K,leader_step,Matrix.mul_one]
    simp_rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Work.F03.inner_color]
    rw [sum_comm]; apply sum_congr rfl; intro i _; rw [← Matrix.dotProduct_mulVec]
    unfold dotProduct; rw [← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site m)) plaqEquiv)]; rfl
  have hh : ContDiffAt ℝ 2 (WilsonQ G m) 0 := Wilson_witness.analytic.contDiffAt
  obtain ⟨h,hX,hY⟩ := Work.F03.hessian_of_limit (Q:=Q) hh (fun x => by
    rw [he]; unfold WilsonQ input Wilson.energy
    simp_rw [map_smul,Finset.sum_div,real_inner_self_eq_norm_sq]; apply tendsto_finsetSum; intro j _
    apply Work.F03.price_limit (V:=fun t : ℝ => faceValue (represent (t • arm G m 1 x)) j) _ (Work.F03.face_deriv j (arm G m 1 x))
    rw [zero_smul]; exact Push.stroll_zero ..) (fun x y z => by unfold Q; simp_rw [map_add,Work.F03.parts_add,add_dotProduct,sum_add_distrib])
    (fun x y => by rw [he,he]; exact sum_congr rfl fun i _ => real_inner_comm ..)
  exact ⟨h,hX,according leader_safe hY⟩
lemma slots_gain {B : FaceRow} (hs : 0<σ) (h : B.strip σ A) (hu : B.read 0=1) (i : Ink G 2) (b) : Rays 3 (fun p : Corn (Keys 1) => (slots B G - slots leader G) i b (axes p)) := by
  simp only [Pi.sub_apply,slots]; split
  · have hp (i j) := price_step_metric hs h i j
    have hv i j : Rays 1 (fun p => B.read (axes p) i j-(Row.read leader (axes p)) i j) := by
      refine (rays_at_zero (AnalyticAt.sub ((hp i j).analytic_real _) ((price_step_metric zero_lt_one (leader_pay 1) i j).analytic_real _))).mpr ?_
      simp [axes_origin,hu]
    intro p; simp_rw [← mul_sub]
    exact (bed_gain B leader hv (b 0) (b 1) (p ∘ stick 0)).const_mul_left _
  intro p; simp only [sub_zero]; exact isBigO_zero ..
end YM.Stationary
end

/-!
# Hessian Fourier settlement. No gauge hypothesis for these trace forms; Lie label
orientation as used by single-period elect, *same* Hessian order. Common
symbol outside fixed-period chart chosen by the stock on the torus; produces
approx. Recorded combinable with any exact (including path) comparison.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {G : Gauge} {m : Side} {σ A ε : ℝ}

section tab
abbrev Award (G : Gauge) := Loc G 1→Loc G 1→Momentum→Momentum→ℂ

/-- actual derivatives in phi-axis momentum of log quadratic. -/
def Awards (f : Award G) (P : Link G m → ℝ) : Prop := ∀ (i j : Loc G 1) (k l : Site m),
    beat P 0 2 ![relay k i,relay l j]= if k+l=0 then (cents m:ℂ)* shop m (f i j (mon l)) else 0
namespace Awards
variable {P Q : Link G m → ℝ} {f g : Award G}
lemma both (h : Awards f P) (he : Awards g Q) (hp : AnalyticAt ℝ P 0) (hq : AnalyticAt ℝ Q 0) : Awards (f+g) (P+Q) := by
  intro i j k l; rw [beat_as_cost, note_add hp hq,smul_add,← beat_as_cost,← beat_as_cost,_root_.add_apply,h,he]; split <;> simp [*, shop, Finset.sum_add_distrib,mul_add]
lemma rebate (h : Awards f P) (hp : AnalyticAt ℝ P 0) (c : ℝ) : Awards ((c:ℂ) • f) (c • P) := by
  intro i j k l; rw [beat_as_cost,note_bill c hp _,smul_comm, ← beat_as_cost,_root_.smul_apply,h]; split <;> simp [*,shop,mul_left_comm,Finset.mul_sum]
lemma less (h : Awards f P) (he : Awards g Q) (hp : AnalyticAt ℝ P 0) (hq : AnalyticAt ℝ Q 0) : Awards (f-g) (P-Q) := by
  simpa only [sub_eq_add_neg, neg_one_smul,Complex.ofReal_neg, Complex.ofReal_one] using h.both (he.rebate hq (-1)) hp hq.const_smul
lemma carry (h : Awards f P) (he : iteratedFDeriv ℝ 2 Q 0= iteratedFDeriv ℝ 2 P 0) : Awards f Q := by
  intro i j k l; rw [← h]; simp only [beat,he]
end Awards

namespace Ticket
variable {α : Type} [Fintype α] [DecidableEq α] {U : OperatorF (Loc G 1) m α α} {F : Film (Loc G 1) α α}
lemma award (h : Ticket F U) (he : IsUnit (U 0).det) : Awards F.figure (fun z => Real.log (U z).det) := by
  intro i j a b; by_cases hp : a+b=0
  · have hh : rolls (mon a) (-mon b) := by rw [eq_neg_of_add_eq_zero_left hp]; exact (rolls.refl _).flip_sign
    rw [h.receipt he a b _ _ hh (rolls.refl _) i j,if_pos hp,if_pos hp, shop, mul_inv_cancel_left₀ (show (cents m:ℂ)≠0 from by exact_mod_cast cents_pos.ne')]; rfl
  rw [h.receipt he a b _ _ (rolls.refl _) (rolls.refl _) i j,if_neg hp,if_neg hp]
end Ticket

def profitable (f : Award G) : Picture G 1 := fun i j p => (2:ℂ)⁻¹*stock (f (j 0,i 0) (j 1,i 1) (axisPair p))
lemma profit (F : Award G) (hs : 0<σ) (hA : 0≤A) (hp : ∀ i j,Firm σ A (starTrack (F i j))) :
    let T := profitable F
    (∀ i j,Firm (σ/2) A (T i j)) ∧ ∀ (m : Side) (P : Link G m→ℝ), Awards F P →
      Recorded T P (cents m*(royalty σ A*Real.exp (-(σ/4)*m.val))) := by
  intro T
  have hz : 0 ≤ royalty σ A := by unfold royalty; positivity
  have h : 0<σ/2 := by positivity
  refine ⟨fun i j => ?_,fun m P he u i j => ?_⟩
  · let v : Fin 2 → Loc G 1 := fun a => (j a,i a)
    have hx := pair_firm (fireworks (F (v 0) (v 1)) (hp _ _) h (by linarith))
    exact ((Firm.const h (2:ℂ)⁻¹).mul hx).mono h le_rfl (mul_le_of_le_one_left hA (by norm_num))
  let v : Fin 2→Loc G 1 := fun a => (j a,i a)
  let x := F (v 0) (v 1)
  let q := mon (u 1)
  let g := T i j (outphase u)
  have hv := (stock_take x (hp _ _) (Work.F07.realStrip _ hs (real_frequency (u 1)))).tryout m
  have ht : g=(2:ℂ)⁻¹ * stock (x q) := rfl
  rw [noteAt,_root_.smul_apply,collected, Fin.sum_univ_two u]
  have hu : beat P 0 (1+1) (glyph u i j)= if u 0+u 1=0 then (cents m:ℂ)*shop m (x q) else 0 := by
    rw [show glyph u i j= ![relay (u 0) (v 0),relay (u 1) (v 1)] by funext k; fin_cases k <;> rfl]; exact he ..
  rw [hu]
  have hh : 0≤cents m := cents_pos.le
  split
  next he =>
    rw [show T i j (outphase u)=_ from ht]
    rw [show Nat.factorial (1+1)=2 from rfl]; simp only [Nat.cast_ofNat, smul_eq_mul, show (↑(Fintype.card (Site m)):ℂ)=(cents m:ℂ) by simp [cents]]
    rw [mul_left_comm, ← mul_sub, ← mul_sub,norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left (le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)) hv) hh
  next he => simp only [smul_zero,sub_self,norm_zero]; positivity
end tab
end YM.Stationary
end
