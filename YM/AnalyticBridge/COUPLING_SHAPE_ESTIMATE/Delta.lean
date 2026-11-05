import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Covariant
import YM.Push.ABSOLUTE_SUMS.Basic


/-!
# Δ from the actual pre-reset local readings 

Independent of the scalar probe. Estimate even with wraps/skipped addresses.
Covariance at each anchor, not of independently fitted representatives.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} {P : Activities G n} {p : BudgetPoint} {δ : ℝ}

def shelf (P : Activities G n) (x : Site n) (i : ℕ) : Form G := if x=(P.reg i).site then stripJet (P.E i) x (P.reg i).support else 0

def screen (P : Activities G n) (x : Site n) := ∑' i, shelf P x i

def probePair : PlaqAxes := ⟨(0,1),by decide⟩

def delta (P : Activities G n) (u : G.Color) := let A : Flux G := Pi.single probePair u; screen P 0 A A

structure Profiled (P : Activities G n) (p : BudgetPoint) (δ : ℝ) : Prop where
  smooth i : p.Regular (P.reg i).support (P.E i)
  bound : P.EBound p δ
  moves s z : Nonempty (P.Moves s z)

lemma Profiled.screen_budget (hs : G.Simple) (h : Profiled P p δ) (x : Site n) : SumBudget (fun i => ‖shelf P x i‖) (96/p.threshold^2 * δ) := by
  obtain ⟨b,hb,hB⟩:=h.bound
  have ht := p.threshold_pos
  apply budget_mono (budget_scale (show 0 ≤ 96/p.threshold^2 by positivity) (hB x)) (fun i : ℕ => norm_nonneg (shelf P x i)) fun i => ?_
  unfold shelf; split
  next he =>
    rw [if_pos he.symm,he]
    refine (strip_bill hs (h.smooth i) _ (hb i)).trans ?_
    exact mul_le_mul_of_nonneg_left (p.loMass _ _ (hb i).1) (by positivity)
  next he => simp only [if_neg (Ne.symm he),mul_zero]; exact (@norm_zero (Form G) _).le

lemma shelf_read (hs : G.Simple) (h : Profiled P p δ) (x : Site n) (A B) : screen P x A B=∑' i, shelf P x i A B := by
  let L := ContinuousLinearMap.apply ℝ (Flux G→L[ℝ] ℝ) A
  let R := ContinuousLinearMap.apply ℝ ℝ B
  have hc : Summable (shelf P x) := Summable.of_norm (f:=shelf P x) (Profiled.screen_budget hs h x).2.1
  exact (R.comp L).map_tsum hc

lemma screen_spin (s : Signed) (z : Site n) (hs : G.Simple) (hn : 10 < n.val) (h : Profiled P p δ) (o) (x y : Flux G) :
    screen P (affine s z o) x y=screen P o (swivels G s x) (swivels G s y) := by
  obtain ⟨J⟩:=h.moves s z; rw [shelf_read hs h,shelf_read hs h,← J.ep.tsum_eq (fun i => _)]
  refine tsum_congr fun i => ?_; simp only [shelf,J.reg_site]
  have he : Injective (affine s z) := fun x y h => s.act_injective (add_right_cancel h)
  by_cases hv : o=(P.reg i).site
  · rw [if_pos (congr_arg (affine s z) hv),if_pos hv,hv]
    have hh : P.E (J.ep i) = P.E i ∘ pull s z := funext (J.valuesE i)
    rw [J.reg_support i, hh]; apply strip_via_pull s z hn hs (h.smooth i)
    rw [← J.reg_support,← hh]; exact h.smooth _
  simp [he.eq_iff,hv]

lemma screen_color (hs : G.Simple) (h : Profiled P p δ) (u : G.El) (x : Site n) (A B : Flux G) :
    screen P x (dye u A) (dye u B)=screen P x A B := by
  rw [shelf_read hs h,shelf_read hs h]; refine tsum_congr fun i => ?_; unfold shelf; split
  · exact strip_color hs (h.smooth i) u _ _ _
  simp

lemma screen_site (hs : G.Simple) (hn : 10 < n.val) (h : Profiled P p δ) (x : Site n) (A B : Flux G) :
    screen P x A B=screen P 0 A B := by
  have he (A : Flux G) : swivels G 1 A=A := by
    ext1 i; let a:=i.val.1; let b:=i.val.2; have hp := i.property
    change parityPrice 1 i • A (PlaqAxes.rotate ..)=_
    simp [parityPrice, StressFlux.sign, PlaqAxes.rotate, PlaqAxes.ordered,hp,hp.le]
  simpa [affine,he] using screen_spin 1 x hs hn h 0 A B

private lemma pivot (s : Signed) (p : PlaqAxes) (u : G.Color) :
    swivels G s (Pi.single (PlaqAxes.transform s p) u)=parityPrice s p • Pi.single p u := by
  funext i
  change parityPrice s i • ((Pi.single (PlaqAxes.transform s p) u : Flux G) (PlaqAxes.transform s i)) = parityPrice s p • (Pi.single p u : Flux G) i
  by_cases hi : i=p
  · subst i; simp
  simp [hi]

private lemma rotate_mirror (u : Axis) (p : PlaqAxes) : PlaqAxes.transform (Signed.mirror u) p = p := by
  change PlaqAxes.rotate _ p=p
  simp [PlaqAxes.rotate,PlaqAxes.ordered, Signed.mirror,p.property.le]

private lemma mirror_pays (u : Axis) (p : PlaqAxes) : parityPrice (Signed.mirror u) p = if u=p.val.1 ∨ u=p.val.2 then -1 else 1 := by
  by_cases h : u=p.val.1
  · subst u; simp [parityPrice,Signed.mirror,StressFlux.sign, p.property,p.property.ne]
  by_cases H : u=p.val.2 <;> simp [parityPrice,Signed.mirror,StressFlux.sign, p.property,H,h,p.property.ne']

private lemma omit_axis {i j : PlaqAxes} (h : i≠j) : ∃ u : Axis, (u=i.val.1 ∨ u=i.val.2) ∧ ¬ (u=j.val.1 ∨ u=j.val.2) := by
  by_contra! he
  rcases i with ⟨⟨a,b⟩,hi⟩; rcases j with ⟨⟨c,d⟩,hj⟩
  have ha : a=c∨a=d := he a (Or.inl rfl)
  have hb : b=c∨b=d := he b (Or.inr rfl)
  change a<b at hi; change c<d at hj
  rcases ha with rfl|rfl <;> rcases hb with ha|hb <;> (subst_eqs; first | exact h rfl | exact (lt_irrefl _ hi) | exact (lt_asymm hi hj))

private lemma cancels (hs : G.Simple) (hn : 10 < n.val) (h : Profiled P p δ) (i j : PlaqAxes) (hv : i≠j) (x y : G.Color) :
    screen P 0 (Pi.single i x) (Pi.single j y)=0 := by
  obtain ⟨u,hu,hp⟩:=omit_axis hv
  let s:=Signed.mirror u
  have hx:=pivot s i x; have hy:= pivot s j y
  simp only [s,rotate_mirror, mirror_pays, if_pos hu, if_neg hp, neg_one_smul, one_smul] at hx hy
  have H := screen_spin s 0 hs hn h 0 (Pi.single i x) (Pi.single j y)
  simp only [hx,hy,s,affine,Signed.act_zero,add_zero,map_neg, neg_apply] at H; linarith

private lemma acts_transitive (p q : PlaqAxes) : ∃ s : Signed, PlaqAxes.transform s p=q ∧ parityPrice s p=1 := by
  let f : Equiv.Perm Axis := Equiv.swap p.val.1 q.val.1
  let g := f.trans (Equiv.swap (f p.val.2) q.val.2)
  have hv : f p.val.1=q.val.1 := Equiv.swap_apply_left ..
  have hw : q.val.1 ≠ f p.val.2 := hv ▸ f.injective.ne p.property.ne
  have he : g p.val.1=q.val.1 := by simp [g,hv,Equiv.swap_apply_of_ne_of_ne hw q.property.ne]
  have hh : g p.val.2=q.val.2 := by simp [g]
  let s : Signed := ⟨g,fun _ => false⟩
  refine ⟨s,?_,?_⟩
  · change PlaqAxes.rotate s p=q; simp [PlaqAxes.rotate,PlaqAxes.ordered,s,he,hh,q.property.le]
  simp [parityPrice,StressFlux.sign,s,he,hh,q.property]

private lemma colored_block (hs : G.Simple) (h : Profiled P p δ) :
    ∃ d : ℝ, ∀ x y : G.Color, screen P 0 (Pi.single probePair x) (Pi.single probePair y)= d*⟪x,y⟫_ℝ := by
  let l := (LinearMap.single ℝ (fun _ : PlaqAxes => G.Color) probePair).toContinuousLinearMap
  let m := (((screen P 0) ∘L l).flip ∘L l).flip
  let B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x => m x)
    (fun x y z => by simp) (fun a x y => by simp) (fun x y z => by simp) (fun a x y => by simp)
  have he (u : G.El) (x : G.Color) : l (G.adjoint u x) = dye u (l x) := by
    funext i; by_cases hi : i=probePair <;> change (Pi.single probePair (G.adjoint u x) : Flux G) i = G.adjoint u ((Pi.single probePair x : Flux G) i) <;> simp [hi]
  have hb : Maxwell.Free.irreduc₂ B := fun u x y => by
    change screen P 0 (l _) (l _) = screen P 0 (l _) (l _)
    simp_rw [he]; exact screen_color hs h ..
  exact Maxwell.Free.invariant_two hs B hb

lemma screen_trace (hs : G.Simple) (hn : 10 < n.val) (h : Profiled P p δ) (x : Site n) (u : G.Color) (hu : ‖u‖=1)
    (A B : Flux G) : screen P x A B=delta P u * ∑ i, ⟪A i,B i⟫_ℝ := by
  obtain ⟨d,hd⟩ := colored_block hs h
  have hg : delta P u=d := by unfold delta; simp only; rw [hd]; simp [hu]
  have he i (a b : G.Color) : screen P 0 (Pi.single i a) (Pi.single i b)=d*⟪a,b⟫_ℝ := by
    obtain ⟨s,h₁,h₂⟩:=acts_transitive probePair i; rw [← h₁, ← hd]
    have H := screen_spin s 0 hs hn h 0 (Pi.single (PlaqAxes.transform s probePair) a) (Pi.single (PlaqAxes.transform s probePair) b)
    simpa only [affine,Signed.act_zero,add_zero,pivot,h₂,one_smul] using H
  rw [hg,screen_site hs hn h,Finset.mul_sum]; conv_lhs => rw [← Finset.univ_sum_single A,← Finset.univ_sum_single B]
  simp only [map_sum, sum_apply]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single i, he]
  · exact fun j _ hj => cancels hs hn h j i hj _ _
  simp




end YM.AnalyticBridge.CouplingShape
