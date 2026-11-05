import YM.AnalyticNext.CUBIC_MATCH.Lift.Cubic
import YM.AnalyticNext.CUBIC_MATCH.Lift.Descend
import YM.AnalyticNext.CUBIC_MATCH.Ward
import YM.Next.FREE_KERNELS.Amend
import YM.Progress.STATIONARY_SCENES.Frames


set_option warningAsError false

/-!
# Reading the period coefficient tensor

Unnormalized translation sums. Test all inputs, on the real unmasked
fields; periods need not divide one another. The color action is on the
*whole* tensor. Equality of the trilinear readouts at these periods, not
imaginary momentum comparison, now suffices to earn an invariant lift at
accountable costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Filter Function Lattice Laurent Bloch Exterior Lift RG Precision Wilson Tree Bid
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {r s t : ℕ} {n : Side} {η C : ℝ}

/-- Color coefficient per column. Not necessarily symmetric. -/
abbrev Shades (G : Gauge) := Tensor.T G.Color ℝ 3

namespace Shades
variable (T : Shades G)

def start (y z : G.Color) := T.toContinuousLinearMap (![0,y,z]) 0

def mid (x z : G.Color) := T.toContinuousLinearMap (![x,0,z]) 1

def last (x y : G.Color) := T.toContinuousLinearMap (![x,y,0]) 2

lemma starts (x y z : G.Color) : T ![x,y,z]=T.start y z x := by
  unfold start
  change _=T _; congr 1; ext1 i; fin_cases i <;> simp
lemma mids (x y z : G.Color) : T ![x,y,z]=T.mid x z y := by
  unfold mid
  change _=T _; congr 1; ext1 i; fin_cases i <;> simp
lemma lasts (x y z : G.Color) : T ![x,y,z]=T.last x y z := by
  unfold last
  change _=T _; congr 1; ext1 i; fin_cases i <;> simp

end Shades

lemma d_step (x : fieldDir G n r) (i) : dColor G n r x i=∑ j, d r n i j • x j := by
  let L (k : G.ColorIndex) := PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) k
  ext u; change _=L u _
  rw [map_sum]; simp_rw [map_smul]; rfl

/-- Real trilinear periodic read. -/
def pair3 (K : Three (Shades G) r s t) (x : fieldDir G n r) (y : fieldDir G n s)
    (z : fieldDir G n t) := ∑ i, ∑ j, ∑ a, acts n K i j a ![x i,y j,z a]

lemma againstX {K : Three (Shades G) (r+1) s t} (h : Pace η C K) (he : 0<η) (x : fieldDir G n r) (y z) :
    pair3 K (dColor G n r x) y z=pair3 (δx K) x y z := by
  unfold pair3; simp_rw [downX h he]
  simp only [sum_apply,smul_apply]
  conv_lhs => simp only [Shades.starts,d_step,map_sum,map_smul]
  conv_rhs => simp only [Shades.starts]
  conv_lhs => arg 2; intro a; arg 2; intro b; rw [Finset.sum_comm]
  conv_lhs => arg 2; intro a; rw [Finset.sum_comm]
  conv_rhs => arg 2; intro a; arg 2; intro b; rw [Finset.sum_comm]
  conv_rhs => arg 2; intro a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
lemma againstY {K : Three (Shades G) r (s+1) t} (h : Pace η C K) (he : 0<η) (x) (y : fieldDir G n s) (z) :
    pair3 K x (dColor G n s y) z=pair3 (δy K) x y z := by
  unfold pair3; simp_rw [downY h he]
  simp only [sum_apply,smul_apply]; conv_lhs => simp only [Shades.mids,d_step,map_sum,map_smul]
  conv_rhs => simp only [Shades.mids]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => arg 2; intro a; rw [Finset.sum_comm]
  conv_rhs => arg 2; intro a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
lemma againstZ {K : Three (Shades G) r s (t+1)} (h : Pace η C K) (he : 0<η) (x y) (z : fieldDir G n t) :
    pair3 K x y (dColor G n t z)=pair3 (δz K) x y z := by
  unfold pair3; simp_rw [downZ h he]
  simp only [sum_apply,smul_apply]
  conv_lhs => simp only [Shades.lasts,d_step,map_sum,map_smul]
  conv_rhs => simp only [Shades.lasts]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
lemma against_three {K : Three (Shades G) 2 2 2} (h : Pace η C K) (he : 0<η) (x y z : Dir G n) :
    pair3 K (dColor G n 1 x) (dColor G n 1 y) (dColor G n 1 z)=pair3 (completely K) x y z := by
  rw [againstX h he,againstY (h.x he.le) he,againstZ ((h.x he.le).y he.le) he]

lemma pair_read (K : Three (Shades G) r s t) (x y z : G.Color) (i j k : _) :
    pair3 (n:=n) K (Pi.single i x) (Pi.single j y) (Pi.single k z) = acts n K i j k ![x,y,z] := by
  unfold pair3; rw [Finset.sum_eq_single i]; swap
  · intro b _ hb; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro c _
    rw [Pi.single_eq_of_ne hb]; exact (acts n K _ _ _).map_coord_zero 0 rfl
  swap; · simp
  rw [Finset.sum_eq_single j]; swap
  · intro b _ hb; apply Finset.sum_eq_zero; intro c _
    rw [Pi.single_eq_of_ne hb]; exact (acts n K _ _ _).map_coord_zero 1 rfl
  swap; · simp
  rw [Finset.sum_eq_single k]; swap
  · intro b _ hb; rw [Pi.single_eq_of_ne hb]; exact (acts n K _ _ _).map_coord_zero 2 rfl
  swap; · simp
  rw [Pi.single_eq_same,Pi.single_eq_same,Pi.single_eq_same]

lemma eta_three {E : Type*} (v : Fin 3 → E) : v=![v 0,v 1,v 2] := funext fun i => by fin_cases i <;> rfl

lemma literal {K : Three (Shades G) r s t} (h : Pace η C K) (he : 0<η) (z : ℕ → Side)
    (hz : Tendsto (fun i => (z i).val) atTop atTop) (i j a : _) (x : Couple) :
    Tendsto (fun p => acts (z p) K (wrap (z p) x.1,i) (wrap (z p) x.2,j) (0,a)) atTop
      (𝓝 (K i j a x)) := by
  simp_rw [acts,sub_zero]; exact entry_value ((h i j a).summable_norm (summable_two he)) z hz x

lemma extinct {K : Three (Shades G) r s t} (h : Pace η C K) (he : 0<η) {z : ℕ → Side}
    (hz : Tendsto (fun i => (z i).val) atTop atTop) (H : ∀ p, ∀ a b c, pair3 (n:=z p) K a b c=0) : K=0 := by
  funext i j a x
  refine tendsto_nhds_unique (literal h he z hz i j a x) ((show Tendsto (fun _ : ℕ => (0 : Shades G)) atTop (𝓝 0) from tendsto_const_nhds).congr' ?_)
  filter_upwards with p
  apply ContinuousMultilinearMap.ext
  intro v
  rw [eta_three v]
  change 0=acts _ K _ _ _ _
  rw [← pair_read,H]

lemma kernel_x {K : Three (Shades G) (r+1) s t} (h : Pace η C K) (he : 0<η) {z : ℕ → Side}
    (hz : Tendsto (fun i => (z i).val) atTop atTop) (H : ∀ p a b c,pair3 K (dColor G (z p) r a) b c=0) : δx K=0 :=
  extinct (h.x he.le) he hz fun p a b c => (againstX h he a b c).symm.trans (H p a b c)
lemma kernel_y {K : Three (Shades G) r (s+1) t} (h : Pace η C K) (he : 0<η) {z : ℕ → Side}
    (hz : Tendsto (fun i => (z i).val) atTop atTop) (H : ∀ p a b c,pair3 K a (dColor G (z p) s b) c=0) : δy K=0 :=
  extinct (h.y he.le) he hz fun p a b c => (againstY h he a b c).symm.trans (H p a b c)
lemma kernel_z {K : Three (Shades G) r s (t+1)} (h : Pace η C K) (he : 0<η) {z : ℕ → Side}
    (hz : Tendsto (fun i => (z i).val) atTop atTop) (H : ∀ p a b c,pair3 K a b (dColor G (z p) t c)=0) : δz K=0 :=
  extinct (h.z he.le) he hz fun p a b c => (againstZ h he a b c).symm.trans (H p a b c)

/-- For correspondence with a PathData correction, order the indices with
an external anchor first, and unroll the entire coefficient. -/
lemma translation {K : Three (Shades G) r s t} (h : Pace η C K) (he : 0<η)
    (x y) (z : fieldDir G n t) : pair3 K x y z=
    ∑ p : Site n, ∑ i : TypeFace r, ∑ j : TypeFace s, ∑ a : TypeFace t,
      ∑' m : Couple,K i j a m ![x (wrap n m.1+p,i),y (wrap n m.2+p,j),z (p,a)] := by
  unfold pair3
  conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun p _ => ?_
  conv_lhs =>
    arg 2; intro a
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs =>
    arg 2; intro a
    arg 2; intro q
    rw [Finset.sum_comm]
  conv_lhs => arg 2; intro a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  let f (t : Site n × Site n) := ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin 3 => G.Color) ℝ (![x (t.1+p,i),y (t.2+p,j),z (p,a)])
  have hh := unroll_sum_apply (K i j a) ((h i j a).summable_norm (summable_two he)) f
  refine Eq.trans ?_ hh
  rw [← Fintype.sum_prod_type (f:=fun t : Site n × Site n => acts n K (t.1,i) (t.2,j) (p,a)
    ![x (t.1,i),y (t.2,j),z (p,a)])]
  rw [← Equiv.sum_comp (Equiv.addRight (p,p))]
  refine Finset.sum_congr rfl fun w _ => ?_; rcases w with ⟨d,b⟩
  change unroll (K i j a) (d+p-p,b+p-p) ![x (d+p,i),y (b+p,j),z (p,a)]=_
  rw [add_sub_cancel_right,add_sub_cancel_right]; rfl

def Shades.invariant (G : Gauge) : Submodule ℝ (Shades G) where
  carrier := {U | ∀ u : G.El, ∀ v, U (fun i => G.adjoint u (v i))=U v}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {A B} h g u v => by
    simp only [add_apply]; exact congr_arg₂ _ (h u v) (g u v)
  smul_mem' := fun x A h u v => by
    simp only [smul_apply]; exact congr_arg _ (h u v)

lemma colored_single (i : Body r n) (u : G.El) (x : G.Color) :
    recolor u r (n:=n) (Pi.single i x)=Pi.single i (G.adjoint u x) := by
  funext j; change G.adjoint u _=_; by_cases h : i=j
  · subst j; rw [Pi.single_eq_same,Pi.single_eq_same]
  rw [Pi.single_eq_of_ne (Ne.symm h),Pi.single_eq_of_ne (Ne.symm h),map_zero]

lemma acquire {K : Three (Shades G) r s t} (h : Pace η C K) (he : 0<η) {z : ℕ → Side}
    (hz : Tendsto (fun i => (z i).val) atTop atTop)
    (H : ∀ p u a b c, pair3 K (recolor u r (n:=z p) a) (recolor u s b) (recolor u t c)=pair3 K a b c)
    (i j a : _) (x : Couple) : K i j a x ∈ Shades.invariant G := by
  have hh p (i : Body r (z p)) j k u (y : Fin 3 → G.Color) : acts (z p) K i j k (fun d => G.adjoint u (y d))=
      acts (z p) K i j k y := by
    rw [show (fun d => G.adjoint u (y d))=![G.adjoint u (y 0),G.adjoint u (y 1),G.adjoint u (y 2)] from eta_three _]
    conv_rhs => arg 2; rw [eta_three y]
    rw [← pair_read,← pair_read,← colored_single,← colored_single,← colored_single,H]
  have ht := literal h he z hz i j a x
  intro u y
  let f (w : Fin 3 → G.Color) := ContinuousMultilinearMap.apply ℝ (fun _ => G.Color) ℝ w
  have ha := (f (fun d => G.adjoint u (y d))).continuous.tendsto (K i j a x)
  apply tendsto_nhds_unique_of_eventuallyEq (ha.comp ht) (((f y).continuous.tendsto _).comp ht)
  exact Eventually.of_forall fun p => hh p _ _ _ u y

private theorem palette {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Submodule ℝ E)
    [FiniteDimensional ℝ E] (hη : 0<η) : ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ C : ℝ, 0 ≤ C →
    ∀ A : Three E 1 1 1, Pace η C A → (∀ i j a p, A i j a p∈ U) →
    δx A=0 → δy A=0 → δz A=0 → ∃ B : Three E 2 2 2,
      Pace θ (F*C) B ∧ (∀ i j a p,B i j a p∈U) ∧ completely B=A := by
  obtain ⟨θ,F,hθ,hF,H⟩ := colors U hη
  refine ⟨θ,F,hθ,hF,fun C hc A hA h hx hy hz => ?_⟩
  let B : Three U 1 1 1 := fun i j a p => ⟨_,h i j a p⟩
  have hb : Pace η C B := fun i j a x => hA i j a x
  have he : apply3 U.subtype B=A := rfl
  have hh {r s t} (R : Three U r s t) (hr : apply3 U.subtype R=0) : R=0 := by
    funext i j a x; exact Subtype.ext (congr_fun (congr_fun (congr_fun (congr_fun hr i) j) a) x)
  obtain ⟨R,pr,qr⟩ := H _ hc B hb (hh _ (by rw [apply3_x,he,hx])) (hh _ (by rw [apply3_y,he,hy])) (hh _ (by rw [apply3_z,he,hz]))
  refine ⟨apply3 U.subtype R,fun i j a x => pr i j a x, fun i j a p => (R i j a p).property,?_⟩
  unfold completely; rw [← apply3_x,← apply3_y,← apply3_z,show δz _=_ from qr,he]

/-- Lift *invariant* kernels, preserving invariance per actual tensor (before
channels and markers). Closes in the `Tensor.T`, not quotiented by color
relations. The uniform prices here are at fixed G. -/
theorem paid_lift (G : Gauge) (hη : 0<η) : ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ C : ℝ, 0 ≤ C →
    ∀ A : Three (Shades G) 1 1 1, Pace η C A → (∀ i j a p, A i j a p∈ Shades.invariant G) →
    δx A=0 → δy A=0 → δz A=0 → ∃ B : Three (Shades G) 2 2 2,
      Pace θ (F*C) B ∧ (∀ i j a p,B i j a p∈ Shades.invariant G) ∧ completely B=A := by
  apply palette (U:=Shades.invariant G) hη

/-- All periods of the represented scalar kernel. Ward identities field by
field really give the cover cycle, also with zero/matching placements. -/
theorem shadows {z : ℕ → Side} {A : ∀ i, Dir G (z i) → ℝ} {K : Three (Shades G) 1 1 1}
    (h : Pace η C K) (he : 0<η) (hz : Tendsto (fun i => (z i).val) atTop atTop)
    (hp : ∀ p, Checks (z p) (A p)) (h₁ : ∀ p,fderiv ℝ (A p) 0=0) (h₂ : ∀ p, iteratedFDeriv ℝ 2 (A p) 0=0)
    (hk : ∀ p, ∀ x y b, pair3 (n:=z p) K x y b=Tensor.coeff (A p) 3 0 ![x,y,b]) :
    (∀ i j a p,K i j a p∈ Shades.invariant G) ∧ δx K=0 ∧ δy K=0 ∧ δz K=0 := by
  have hf p u := Checks.horizontal_tensor (hp p) (h₁ p) (h₂ p) u
  have hu p : Tensor.Sym (Tensor.coeff (A p) 3 0) := Tensor.coeff_symm ((hp p).analytic.of_le le_top)
  have hx (p x y w) : Tensor.coeff (A p) 3 0 ![dColor G (z p) 0 x,y,w]=0 :=
    DFunLike.congr_fun (hf p x) ![y,w]
  refine ⟨acquire h he hz (fun p u x y b => ?_), kernel_x h he hz fun p x y b => (hk ..).trans (hx p x y b),
    kernel_y h he hz fun p x y b => ?_, kernel_z h he hz fun p x y b => ?_⟩
  · rw [hk,hk]
    have ht := (hp p).colored_tensor u ![x,y,b]
    exact Eq.trans (congr_arg ((Tensor.coeff (A p) 3 0) : _ → ℝ) (funext fun i => by fin_cases i <;> rfl)) ht
  · rw [hk]; rw [← hu p ![_,_,_] (Equiv.swap 0 1)]
    have ht (x y z : Dir G (z p)) : ![x,y,z] ∘ Equiv.swap (0:Fin 3) 1=![y,x,z] := funext fun i => by fin_cases i <;> rfl
    rw [ht,hx]
  rw [hk, ← hu p ![_,_,_] (Equiv.swap 0 2)]
  have ht (x y z : Dir G (z p)) : ![x,y,z] ∘ Equiv.swap (0:Fin 3) 2=![z,y,x] := funext fun i => by fin_cases i <;> rfl
  rw [ht,hx]
end YM.CubicMatch
