import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Infinitesimal


/-!
# Local affine extraction

On both endpoints of the real tested support, lifts about the anchor.
Pulled directions need NOT be affine on other edges or across a wrap.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Filter Function Lattice Wilson RG ProjectorNext.Equivariance
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side}

/-- Real curl space; norm here is the sup over the six pairs. -/
abbrev Flux (G : Gauge) := PlaqAxes → G.Color

abbrev Offset (G : Gauge) := Axis → G.Color
abbrev Leaning (G : Gauge) := Axis → Axis → G.Color -- slope: column i of edge in j is u j i

def slide (z : Cover) (c : Offset G) := ∑ i, z i • c i
lemma slide_plus (z u : Cover) (c : Offset G) : slide (z+u) c=slide z c+slide u c := by
  simp [slide,add_smul,Finset.sum_add_distrib]
lemma slide_add (z : Cover) (c d : Offset G) : slide z (c+d)=slide z c+slide z d := by
  simp [slide,smul_add,Finset.sum_add_distrib]
lemma slide_sub (z : Cover) (c d : Offset G) : slide z (c-d)=slide z c-slide z d := by
  simp [slide,smul_sub,Finset.sum_sub_distrib]
lemma slide_neg (z : Cover) (c : Offset G) : slide z (-c)= -slide z c := by simp [slide, Finset.sum_neg_distrib]
lemma slide_step (c : Offset G) (i : Axis) : slide (step i) c = c i := by
  simp only [slide,step_apply,ite_smul,one_smul,zero_smul]; simp

def profile (o x : Site n) (i : Axis) (c : Offset G) (d : Leaning G) := c i + slide (lift (x-o)) (d i)

def OnStencil (o : Site n) (X : Support n) (c : Offset G) (d : Leaning G) (A : Directions G n) :=
  ∀ x∈X, ∀ i, x+step i∈X → A (x,i)=profile o x i c d

def skew (d : Leaning G) : Flux G := fun i => d i.1.2 i.1.1 - d i.1.1 i.1.2

lemma onStencil_of_affine {A : Directions G n} {o : Site n} (h : IsAffineDirection o A) (X : Support n) :
    ∃ c d, OnStencil o X c d A := by
  obtain ⟨c,d,h⟩:=h; exact ⟨c,d,fun x _ i _ => h (x,i)⟩

lemma OnStencil.mono {A : Directions G n} {o : Site n} {X Y : Support n} {c d} (h : OnStencil o Y c d A)
    (hh : X⊆Y) : OnStencil o X c d A := fun x hx i hi => h x (hh hx) i (hh hi)

lemma OnStencil.add {A B : Directions G n} {o : Site n} {X : Support n} {c d c' d'} (h : OnStencil o X c d A)
    (h' : OnStencil o X c' d' B) : OnStencil o X (c+c') (d+d') (A+B) := by
  intro x hx i hi; simp only [Pi.add_apply,h x hx i hi,h' x hx i hi,profile,slide_add]; abel
lemma OnStencil.sub {A B : Directions G n} {o : Site n} {X : Support n} {c d c' d'} (h : OnStencil o X c d A)
    (h' : OnStencil o X c' d' B) : OnStencil o X (c-c') (d-d') (A-B) := by
  intro x hx i hi; simp only [Pi.sub_apply,h x hx i hi,h' x hx i hi,profile,slide_sub]; abel

lemma skew_sub (d e : Leaning G) : skew (d-e)=skew d-skew e := by funext i; simp only [skew,Pi.sub_apply]; abel

private def planar (d : Leaning G) (x y : Cover) := slide x (fun i => slide y (d i))

private lemma equal_plane (d : Leaning G) (h : ∀ i j, d i j = d j i) (x y : Cover) : planar d x y=planar d y x := by
  unfold planar slide; simp_rw [Finset.smul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm]; congr 2; exact h ..
private lemma plus_plane (d : Leaning G) (x y z : Cover) : planar d (x+y) z=planar d x z+planar d y z := slide_plus ..
private lemma one_plane (d : Leaning G) (x : Cover) (i : Axis) : planar d (step i) x=slide x (d i) := slide_step ..

private def voltage (c : Offset G) (d : Leaning G) (x : Cover) : G.Color := slide x c +
    (1/2:ℝ) • (planar d x x - slide x fun i => d i i)

private lemma voltage_step (c : Offset G) (d : Leaning G) (h : ∀ i j, d i j=d j i) (x : Cover) (i : Axis) :
    voltage c d (x+step i)-voltage c d x=c i+slide x (d i) := by
  have hh j : planar d j (x+step i)=planar d j x+planar d j (step i) := by
    nth_rw 1 [equal_plane d h j]
    rw [plus_plane,equal_plane d h x j,equal_plane d h (step i) j]
  unfold voltage
  rw [plus_plane,hh,hh,equal_plane d h x (step i)]; simp only [one_plane,slide_plus,slide_step]; module

/-- Zero affine curl is a pure gauge tangent on the support. The extension
as a gradient on the torus need only match the local edges. -/
lemma exact_on_lift (hn : 2 ≤ n.val) {o : Site n} {X : Support n} (hx : Nonwrapping X o)
    {A : Directions G n} {c d} (hA : OnStencil o X c d A) (hd : skew d=0) :
    ∃ φ, ∀ e : Edge (Site n), e.1∈X → e.1+step e.2∈X → A e=slope φ e := by
  have hw (i j) (h : i<j) : d j i=d i j := sub_eq_zero.mp (congr_fun hd (⟨(i,j),h⟩:PlaqAxes))
  have hs i j : d i j=d j i := by cases lt_trichotomy i j with
    | inl h => exact (hw _ _ h).symm
    | inr h => rcases h with rfl|h <;> first | exact hw _ _ h | rfl
  refine ⟨fun x => -voltage c d (lift (x-o)),?_⟩
  rintro ⟨x,i⟩ hg hk
  rw [hA x hg i hk,slope,profile,← voltage_step c d hs, Next.Foundations.lift_end hn hx x hg]; abel

def lower (w : Flux G) : Leaning G := fun j i => if h : i<j then w ⟨(i,j),h⟩ else 0

lemma lower_skew (w : Flux G) : skew (lower w)=w := by
  funext i; rcases i with ⟨⟨a,b⟩,h⟩; simp only [skew,lower,dif_pos h,dif_neg (not_lt.mpr (le_of_lt h)),sub_zero]

def rise (G : Gauge) (o : Site n) : Flux G →L[ℝ] Directions G n := LinearMap.toContinuousLinearMap {
  toFun w e := slide (lift (e.1-o)) (lower w e.2)
  map_add' := fun a b => funext fun i => by
    have hp j : lower (a+b) j = lower a j+lower b j := by funext x; by_cases h : x<j <;> simp [lower,h]
    rw [hp,slide_add]; rfl
  map_smul' := fun t a => funext fun i => by
    have hp j x : lower (t • a) j x = t • lower a j x := by by_cases h : x<j <;> simp [lower,h]
    simp only [slide,hp,RingHom.id_apply,Pi.smul_apply,Finset.smul_sum]; apply Finset.sum_congr rfl; intros; apply smul_comm }
lemma rise_apply (w : Flux G) (o : Site n) (e) : rise G o w e = slide (lift (e.1-o)) (lower w e.2) := rfl
lemma rise_hits (w : Flux G) (o : Site n) (X : Support n) : OnStencil o X 0 (lower w) (rise G o w) := fun x _ i _ => by simp [profile, rise_apply]

lemma via_skew (hs : G.Simple) (hn : 2 ≤ n.val) {o : Site n} {X : Support n} (hx : Nonwrapping X o)
    {A : Directions G n} {c d} (hA : OnStencil o X c d A) {f : Config G n→ℝ} {p : BudgetPoint} (h : p.Regular X f) (B) :
    H f A B=H f (rise G o (skew d)) B := by
  obtain ⟨φ,hφ⟩ := exact_on_lift hn hx (hA.sub (rise_hits (skew d) o X)) (by rw [skew_sub,lower_skew,sub_self])
  have he : H f (A-rise G o (skew d)) B=0 := (H_local hs h B hφ).trans ((symmetric h ..).trans (absorbs hs h φ B))
  exact sub_eq_zero.mp (by simpa using he)

private def spinCoef (s : Signed) (a : Offset G) : Offset G := fun i => if s.flip i then -a (s.perm i) else a (s.perm i)
private lemma slide_spin (s : Signed) (z : Cover) (a : Offset G) : slide (s.act z) a=slide z (spinCoef s a) := by
  unfold slide; rw [← Equiv.sum_comp s.perm]; refine Finset.sum_congr rfl fun i _ => ?_; cases h : s.flip i <;> simp [spinCoef,h]

/-- Direction positivity reversal includes the endpoint shift. -/
lemma pull_onSt (s : Signed) (z : Site n) (hn : 2 ≤ n.val) {o : Site n} {X : Support n}
    (hx : Nonwrapping X o) {A : Directions G n} {c d} (h : OnStencil (affine s z o) (X.image (affine s z)) c d A) :
    ∃ c' d', OnStencil o X c' d' (pulledDirection s z 1 A) := by
  let v i := spinCoef s (d (s.perm i))
  have hh (i : Site n) (hi : i∈X) : lift (affine s z i - affine s z o) = s.act (lift (i-o)) := by
    unfold affine; rw [add_sub_add_right_eq_sub,← s.act_sub]; apply lift_eq_iff.mpr
    refine ⟨by rw [← wrap_signed,wrap_lift],?_⟩
    intro a; obtain ⟨j,rfl⟩ := s.perm.surjective a; rw [Signed.act_at]
    have hv := hx i hi; have ht : (lift (i-o) j).natAbs ≤ separation i o := component_le _ _
    split <;> omega
  refine ⟨fun i => if s.flip i then - (c (s.perm i)+v i i) else c (s.perm i),
          fun i => if s.flip i then -(v i) else v i,?_⟩
  intro x hg i hi
  have he := (send_mem s z X (x,i)).mpr ⟨hg,hi⟩
  change roll _ _ _ _ _ = _
  rw [roll_apply, send_formula]
  have hf := affine_end s z x i
  cases hw : s.flip i
  · simp only [send_formula,hw,Bool.false_eq_true, ↓reduceIte] at he ⊢
    rw [h _ he.1 _ he.2,profile,hh x hg,slide_spin]; simp [profile,hw,v]
  simp only [send_formula,hw,↓reduceIte, Pi.one_apply, inv_one] at he ⊢
  have ht : affine s z x-step (s.perm i) = affine s z (x+step i) := by simp [hf,Lattice.Step.vec,Lattice.Step.rotate,posDir,hw,sub_eq_add_neg]
  rw [h _ he.1 _ he.2,profile,ht,hh (x+step i) hi,slide_spin,Next.Foundations.lift_end hn hx x hg, profile]
  simp only [v, hw, if_true,slide_plus,slide_step,slide_neg,G.adjoint_one]; abel

end YM.AnalyticBridge.CouplingShape
