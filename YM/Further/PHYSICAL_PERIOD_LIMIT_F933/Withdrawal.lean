import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Polytrace

/-! # Position motions, even through nonzero offshell gradient.

Can then use Envelope on the actual orbit (supplied on Crit). Constants even
without representation arguments to cancel trace colors (e.g. if comparing
offshell without full fine Ward). -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Withdrawal
open Jacobi Polytrace Function Lattice Finset Push.Uniform Filter
open scoped Topology ContDiff BigOperators Classical
variable {κ ι : Type} [Fintype κ] [Fintype ι] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

abbrev move (v : X) (g : X → Positions ι) (x : X) (i : ι) := blade v (fun y => g y i) x
abbrev rise (v w : X) (g : X → Positions ι) (x : X) (i : ι) := mixed v w (fun y => g y i) x

section
variable (v w : X) {f : Positions ι → ℝ} {g : X → Positions ι} {x : X}

lemma turn (h : ContDiffAt ℝ ω g x) (i) : fderiv ℝ g x v i=move v g x i := by
  let p := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : ι=>ℝ) i
  unfold move blade; rw [show (fun y=>g y i)= p ∘ g from rfl,fderiv_comp x p.differentiableAt (h.differentiableAt (by simp)), p.fderiv]; rfl
lemma entered (h : ContDiffAt ℝ ω g x) (hf : ContDiffAt ℝ ω f (g x)) :
    blade w (f ∘ g) x = ∑ i, move w g x i * blade (bolt i) f (g x) := by
  unfold blade
  rw [fderiv_comp _ (hf.differentiableAt (by simp)) (h.differentiableAt (by simp)),ContinuousLinearMap.comp_apply, by_row]
  simp_rw [turn _ h,smul_eq_mul]

lemma torn (h : ContDiffAt ℝ ω g x) (hf : ContDiffAt ℝ ω f (g x)) :
    mixed v w (f ∘ g) x= (∑i, ∑j, move w g x i * (move v g x j * mixed (bolt j) (bolt i) f (g x))) +
      ∑ i, blade (bolt i) f (g x) * rise v w g x i := by
  have he : blade w (f ∘ g) =ᶠ[𝓝 x] fun y=>∑i,move w g y i* blade (bolt i) f (g y) := by
    filter_upwards [h.eventually (by simp), (h.continuousAt).tendsto.eventually (hf.eventually (by simp))] with y h hy
    exact entered w h hy
  have hx i : ContDiffAt ℝ ω (fun y=>move w g y i) x := smooth w ((contDiffAt_pi.mp h) i)
  have ht i := smooth (bolt i) hf
  have hh i : ContDiffAt ℝ ω (fun y=>blade (bolt i) f (g y)) x := (ht i).comp _ h
  suffices hl : ∀ i ∈ (Finset.univ : Finset ι), blade v (fun y=>move w g y i * blade (bolt i) f (g y)) x =
      (∑ j,move w g x i*(move v g x j * mixed (bolt j) (bolt i) f (g x))) + blade (bolt i) f (g x) * rise v w g x i by
    rw [mixed, show blade v (blade w (f ∘ g)) x= blade v (fun y=>∑ i,_) x from congr_arg (fun L : X →L[ℝ] ℝ => L v) he.fderiv_eq,
      series v (fun i _=>(hx i).mul (hh i)), Finset.sum_congr rfl hl, Finset.sum_add_distrib]
  intro i _
  rw [product _ (hx i) (hh i)]
  rw [show blade v (fun y=>blade (bolt i) f (g y)) x=∑ j,move v g x j * mixed (bolt j) (bolt i) f (g x) from entered v h (ht i), ← Finset.mul_sum]

lemma come (v w) (g : X→Positions ι) {L : Positions ι →L[ℝ] ℝ} (hf : ContDiffAt ℝ ω g x) :
    mixed v w (L ∘ g) x = L (mixed v w g x) := by
  have he q (_t : ContDiffAt ℝ ω g q) (w) : blade w (L ∘ g) q = L (blade w g q) := by
    unfold blade; rw [fderiv_comp _ L.differentiableAt (_t.differentiableAt (by simp)), L.fderiv]; rfl
  have hh : blade w (L ∘ g) =ᶠ[𝓝 x] L ∘ blade w g := (hf.eventually (by simp)).mono fun i h => he i h w
  unfold mixed blade; rw [hh.fderiv_eq,fderiv_comp _ L.differentiableAt ((smooth w hf).differentiableAt (by simp)),L.fderiv]; rfl
end

section Cost
variable {n : Side} {l : ι→Site n} {m : κ→Site n} {K : ℕ}

-- Backbone using counting normalization on BOTH V tensors.
omit [Fintype κ] in
lemma fade (X Y : κ) (hm : Multiplicity l K) {r t d : ℝ} (hp : 0 < t) (ht : t+t ≤ r) (hs : t ≤ d) :
    let D := Decay (n:=n); let Q := space K t
    (∑ (i:ι),∑j:ι,D r (l i) (m Y)*D r (l j) (m X)*D d (l j) (l i)) ≤ Q^2 * D t (m X) (m Y) := by
  let a := Decay (n:=n) t
  intro D Q
  have ha x y : 0 ≤ a x y := (decay_pos ..).le
  have h i j : D r (l i) (m Y)*D r (l j) (m X)*D d (l j) (l i) ≤
      a (m X) (m Y)*(a (m Y) (l i)*a (m X) (l j)) := by
    let A := l i; let B:= l j; let x := m X; let y := m Y
    change Decay r A y*Decay r B x*Decay d B A ≤ a x y * _
    rw [decay_comm r A y, decay_comm r B x]
    apply (mul_le_mul
      (mul_le_mul (separate ht (n:=n) y A) (separate ht (n:=n) x B) (decay_pos ..).le
        (show 0≤a y A*a y A from mul_nonneg (ha ..) (ha ..)))
      (fee hs B A) (decay_pos ..).le (by
        have := mul_nonneg (ha x B) (ha x B); have := mul_nonneg (ha y A) (ha y A)
        change 0 ≤ a y A * a y A * (a x B * a x B); positivity)).trans
    have h : a x B*a B A*a y A ≤ a x y := by rw [show a y A=a A y from decay_comm _ _ _]; exact (mul_le_mul_of_nonneg_right (decay_step hp.le ..) (ha ..)).trans (decay_step hp.le ..)
    have he := mul_le_mul_of_nonneg_right h (mul_nonneg (ha y A) (ha x B))
    rw [show a x B*a B A*a y A * (a y A*a x B)=Decay t y A * Decay t y A*(Decay t x B * Decay t x B)* Decay t B A by dsimp only [a]; ring] at he
    exact he
  have hQ : 0 ≤ Q := space_pos _ hp
  apply (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _=>h i j).trans
  rw [show (∑ i:ι,∑ j:ι,_)=a (m X) (m Y)*((∑ i:ι,a (m Y) (l i))*∑ j:ι,a (m X) (l j)) by simp_rw [Finset.sum_mul, Finset.mul_sum],sq,mul_comm (Q*Q)]
  apply mul_le_mul_of_nonneg_left _ (ha ..); gcongr
  · exact Finset.sum_nonneg fun _ _=> ha ..
  all_goals exact hm.count _ hp _
omit [Fintype κ] in
lemma suture (X Y : κ) (hm : Multiplicity l K) {r t : ℝ} (hp : 0<t) (ht : t+t ≤ r) :
    let D := Decay (n:=n); let Q := space K t
    (∑ i:ι, D r (l i) (m X) * D r (l i) (m Y)) ≤ Q * D t (m X) (m Y) := by
  let a := Decay (n:=n) t
  intro D Q
  have hA i j : 0 ≤ a i j := (decay_pos ..).le
  have h i : D r (l i) (m X)*D r (l i) (m Y) ≤ a (m X) (l i)*a (m X) (m Y) := by
    let A:= l i; let x := m X; let y := m Y
    change Decay r A x*Decay r A y ≤ a x A*a x y
    rw [decay_comm r]
    apply (mul_le_mul (separate ht _ _) (fee (le_trans (le_add_of_nonneg_right hp.le) ht) _ _) (decay_pos ..).le (show 0 ≤ a x A*a x A from mul_nonneg (hA ..) (hA ..))).trans
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (decay_step hp.le ..) (hA ..)
  apply (Finset.sum_le_sum (fun i _=>h i)).trans; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hm.count _ hp _) (hA ..)

variable {C B d r t : ℝ}

def flowFee (C B : ℝ) (K : ℕ) (t : ℝ) := B*B*C*(space K t)^2+C*B*space K t
lemma flow_nonneg (hc : 0≤C) (hB : 0≤B) (K : ℕ) (hp : 0<t) : 0≤ flowFee C B K t := by unfold flowFee; have := space_pos K hp; positivity
lemma merged {f : Positions ι → ℝ} {g : Positions κ → Positions ι} {x : Positions κ}
    (hg : ContDiffAt ℝ ω g x) (hf : ContDiffAt ℝ ω f (g x)) (hm : Multiplicity l K) (hc : 0≤C) (hB : 0≤B)
    (hp : 0<t) (ht : t+t≤r) (hs : t≤d)
    (hb : ∀ i, ‖blade (bolt i) f (g x)‖ ≤ C) (hT : ∀ i j, ‖mixed (bolt i) (bolt j) f (g x)‖ ≤ C * Decay d (l i) (l j))
    (h : ∀ i (X : κ), ‖move (bolt X) g x i‖ ≤ B*Decay r (l i) (m X))
    (h' : ∀ i (X Y : κ), ‖rise (bolt X) (bolt Y) g x i‖ ≤ B*(Decay r (l i) (m X)*Decay r (l i) (m Y))) (X Y : κ) :
    ‖mixed (bolt X) (bolt Y) (f ∘ g) x‖ ≤ flowFee C B K t * Decay t (m X) (m Y) := by
  let D := Decay (n:=n)
  have hx i j : 0 ≤ D r i j := (decay_pos ..).le
  rw [torn _ _ hg hf,flowFee, add_mul]; apply (norm_add_le ..).trans; apply add_le_add
  · apply le_trans (norm_sum_le ..)
    have he i j : ‖_‖ ≤ B*B*C*(D r (l i) (m Y)*D r (l j) (m X)*D d (l j) (l i)) :=
      (show ‖move (bolt Y) g x i * (move (bolt X) g x j * mixed (bolt j) (bolt i) f (g x))‖ ≤ _ from by
        simp only [norm_mul]
        apply (mul_le_mul (h i Y) (mul_le_mul (h j X) (hT j i) (norm_nonneg _) (mul_nonneg hB (hx ..)))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg hB (hx ..))).trans_eq; dsimp only [D]; ring)
    apply le_trans (Finset.sum_le_sum fun i _ => (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>he i j))
    simp_rw [← Finset.mul_sum,mul_assoc] -- use eta? revert mul_assoc below
    have hu := mul_le_mul_of_nonneg_left (fade (m:=m) X Y hm hp ht hs) (mul_nonneg (mul_nonneg hB hB) hc)
    simpa only [mul_assoc,D] using hu
  apply le_trans (norm_sum_le ..)
  have hv i : ‖blade (bolt i) f (g x)*rise (bolt X) (bolt Y) g x i‖ ≤ C*B*(D r (l i) (m X)*D r (l i) (m Y)) := by
    rw [norm_mul,mul_assoc C]; exact mul_le_mul (hb i) (h' i X Y) (norm_nonneg _) hc
  apply le_trans (Finset.sum_le_sum (fun i _=>hv i)); rw [← Finset.mul_sum, mul_assoc (C*B)]; exact mul_le_mul_of_nonneg_left (suture (m:=m) X Y hm hp ht) (mul_nonneg hc hB)
end Cost
end YM.Further.PhysicalPeriodLimitF933.Withdrawal
