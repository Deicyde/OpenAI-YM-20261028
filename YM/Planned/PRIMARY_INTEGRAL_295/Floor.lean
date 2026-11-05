import YM.Planned.PRIMARY_INTEGRAL_295.Cedar
import YM.Progress.STATIONARY_SCENES.Green
import YM.Push.STATIONARY_UNIFORM.Count
/-!
# E.EGd needed on localized canonical column windows

Use Green.inverse exactly with order gap purchase, then component y
operator derivative all finite windows. Here finite volume allowance
post-L $Bk$ -- doesn't establish full window matrix chains or global
history precision theorem. Means achieved later on physical requests.
Not globally selected cut approximations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Floor
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Oval Cedar Precision Exterior Tree Streets
open Progress.StationaryScenes.Green Push.Uniform Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {E F ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n k : ℕ} {C M σ α : ℝ} {f : Side}

-- degrees: Wein.
structure Aim where
    C : ℝ -- weighted Both
    t : ℝ -- Bottom delta
    σ : ℝ
    r : ℝ -- θ Green
    ht : 0<t
    hc : 1≤C
    wave : 0<σ ∧ r∈Ioc 0 1
    bound : r*C ≤ t/2

namespace Aim
variable (h:Aim)
def starry:=h.r*h.σ
lemma starry_pos: 0<h.starry := mul_pos h.wave.2.1 h.wave.1
def cap := (min (1:ℝ) (h.t/2))⁻¹
lemma cap_pos : 0 < h.cap := inv_pos.mpr (lt_min one_pos (half_pos h.ht))
lemma cap_t {u:ℝ} (hp: h.cap ≤ u) (hk:0<u) : u⁻¹ ≤ h.t := by
  have he : u⁻¹≤min (1:ℝ) (h.t/2):= by simpa [cap] using inv_le_inv₀ hk h.cap_pos|>.mpr hp
  apply he.trans; have hb:=h.ht; exact (min_le_right ..).trans (by linarith)

def Dust (a b : Site f) := Decay h.starry a b
lemma dust_pos (a b : Site f) : 0<h.Dust a b := decay_pos ..
lemma dust_le (a b : Site f) : h.Dust a b≤1 := decay_le h.starry_pos.le ..
lemma dust_link (a b c: Site f):h.Dust a b*h.Dust b c ≤ h.Dust a c := decay_step h.starry_pos.le ..

variable [Fintype ι]
structure Camp (A : Matrix ι ι ℝ) (l:ι→Site f) : Prop where
    bottom : Bottom A h.t
    hm : A.IsHermitian
    both : Both l l A h.σ h.C h.C

lemma Camp.cost [DecidableEq ι] {A : Matrix ι ι ℝ} {l:ι→Site f} (hp : h.Camp A l) :
    A * A⁻¹=1 ∧ A⁻¹ * A=1 ∧ ∀ i j, ‖(A⁻¹) i j‖≤ h.cap * h.Dust (l i) (l j) := by
  have hx:= Progress.StationaryScenes.Green.inverse h.wave.1.le h.ht h.wave.2.1.le h.wave.2.2 h.bound hp.hm hp.bottom hp.both 0 le_rfl
  simp only [zero_smul,add_zero,mul_one] at hx
  refine ⟨hx.1,hx.2.1,fun i j=>?_⟩
  have he : h.Dust (l i) (l j)=(wt (h.r*h.σ) (l i) (l j))⁻¹:=by unfold Dust Decay starry wt; rw [neg_mul,Real.exp_neg]
  rw [he,← div_eq_mul_inv, le_div_iff₀ (wt_pos ..), Real.norm_eq_abs,mul_comm]; exact hx.2.2 i j

lemma Camp.take [Fintype F] {A : Matrix ι ι ℝ} {l:ι→Site f} (hp:h.Camp A l) (e:F ↪ ι): h.Camp (A.submatrix e e) (l ∘ e) :=
   ⟨hp.bottom.restrict e,hp.hm.submatrix _,hp.both.1.restrict e e,hp.both.2.restrict e e⟩
end Aim

section Cells
variable [Fintype ι] [DecidableEq ι] {A:E→Matrix ι ι ℝ}


lemma det_mood (h:∀ i j,ContDiffAt ℝ n (fun y=>A y i j) 0):ContDiffAt ℝ n (fun y=>(A y).det) 0 := by
    simp_rw [det_apply']; apply ContDiffAt.sum; intro i _; exact contDiffAt_const.mul (contDiffAt_prod (fun j _=> h _ _))
lemma pass_mood (h:∀ i j,ContDiffAt ℝ n (fun y=>A y i j) 0) (he: A 0*(A 0)⁻¹=1) :
    (∀ i j, ContDiffAt ℝ n (fun y=>(A y)⁻¹ i j) 0) ∧ ∀ᶠ x in 𝓝 0,A x*(A x)⁻¹=1 ∧ (A x)⁻¹*A x=1 := by
  have hd:=det_mood h
  have hc := Matrix.det_ne_zero_of_right_inverse he
  constructor
  · intro i j; simp_rw [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul,adjugate_apply]
    apply (hd.inv hc).mul; apply det_mood; intro x y; by_cases hq:x=j
    · simp only [hq,Matrix.updateRow_self]; exact contDiffAt_const
    simp only [Matrix.updateRow_ne hq]; exact h _ _
  have ht:∀ᶠ x in 𝓝 (0:E),(A x).det≠0:= hd.continuousAt.eventually (isOpen_ne_fun continuous_id continuous_const|>.mem_nhds hc)
  exact ht.mono (fun y hy=> ⟨Matrix.mul_nonsing_inv (A y) (isUnit_iff_ne_zero.mpr hy),
    Matrix.nonsing_inv_mul (A y) (isUnit_iff_ne_zero.mpr hy)⟩)

-- memberwise tickets to exponential rate business only in local volume.
def Vault (h:Aim) (l:ι→ Site f) (A:E→Matrix ι ι ℝ) (n:ℕ) (R:ℝ) : Prop:= ∀ i j, Ember n (fun x=>A x i j) (R*h.Dust (l i) (l j))

def willow (u:ℝ) : ℕ→ℝ
    | 0=>u
    | n+1=> u + (2^(n+2)*u^4)*willow u n
lemma will_le {u:ℝ} (h:1≤u) (n:ℕ):u≤willow u n:=by
   induction n with
   | zero=>exact le_rfl
   | succ n ih =>
     have ht := zero_le_one.trans (h.trans ih)
     exact le_add_of_nonneg_right (by positivity)
lemma will_power (n:ℕ): ∃ (M:ℝ)(b:ℕ),1≤M∧∀ u≥1,willow u n ≤ M*u^b:=by
   induction n with
   | zero=>exact ⟨1,1,le_rfl,fun _ _=>by simp [willow]⟩
   | succ n ih=>
     obtain ⟨C,b,hC,h⟩:=ih; have he:1≤(2:ℝ)^(n+2):=one_le_pow₀ (by norm_num)
     refine ⟨1+2^(n+2)*C,b+4,le_add_of_nonneg_right (by positivity),fun u hu=>?_⟩
     have hx:= pow_le_pow_right₀ hu (show 1≤b+4 by omega); rw [pow_one] at hx
     change u+(2^(n+2)*u^4)*willow u n ≤ _; rw [add_mul,one_mul]; refine add_le_add hx ((mul_le_mul_of_nonneg_left (h u hu) (by positivity)).trans_eq ?_); ring

variable (h:Aim) (l:ι→Site f) {u:ℝ} (hp : h.Camp (A 0) l) (hc: h.cap ≤ u) (hu: 1≤u)

include hp hc hu

theorem ribbons (ha:Vault h l A k u) (hw : (Fintype.card ι:ℝ) ≤ u) : Vault h l (fun y=>(A y)⁻¹) k (willow u k) := by
  classical
  let r (i j:ι):=h.Dust (l i) (l j)
  have he i j: 0 ≤ r i j:= (h.dust_pos ..).le
  obtain ⟨hf,hf',hS⟩:=Aim.Camp.cost h hp
  let F (x:E):=(A x)⁻¹
  have hs i j : ‖F 0 i j‖ ≤ u*r i j:= (hS ..).trans (mul_le_mul_of_nonneg_right hc (he ..))
  induction k with
  | zero =>
    have he':= pass_mood (n:=0) (fun i j=>(ha i j).1) hf
    refine fun i j=> ⟨he'.1 i j,mul_nonneg (zero_le_one.trans hu) (he ..),fun n hn=>?_⟩
    have hn':n=0:=Nat.le_zero.mp hn
    subst n; rw [norm_iteratedFDeriv_zero]; exact hs ..
  | succ n ih =>
    specialize ih (fun i j=> Ember.down (ha i j) (Nat.le_succ n))
    let k:=n+1
    let m:=(Fintype.card ι:ℝ)
    let z:= willow u n; have hz: 1 ≤ z:= hu.trans (will_le hu _)
    obtain ⟨hB,hH⟩:= pass_mood (n:=n+1) (fun i j=> (ha i j).1) hf
    intro i j
    let D (x:E):=A x - A 0
    let f (p q:ι) (x:E) := F 0 i p*(D x p q*F x q j)
    let C := 2^(n+2)*(u*u*z)*r i j
    have hq (p q:ι): Ember k (f p q) C:=by
      have ht := ha p q
      have ht' : Ember k (fun y=>D y p q) (2*u*r p q):= by
        have hx:= Ember.weakening (Ember.constant (E:=E) (A 0 p q) k) ht.2.value
        have hh : 2*u*r p q = u*r p q + u*r p q:=by ring
        rw [hh]; exact Ember.erase ht hx
      have hx:= Ember.scaled (Ember.reduced (f:=fun y=>D y p q) (by simp [D]) ht' (hB q j) (ih q j).2) (F 0 i p)
      apply Ember.weakening (show Ember k _ _ from hx)
      change ‖F 0 i p‖*(2^k*(2*u*r p q*(z*r q j))) ≤ C
      have hb : 0≤ r p q:= he ..; have ha':0≤r q j:=he ..
      apply (mul_le_mul_of_nonneg_right (hs i p) (by positivity)).trans
      have he' : r i p*r p q*r q j ≤ r i j := (mul_le_mul_of_nonneg_right (h.dust_link ..) (he ..)).trans (h.dust_link ..)
      calc
       _ = (2^(n+2)*(u*u*z)) * (r i p*r p q*r q j) := by unfold k; ring
       _ ≤ C:= mul_le_mul_of_nonneg_left he' (by positivity)
    let g:=fun x:E => F 0 i j - ∑ p, ∑ q, f p q x
    have hG := Ember.cumul (fun p x=> ∑ q, f p q x) (fun p=> Ember.cumul (f p) (hq p))
    have hR := Ember.erase (Ember.weakening (Ember.constant (E:=E) (F 0 i j) k) (hs i j)) hG
    have hU:= show Ember k g (willow u k * r i j) from Ember.weakening hR ?_
    · apply Ember.renamed hU
      filter_upwards [hH] with x hx
      change F x i j = g x
      have he : F x=F 0- F 0*(D x*F x) := by
         unfold D; rw [Matrix.sub_mul, hx.1, Matrix.mul_sub, ←Matrix.mul_assoc,hf']; simp
      unfold g
      nth_rw 1 [he]; simp_rw [Matrix.sub_apply, Matrix.mul_apply, Finset.mul_sum]; rfl
    change u*r i j + m*(m*C) ≤ _
    rw [show willow u k=u + (2^(n+2)*u^4)*z from rfl,add_mul]; apply add_le_add_right
    have he := he i j; have hC :0≤C:=by unfold C; positivity
    have hm:0 ≤ m:=Nat.cast_nonneg _
    calc
      _ ≤ u*(u*C):=mul_le_mul hw (mul_le_mul_of_nonneg_right hw hC) (by positivity) (by linarith)
      _ = _:=by unfold C; ring
end Cells
end YM.Planned.PrimaryIntegral295.Floor
