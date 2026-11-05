import YM.WilsonBulk.Spectral.Raw
import YM.Work.F08.Rows

/-! Release the analytic inverse in the bulk real `Laurent.Width`, at a prescribed smaller width
controlled BEFORE L. JAUNT attaches to every period and t, forever using same cover kernel.
Real part on coefficients, actual +displacement sign on continuum tests. -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Work.F08 Precision Exterior Stationary Audience Matrix
open scoped Topology BigOperators Matrix

variable {L c f : Side} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {σ η C W : ℝ} {H : Momentum → CompM α β}

lemma firm_cell (A : ℝ) (h : Poster σ H) (hσ : 0<σ) (hu : ∀ p∈strip σ, vflux (H p) ≤ A) (i j) :
    Firm σ A (fun p => H p i j) := by
  refine ⟨⟨hσ,fun p hp=> h.shape hp i j, fun p hp x=>?_⟩,fun p hp=>(flux_tilt _ _ _).trans (hu p hp)⟩
  rw [← h.shifts ⟨x,rfl⟩ hp]

def crystals (H : Momentum → CompM α β) : Row α β := fun i j x => (market (fun p => H p i j) 0 x).re
def castCost (σ A : ℝ) := A*(2*((1+σ/4)/(σ/4)))^(Fintype.card Axis)
lemma castCost_nonneg (hσ : 0≤σ) (hA : 0≤ C) : 0 ≤ castCost σ C := by unfold castCost; positivity
lemma crystal_budget (A : ℝ) (h : Poster σ H) (hσ : 0<σ) (hu : ∀ p∈strip σ, vflux (H p) ≤ A) :
    (crystals H).strip (σ/2) (castCost σ A) := by
  intro i j
  have ht := firm_cell A h hσ hu i j
  refine budget_minor (ht.1.issues ht.2 (σ/2) (σ/4) (by positivity) (by positivity)
    (by linarith)) (fun x => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ?_
  intro i; exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos _).le

omit [Fintype α] [DecidableEq α] in
lemma jaunt_sees {U V : CircM c α β} (hU : Jaunt U H 0) (hV : Jaunt V H 0) : U=V := by
  apply cancel_rotation
  ext i ⟨p,j⟩
  rw [Matrix.mul_apply, Matrix.mul_apply]
  let v (x : Co c β):= rotations c β x (p,j)
  change (U *ᵥ v) i = (V *ᵥ v) i
  rw [show v=tune p (Pi.single j 1) from funext (fun x=> coef_wave p x.1 x.2 _),
    hU _ _ (rolls.refl _), hV _ _ (rolls.refl _)]

variable {K : Momentum → CompM α α} {U : Matrix (Co c α) (Co c α) ℝ}
lemma inverse_poster (h : Poster σ K) (hQ : ∀ p∈ strip σ, IsUnit (K p).det) :
    Poster σ (fun p => (K p)⁻¹) :=
  ⟨fun hp => BillD.take (h.shape hp) (hQ _ hp),fun hu hp => by rw [h.shifts hu hp]⟩
lemma inverse_reality (p : Momentum) {M : ℕ → Side} (hM : Tendsto (fun i => (M i).val) atTop atTop)
    (hV : ∀ i, ∃ A : Matrix (Co (M i) α) (Co (M i) α) ℝ, Jaunt (approached A) K 0)
    (hR : Poster σ K) (hσ : 0<σ) (hp : star p=p) (i j) :
    star ((K (-p))⁻¹ i j)=(K p)⁻¹ i j := by
  choose A hA using hV
  have he := judge hM hA hR hσ hp
  have hr : ((K (-p))⁻¹)ᵀ=((K p)⁻¹)ᴴ := by rw [transpose_nonsing_inv, conjTranspose_nonsing_inv,he] -- check
  have hv := congrFun (congrFun hr j) i
  change (K (-p))⁻¹ i j=star ((K p)⁻¹ i j) at hv
  rw [hv,star_star]

section bound

variable {X : Slab α}
lemma output_inverse (h : Poster σ K) (hQ : Freezer X.dual X K σ C) (hσ : 0<σ)
    (hW : ∀ p∈strip σ, vflux (K p)⁻¹ ≤ W)
    (hp : ∀ (p : Momentum), star p=p → ∀ i j, star ((K (-p))⁻¹ i j)=(K p)⁻¹ i j)
    (ht : Jaunt (approached U) K 0) : U*(crystals (fun p=> (K p)⁻¹)).acts c=1 := by
  classical
  have hI:= inverse_poster h hQ.period
  let C:= crystals (fun p=> (K p)⁻¹)
  have hc: C.strip (σ/2) (castCost σ W):= crystal_budget W hI hσ hW
  have he:= Jaunt.row (m:=c) C (Row.rights _ _ hc (by positivity))
  have hg:= ht.hoist he
  apply prom_inj; rw [prom_one',prom_mul]; apply jaunt_sees (H:=fun _=>1) ?_ Jaunt.noop
  intro p q hv v
  rw [show crystals _= C from rfl,hg p q hv v]
  have hx:= hv.metric (real_frequency p)
  have hX : C.read q=(K q)⁻¹ := by
    ext i j
    have hy:= re_cast (firm_cell W hI hσ hW i j) hx; change Row.read C q i j=((K q)⁻¹ i j+star ((K (-q))⁻¹ i j))/2 at hy -- fix
    rw [hy,hp q hx]; ring
  change tune _ ((K q * C.read q) *ᵥ v) = _
  rw [hX,mul_nonsing_inv _ (hQ.period _ (Work.F07.realStrip _ hσ hx))]
end bound
end YM.WilsonBulk
