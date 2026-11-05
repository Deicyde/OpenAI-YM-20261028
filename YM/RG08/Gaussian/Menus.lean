import YM.RG08.Gaussian.Regroup

/-! # Recover cover Rows from evaluations on genuine shifted stencils

`Menu` for producing block-dependent prices. Exact period resolution independent
of sizes. No kernel width originally only available post-block should use this
lemma by feeding in a different reduced width. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Finset Laurent Lattice Wilson RG Precision Exterior Bloch Matrix
open Next.Free Work.F08 Stationary
open scoped Topology BigOperators Classical

abbrev Offers (L : Side) (α β : Type) := (c f : Side) → f.val=c.val*L.val → Matrix (Co c α) (Co c β) ℝ

/-- Same stencil, strip on true displacements. -/
def Repeats {L : Side} {α β : Type} (O : Offers L α β) (σ : ℝ) : Prop :=
    ∃ C : ℝ, 0 ≤ C ∧ ∃ R : Row α β, R.strip σ C ∧ ∀ c f h,R.acts c=O c f h

variable {α β γ : Type} {L : Side} {σ : ℝ}

lemma repeater {O : Offers L α β} (h : ∃ (K : Row α β) (C : ℝ), K.strip σ C ∧ ∀ c f hp,K.acts c= O c f hp) :
    Repeats O σ := by
  obtain ⟨K,C,H,h'⟩ := h; exact ⟨max 0 C,le_max_left ..,K,strip_mono H le_rfl (le_max_right ..),h'⟩

namespace Repeats
variable {X Y : Offers L α β}
lemma minus (h : Repeats X σ) (g : Repeats Y σ) (hh : 0≤σ) :
    Repeats (fun c f i => X c f i-Y c f i) σ := by
  obtain ⟨x,hx,A,h,H⟩ := h; obtain ⟨y,hy,B,t,T⟩ := g
  exact ⟨x+y,add_nonneg hx hy,minusRows A B, strip_minus h t,fun c f i => by rw [acts_minus hh h t,H c f i,T c f i]⟩
lemma plus (h : Repeats X σ) (g : Repeats Y σ) (hh : 0<σ) :
    Repeats (fun c f i => X c f i + Y c f i) σ := by
  obtain ⟨x,hx,A,h,H⟩ := h; obtain ⟨y,hy,B,t,T⟩ := g
  refine repeater ⟨plusRows A B,_,strip_minus h (strip_scale t _),fun c f i => ?_⟩
  rw [Whole.acts_plus (show Whole A from ⟨_,_,hh,h⟩) (show Whole B from ⟨_,_,hh,t⟩), H c f i,T c f i]
lemma mult [Fintype β] {Z : Offers L β γ} (h : Repeats X σ) (g : Repeats Z σ) (hh : 0≤σ) :
    Repeats (fun c f i => X c f i * Z c f i) σ := by
  obtain ⟨x,hx,A,h,H⟩ := h; obtain ⟨y,hy,B,t,T⟩ := g
  exact repeater ⟨composeRows A B,_,strip_compose hh h t,fun c f i => by rw [acts_compose hh h t,H c f i,T c f i]⟩
lemma repl {X Y : Offers L α β} (h : Repeats X σ) (g : ∀ c f h, X c f h=Y c f h) : Repeats Y σ := by rw [show Y=X from (funext fun c => funext fun f => funext fun h => g c f h).symm]; exact h
end Repeats

abbrev View (L : Side) (α : Type) := (c f : Side) → f.val=c.val*L.val → Corn (Co c α) → Site c → ℝ

variable [Fintype α]

def Menu (M : View L α) : Prop :=
    ∀ σ : ℝ, 0 < σ → ∃ (b : Row Unit α) (K : ℝ), b.strip σ K ∧
      ∀ c f h x z, M c f h x z=(b.acts c *ᵥ x) (z,())

namespace Menu

variable {M N : View L α}
lemma relabel (h : Menu M) (ht : ∀ c f b x z,M c f b x z=N c f b x z) : Menu N := by
  rw [show N=M from (funext (fun c => funext (fun f => funext (fun b => funext (fun x => funext (ht c f b x)))))).symm]; exact h

lemma single [DecidableEq α] (L : Side) (p : α) (d : Cover) : Menu (L:=L)
    (fun c _ _ x z => x (z+wrap c d,p)) := by
  intro σ hp
  let A : Row Unit α := fun _ i z => if i=p then token d z else 0
  refine ⟨A,envelopeW σ d,fun i j => ?_,fun c f h x z => ?_⟩
  · unfold A; by_cases h : j=p
    · simpa [Width,h] using token_rate d σ
    simp [Width,SumBudget,h,(envelope_pos ..).le]
  have he (y : Site c × α) : A.acts c (z,()) y = if y=(z+wrap c d,p) then 1 else 0 := by
    classical
    rw [Row.acts,of_apply,tsum_eq_single d]; swap; · intro t ht; unfold A; split <;> simp_all [token]
    obtain ⟨y,j⟩ := y; by_cases hm : j=p <;> by_cases h : y=z+wrap c d <;> simp [*, A,token]
  unfold Matrix.mulVec dotProduct; simp_rw [he,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',mem_univ,if_true]

lemma zero (L : Side) (α : Type) [Fintype α] : Menu (L:=L) (α:=α) (fun _ _ _ _ _ => 0) :=
    fun _ h => ⟨0,0,fun _ _ => by simp [Width, SumBudget],fun c _ _ x _ => by simp⟩

lemma add (h : Menu M) (k : Menu N) : Menu (L:=L) (fun c f v x z => M c f v x z + N c f v x z) := by
  intro σ t; obtain ⟨b,K,h,H⟩ := h σ t; obtain ⟨a,C,k,P⟩ := k σ t
  refine ⟨plusRows b a,_,strip_minus h (strip_scale k _),fun i j u x z => ?_⟩
  dsimp only; rw [Whole.acts_plus (show Whole b from ⟨_,_,t,h⟩) (show Whole a from ⟨_,_,t,k⟩), H,P, Matrix.add_mulVec]; rfl
lemma scale (h : Menu M) (u : ℝ) : Menu (L:=L) (fun c f v x z => u * M c f v x z) := by
  intro σ t; obtain ⟨b,K,h,H⟩ := h σ t
  exact ⟨scaleRows u b,_,strip_scale h u,fun c f v x z => by dsimp only; rw [acts_scale,Matrix.smul_mulVec,H]; rfl⟩
lemma sub (h : Menu M) (k : Menu N) : Menu (L:=L) (fun c f v x z => M c f v x z - N c f v x z) :=
    (h.add (k.scale (-1))).relabel (fun _ _ _ _ _ => by simp [sub_eq_add_neg])
lemma total {ι : Type} (s : Finset ι) (f : ι → View L α) (h : ∀ i∈s,Menu (f i)) : Menu (L:=L)
    (fun c n v x z => ∑ i∈s,f i c n v x z) := by
  induction s using Finset.induction_on with
  | empty => exact relabel (zero L α) (fun c n v x z => by simp)
  | insert i s hi ih =>
    refine ((h i (mem_insert_self ..)).add (ih (fun j hj => h j (mem_insert_of_mem hj)))).relabel
      (fun c n v x z => ?_)
    rw [Finset.sum_insert hi]

end Menu

lemma menu_repeats [Fintype β] {O : Offers L β α} (hp : 0 < σ)
    (he : ∀ i : β, Menu (L:=L) (fun c f h x z => (O c f h*ᵥ x) (z,i))) : Repeats O σ := by
  choose V d hd h using fun i : β => he i σ hp
  let K : Row β α := fun i => V i ()
  refine repeater ⟨K, ∑ i : β, |d i|,fun i j => Width.mono (hd i () j) le_rfl
    ((le_abs_self _).trans (single_le_sum (f:=fun j => |d j|) (fun j _ => abs_nonneg (d j)) (mem_univ i))),?_⟩
  intro c f H; apply matrix_eq
  intro x; funext y; obtain ⟨z,j⟩ := y; dsimp only at h; rw [h j c f H x z]
  unfold K; unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]; rfl

end YM.RG08
