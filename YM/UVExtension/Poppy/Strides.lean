import YM.UVExtension.Poppy.Meter
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Poppy
open Finset Set Function Filter Metric Lattice Extraction Fallow
open scoped Topology BigOperators ContDiff Classical
variable {S:Schedule}{n m k N:ℕ}
/-- normalized coordinate finite differences on the torus in literal cutoff lattice units.
advance ≥ 1, weight normalized by actual separation of the two samples.
Forward: start=0. Backward: start = -advance steps on axis.
Centered: advance=twice radius and start = -radius steps. Even allows a
fixed integer stencil offset before any differencing operation. -/
structure Stride (n:ℕ) where
    axis : Axel n
    start : Tabletop n
    advance : ℕ
    positive : 0 < advance

def shift (t:ℝ)(s:Stride n)(F:Tabletop n→ℂ)(x: Tabletop n) := (( (t*s.advance:ℝ):ℂ))⁻¹ * (F (x+s.start+s.advance • hike s.axis)- F (x+s.start))

def strides (t:ℝ)(F:Tabletop n→ℂ): List (Stride n)→Tabletop n→ℂ
   | []=> F
   | a::m=> shift t a (strides t F m)

def bundle (m:List (Stride n)): Type := (j: Fin m.length) → Fin (m[j].advance)
lemma walks1 (S : Stride n)(t:ℝ)(ht:0<t)(F:Tabletop n→ℂ)(x:Tabletop n): shift t S F x= (↑(S.advance):ℂ)⁻¹ * ∑ k : Fin S.advance, climbing t F S.axis (x+S.start+k.val • hike S.axis):=by
   let Q (i:ℕ):= climbing t F S.axis (x+S.start+i • hike S.axis); let D (i:ℕ):= F (x+S.start+i • hike S.axis); have hx:(t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ht.ne'
   have he (k:ℕ): ∑ i∈Finset.range k,Q i= (t:ℂ)⁻¹ * (D k-D 0):=by
      induction k with
      | zero=> simp
      | succ i ih=> rw [Finset.sum_range_succ,ih]; unfold Q climbing; rw [← mul_add]; congr 1; unfold D; rw [add_smul,one_smul,←add_assoc]; ring
   change _=(↑(S.advance):ℂ)⁻¹ * ∑ k : Fin S.advance, Q k.val; unfold shift; rw [← show (∑ i∈Finset.range S.advance,Q i)=_ from Finset.sum_range Q]
   rw [he, Complex.ofReal_mul, mul_inv_rev]; unfold D; simp only [zero_smul,add_zero, Complex.ofReal_natCast,mul_assoc]

-- portable certificate: convex average over finitely many offsets (for a fixed word)
lemma ancestors (l:List (Stride n)) : ∃ (I: Type) (_:Fintype I),letI := ‹Fintype I›; ∃ (u:I→Tabletop n) (c:I→ℂ),(∑ i,c i)=1∧∀ (t:ℝ),0<t → ∀ (F:Tabletop n→ℂ) x, strides t F l x=∑ j,c j*rake t F (l.map Stride.axis) (x+u j):=by
   induction l with
   | nil=> refine ⟨Unit,inferInstance,fun _=>0,fun _=>1,by simp,?_⟩; intro t ht F x; simp [strides,rake]
   | cons a l ih=>
      obtain ⟨I,J,u,c,hc,hF⟩:=ih
      let y (i : I × Fin a.advance):= c i.1 * (a.advance:ℂ)⁻¹
      let v (j:Fin a.advance) := a.start + j.val • hike a.axis
      have hp: (a.advance:ℂ)≠0:= Nat.cast_ne_zero.mpr a.positive.ne'
      refine ⟨I× Fin a.advance,inferInstance,fun i=>u i.1 + v i.2,y,?_,?_⟩
      · rw [Fintype.sum_prod_type]; simp only [y, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; simp_rw [mul_left_comm (↑a.advance:ℂ),mul_inv_cancel₀ hp,mul_one]; exact hc
      intro t ht F x; let f:= rake t F (l.map Stride.axis); have he j: climbing t (strides t F l) a.axis (x+v j)=∑ i : I,c i* climbing t f a.axis (x+(u i+ v j)):=by
          unfold climbing; rw [hF t ht F _,hF t ht F _,←Finset.sum_sub_distrib,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold f; rw [← mul_sub,mul_left_comm]; congr 2 <;> try rw [show x+v j+hike a.axis+u i= x+(u i+v j)+hike a.axis by abel, show x+v j+u i=x+(u i+v j) by abel]
      rw [strides,walks1 _ _ ht,Fintype.sum_prod_type, Finset.sum_comm]; simp only [y,List.map_cons,rake]; simp_rw [mul_assoc,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold v at he; rw [add_assoc x,he]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; exact mul_left_comm ..
end YM.UVExtension.Poppy
