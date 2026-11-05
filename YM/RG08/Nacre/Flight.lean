import YM.RG08.Nacre.Ibis

/-! # Completed Taylor laws are exactly linear for any finite-size lists of
 supported curvature cards and any scalars. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Nacre
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost Sedan Extra.Iteration
open PowerSeries Finset.Nat
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{r e n k:ℕ}

private lemma deck_scalar {I: Type}[Fintype I](f:Still I)(hf:Pace f)(i:ℕ)(s:ℝ):Camera.deck i (s • f)=s • Camera.deck i f:=by
 induction i generalizing f with
 | zero=>rfl
 | succ i hi=>
    ext x
    have h (j:I): Camera.wedge j (s • f) =ᶠ[𝓝 0] s • Camera.wedge j f:=by
      filter_upwards [Pace.diff hf] with x hx
      unfold Camera.wedge;rw [fderiv_const_smul hx];rfl
    change _*Camera.deck i _ _= s*(_* _);rw [deck_same (h:=h _) _,hi _ (Pace.wedge _ hf),Pi.smul_apply,smul_eq_mul];ring

private lemma stored_scalar (F:Flake n (Market (Rayk G 2)))(o:Fin n)(x:Coord (n:=n))(s:ℝ)(k:ℕ):stored (deposit (s • F) o x) k=s • stored (deposit F o x) k:=by
 let a:=deposit F o x;let c:=deposit (s • F) o x;let P:=attic a.length
 have he:c.coeff=s • a.coeff:=by ext j;change (if _ then (s • F) _ else 0)=_; simp only [a,deposit,neck,Pi.smul_apply];split_ifs <;>simp
 have hh:showAtom c (0:Site P)=s • showAtom a 0:=by ext j;simp only [showAtom,Atom.unmasked,Atom.poly,he,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum];rfl
 have hc(a:Atom G n):Pace (showAtom a (0:Site P)):=by obtain ⟨C,hC,H⟩:=per_atom G n 1 (by positivity:0<(1:ℝ));exact (H a _ _).analytic
 ext W
 change (∑ j:Tape k (Bedge G P),if W= (Isles.reach ∘ j) then Camera.deck k (showAtom c 0) j else 0)=s* ∑ j:Tape k (Bedge G P),if W=(Isles.reach ∘ j) then Camera.deck k (showAtom a 0) j else 0
 rw [hh,deck_scalar _ (hc a),Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;split_ifs <;>simp

lemma completed_scale (p:ℝ){n:ℕ}(F:Rudder.Raw G.ColorIndex n)(i:Fin n)(k:ℕ):completed (p • F) i k=p • completed F i k:=by
 have he:compress 2 (p • F)=p • compress 2 F:=rfl
 ext x
 simp only [completed,Carrel.average,grown,bleach,Carrel.mass,he,Carrel.account,stored_scalar,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,woven,adjust,tsum_mul_left]
 rw [mul_left_comm p]; congr 1;rw [Finset.mul_sum]; apply Finset.sum_congr rfl;intro m _; rw [mul_left_comm p, Finset.mul_sum]; rw [Finset.mul_sum,Finset.mul_sum];apply Finset.sum_congr rfl;intro s _;ring
variable {F V: Gird G r}
lemma completed_add (h:Honor G (Mount.rank r) F)(ht:Honor G (Mount.rank r) V)(k:ℕ)(j:Fin k): completed (F+V) (stick r) k=completed F (stick r) k+completed V (stick r) k:=by
 obtain ⟨hf,s,u,hs,hu,hU⟩:=h.plus ht
 obtain ⟨w,e,n,he,hN,hO⟩:=ht
 have hx:= Carrel.cracks (F+V) V (stick r) j (p:=max u n) (σ:=min s e) (hu.trans (le_max_left ..)) (lt_min hs he) (hU.mono (min_le_left ..) (le_max_left ..) (fun _=>le_rfl)) (hO.mono (min_le_right ..) (le_max_right ..) (fun _=>le_rfl))
 rw [add_sub_cancel_right] at hx
 exact (eq_sub_iff_add_eq.mp hx).symm -- check
lemma completed_galaxy {I:Type}(x:Finset I)(p:I→ℝ)(f:I→Gird G r)(h:∀ i∈x, Honor G (Mount.rank r) (f i))(k:ℕ)(j:Fin k):
   Honor G (Mount.rank r) (∑ a∈x,p a • f a) ∧ completed (∑ a∈x,p a • f a) (stick r) k=∑ a∈x,p a • completed (f a) (stick r) k:=by
 induction x using Finset.induction_on with
 | empty=>
          cases k
          · exact Fin.elim0 j
          rw [sum_empty,sum_empty]; exact ⟨Honor.nil,completed_null ..⟩
 | insert a s he ih=>
   obtain ⟨hc,hI⟩:=ih (fun i hi=>h i (mem_insert_of_mem hi))
   have hu:=(h a (mem_insert_self ..)).smul (p a)
   rw [sum_insert he,sum_insert he,completed_add hu hc _ j, hI,completed_scale];exact ⟨hu.plus hc,rfl⟩
end YM.RG08.Nacre
