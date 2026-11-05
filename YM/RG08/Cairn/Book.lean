import YM.RG08.Cairn.Packs
import YM.RG08.Tack.Loops
import YM.RG08.Aggregate.Voice

/-! # All-orders precision-width receipts for packing Φ into block units.
    hypotheses may refer to gauge/rotation laws only before substitution;
    exchange included. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cairn
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03 Matrix
open Tack Rudder Aggregate
open scoped BigOperators Classical ContDiff Topology Matrix Matrix.Norms.Frobenius NNReal InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}{I J:Type}{n e:ℕ}

def box (P:Patch)(F:Flake n (Market (Loc G 1))):Flake n (Market (Head P G)):=install (⟨Sum.inl,Sum.inl_injective⟩ :Co P.L (Loc G 1)↪ Head P G) (Cairn.coast P.L F)
def upper (P:Patch)(F:Flake n (Market (Loc G 1))):Flake n (Market (Head P G)):=install (⟨Sum.inr,Sum.inr_injective⟩ :Loc G 1↪ Head P G) F
lemma box_sym {F: Flake n (Market (Loc G 1))}(h:Cohort F)(ht:Forms.Sym F)(P:Patch): Cohort (Cairn.box P F) ∧ Forms.Sym (Cairn.box P F):=⟨install_wind _ (coast_y _ h),install_sym _ (coast_sym _ ht)⟩
lemma box_cost {F: Flake n (Market (Loc G 1))}{σ p:ℝ}(h:Held (carpet _) σ p F)(ht:0≤σ)(P:Patch): Held (carpet _) σ (Real.exp (8*σ)*p) (Cairn.box P F):=install_held _ (coast_held _ h ht)
lemma box_sub (P:Patch)(A B:Flake n (Market (Loc G 1))): Cairn.box P (A-B)=Cairn.box P A-Cairn.box P B:=by
 unfold Cairn.box;rw [show coast P.L (A-B)=coast P.L A-coast P.L B from rfl,install_sub]
lemma low_poly (S:StepData c f){F:Flake n (Market (Loc G 1))}(o:Fin n)(h:Cohort F):parley (pour (P:=c) (Cairn.box S.patch F) o) = MvPolynomial.rename (lowSlot S) (parley (pour (P:=f) F o)):=by
 rw [Cairn.box,install_poly,coast_poly S o h,MvPolynomial.rename_rename];rfl
lemma high_poly (S:StepData c f)(F:Flake n (Market (Loc G 1)))(o:Fin n):parley (pour (P:=c) (upper S.patch F) o) = MvPolynomial.rename (highSlot S) (parley (pour (P:=c) F o)):=by rw [upper,install_poly];rfl

variable [Fintype I][Fintype J]
omit [Fintype I] [Fintype J] in
lemma censor (m:I→J)(f:Port I)(e:ℕ): tap e (belt (fun i=>rod (m i)) f)= MvPolynomial.rename m (tap e f):=by
 have he (p:Inn I):lug (fun i=>rod (m i)) p = liftInn (MvPolynomial.rename m p):=by
   induction p using MvPolynomial.induction_on with
   | C b=>unfold lug;rw [MvPolynomial.aeval_C,MvPolynomial.rename_C,PowerSeries.algebraMap_apply];rfl
   | add _ _ ha hb=>simp only [map_add,ha,hb]
   | mul_X p j hp=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,hp,MvPolynomial.rename_X,lug,MvPolynomial.aeval_X]
 change tap e (spool (lug (I:=I) (fun i=>rod (m i))) f)=_;rw [ships];simp_rw [he];unfold tap;rw [Finset.sum_eq_single e (fun b hb hbe=>by rw [PowerSeries.coeff_C,if_neg (by simp only [mem_range] at hb;omega)]) (by simp)];simp

-- peripheral version

def leaf (S:StepData c f){n:ℕ}(F:Rudder.Raw G.ColorIndex n)(o:Fin n)(e:ℕ) : Port (Epic S.patch G c):= PowerSeries.X^e *belt (fun i=>rod (lowSlot S i)) (tax n (booked F o f))
def uplift (S:StepData c f){n:ℕ}(F:Rudder.Raw G.ColorIndex n)(o:Fin n)(e:ℕ) : Port (Epic S.patch G c):=PowerSeries.X^e *belt (fun i=>rod (highSlot S i)) (tax n (booked F o c))
lemma leaf_frame (S:StepData c f){F:Rudder.Raw G.ColorIndex n}(o:Fin n)(m k:ℕ){σ p:ℝ}(h:Cohort F)(ht:Held (carpet _) σ p F)(hp:0≤p)(hs:0<σ)(i:Fin (k+n)): tap (m+k) (leaf S F o m)=parley (pour (P:=c) (box _ (completed F o (k+n))) i):=by
 rw [tap,leaf,add_comm m k,PowerSeries.coeff_X_pow_mul (n:=m),← show ∀ (F:Port (Epic S.patch G c)), tap k F=PowerSeries.coeff k F from fun _=>rfl,censor,Camera.audited,reserve o i h ht hp hs]
 obtain ⟨D,hD,h⟩:=completed_held G (k+n) o hs
 exact (low_poly S i (h F hp ht).2.2).symm
lemma upper_frame (S:StepData c f){F:Rudder.Raw G.ColorIndex n}(o:Fin n)(m k:ℕ){σ p:ℝ}(h:Cohort F)(ht:Held (carpet _) σ p F)(hp:0≤p)(hs:0<σ)(i:Fin (k+n)): tap (m+k) (uplift S F o m)=parley (pour (P:=c) (upper _ (completed F o (k+n))) i):=by
 rw [tap,uplift,add_comm m k,PowerSeries.coeff_X_pow_mul (n:=m),← show ∀ (F:Port (Epic S.patch G c)), tap k F=PowerSeries.coeff k F from fun _=>rfl,censor,Camera.audited,reserve o i h ht hp hs,high_poly S ..]

-- compare actual with channels including higher g, no budget constants post in A/B
lemma routes (S:StepData c f)(w:Cellar (Epic S.patch G c)): offers G (w ∘ lowSlot S)=represent (low S w) ∧ offers G (w ∘ highSlot S)=represent (high S w):= ⟨funext fun e=>by rw [Work.F03.represent_link];rfl,funext fun e=>by rw [Work.F03.represent_link];rfl⟩
def power (x:I→J)(A:Strip J I):Strip I I := A ∘ x -- general K instead
omit [Fintype I] [Fintype J] in
lemma driven {N:Type}[Fintype N](x:J→I)(A:Strip I N)(f:Port J):
    belt (rescaleFields A) (belt (fun i=>rod (x i)) f)=belt (rescaleFields (A ∘ x)) f:=by
 change ((belt (rescaleFields A)).comp (belt _)) f=_
 rw [switched];simp_rw [belt_x];rfl

lemma lower_same (S:StepData c f){F:Rudder.Raw G.ColorIndex n}(o:Fin n)(m:ℕ){σ p:ℝ}(h:Cohort F)(ht:Held (carpet _) σ p F)(hp:0≤p)(hs:0<σ)(hf:Symmetry.hue (Symmetry.dressed G n) F) (s:Signed)(v:Site f)(A B:Strip (Epic S.patch G c) I)(hA:∀ i,Pace (A i))(hB:∀ i,Pace (B i))(he:roll A 0=0)(hz:roll B 0=0)
 (hx:∀ᶠ z:Cellar I in 𝓝 0,∃ t:Site f→G.El,represent (low S (roll B z))=Lattice.gauge t (Lattice.pull s v (represent (low S (roll A z))))):
   belt (rescaleFields A) (leaf S F o m)=belt (rescaleFields B) (leaf S F o m):=by
 rw [leaf,_root_.map_mul,_root_.map_pow,_root_.map_mul,_root_.map_pow,belt_g,belt_g,driven,driven]
 have he'(i):roll (A ∘ lowSlot (G:=G) S) 0 i=0:=congrFun he _ ;have ht'(i):roll (B ∘ lowSlot (G:=G) S) 0 i=0:=congrFun hz _
 apply congrArg (fun p:Port I=>PowerSeries.X ^ m*p)
 apply switch_rep _ _ (fun i=>hA _) (fun i=>hB _) (funext he') (funext ht') s v o h hf hs hp ht
 filter_upwards [hx] with v H; obtain ⟨t,hg⟩:=H;refine ⟨t,?_⟩
 rw [←(routes S _).1,←(routes S _).1] at hg; exact hg
end YM.RG08.Cairn
