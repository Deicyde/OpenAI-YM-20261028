import YM.TraceExtension.Fen.Tep
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} {d k:ℕ}{σ A C q:ℝ}(R:Rep G n) (h:R.path.Bounds R.clip σ A C){I:Type}(b:I→Barley)
lemma ul_roll (i:Barley)(x:Site n)(U:Config G n) : ul R.path R.clip i 0 (Lattice.translate x U)=ul R.path R.clip i x U:=by
    have ht(w:Slot): w.atSite (Lattice.translate x U) 0=w.atSite U x:=by simp only[Slot.atSite,Push.Local.expand_translate,zero_add]
    cases i with
    | inr j=> rw [fresh_loop,fresh_loop]; simp only[Atom.unmasked,ht]
    | inl j=> change _*_=_*_; apply congr_arg (_*·); unfold Low.plain; simp only[ht]; rw [show faceValue (Lattice.translate x U) (0,j.1)=faceValue U (x,j.1) from ?_]; rw [faceValue,← pull_one,travel_pull,faceValue]; simp [affine]
lemma roll_c (X:Site n)(F:Signed)(U:Config G n): Seat.view (F,F.act X) U=Lattice.translate X (pull F 0 U):=by rw[← pull_one,pull_pull,mul_one,affine, add_zero]; rfl
lemma aton {n:Side}{k:ℕ}(U:Config G n)(o:Site n){p: ℕ→Atom G k}(h:SumBudget (fun i=>(p i).budget σ) A)(hs:0<σ):Summable (fun i=> (p i).unmasked U o):=by
    refine Summable.of_norm_bounded (h.2.1.mul_right ((2:ℝ)^k)) (fun i=>?_); exact ((p i).unmasked_bound ..).trans (mul_le_mul_of_nonneg_right ((p i).lower_budget σ hs) (by positivity))
include h
lemma stanza (o:Site n)(U:Config G n): Summable (fun i:GreenA=>ul R.path R.clip (legF i) o U):=by
    exact Summable.sum _ (Low.plain_sum h _ _) (Summable.sum _ (aton U o h.three h.width) (aton U o h.four h.width))
lemma main_cal (U:Config G n): mainTerm R.clip R.path U= ∑' i:Seat n×GreenA,fer R i.1 (legF i.2) U:=by
    unfold fer; let V(i:GreenA) := ul R.path R.clip (legF i) (0:Site n); rw [← layer_total V U (fun P=> stanza R h 0 P)]; unfold mainTerm layer Patch.average; apply congr_arg (VerifiedReset.factor * ·); rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun s _=>?_ ; rw [← Equiv.sum_comp s.actEquiv.toEquiv]
    let p:=R.clip; let W:=R.path; let A:=pull s 0 U; let f(x)(b:GreenA):=ul W p (legF b) x A
    let g x:=∑ j: PlaqAxes,(p.direct*G.price (faceValue A (x,j))+ ‖W.ell A (x,j)‖^2/2)
    have hz(x:Site n): (∑' i,V i (Seat.view (s,s.act x) U))= g x+ (∑' i,(W.cubic i).unmasked A x)+(∑' i,(W.quartic i).unmasked A x):=by
        have ht: (fun i=>V i (Seat.view (s,s.act x) U))= f x:=funext fun i=> by rw [roll_c]; exact ul_roll ..
        rw [ht]
        rw[Summable.tsum_sum (f:=f x) ((stanza R h x A).comp_injective Sum.inl_injective) ((stanza R h x A).comp_injective Sum.inr_injective)]; rw[show (∑' k:High,f x (Sum.inr k))= _ from Summable.tsum_sum (f:=fun k:High=>f x (.inr k)) (aton A x h.three h.width) (aton A x h.four h.width), show (∑' i:Low, f x (Sum.inl i))=g x from Low.plain_total h x A]; rw [add_assoc]; rfl
    unfold Precision.quadratic uncut; dsimp only; rw [Fintype.sum_prod_type]; simp only [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _=>?_ ); exact (hz i).symm
lemma calibre (U:Config G n): HasSum (fun i:Seat n×GreenA=>fer R i.1 (legF i.2) U) (mainTerm R.clip R.path U):=by
    let f(i:Seat n×GreenA):= ul R.path R.clip (legF i.2) 0 (i.1.view U); have ht:Summable f:= Summable.of_norm ((summable_prod_of_nonneg (f:=fun i:Seat n×GreenA=>‖f i‖) (fun i=>norm_nonneg (f i))).2 ⟨fun i=> (stanza R h 0 (i.view U)).norm, Summable.of_finite⟩)
    rw[main_cal R h]; exact (ht.mul_left VerifiedReset.factor).hasSum
end YM.Trace.Fen
