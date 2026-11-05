import YM.MergeProof.Tuna
import YM.MergeProof.Zing
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories
variable (T: GaugeDoor R E) (q:ι→Leaf R)
    (w':Wing)(h:∀ i,(q i).turn=w')
    [Countable ι] {m:StepData c f}
    (hp : SoundDoor m T)(he:Tunes T) (r:ι→ℂ)
    (hc:Summable (fun i=> ‖r i‖*load (q i)))
variable {s:B.Mode}(v:V)
-- shrink to two wings. pay sum scales. do not pass through sum weights nil.
omit [Countable ι] in
lemma prose_me (t:ι→ℝ)(M:Leaf R)(h:Grouped M t q) (U : Config G f): HasSum (fun i=> (↑(t i):ℂ)*prose (q i) U) (prose M U):=by
   unfold prose; simp_rw [h.turn]; cases M.turn with
   | gasKey j=> simp
   | logKey j=> refine ((Complex.ofRealCLM).hasSum (h.earn U)).congr_fun (fun i=>?_); exact (Complex.ofReal_mul ..).symm
omit [Countable ι] in
lemma entry_me (t:ι→ℝ)(M:Leaf R)(h:Grouped M t q) (p:Box f)(U : Config G f): HasSum (fun i=> (↑(t i):ℂ)*entry (q i) p U) (entry M p U):=by
   unfold entry; simp_rw [h.turn]; cases M.turn with
   | gasKey j=>
       dsimp only
       split; · exact ((Complex.ofRealCLM).hasSum (h.earn U)).congr_fun (fun i=>(Complex.ofReal_mul ..).symm)
       simp
   | logKey j=> simp
omit [Countable ι] in
private lemma com {Z:ι→ℂ} {r_:ι→ℂ}{a b:ℂ}(hr:HasSum (fun i=>(↑(r_ i).re:ℂ)*Z i) a)(hi:HasSum (fun i=>(↑(r_ i).im:ℂ)*Z i) b) : HasSum (fun i=> r_ i*Z i) (a+Complex.I*b):= (hr.add (hi.mul_left _)).congr_fun (fun i=> by nth_rw 1 [← Complex.re_add_im (r_ i)]; ring)
include h hp he hc
-- per leaf cost bound at e ≤P. Frame supplies α and ω totals.
lemma solo [Nonempty ι] (v:V)(B:Census V)(w:V→ℝ)(hw:∀ i,0<w i): ∃ F:Bool→Hat B R, (∀ i,(F i).s=B.fire v ∧ (F i).M.turn=w') ∧ (∑ i,fare (F i) w)≤ 2*w v*∑' i, ‖r i‖*(q i).weight ∧
    (∀ U,∑ i,odour (F i) U=Poly.send (B.fire v) (∑' i,r i*prose (q i) U))∧ (∀ i U,∑ j,fragrance (F j) U i=Poly.send (B.fire v) (∑' j, r j*entry (q j) i U)) ∧
    ∀ i U, (∑ j,owl (F j) T v i U)=∑' j, r j*quoted T (q j) i U:=by
   let a i:= (r i).re; let b i:=(r i).im; let k i:=(q i).weight; have hs : Summable (fun i=> ‖r i‖*k i):= hc.of_nonneg_of_le (fun i=> mul_nonneg (norm_nonneg _) (Leaf.profit (q i))) (fun i=> mul_le_mul_of_nonneg_left (R.p.loMass _ _ (Leaf.profit (q i))) (norm_nonneg _))
   have hh i: ‖a i‖*k i≤ ‖r i‖*k i:= mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (Leaf.profit _)
   have hx i: ‖b i‖*k i≤ ‖r i‖*k i:= mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm _) (Leaf.profit _)
   have hH := hs.of_nonneg_of_le (fun i=> mul_nonneg (norm_nonneg (a i)) (Leaf.profit (q i))) hh; have hX:= hs.of_nonneg_of_le (fun i=> mul_nonneg (norm_nonneg (b i)) (Leaf.profit (q i))) hx
   obtain ⟨M,hM,hm,hm'⟩:= squash q w' h a hH; obtain ⟨N,hN,hn,hn'⟩:= squash q w' h b hX
   let m:Hat B R:= ⟨M,B.fire v,Finset.singleton_nonempty _,1⟩; let n:= ({M:=N,charge:=Complex.I,s:=B.fire v,shiny:= Finset.singleton_nonempty _}:Hat B R); let f:= fun x:Bool=> if x then m else n
   have hy:f true=m:=by simp [f]
   have hv:f false=n:=by simp [f]
   refine ⟨f,fun i=> ?_,?_,fun U=>?_,fun i U=> ?_,fun i U=>?_⟩
   · cases i; rw [hv]; exact ⟨rfl,hn⟩; rw [hy]; exact ⟨rfl,hm⟩
   · rw [Fintype.sum_bool, hy,hv]; simp only [fare,sumFee,m,n,Poly.solo_toll, norm_one,Complex.norm_I,mul_one,hm',hn']; let x:=∑' i, ‖r i‖*k i; have hh:=mul_le_mul_of_nonneg_left (hH.tsum_le_tsum hh hs) (hw v|>.le); have ht:= mul_le_mul_of_nonneg_left (hX.tsum_le_tsum hx hs) (hw v|>.le); nlinarith only [hh,ht]
   · have ht:=com (r_:=r) (Z:=fun i=> prose (q i) U) (prose_me q a M hM U) (prose_me q b N hN U); rw [ht.tsum_eq,Fintype.sum_bool,hv,hy]; unfold odour; dsimp only [m,n]; rw [← Extra.Trajectories.send_add]; congr 1; ring
   · have ht:=com (r_:=r) (Z:=fun j=> entry (q j) i U) (entry_me q a M hM i U) (entry_me q b N hN i U); rw [ht.tsum_eq,Fintype.sum_bool,hv,hy]; unfold fragrance; dsimp only [m,n]; rw [← Extra.Trajectories.send_add]; congr 1; ring
   have ht:=com (r_:=r) (Z:=fun j=> quoted T (q j) i U) (tables T a hM he hp i U) (tables T b hN he hp i U); rw [ht.tsum_eq,Fintype.sum_bool,hv,hy]; simp only [owl,m,n,↓reduceIte,one_mul]
end YM.MergeProof.Menu
