import YM.UVExtension.Crown.Top
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Set Filter RG Lattice Wilson Precision
open Lamppost AnalyticBridge VerifiedReset Collection
open Oriel Oriel.Charted Push Push.AbsoluteSums Metric RG.Shoot Complex Finset
open scoped Topology ContDiff Matrix.Norms.Frobenius NNReal Classical
variable {G : Gauge} (h:G.Simple)(T:Levels G) (N:ℕ)(X:ℕ→Type)[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℂ (X i)]
namespace Cart
variable (V:Cart T N X)(r:ℕ)(hr:r ≤ N)
set_option quotPrecheck false
local notation "c'"=> tally T N X V
local notation "Λp"=> fun i=>pulse T i
variable (hf:Fees T) {v:ℂ}{z:PlotN N}(hp:z∈Harbor N)
local notation "fl"=> (V.locket T N X r)
variable (hh:v∈Broad T)
noncomputable def lodgeX (w:ℂ): PlotN N:= chosenB h T N X V r hf (b:=w)
include hr
lemma limitNodes (w:ℂ) (hw:w∈palms): (lodgeX h T N X V r hf w) ⟨r,Nat.lt_add_one_iff.mpr hr⟩=w:=by
    let f:= lodgeX h T N X V r hf w; have hz:f=fl w f:= (zoned h T N X V r hf hw).2.symm; rw [show lodgeX h T N X V r hf w= _ from hz]; unfold locket; rw [if_pos (show r ≤ r from le_rfl)]; dsimp only; unfold Cart.pieces; rw [Finset.sum_eq_zero (fun j hj=>if_neg (not_le.mpr (Finset.mem_range.mp hj))), sub_zero, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr (pulse_pos T r).ne')]
omit hr
lemma homage (p q:PlotN N)(H:∀ i:Fin (N+1),r ≤ i.val→p i=q i) (m:ℕ) (hx:r ≤ m)(ht:m ≤ N): pivot T N X V p m ht=pivot T N X V q m ht:=by
   have h (m) h hm:node N p m hm=node N q m hm:=H _ h
   induction ht using Nat.decreasingInduction with
   | self=> unfold pivot; rw [roof,roof,h N hx le_rfl] -- H expands?
   | of_succ i hi ih=> unfold pivot; rw [edge T N X V p i hi,edge T N X V q i hi,h i hx hi.le,ih (hx.trans i.le_succ)]
noncomputable def erased (z:PlotN N): PlotN N:=fun i=> if r ≤ i.val then z i else 0
lemma sliceV (z:PlotN N)(i:ℕ): pieces T N X V r i (erased N r z)=pieces T N X V r i z:=by
   apply Finset.sum_congr rfl; intro j _; split_ifs; swap; · rfl
   next h =>
   unfold tally; split_ifs; swap; · rfl
   next ht => exact congr_arg (V.gain j ht) (homage T N X V r _ z (fun _ h=> if_pos h) (j+1) (h.trans j.le_succ) ht)
lemma billsA (z:PlotN N)(i:ℕ)(he:r≤ i) : pieces T N X V r i z = (∑ j∈ range i, V.tally T N X z j) -∑ j∈ range r,V.tally T N X z j:=by
   unfold pieces; induction i,he using Nat.le_induction with
   | base=> rw [sub_self]; exact sum_eq_zero fun i hi=> if_neg (not_le.mpr (mem_range.mp hi))
   | succ i h ih=> rw [sum_range_succ,sum_range_succ,ih,if_pos h]; abel
include hr hh
lemma recount (x:ℂ) (he:x∈palms)(hg:x=node N (picked h T N X V hf (b:=v)) r hr): Cart.lodgeX h T N X V r hf x= erased N r (picked h T N X V hf (b:=v)):=by
    let z:= picked h T N X V hf (b:=v); have hz:= laced h T N X V hf hh; have hp m (hm:m≤N) : node N z m hm = (pulse T m:ℂ)⁻¹*(v-∑j∈ range m,V.tally T N X z j):= congr_fun hz.2.symm _
    apply uniquely h T N X V r hf he
    · funext i; unfold locket; split; swap; · next ht=> exact (if_neg ht).symm
      next hQ=>
      change (pulse T i.val:ℂ)⁻¹*(↑(pulse T r)*x - _) = erased N r z i; rw [show erased N r z i= z i from (if_pos hQ:erased N r z i=z i)]; rw [show z i=node N z i.val (Nat.le_of_lt_succ i.isLt) from rfl,hp, sliceV, billsA T N X V r z i.val hQ, hg, show node N (picked h T N X V hf (b:=v)) r hr=_ from hp r hr, mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (pulse_pos T r).ne')]; congr 1; abel
    apply mem_closedBall_zero_iff.mpr; refine (pi_norm_le_iff_of_nonneg (by norm_num [rad,rim])).2 fun i=>?_ ; unfold erased; split; next => exact (norm_le_pi_norm z _).trans (mem_closedBall_zero_iff.mp hz.1)
    norm_num [rad,rim]

-- harmonic center q full captured. guard nearly all.
lemma ground : ‖node N (picked h T N X V hf (b:=v)) r hr‖ ≤ rad*5/8:=by
    let z:= picked h T N X V hf (b:=v); have hz:= laced h T N X V hf hh; let i:Fin (N+1):=⟨r,Nat.lt_add_one_iff.mpr hr⟩
    change ‖z i‖ ≤ _; rw [show z i=_ from congr_fun hz.2.symm i]; unfold veil; rw [norm_mul,norm_inv,norm_real,Real.norm_of_nonneg (pulse_pos ..|>.le)]
    apply (inv_mul_le_iff₀ (pulse_pos ..)).2; apply (norm_sub_le ..).trans; have hL:‖v‖ ≤ flatTime T:= (mem_ball_zero_iff.mp hh).le
    apply (add_le_add hL (arrive h T N X V hf hz.1 i)).trans; unfold flatTime; unfold soft rad rim; linarith only [pulse_mono T h (Nat.zero_le (i:ℕ)),pulse_pos T (i:ℕ)]
omit hh hr
include h
lemma pale (x:ℝ) (ha:(x:ℂ)∈palms)(hy:∀ z:PlotN N,z∈Harbor N→ Light N z→∀ i,(tally T N X V z i).im=0): Light N (V.lodgeX h T N X r hf x):=by
   let f:= fl x
   have hp (k:ℕ): f^[k] 0∈ Harbor N ∧ Light N (f^[k] 0):=by
      induction k with
      | zero=> exact ⟨harbor N,by simp [Light]⟩
      | succ k ih=>
        rw [iterate_succ_apply']; refine ⟨V.possibly h T N X r hf _ ha ih.1,fun i=>?_⟩; let w:= (f^[k] 0)
        unfold f locket; split; swap; · rfl
        have hh(j): (if r≤j then tally T N X V w j else 0).im=0:=by split; exact hy w ih.1 ih.2 j; rfl
        change (((pulse T i.val:ℂ))⁻¹ * ((pulse T r:ℂ)* (x:ℂ) - pieces T N X V r i.val w)).im=0; unfold pieces; simp [← Complex.ofReal_inv,mul_im,hh]
   let g:= fun k:ℕ=> f^[k] 0
   have ht : Tendsto g atTop (𝓝 (lodgeX h T N X V r hf x)):=by
      refine Metric.tendsto_nhds.mpr fun ε he=>?_; have hF:Tendsto (fun k:ℕ=>rad*(1/2)^k/(1-1/2)) atTop (𝓝 0):= by simpa only [mul_zero,zero_div] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤ (1/2:ℝ)) (by norm_num)).const_mul rad).div_const ((1:ℝ)-1/2))
      filter_upwards [hF.eventually (gt_mem_nhds he)] with k hk; exact (wheels h T N X V r hf ha k).trans_lt hk
   have hh:= mem_iInter.mp (isClosed_iInter (f:=fun i:Fin (N+1)=> {z:PlotN N| (z i).im=0}) (fun i=> isClosed_eq (Complex.continuous_im.comp (continuous_apply i)) continuous_const) |>.mem_of_tendsto ht (Eventually.of_forall fun k=> by simp only [mem_iInter]; exact (hp k).2)); exact hh
end Cart
end YM.UVExtension.Camp
