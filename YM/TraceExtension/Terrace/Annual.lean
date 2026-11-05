import YM.TraceExtension.Terrace.Casa
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Asymptotics
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=> C.path
local notation "H!"=> (C.path.levels.clock.hatBeta)
def CutQ (P:Levels G)(f:ℕ→ℕ):Prop:= ∀ᶠ k in atTop,(f k:ℝ) ≤ (P.clock.hatBeta k)^ (4:ℕ)
lemma CalmsK (P:Levels G)(h:G.Simple):Calms P.S 0 P.clock.hatBeta:=by
    intro e he; refine isBigO_iff.mpr ⟨1,?_⟩
    let t v:= P.clock.bar+G.slopeConstant*v
    have h0:= Real.isLittleO_log_id_atTop
    have hx := (Real.isLittleO_pow_exp_atTop (n:=1)).tendsto_div_nhds_zero
    have hz:P.S.scale = P.S.scale :=rfl
    have hf: Tendsto (fun i=> (P.clock.hatBeta i)/factor P.S e i) atTop (𝓝 0):=by
         have ht:= P.S.divergent.atTop_mul_const he
         have hp:Tendsto (factor P.S e) atTop atTop:= Real.tendsto_exp_atTop.comp ht
         have h':Tendsto (fun i=> P.S.scale i / factor P.S e i) atTop (𝓝 0):=by
            have hh:= (hx.comp ht).div_const e; rw[zero_div] at hh
            refine hh.congr fun i=>?_ ; simp only[comp_apply,pow_one]; change (_*e / _)/e= _; field_simp
         have hv:= h'.const_mul G.slopeConstant
         rw [mul_zero] at hv; simpa only [Calendar.hatBeta, add_div,mul_div_assoc,add_zero] using! (tendsto_const_nhds.div_atTop hp (a:=P.clock.bar)).add hv
    filter_upwards [hf.eventually (ge_mem_nhds zero_lt_one)] with i hi; rw [Real.norm_of_nonneg (bell P i|>.le),Real.norm_of_nonneg (Real.exp_pos _).le]; exact (div_le_iff₀ (Real.exp_pos _)).mp hi
lemma Fortissimo {P:Levels G}{x:ℕ→ℝ}(h:Calms P.S 0 x)(d:ℕ): Calms P.S 0 (fun i=> (x i)^d):=by
    induction d with
    | zero=> exact (show (fun i:ℕ=>(1:ℝ))=(fun i=> (x i)^0) from funext fun i=>(pow_zero _).symm) ▸ (fun p hp => factor_const _ _ p hp)
    | succ n IH=> simp_rw[pow_succ]; exact (by simpa only[zero_add] using! IH.mul h)
lemma waters (C:Family G)(d k:ℕ):outward C d k =Real.exp (Work.D01.columnLogs C.path.levels k)* factor C.S (d:ℝ) k:=by
   induction k with
   | zero=> simp [Work.D01.columnLogs,factor,outward]
   | succ k IH=>
      let P:=C.path.levels.params (k+1)
      rw[outward,Finset.prod_range_succ,show (∏ i∈_,_)=_ from IH,D01.columnLogs_succ,factor, factor, Real.exp_add,Real.exp_log (zero_lt_one.trans_le P.columns_ge),C.S.scale_succ,add_mul,Real.exp_add, mul_comm (Real.log _),Real.exp_nat_mul,Real.exp_log (show 0 < ((C.S.block k).val:ℝ) from Nat.cast_pos.mpr (C.S.block k).property)];
      unfold P; ring
variable {N k d p:ℕ}
lemma majesty (g:Film G (C.side k p))(x y:C.label d) (hp: Bill C N p d k g x y) : (C.labels.level d).coeffSize (columns C d k N p y) ≤2:=by
    let T:= C.labels.level d; have hb : AgeK (A) (-(1/4:ℝ)) k ≤ 1:= (wane (H! k) (by norm_num :(-(1/4:ℝ)) ≤ 0)).trans_eq (w0 _); let t:= (A|>.clock.threshold k); have ht:t ≤ 1:= (A|>.budget k).threshold_le;have ht':0<t:= (A|>.budget k).threshold_pos; have hs:t^ (2:ℕ)*AgeK (A) (-(1/4:ℝ)) k ≤1:=(mul_le_mul (pow_le_one₀ ht'.le ht (n:=2)) hb (wake ..|>.le) zero_le_one).trans_eq (one_mul _)
    apply (Work.G08.size_triangle T _ x).trans; rw[Work.G08.size_sub_rev]; linarith only [hp.bias,hs,hp.norms]
lemma annual (C:Family G)(H:C.Makes) (g:Film G (C.side k p))(x y:C.label d)(hp: Bill C N p d k g x y)(hk:C.ref d ≤ k)(hn:k≤N): ‖y‖ ≤2*outward C d k:=by
    exact (Push.RelayDifference.norm_cost _ y).trans ((at_current _ H hk hn p y).trans ((mul_le_mul_of_nonneg_left (majesty g x y hp) (zero_le_one.trans (outward_nn ..))).trans_eq (mul_comm ..)))
lemma land_forms (S:Schedule)(p:ℝ)(x:ℕ→ℝ)(h:Calms S 0 x)(hp:p<0): Fast S (fun i=>factor S p i*x i):= (show Fast S (factor S p) from ⟨p,hp,isBigO_refl ..⟩).mul h
lemma tranquil(d i j:ℕ)(h:G.Simple): Fast C.S (nativeC C d i j):=by
   let P:= A; let x:= H!; let a:= ‖alto (T!) j d‖; let E:= 2*(a *stakes C i j*factor C.S (1/8:ℝ) j)/fly (A) d j
   have he: Calms C.S 0 (fun k=>x k ^4 * E):= by
       simpa only [add_zero] using! (Fortissimo (P:=P) (CalmsK P h) 4).mul (show Calms C.S 0 (fun _=>E) from fun b hb=> factor_const _ _ b hb)
   rw [show nativeC C d i j=(fun k=>factor C.S (-1/8) k*(x k^4*E)) from ?_]; exact land_forms _ _ _ he (by norm_num)
   funext k; unfold nativeC E a x; simp only [factor,Bid.gainChart]; rw [mul_sub, Real.exp_sub,neg_div,mul_neg,Real.exp_neg]; ring_nf; simp only[inv_inv];ring
lemma passing (P:Levels G)(h:G.Simple)(R:ℕ→ℕ)(hp:CutQ P R)(i:ℕ): ∀ᶠ k in atTop, room P i k (R k):=by
    let X(k):= P.S.a k*(R k); have hv: Calms P.S 0 (fun k=> (R k:ℝ)):=by
       apply (Fortissimo (P:=P) (CalmsK P h) 4).smaller; refine isBigO_iff.mpr ⟨1,?_⟩; filter_upwards[hp] with k hx; rw[Real.norm_of_nonneg (Nat.cast_nonneg _),one_mul]; exact hx.trans (Real.le_norm_self _)
    have hf:Fast P.S X:= (show (fun k=>factor P.S (-1) k*(R k))= X from funext (fun k=>by rw [shrunk])) ▸ land_forms P.S (-1) _ hv (by norm_num)
    obtain ⟨p,hp,hX⟩:= Fast.money hf
    have hE : Tendsto X atTop (𝓝 0):=by
        apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) (hX.mono fun k h=>h.le) (Real.tendsto_exp_atBot.comp (by simpa [mul_comm _ p] using! P.S.divergent.const_mul_atTop_of_neg hp))
    have hu := ((hE.add (tail_zero P)).const_mul 2); rw[add_zero,mul_zero] at hu; exact hu.eventually (gt_mem_nhds (P.S.a_pos i))
end YM.Trace.Terrace
