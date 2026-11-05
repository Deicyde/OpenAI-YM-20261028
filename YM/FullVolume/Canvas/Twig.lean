import YM.FullVolume.Canvas.Texts
/-! Define closed subspace Invariant and Loop bookkeeping via actual H.Scale supports orientation.Iota stamps & Σ shift.Germs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Shade
open Filter Set Function lp Lattice Laurent Bloch Exterior RG Precision Wilson Tralis ContinuousLinearMap
open scoped Topology BigOperators InnerProductSpace ContDiff Matrix.Norms.Frobenius NNReal ENNReal
variable {G:Gauge}{t:ℕ}[NeZero t]{σ:ℝ}
private lemma ballots (i:ℕ)(x:Fin (t+1)→G.Color): ∃ F:Cameo G t→L[ℝ] ℝ,∀ C:Cameo G t,F C=(ringT σ C i).poly x:=by
    let L (a:Ink G (t+1)):= chants t σ i
    refine ⟨∑ j: Ink G (t+1),((∏ i,x i (j i))/L j) • lp.evalCLM ℝ (fun _:InkSpot G t=>ℝ) 2 (i,j),fun C=>?_⟩
    rw [_root_.sum_apply]; refine Finset.sum_congr rfl fun j _=>?_ ; change ((∏ i,x i (j i))/L j)*C (i,j)=C (i,j)/L j*(∏ i,x i (j i)); ring
-- Bs simplification.Arm.Length
private def merry (σ:ℝ)(F:Cameo G 1)(r:Fin 2→PlaqAxes)(x: Ink G 2)(i) := if (fun j:Fin 2=> ((letter (t:=1) i j)).plaq)=r then F (i,x)/chants 1 σ i else 0
private def tokenN (i:ℕ)(t:Option Axis):ℝ:= match t with
    | none=>1
    | some l => ((((letter (t:=1) i 1).offset l)-((letter (t:=1) i 0).offset l):ℤ):ℝ)
-- length bound via offsets & path
private lemma point (i:ℕ)(k:Axis): (tokenN i (some k))=((carrierPath 1 i).2 (0,k):ℤ):=by
    unfold tokenN letter; simp only [Fin.cons_zero, show (1:Fin (1+1))=(0:Fin 1).succ from rfl, Fin.cons_succ, walkSlot_end,Pi.zero_apply,sub_zero]
private def zephyr (t:Option Axis)(i) := |tokenN i t| / chants 1 σ i -- include σ
lemma perfume {e:Option Axis}(h:0<σ): Summable (zephyr (σ:=σ) e):=by
    cases e with
    | none=>exact (silts 1 h).congr fun i=>by simp [zephyr,tokenN,chants,Real.exp_neg]
    | some x=>
      let z(i:ℕ):= chants 1 (-(σ/2)) i
      refine Summable.of_nonneg_of_le (fun i=> div_nonneg (abs_nonneg _) (Real.exp_pos _).le) (f:=fun i=> z i/(σ/2)) (fun i=>?_) ((silts _ (by linarith:0<σ/2)).div_const _)
      let u:= stretch 1 i; have he : |tokenN i (some x)| ≤ u:=by
            rw [point]; simp only [←Int.cast_abs,←Int.natCast_natAbs]
            exact_mod_cast (le_trans (b:=(size ((carrierPath 1 i).2):ℕ)) (by exact_mod_cast Finset.single_le_sum (f:=fun v=> (((carrierPath 1 i).2 v)).natAbs) (fun i _=>Nat.zero_le _) (Finset.mem_univ (0,x))) (by unfold u stretch; omega))
      have hσ : 0<σ/2:=by linarith
      apply (div_le_div_of_nonneg_right he (Real.exp_pos (σ*stretch 1 i)).le).trans
      rw [div_le_div_iff₀ (show 0 < Real.exp (σ*stretch 1 i) from Real.exp_pos _) hσ]; unfold z chants; rw [← Real.exp_add]
      have hh : (-(σ/2)*u + σ*u:ℝ)=u * (σ/2):=by ring
      change ↑u*_ ≤ Real.exp (_*↑u+_*↑u); rw [hh]; linarith [Real.add_one_le_exp (u*(σ/2):ℝ)]
private lemma forrain {r: Fin 2→ PlaqAxes} {x: Ink G 2} (t:Option Axis) (h:0<σ):
    ∃ F:Cameo G 1→L[ℝ] ℝ,∀ C, HasSum (fun i=> merry σ C r x i* tokenN i t) (F C):=by
    let g(C:Cameo G 1)(i:ℕ):= merry σ C r x i*tokenN i t
    have he C i: ‖g C i‖≤ zephyr (σ:=σ) t i * ‖C‖:=by
        unfold g merry zephyr; split
        · have hx:= lp.norm_apply_le_norm (by norm_num) C (i,x);  have hg : 0<chants 1 σ i:= Real.exp_pos _; rw [norm_mul,norm_div, Real.norm_of_nonneg hg.le,mul_comm _ ‖C‖,Real.norm_eq_abs (tokenN ..),div_mul_eq_mul_div,← mul_div_assoc]; gcongr
        rw [zero_mul,_root_.norm_zero]; exact mul_nonneg (div_nonneg (abs_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
    have hu C:= Summable.of_nonneg_of_le (fun i=> norm_nonneg (g C i)) (he C) ((perfume h).mul_right _)
    let S:Cameo G 1→ₗ[ℝ] ℝ:={ toFun:= fun C=>∑' i,g C i,
                                 map_add':=fun C D=>by
                                   rw [← (hu C).of_norm.tsum_add (hu D).of_norm]; apply tsum_congr; intro i; unfold g merry; split <;> simp [add_div,add_mul],
                                 map_smul':=fun c C=>by
                                   rw [RingHom.id_apply, smul_eq_mul,← tsum_mul_left]; refine tsum_congr fun i=>?_ ; unfold g merry; split <;> simp [mul_div_assoc,mul_assoc] }
    have hh C : ‖S C‖≤ (∑' i,zephyr (σ:=σ) t i)*‖C‖:= (norm_tsum_le_tsum_norm (hu C)).trans (((hu C).tsum_le_tsum (he C) ((perfume h).mul_right _)).trans_eq (tsum_mul_right ..)) -- fix
    exact ⟨S.mkContinuous _ hh,fun C=> (hu C).of_norm.hasSum⟩
-- in-lanes strips
lemma senses (G:Gauge)(t:ℕ)[NeZero t](σ:ℝ): ∃ P:Submodule ℝ (Cameo G t), IsClosed (P:Set (Cameo G t)) ∧ ∀ (C:Cameo G t),C∈P ↔ ∀ i, (ringT σ C i).Invariant:=by
   choose F H using ballots (t:=t) (σ:=σ) (G:=G)
   let S:ℕ×G.El×(Fin (t+1) → G.Color)→ Cameo G t→L[ℝ]ℝ:=fun p=> F p.1 (fun j=> G.adjoint p.2.1 (p.2.2 j)) - F p.1 p.2.2
   refine ⟨⨅ i,(S i).ker,by rw [Submodule.coe_iInf]; exact isClosed_iInter (fun i=> (S i).isClosed_ker),fun C=> ?_⟩
   rw [Submodule.mem_iInf]; constructor
   · intro h i u x; have he : S (i,u,x) C = 0 := h (i,u,x); unfold S at he; dsimp only at he
     rw [← H,← H]; exact sub_eq_zero.mp he
   rintro h ⟨i,u,x⟩; change S (i,u,x) C=0; exact sub_eq_zero.mpr ((H ..).trans ((h i u x).trans (H ..).symm))
lemma clocks (h:0<σ) : ∃ P:Submodule ℝ (Cameo G 1), IsClosed (P:Set (Cameo G 1)) ∧ ∀ (C:Cameo G 1), C∈ P↔ Bs G (ringT σ C) ∧ ∀ i,(ringT σ C i).Invariant:=by
   choose F hF using fun (r:Fin 2→PlaqAxes) (x:Ink G 2)(t:Option Axis)=> forrain (r:=r) (x:=x) t h
   let S:= fun i:(Fin 2→PlaqAxes)×Ink G 2×Option Axis=> F i.1 i.2.1 i.2.2
   obtain ⟨P,hp,hS⟩:= senses G 1 σ
   refine ⟨(⨅ i,(S i).ker) ⊓ P, by rw [Submodule.coe_inf,Submodule.coe_iInf]; exact (isClosed_iInter fun i=> (S i).isClosed_ker).inter hp,fun C=> ?_⟩
   rw [Submodule.mem_inf, Submodule.mem_iInf,hS]; refine and_congr ?_ Iff.rfl
   have he (W : PathData G) (h:W.loop=ringT σ C)(r x): W.loop_coeff r x=merry σ C r x:=by funext i; unfold PathData.loop_coeff; rw [h]; rfl
   constructor
   · intro H i x R hr; have hb t:S (i,x,t) C=0:= H (i,x,t); have hx t := hF i x t C; change ∀ t, F i x t C=0 at hb
     simp_rw [hb] at hx; rw [he R hr i x]
     exact ⟨by simpa only [tokenN,mul_one] using hx none,fun l=> hx (some l)⟩
   rintro H ⟨i,x,t⟩
   let V:PathData G:=⟨ (fun x _ =>(0,⟨[],x⟩)),ringT σ C,fun i=>(ringT σ (0:Cameo G 2) i),ringT σ (0:Cameo G 3)⟩
   obtain ⟨hK,ht⟩:= H i x V rfl; change F i x t C=0
   have heq:∀ k,V.loop_coeff i x k=merry σ C i x k:=fun _ => congr_fun (he V rfl i x) _ -- fix
   cases t
   · rw [he V rfl i x] at hK; exact (hF i x none C).unique (by simpa only [tokenN,mul_one] using hK)
   next t=>
     specialize ht t; simp_rw [heq] at ht; exact (hF i x (some t) C).unique ht
-- norms
end YM.Stationary.Shade
