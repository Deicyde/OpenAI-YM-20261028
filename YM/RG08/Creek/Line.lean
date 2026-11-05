import YM.RG08.Creek.Range
/-! # Cost of ancestor separation at any m.Label cells in their own metrics. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door Wings
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I J Y:Type}[Fintype I][DecidableEq I]{S:Schedule}{L:Side}{m i n k:ℕ}{ρ χ:ℝ}
section ages
-- iterative true root projection at m
def asc (S:Schedule)(m:ℕ)(i:ℕ)(x:Cover): Cover:=match i with
   | 0=>x
   | i+1=>if m ≤ i then asc S m i (growP (S.block i) x) else x
lemma asc_t (S:Schedule)(m:ℕ)(x):asc S m m x=x:=by cases m <;> simp [asc]
abbrev swell (S:Schedule)(m i:ℕ):ℝ:= Real.exp (S.scale i-S.scale m)
lemma swell_step (S:Schedule)(m i:ℕ): swell S m (i+1)=(S.block i).val*swell S m i:=by unfold swell; rw [S.scale_succ, show S.scale i+_ - _ = Real.log ((S.block i).val:ℝ)+(S.scale i - S.scale m) by ring, Real.exp_add,Real.exp_log (by positivity)]
-- lower bound in fine mesh. If separation >=rho+8 at pivot, descendant pays rho plus 6
def initialR (ρ:ℝ)(x: Places I)(t:Finset I):Prop:= ∀ (i:↥t)(j:↥t), i≠j → ρ+8 ≤ (size (x i.val-x j.val):ℝ)
def rural (S:Schedule)(ρ:ℝ)(m:ℕ)(i:ℕ): Verts I:=fun x T=> initialR ρ (asc S m i ∘ x) T
lemma rule_w (S:Schedule)(ρ:ℝ)(m i:ℕ): WardL (rural S ρ m i (I:=I)):= by
   refine ⟨fun x t h s hp a b hx=> ?_, fun t x y hx=>?_⟩
   · exact h ⟨a.val,hp a.property⟩ ⟨b.val,hp b.property⟩ (fun h=>hx (Subtype.ext (congr_arg (Subtype.val (p:=fun (x:I)=> x∈t)) h)))
   apply propext; unfold rural initialR; simp_rw [Function.comp_apply, fun (i:↥t)=> hx i i.property]
lemma r_rules (h:m ≤ i)(S : Schedule): growsR (rural S ρ m (i+1) (I:=I)) (rural S ρ m i) (S.block i):= by
   intro x T hp p
   unfold rural; rw [show asc S m (i+1) ∘ footT _ x p=asc S m i ∘ x from ?_]; exact hp
   funext k; dsimp only [footT,Function.comp_apply]; rw [asc,if_pos h,show growP (S.block i) (stemA _ (x k) (p k))= _ from (stemA_fit _ (x k,p k)|>.1)]
lemma birth_sep {x y:Cover}(h:m ≤ i)(hv:ρ+8 ≤ (size (asc S m i x-asc S m i y):ℝ)): ρ*swell S m i+6 ≤ (size (x-y):ℝ) := by
   induction i,h using Nat.le_induction generalizing x y with
   | base=> rw [asc_t,asc_t] at hv; simp only [swell,sub_self,Real.exp_zero,mul_one]; linarith
   | succ i he ih=>
      unfold asc at hv; rw [if_pos he, if_pos he] at hv
      let L:=S.block i; have hp : 0<(L.val:ℝ):=by positivity
      have hL : (3:ℝ) ≤ (L.val:ℝ):= by exact_mod_cast S.block_large i
      have hX:=ih hv
      let k:= growP L; let p:=growL L
      have hV : (↑L.val:ℝ)*size (k x-k y) ≤ 1*size (x-y)+4*(↑L.val:ℝ):=by simpa only [(grows L x),(grows L y)] using (marks_size (v:=(↑L.val:ℝ)) hp.le (w:=1) (le_of_eq (mul_one ..).symm) (growP L x) (growP L y) (growL L x) (growL L y))
      rw [swell_step]
      change ρ*_+6 ≤ (size (k x-k y):ℝ) at hX
      change ρ*((L.val:ℝ)*_)+6 ≤ _; nlinarith only [mul_le_mul_of_nonneg_left hX hp.le,hL,hV]
lemma vast_r (h:m ≤ i)(ρ:ℝ)(S:Schedule): Vast (rural S ρ m i (I:=I)) (ρ*swell S m i):= fun x T a b hp hv=> (le_add_of_nonneg_right (by norm_num)).trans (birth_sep h (hp a b hv))
end ages
section wages
variable {u:Y→ Windows}{b:J→ Plot.Dial u}{V θ : High b 1→ℝ}{X:Chain}
open Plot.High
-- y_s pol dominated by $V_i * exp(-spacing)$. Supply comparator C,p on hLengths. β / g explicitly B maps.
lemma harvest_damp (hV:∀ i,0<θ i)(he: Weighed (High.glass X) V)(hx:Weighed (glass X) (fun i=>(θ i)⁻¹)) : ∃ (A:ℝ)(p:ℕ),0<A ∧ ∀ (i: High b 1)(ρ χ:ℝ),0≤χ → A* (Dial.fee X (b i.z))^p*(1+χ)≤ ρ → V i*Real.exp (-θ i*(ρ*swell X.S i.K i.i)) ≤ Real.exp (-χ) := by
   let ψ : High b 1→ ℝ := glass X; have hY:=glint X b 1
   let w: High b 1→ℝ:= fun i=>max (V i) 1
   have hw : Weighed ψ w := (he.plus Weighed.one hY).mono (fun i=>(show (0:ℝ)≤1 by norm_num).trans (le_max_right ..)) (fun i=>max_le (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_left (he.positive i)))
   obtain ⟨C,p,hC,H⟩:= hw.times hx; obtain ⟨U,hU,hg⟩:=gain_poly 1 0 (by norm_num) p
   let A:= 1+C*U; refine ⟨A,p,add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg hC hU),fun i ρ χ hχ h=>?_⟩
   let z:= swell X.S i.K i.i; have hz : 0<z:= Real.exp_pos ..; let P:=(Dial.fee X (b i.z))^p; have hP:0≤P:= pow_nonneg (zero_le_one.trans (by apply age_one; exact (u _|>.pos))) _ -- parent
   have hW : w i*(θ i)⁻¹ ≤ A*P*z := by
     have hv: ψ i^p ≤ U*P*z := by
       have hp:= hg X.S _ i.K _ _ (u (b i.z).a|>.pos) i.heap
       have he: gain X.S 1 (b i.z).K i.i=z⁻¹:= by unfold z swell gain Plot.High.K; rw [neg_mul,one_mul, Real.exp_neg]
       rw [he, gain,neg_zero, zero_mul,Real.exp_zero,mul_one,← div_eq_mul_inv] at hp; exact (div_le_iff₀ hz).mp hp
     apply (H i).2.trans ((mul_le_mul_of_nonneg_left hv hC).trans ?_)
     rw [show C*_ = C*U*(P*z) by ring]; rw [mul_assoc A]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) (mul_nonneg hP hz.le)
   let x:=θ i; have hh:0<x:=hV i
   have hT: w i ≤ A*P*z*x:= (div_le_iff₀ hh).mp ((le_of_eq (div_eq_mul_inv ..)).trans hW)
   have hQ: w i*(1+χ) ≤ x*(ρ*z):=(mul_le_mul_of_nonneg_right hT (by linarith)).trans (by rw [show _*x*(1+χ)=x*(A*P*(1+χ)*z) by ring]; gcongr)
   have hm: V i ≤ Real.exp (w i):= (le_max_left ..).trans ((le_add_of_nonneg_right (by norm_num)).trans (Real.add_one_le_exp _))
   refine le_trans (mul_le_mul_of_nonneg_right hm (Real.exp_pos _|>.le)) ?_
   rw [← Real.exp_add]; apply Real.exp_monotone; have ht:(1:ℝ)≤ w i:= le_max_right ..; change w i+ -x*(ρ*z)≤_; nlinarith
end wages
end YM.RG08.Creek
