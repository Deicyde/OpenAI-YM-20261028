import YM.TraceExtension.Det.Puff
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k l m n r:ℕ}{α a b c τ A C D:ℝ}
variable {W:Type*}{g:W→Side}{F:∀ w,WildM G (g w) k m}{o:∀ w,Site (g w)}{Y:∀ w,Gal G (g w)}
lemma Parked.mu (G:Gauge)(g:W→Side)(n:ℕ): Parked (fun w=> mail ∘ input G (g w)) n:=by
    obtain ⟨C,hc,h⟩:= mail_p G n 1 zero_le_one; exact ⟨1,C,zero_lt_one,hc,fun w=>h _⟩
structure Flare (g:W→Side)(R:W→PathData G)(p:Clip)(σ C:ℝ) : Prop where
    tanks w: ∃ B:Bed,∃ α β D:ℝ, (R w).Bounds p σ C D∧ Floor B p (g w) α β∧ Attached B (R w)∧ Bid.Sworn B (g w) G
-- Floor α β may vary arbitrarily; hull_car doesn't use a,b but arguments stuck. update
variable {R:W→PathData G}{μ:W→ℝ}
lemma Flare.house (h:Flare g R p α C)(ha:0<α)(hb:0<b)(hx:∀ w,b≤μ w∧μ w≤c)(n:ℕ):
    Parked (fun w=> stock p (R w) (μ w) ∘ input G (g w)) n ∧ Parked (fun w=> ammo (μ w) ∘ input G (g w)) n∧Parked (fun w=> shellB p (R w) (μ w) ∘ input G (g w)) n∧Parked (fun w=> shellG (μ w) ∘ input G (g w)) n:=by
    choose B A D E hE hF ht hs using h.tanks
    obtain ⟨a,N,hA,hN,H⟩:= body_charge G p n α ha C c
    have hY w:= H (g w) _ _ (hE w) _ (hb.le.trans (hx w).1) (hx w).2
    obtain ⟨v,P,hP,hv,hm⟩:=Park.inverse_house (n:=n) G 1 hA hN (pow_pos hb 2)
    obtain ⟨u,T,hT,hu,hQ⟩:=Park.inverse_house (n:=n) G 0 hA hN (pow_pos hb 2)
    refine ⟨⟨a,N,hA,hN,fun w=> (hY w).1⟩,⟨a,N,hA,hN,fun w=>(hY w).2⟩,⟨v,P,hP,hv,fun w=>?_⟩,⟨u,T,hT,hu,fun w=>?_⟩⟩
    · obtain ⟨hx,hz,_⟩:= hull_m hb (hx w).1 (hE w) (hF w) (ht w) (hs w)
      let K:=stock p (R w) (μ w) ∘ input G (g w); have he: K 0=stock p (R w) (μ w) (1: Config G (g w)):=by simp[K]
      rw[← he] at hz hx
      exact hm _ K (hY w).1 hx.det_pos.ne'.isUnit hz hx.isHermitian
    obtain ⟨_,_,hz⟩:= hull_m hb (hx w).1 (hE w) (hF w) (ht w) (hs w)
    let K:=ammo (μ w) ∘ input G (g w); have he: K 0=ammo (μ w) (1: Config G (g w)):=by simp[K]
    rw [←he] at hz
    have hv:(K 0).PosDef:=ammo_safe _ (hb.trans_le (hx w).1)
    exact hQ _ K (hY w).2 hv.det_pos.ne'.isUnit hz hv.isHermitian
lemma shoreX_step {p:Clip}(hs:Parked (fun w=> shellB p (R w) (μ w) ∘ input G (g w)) 1)(h:∀ w i, Pet (af G (g w)) (o w) (fun z=> larch (Y w) z i) a (C*Decay a (o w) i.1) 3)(he:∀ w,Cloaked (Y w))(ha:0<a)(hp:0≤C): CodeM o (fun w=> shoreX p (R w) (μ w) (Y w) ∘ input G (g w)) 1:=by
    obtain ⟨b,D,hb,hD,F⟩:=hs.top; let v:ℝ:= min a b/3; have hv:0<v:=by unfold v; exact div_pos (lt_min ha hb) (by linarith)
    let c:ℝ:=(2:ℝ)^1*‖ContinuousLinearMap.mul ℝ ℝ‖* D*C
    let d:ℝ:=(Fintype.card (Loc G 1):ℝ)* countCost v; have hh:0≤d:=mul_nonneg (by positivity) (count_pos hv).le; have hc: 0≤c:=by unfold c; positivity
    refine ⟨v,c*d*d,hv,by positivity,fun w k=>?_⟩
    let s:=g w; let o:= o w; let V:=shellB p (R w) (μ w) ∘ input G (g w); let U(x):= refrain (Y w) (input G (g w) x); let M i j x:= V x j i * U x i j k
    have hx:3*v=min a b:=by unfold v;ring
    have hz:v ≤ b:= (show v ≤ min a b by linarith only[hv,hx]).trans (min_le_right ..); have hs: v ≤ a:= (show v ≤ min a b by linarith only [hv,hx]).trans (min_le_left ..)
    let S:ℝ:=c*Decay v o k.1; have hS:0≤S:=mul_nonneg hc (decay_pos ..|>.le)
    have hT (i j:Lines G (g w) 1): Pet Prod.fst o (M i j) v (S*Decay v o i.1*Decay v o j.1) 1:=by
       have hD' :0 ≤ D*Decay b j.1 i.1:=mul_nonneg hD (decay_pos ..|>.le)
       have hr:0≤C*Decay a o k.1*Decay a o j.1*Decay a o i.1:=mul_nonneg (mul_nonneg (mul_nonneg hp (decay_pos ..|>.le)) (decay_pos ..|>.le)) (decay_pos ..|>.le)
       have hm:=refrain_pay (m:=1) o (he w) (h w) k i j
       apply Pet.tilt (Pet.bins (ContinuousLinearMap.mul ℝ ℝ) (((F w j i).tilt le_rfl hz le_rfl).switch hD' o hv.le) (hm.tilt le_rfl hs le_rfl) (mul_nonneg hD' (Real.exp_pos _|>.le)) hr) _ le_rfl le_rfl
       have ht : Decay b j.1 i.1 * Decay a o j.1 * Real.exp (v*↑(1:ℕ)*separation o j.1) ≤ Decay v o j.1:=by
           apply le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (decay_pos ..|>.le) (decay_le hb.le ..)) (Real.exp_pos _|>.le))
           unfold Decay; simp only [Nat.cast_one,mul_one,← Real.exp_add]; apply Real.exp_monotone; have hw:3*v ≤ a:= hx ▸ min_le_left ..; nlinarith [show (0:ℝ) ≤ separation o j.1 by positivity]
       calc
         _ = c * (Decay a o k.1*Decay a o i.1)* (Decay b j.1 i.1 * Decay a o j.1 * Real.exp (v*↑(1:ℕ)*separation o j.1)):= by unfold c o; ring
         _ ≤ c*(Decay v o k.1*Decay v o i.1)*Decay v o j.1 := mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul (slough _ _ hs) (slough _ _ hs) (decay_pos ..|>.le) (decay_pos ..|>.le)) hc) ht (mul_nonneg (mul_nonneg (decay_pos ..|>.le) (decay_pos .. |>.le)) (Real.exp_pos _|>.le)) (mul_nonneg hc (mul_nonneg (decay_pos ..|>.le) (decay_pos ..|>.le)))
         _ = _:=by unfold S; ring
    have he(i:Lines G (g w) 1): Pet Prod.fst o (fun z=> ∑ j,M i j z) v (S*Decay v o i.1*d) 1:=by
        apply Pet.weighted o (fun j _=> hT i j); rw [← mul_sum]; exact mul_le_mul_of_nonneg_left ((pay_gate G (g w)).count _ hv o) (mul_nonneg hS (decay_pos ..|>.le))
    have hf: Pet Prod.fst o (fun z=>∑ i,∑ j,M i j z) v (c*d*d*Decay v o k.1) 1:=by
        apply Pet.weighted o (fun i _=> he i); rw [← sum_mul, ← mul_sum]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((pay_gate G (g w) (n:=1)).count Prod.fst hv o) hS) hh).trans_eq; unfold S d; ring
    refine hf.grows (Eventually.of_forall fun x=>?_); unfold shoreX trapw; simp only [Function.comp_apply, Finset.sum_apply]; rfl
lemma ashore_budget (X:Pella o (fun w=> tidal (Y w) ∘ input G (g w)) 1)(hv:Parked (fun w=>shellB p (R w) (μ w) ∘ input G (g w)) 1)(ht:Parked (fun w=> shellG (μ w) ∘ input G (g w)) 1)
    (hx:CodeM o (fun w=> shoreX p (R w) (μ w) (Y w) ∘ input G (g w)) 1): CodeM o (fun w=> ashore p (R w) (μ w) (Y w) ∘ input G (g w)) 1:=by
    let F(w):=shoreM p (R w) (μ w) (Y w) ∘ input G (g w)
    have hh:=X.up X.swap; have hm := ((hh.leftM (Parked.spins (Parked.mu G g 1))).leftM ht).rightM hv
    have he:Pella o F 1:=by
       let T (w:W)(x:Link G (g w)):=let V:=input G (g w) x; (shellG (μ w) V*((mail V)ᵀ*(tidal (Y w) V+(tidal (Y w) V)ᵀ)))*shellB p (R w) (μ w) V
       rw [show F=T from ?_]
       exact hm
       funext w x; unfold T F; simp only[Function.comp_apply, shoreM, Matrix.mul_assoc]
    exact (hx.eval (1/2:ℝ)).sub (juke_budget he)
end YM.Trace.Det
