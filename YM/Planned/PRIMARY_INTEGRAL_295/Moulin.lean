import YM.Planned.PRIMARY_INTEGRAL_295.Drupes
import YM.Planned.PRIMARY_INTEGRAL_295.Festoons
import YM.Planned.PRIMARY_INTEGRAL_295.Honey
import YM.Planned.PRIMARY_INTEGRAL_295.Mowing
/-!
# D-costs for one true Fine D row power through finite R, unscaled ball

Prerelease World. Exponential rate reserve chosen by input path
σ.Wire before Telescope. Mat.F support & signed. Finite-polynomial.L
analytic tilt.As proves Post[C] in Q.Aim. Include arbitrary rotations per
row in the same K, no claiming at independent flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Moulin
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform Honey Drupes Density Mowing Festoons
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Gauge} {k n : ℕ} {c f : Side} {S:StepData c f}

section
lemma absolute (i:G.ColorIndex)(x:G.Color): |x i| ≤ ‖x‖:= by
   have ht:= abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) x
   rw [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one] at ht; linarith
lemma got {f:E→G.Color} {x:E} {M:ℝ} (i:G.ColorIndex)(hf:Allows n f x M):Allows n (fun v=>f v i) x M:=by
   let L:=EuclideanSpace.proj (𝕜:=ℝ) i
   have hh:‖L‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=> (absolute i y).trans_eq (one_mul _).symm)
   have he:=hf.linear L hh; rwa [one_mul] at he

variable {M:ℝ}
lemma stinted (L: E×F→G.Color) (p:E) (q:F) (hv:‖q‖≤1) (i:G.ColorIndex) (h: Allows (n+1) L (p,0) M):
    Allows n (fun x=> ballast*(fderiv ℝ (fun z=>L (x,z)) 0 q) i) p (|ballast| * M):= (got i (banded q h hv)).smul ballast

lemma catapult {X:ℝ} {V : E→ℝ} {r:ℕ} {i j:Site c}(x:E)(hx:0≤X) {α:ℝ}(hα:0<α) (he: Allows n V x X)
    (hr: r < separation i j → V=0): Allows n V x (Real.exp (α*r)*X*Decay α i j):=by
   by_cases hp:r<separation i j
   · rw [hr hp]; apply allows_const; change ‖(0:ℝ)‖ ≤ _; rw [norm_zero]; have ht:=decay_pos α i j; positivity
   apply he.mono; have he: 1≤Real.exp (α*r)*Decay α i j:=by
      unfold Decay; rw [←Real.exp_add]; apply Real.one_le_exp; have hx: (separation i j:ℝ) ≤ (r:ℝ):=Nat.cast_le.mpr (le_of_not_gt hp); nlinarith
   apply le_trans _ (show Real.exp (α*r)*Decay α i j*X= _ from mul_right_comm ..).le
   exact le_mul_of_one_le_left hx he
end

section
-- freeze analytic U.bar. compose.
variable (K:Core G S) (s:Signed)
def close (p:Hollow G c f):Config G f:= K.seek s p.1 0
lemma cooled {x:Hollow G c f} {C:ℝ} (h:Inputs (termook s K) n C) (hx:‖x‖ ≤1)(p:Bond f):Allows n (fun y=>G.mat (close K s y p)) x C := by
   let L:Hollow G c f →L[ℝ] Hollow G c f:= ContinuousLinearMap.inl ℝ (Dir G c) (Temps G f) ∘L ContinuousLinearMap.fst ..
   have he y: ‖L y‖ ≤ ‖y‖:= by change max ‖y.1‖ ‖(0:Temps G f)‖ ≤ _; simp [norm_fst_le y]
   exact pulse_left L (f:=fun y=> G.mat (termook s K y p)) (h.2.2 _ _ ((he x).trans hx)) (ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one fun y hy=> (he y).trans hy.le)
end

section Cuts
variable (G:Gauge) (n:ℕ) (A:Clip)(σ : ℝ) (hσ : 0<σ)
include hσ

private lemma upcharge : ∃ D:ℝ,1≤D∧∀ c f (S:StepData c f) (K:Core G S) s (i:Cell f) v, ‖v‖ ≤1 → ∀ Z:Slot,
     Allows (n+1) (Function.uncurry (perif K i s Z)) (v,0) (D*Real.exp ((σ/4)*Z.length)) :=by
   obtain ⟨C,hC,hy,hB⟩:= winding G (n+1)
   obtain ⟨D,hD,hd⟩:= measured C (zero_le_one.trans hC) G (n+1) (σ/4) (by positivity)
   refine ⟨D,hD,fun c f S K s i v hv Z=> ?_⟩; let B:=termook s K; have hm:= hB c f S K s
   have he: ‖((v,0): Hollow G c f)‖≤1:=by change max ‖v‖ _≤_; simp [hv]
   exact hd (U:=B) (fun p=>hm.2.2 p _ he) (fun p=> cooled K s hm he p) i.1 Z

-- toolkit for extracting `shot` over a represented finite clamp. Must not
-- infer for kernels crossed elsewhere. Derivative needs germ about v for sum.
private lemma satiny : ∃ D:ℝ,1≤D ∧ ∀ c f(S:StepData c f)(K:Core G S)(q:Cell f)(s:Signed)(j:G.ColorIndex)(p:Acres f G)
     (v:Dir G c), ‖v‖≤1/2 → ∀ Z:Slot, Allows n (Mowing.shot (perif K q s Z) p j) v
       (Real.exp ((σ/2)*Z.length)*D*Decay (σ/4) (origin S (dropF G s (q,true) j)) (chair S p)) := by
   obtain ⟨D,hD,h⟩:= upcharge G n σ hσ
   let x:=σ/4
   let C:= |ballast| * D * Real.exp x
   have hc :0≤C:=by unfold C; positivity
   refine ⟨C+1,by linarith,fun c f S K q s j p v hv Z=>?_⟩
   have ht := stinted _ _ (Pi.single p 1) (show ‖(Pi.single p (1:ℝ):Temps G f)‖≤1 by apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i; by_cases h:i=p <;> simp [h]) j (h c f S K s q v (hv.trans (by norm_num)) Z)
   let i:=origin S (dropF G s (q,true) j); let l:= chair S p
   let T:=Real.exp (x*Z.length)
   have h':0 ≤ |ballast| * (D*T):=by unfold T; positivity
   refine (catapult (V:= Mowing.shot (perif K q s Z) p j) v h' (show 0<x from by unfold x; positivity) ht (r:=Z.length + 1) (i:=i) (j:=l)
      (fun hi=>funext (fun a=> curved s K a p q j Z hi))).mono ?_
   have hP:Real.exp (x* ↑(Z.length+1)) * (|ballast| * (D*T)) = Real.exp ((σ/2)*Z.length)*C:=by
      unfold T C; push_cast; rw [mul_add,Real.exp_add,show σ/2=x+x from by unfold x; ring,add_mul,Real.exp_add]; ring_nf
   rw [hP]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le) (decay_pos ..).le

lemma basket (M:ℝ) (hM:0≤M):∃ D:ℝ,1≤D ∧ ∀ c f(S:StepData c f) (K:Core G S), K.tube.high=A→ (∃ Λ:ℝ,K.tube.up.Bounds A σ M Λ) → ∀ i:Twin f, ∀ j:G.ColorIndex, ∀ s:Signed, ∀ v:Dir G c,‖v‖≤1/2→∀ p:Acres f G,
      let k:=dropF G (c:=c) s i j; Allows n (fun x=>K.D x k p) v (D*Decay (σ/4) (origin S k) (chair S p)):=by
   obtain ⟨C,hC,h⟩:=satiny G n σ hσ
   obtain ⟨V,hV,hv,hW⟩:=winding G (n+1)
   obtain ⟨B,hB,hb⟩:= Drupes.shot V (zero_le_one.trans hV) G (n+1) A
   let x:=σ/4; have hx:0<x:=by unfold x; positivity
   let T:=Real.exp (x*5)*(|ballast| * B); let D:=1+T+C*M; have hT:0≤T:=by unfold T; positivity
   have hp:D≥1:=by unfold D; nlinarith
   refine ⟨D,hp, fun c f S K hA ⟨Λ,hP⟩ ⟨q,i⟩ j s v hk p=>?_⟩; intro k; let r:= origin S k; let l:= chair S p
   let Z':= Decay x r l; have hz:0≤Z':=(decay_pos ..).le; let P:=Little.Core.jump K k.1; let d:=Mowing.shot P p j
   change Allows n d v (D*Z')
   cases i
   · -- raw shoot derivative (p, false)
     have he : Allows (n+1) (Function.uncurry P) (v, (0:Temps G f)) B:=by
        apply (show Allows _ (fun y=> Pressure.shoot A (termook s K y) q) (v, (0:Temps G f)) B from
           hb (fun p=> (hW c f S K s).2.2 p _ (by rw [Prod.norm_def,norm_zero]; apply max_le; linarith; norm_num)) q).germ
        rw [← hA]; rfl -- event instead
     have hu := stinted _ _ (Pi.single p 1) (show ‖(Pi.single p (1:ℝ):Temps G f)‖≤1 by apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i; by_cases h:i=p <;> simp [h]) j he
     apply ((catapult v (show 0≤ |ballast| *B by positivity) hx (show Allows n d v _ from hu) (r:=5) (i:=r) (j:=l)
       (fun hi=>funext (fun v=>Mowing.cool s K v p q j hi))).mono)
     refine mul_le_mul_of_nonneg_right ?_ hz; unfold D T; push_cast; nlinarith
   let R:=garth 1 K.R; let L(Z:Slot):= chip K.tube.up q.2 Z
   let F(Z:Slot):=Mowing.shot (perif K q s Z) p j
   let y:=σ/2; let G'(Z:Slot):= Real.exp (y*Z.length)*C*Z'
   have hg(Z):=h c f S K q s j p v hk Z
   have hw:= Push.Uniform.allows_sum (s:=R) (f:=fun i a=> L i • F i a) (fun i _=> (hg i).smul (L i))
   have he:d =ᶠ[𝓝 v] fun a=> ∑ i∈R, L i • F i a := by
      filter_upwards [continuous_norm.continuousAt.eventually (ge_mem_nhds (show ‖v‖<1 by linarith))] with a ha
      have hy:P a = fun z=>∑ i∈R,L i • perif K q s i a z:=by
         funext z; change K.etched s a z (q,true) = _
         rw [etched,if_pos rfl, Festoons.clipped_mb _ hP K _ _ q rfl]; rfl
      obtain ⟨B,hB,h⟩:= upcharge G n σ hσ
      have hA(i:Slot): DifferentiableAt ℝ (perif K q s i a) 0:=by
         let p: Temps G f→ Hollow G c f:= fun x=>(a,x)
         have hx : DifferentiableAt ℝ p 0:= DifferentiableAt.prodMk (differentiableAt_const _) differentiableAt_id
         exact (show DifferentiableAt ℝ (Function.uncurry (perif K q s i)) (p 0) from (h c f S K s q a ha i).analytic.differentiableAt (by simp)).comp _ hx
      let e:= EuclideanSpace.proj (𝕜:=ℝ) j; change ballast * e (fderiv ℝ (P a) 0 (Pi.single p 1))=_
      rw [hy,fderiv_fun_sum (by intro i hi; exact (hA i).const_smul (L i)),sum_apply, map_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
      rw [fderiv_fun_const_smul (hA i),smul_apply,map_smul]; unfold F Mowing.shot; change ballast*(L i * (fderiv ℝ (perif K q s i a) 0 (Pi.single p 1) j))= L i * _; exact mul_left_comm .. 
   apply ((hw.germ he.symm).mono)
   have hs := Price.cooked K.tube.up hP q.2 1 K.R
   have he(z:Slot) : |L z| * G' z≤ C*Z'*(|L z| *Real.exp (σ*z.length)) := by
      unfold G'; have hk := Real.exp_monotone (mul_le_mul_of_nonneg_right (show y≤σ from by unfold y; linarith) (show 0≤(z.length:ℝ) by positivity))
      apply le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk (abs_nonneg _)) (show 0≤C*Z' by positivity))
      apply le_of_eq; ring
   change (∑ i∈R,|L i| *G' i) ≤ _
   apply (Finset.sum_le_sum (fun i _=>he i)).trans; rw [←Finset.mul_sum]; calc
      _ ≤ C*Z'*M := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ D*Z':= by rw [mul_right_comm]; apply mul_le_mul_of_nonneg_right _ hz; unfold D; linarith
end Cuts
end YM.Planned.PrimaryIntegral295.Moulin
