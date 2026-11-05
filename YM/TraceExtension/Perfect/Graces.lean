import YM.TraceExtension.Perfect.Temple
import YM.Planned.STATIONARY_JET_PORT.InUse
import YM.Push.STATIONARY_UNIFORM.Continue

/-! # Invoke Before on path-matched solution. No competing branch in Ward proof -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {n N:ℕ}
section temp
open Push.Uniform
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
 {D Y V α :ℝ}{B:I→ Site ⟨1,Nat.zero_lt_one⟩}
-- unify classical.decide templates
lemma rail_entry (f:Rays I→Rays J)(x:Rays I)(v:Fin n→I)(j:J):
     leaf f x n v j=Push.Uniform.entry f x v j:=by
 unfold leaf bank entry; rw [show desk (I:=I) =bolt (ι:=I) from funext fun i=> by ext j; by_cases he:j=i <;> simp [desk,bolt,he]]; rfl
lemma footed (A:I→ℕ)(f:Rays I→ Rays J) (x:Rays I)(a : ℝ)(j : J) {n:ℕ}(h:ContDiffAt ℝ ω f x):
   sail f x A n j a 0 0 = cost A a 0 0 (leaf (fun z=> f z j) x n):=by
   unfold sail leaf; rw [show (fun z=> f z j)=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:J=>ℝ) j) ∘ f from rfl,(ContinuousLinearMap.proj ..).iteratedFDeriv_comp_left h le_top];rfl
variable {c: Side}
lemma shade_total {l:I→Site c}{m:J→Site c}{f:Rays I→Rays J}{K:ℕ} {x:Rays I}(h:Push.Uniform.Envelope l m α n f x D)(hp:Multiplicity l K)(hN:n≠0)(hD:0 ≤ D)(ha:0<α)(i : J): sail f x (fun j=> separation (m i) (l j)) n i (α/2) 0 0 ≤ D*(K*countCost (α/2))^n:=by
 let A k:=separation (m i) (l k); let g j:= Decay (α/2) (m i) (l j)
 unfold sail cost; refine (Finset.sum_le_sum (g:=fun s:Fin n→I=> D*∏ j:Fin n, g (s j)) ?_).trans ?_
 · intro v _; have ht:= h n hN le_rfl v i; rw [← rail_entry f] at ht
   apply (mul_le_mul_of_nonneg_left ht (show 0 ≤ spot (α/2) 0 0 (limitN A v) from (spot_pos ..).le)).trans
   rw [mul_left_comm,show (∏ j,g (v j))=_ from (glaze_prod l (m i) v (α/2)).symm]; refine mul_le_mul_of_nonneg_left ?_ hD
   unfold glaze spot shelter; simp only [pow_zero, sub_zero, max_eq_right (Nat.cast_nonneg _),one_mul,← Real.exp_add]; apply Real.exp_monotone
   have he(k): limitN A v ≥ A (v k):=limitN_ge A v k; have hf : Nonempty (Fin n) := ⟨⟨0,Nat.pos_of_ne_zero hN⟩⟩
   obtain ⟨j,hj⟩:= limitN_mem A v hf
   have hs : (limitN A v:ℝ) ≤ spanSites l (m i) v := by
      apply Nat.cast_le.mpr
      rw [hj]; exact Finset.single_le_sum (f:=fun j=> A (v j)) (fun k _=> Nat.zero_le _) (Finset.mem_univ j)
   change α/2*(limitN A v:ℝ)+_ ≤ _; nlinarith only [hs, mul_le_mul_of_nonneg_left hs ha.le]
 rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left ?_ hD
 rw [← Fintype.prod_sum];
 refine (Finset.prod_le_prod (fun j _=> Finset.sum_nonneg fun _ _=> (Real.exp_pos _).le) (g:=fun _=> (K:ℝ)*countCost (α/2)) (fun j _=> hp.count l (half_pos ha) (m i))).trans_eq ?_; simp
end temp

structure Lot (G : Gauge) (P : Patch) (Y : KernelChoices) (p:Clip)(α D:ℝ) where
    c : Side
    f : Side
    s : StepData c f
    kit : s.kernel=Y
    patch : s.patch=P
    wood : Forest s.ratio
    b : PathData G
    Λ: ℝ
    ρ : Bid.Dir G c→AxisChart G wood
    law: Critical wood p b ρ
    price: b.Bounds p α D Λ
    size : Bid.Larger (G:=G) s
namespace Lot
open Push.Uniform Planned.JetPort
variable {G:Gauge} {P:Patch}{Y:KernelChoices}{p:Clip}{α D:ℝ} {W:Type*}(L:W→ Lot G P Y p α D)

lemma earnings (e:∀ w, Key (L w).wood G): Calm
   (fun (w:W) (i: Primary (L w).c G)=> separation (address (L w).wood G (Sum.inr (e w))) (address (L w).wood G (Sum.inl i)))
   (fun w v=> station (L w).ρ v (e w)) N:=by
 classical
 rcases isEmpty_or_nonempty W with hs|hs; · exact ⟨fun i=>isEmptyElim i,1,0,zero_lt_one,le_rfl,fun i=>isEmptyElim i⟩
 obtain ⟨w₀⟩:=hs
 obtain ⟨A⟩:= pre_order G α D P.J Y (n:=N+3) (by omega)
 let V:=A.tables p P
 choose ρ H using fun w=> A.graph (L w).wood (L w).price (L w).size (by rw [(L w).patch]) (L w).kit
 have hx(w:W): Counter V N (Classical.arbitrary (L w).s.Choices) p (L w).b (ρ w):=by
     unfold V; rw [← show A.tables p (L w).s.patch=A.tables p P from congr_arg _ (L w).patch]
     apply Counter.service (B:=_) (H w) (L w).price (L w).size (by rw [(L w).patch]) (L w).kit
 have hH(w:W): (0: Positions (Primary (L w).c G)) ∈ domain V:= Metric.mem_ball_self (show 0<V.horizon from ((congr_arg (fun z : Patch=> (A.tables p z).horizon) (L w).patch) ▸ (H w).1))
 let Z := fun (w:W) (i: Primary (L w).c G) => separation (address (L w).wood G (Sum.inr (e w))) (address (L w).wood G (Sum.inl i)); let a:= pathRate V N;let C:= pathCost V N
 have ht:= (hx w₀).carrier (hH w₀)|>.2 N (by omega);have ha:0<a:=ht.1;have hC:0<C:=ht.2.1
 let E w (v:Positions (Primary (L w).c G)):= station (ρ w) v (e w)
 have he : Calm Z E N:=by
     let b:= (townCost G*(Push.Uniform.countCost (a/2)))
     have hh :0≤b:=mul_nonneg (Nat.cast_nonneg _) (count_pos (half_pos ha)).le
     have hv (w:W):ContDiffAt ℝ ω (station (ρ w)) 0:= (H w).series (by rw [show A.tables p (L w).s.patch=A.tables p P from by rw [(L w).patch]]; exact hH w)
     refine ⟨fun w=> contDiffAt_pi.mp (hv w) _,a/2,C*(1+b)^N, half_pos ha,by positivity, fun w n hn=> ?_⟩
     rcases n with _|n
     · have hx': station (ρ w) 0=0:=by simp [station,(H w).2.2.2.2.2.1.1]
       rw [zero_price, show E w 0=0 from by simp [E,hx'], norm_zero,mul_zero]; positivity
     unfold E; rw [← footed _ _ _ _ _ (hv w)]
     let T:=Multiplicity.comp (a:=address (L w).wood G) (town (L w).wood) (Sum.inl_injective (β:=Key (L w).wood G))
     have hx' := (hx w).carrier (hH w) |>.2 N (by omega) |>.2.2.2
     have hu : Push.Uniform.Envelope _ _ _ (n+1) _ _ _:= fun i hi hQ=> hx' i hi (hQ.trans hn)
     refine (shade_total (x:=0) hu T (Nat.succ_ne_zero _) hC.le ha (e w)).trans ?_; change C*b^(n+1) ≤ _;  exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hh (show b ≤ 1+b by linarith) _).trans (pow_le_pow_right₀ (by linarith only[hh]) hn)) hC.le
 apply he.near; intro w
 let K:= tint G (Body 1 (L w).c)
 filter_upwards [(show Tendsto K _ (𝓝 0) from (K.map_zero) ▸ K.continuous.tendsto 0).eventually ((H w).is_extension (L w).law)] with x hx; unfold E station; rw [Function.comp_apply,Function.comp_apply,← hx]; rfl
end Lot
end YM.Trace.Perfect
