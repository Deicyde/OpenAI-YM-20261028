import YM.UVExtension.Wren.Stage
import YM.UVExtension.Concert.Lyres
/-!
 Walt of varying E probes at V for ONE period. Arity varies; handle ALL with
 shared finite chart dimension along each tests-of-length. norm on directions
 globally bounded after volume fixed; no compactness asserted at flag faces.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Finset Wilson Pressure
open ConnectedActivityE6 Blaze March Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset Quotes Next.Foundations
open Steady Concert
open scoped BigOperators Topology InnerProductSpace ContDiff Classical Matrix.Norms.Frobenius
variable {ι θ X κ:Type}{v:Filter ι} {G: Gauge} {c f: Side} {A:Support c}{k j n:ℕ}{u B t w:ℝ}
variable {P:κ→ RegularAddress c} {p: BudgetPoint}
namespace Gala
/-- all angular tests on poll ≤ k, pays dimension at fixed angle. -/
abbrev Baton (v:Filter ι)(f:ι→ Bool→ Config G c→ℝ)(X:ι→ Config G c)(u:ℝ)(k:ℕ) := ∀ (Y:Type)[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y](W:ι→ Y→ Config G c)(t:ι→ Y), (∀ i,W i (t i)=X i)→ (∀ i,Mode (W i) (t i) k u)→ Walt v t k (fun n b=> (f n b)∘ (W n))
variable {X:ι→ Config G c}{f:ι→ Bool→ Config G c→ℝ} {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma bis (x:ι→ E)(F:ι→Bool→ E×ℝ→ℝ)(h: Walt v (fun i=>(x i,0)) (j+1) F): Walt v x j (fun n b t=> deriv (fun y:ℝ=>F n b (t,y)) 0) :=by
   obtain ⟨u,hP,hr⟩:=h.cap; refine Walt.earns _ u (hr.mono (fun i hh b=> nestle _ (hh b))) fun ε he=> ?_
   filter_upwards [hr,h.hem ε he] with i hn hx
   apply Brush.shimmy (nestle _ hx)
   let V (y:E):=(y,(0:ℝ)); have ht: Tendsto V (𝓝 (x i)) (𝓝 ((x i),0)):= (continuous_id.prodMk continuous_const).continuousAt (x:=x i)
   filter_upwards [eventually_all.mpr (fun b=> ht.eventually ((hn b).smooth.eventually (by simp)))] with y hy
   let g(t:ℝ):=(y,t); have hY b: DifferentiableAt ℝ (fun t=> F i b (g t)) 0:= ((hy b|>.differentiableAt (by simp)).comp 0 (show DifferentiableAt ℝ g 0 from (differentiableAt_const _).prodMk differentiableAt_id))
   exact (deriv_fun_sub (hY true) (hY false)).symm
variable (h:Baton v f X u k) (N : Sailor G B w k) (hz:0≤w) (hn : k*w≤u)
include h N
lemma explores [FiniteDimensional ℝ E](i:ℕ)(l:ι→ List (Directions G c))(he:∀ n,(l n).length=i)(hK:∀ n,∀ x∈l n,‖x‖≤ B) (V:ι→ E→ Config G c)(x:ι→ E)(hp:∀ n, V n (x n)=X n) (hT:∀ n, Mode (V n) (x n) k t) (ht:t+i*w ≤ u)(hi:j+i≤k): Walt v x j (fun n b=> (leftDerivs (f n b) (l n)) ∘ (V n)):=by
    induction i generalizing j E t l with
    | zero =>
      have he n : l n=[]:= List.length_eq_zero_iff.mp (he n); have hh:t≤u:= by simpa using ht
      simp_rw [he]; exact (h E V x hp (fun n=> ⟨(hT n).pos.trans hh,fun i=> ((hT n).atLink i).climb le_rfl hh⟩)).thin hi
    | succ i ih =>
      have hp' n: ∃ A k,l n=A::k:=List.exists_cons_of_ne_nil (by intro h; specialize he n; rw [h] at he; exact Nat.succ_ne_zero i he.symm)
      choose A m hm using hp'; let U n (y:E×ℝ) := increment (V n y.1) (y.2 • A n)
      have hA n :Mode (U n) (x n,0) k (w+t):= N.stroke c (A n) (hK n _ (by simp [hm])) E (V n) (x n) t (hT n)
      have hg: w+t+i*w≤u:=by push_cast at ht; linarith
      simp_rw [hm]; exact bis x _ (ih (j:=j+1) m (fun n=> by specialize he n; simpa [hm] using he) (fun n i hi=> hK n i (by simp [hm,hi])) U (fun n=> (x n,0)) (fun n=> by simp [U,hp,Work.G07.at_zero_increment]) hA hg (by omega))
include hz hn
lemma surveys (m:ℕ)(hp:m≤k)(l:ι→ List (Directions G c))(he:∀ n,(l n).length=m)(hf:∀ n,∀ i∈l n, ‖i‖≤ B) : Together v (fun n b=> leftDerivs (f n b) (l n) (X n)):=by
    have hh : 0+(m:ℝ)*w≤u:=(by rw [zero_add]; exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hp) hz).trans hn)
    let V(n:ι)(_ : ℝ):= X n; have hP n: Mode (V n) 0 k 0:=⟨le_rfl,fun i=> a_oneB G (X n i) le_rfl⟩
    exact (explores h N m l he hf V _ (fun _=>rfl) hP hh (j:=0) (by omega)).atProbe
omit h N hz hn
-- evaluate taps with length fixed. Need bound on point gauge norm after c fixed, use exp power over canvas. no chart dimension.
lemma tilt (o : Site c)(p: BudgetPoint): ∃ B:ℝ,1 ≤ B ∧ ∀ i: Directions G c, p.dirBound o i→ ‖i‖≤ p.threshold*B:=by
   let t (i:Bond c):=(1+(separation i.1 o:ℝ))^p.power; let B:= 1+∑ i,t i; have hh : 1≤B:= le_add_of_nonneg_right (Finset.sum_nonneg (by intro i hi; unfold t; positivity))
   exact ⟨B,hh,fun i h=> (pi_norm_le_iff_of_nonneg (mul_nonneg p.threshold_pos.le (zero_le_one.trans hh))).mpr (fun j=> (h j).trans (mul_le_mul_of_nonneg_left ((single_le_sum (f:=t) (by intro i hi; unfold t; positivity) (mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)) p.threshold_pos.le))⟩
variable {f':ι→ Config G c→ℝ}{s:Filter θ} {U:θ→ι×ι}
include hz hn
lemma progresses {o : Site c} {Z: Support c} (N:Sailor G p.threshold w k)(Y:θ→ Tap p G o Z)(n:ℕ)(hy:∀ i,(Y i).poll.length=n) (hf:p.order≤k) (hu:n≤p.order) (hp:Baton s (fun n b v=> f' (if b then (U n).1 else (U n).2) v) (fun n=> (Y n).view) u k): Together s (fun n b=> (Y n).read (f' (if b then (U n).1 else (U n).2))) :=by
   obtain ⟨B,hh,hK⟩:= tilt (G:=G) o p; have ht : 0<B:=zero_lt_one.trans_le hh
   let l i:= ((Y i).poll.map (fun V=> B⁻¹ • V)); have hx i:(l i).length=n:= by simp [l,hy]
   have hv i: (Y i).poll= (l i).map (fun V=>B•V):=by unfold l; simp only [List.map_map]; simp only [Function.comp_def,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]; exact congr_fun List.map_id_fun.symm _
   refine ((surveys hp N hz hn n (hu.trans hf) l hx ?_).continuous (T:=fun v:ℝ=> B^n*v) (continuous_const.mul continuous_id)).shimmy ?_
   · intro i x hx; obtain ⟨r,hr,rfl⟩:= List.mem_map.mp hx; rw [norm_smul,norm_inv,Real.norm_of_nonneg ht.le]; apply (mul_le_mul_of_nonneg_left (hK r ((Y i).innerP _ hr)) (inv_nonneg.mpr ht.le)).trans_eq; field_simp
   filter_upwards with i; funext b; unfold Tap.read; rw [hv,expands (l i) B, hx,smul_eq_mul]

lemma podium (N:Sailor G p.threshold w k) {o : Site c} {Z : Support c}(h:∀ (Y:ι×ι→ Tap p G o Z), Baton (v×ˢv) (fun (n:ι×ι) (b:Bool) v=>f' (if b then n.1 else n.2) v) (fun n=> (Y n).view) u k)(hp:p.order≤k) : ∀ ε:ℝ,0<ε→ ∀ᶠ n in v×ˢv,∀ X:Tap p G o Z, ‖X.read (f' n.1)-X.read (f' n.2)‖≤ε:=by
    let S(i:Fin (p.order+1)):= {u:Tap p G o Z//u.poll.length=i.val}; intro ε he
    have ht (i:Fin (p.order+1)):∀ᶠ n in v×ˢv,∀ X:S i, ‖Tap.read X.val (f' n.1)-Tap.read X.val (f' n.2)‖≤ε:=by
       refine Tune.unanimously _ _ _ fun W=> ?_
       let Y j:= (W j).val; exact (progresses (U:=fun n=> n) hz hn N Y i.val (fun n=> (W n).property) hp (by have :=i.isLt; omega) (h Y)).cap _ he -- Boolean
    filter_upwards [eventually_all.mpr ht] with n hn x; exact hn ⟨x.poll.length,Nat.lt_succ_of_le x.card⟩ ⟨x,rfl⟩
end Gala
end YM.UVExtension.Wren
