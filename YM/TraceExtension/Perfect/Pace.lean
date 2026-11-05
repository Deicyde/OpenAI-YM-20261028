import YM.TraceExtension.Perfect.Bellow
import YM.TraceExtension.Perfect.Sail
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}{η σ Λ A C:ℝ}{W:Type}{F:Filter W}{n:W→Side}{k t:ℕ}
local notation "S"=> Sheaf
lemma Calm.super {I:W→Type}[∀ w,Fintype (I w)][∀ w,DecidableEq (I w)]{G:∀ w,Rays (I w)→ℝ}{D:∀ w,I w→ℕ}(h:Calm D G k)(t:ℕ) : ∃ a C:ℝ,0<a ∧ 0≤C∧∀ (u:ℝ),0≤u→u≤a→∀ j≤k,∀ w,cost (D w) u t 0 (leaf (G w) 0 j)≤C:=by
 obtain ⟨v,C,hy,hp,H⟩:= h.shape; obtain ⟨V,x,B⟩:= shelter_paid (t:=t) (half_pos hy |>.le) (half_lt_self hy)
 refine ⟨v/2,V*C,half_pos hy,by positivity,fun u hu ht j hj w=> (cost_tiny (leaf (G w) 0 j) (D w) _ _ _ t 0 hu ht le_rfl).trans ((le_trans ?_ (mul_le_mul_of_nonneg_left (H w j hj) x.le)))⟩
 unfold cost; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; rw [← mul_assoc V]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 unfold spot; simp only [sub_zero,max_eq_right,Nat.cast_nonneg]; refine (B _ (by positivity)).trans_eq ?_; simp [shelter]

lemma dust_pay (o:∀ w,Site (n w))(a:Axis)(R:W→PathData G)(Λ:W→ℝ)(hp:0<η)(h:∀ w,(R w).Bounds p η A (Λ w)): Calm (fun w=>landW (o w)) (fun w=>ballX (dust p (R w) a (o w))) k:=by
 let p(v:Cover)(w):= o w+wrap (n w) v
 let L:=fun w=> landW (G:=G) (o w)
 have ht(u: Axis)(v:Cover) := (brew (G:=G) (k:=k) (p v) u a).heater (D':=L) (size v) (fun w i=> by
    have he:separation (o w) (p v w) ≤ size v:=by unfold p;rw[separation_comm,separation,add_comm (o w),add_sub_cancel_right]; exact Next.Free.within_size ..
    cases i with
    | inl i=> exact ((separation_triangle (o w) (p v w) i.1).trans (Nat.add_le_add_right he _)).trans_eq (Nat.add_comm ..)
    | inr i=> exact ((separation_triangle (o w) (p v w) i.1).trans (Nat.add_le_add_right he _)).trans_eq (Nat.add_comm ..))
 let y(w)(i:Axis)(v:Acr G (n w)):= (∑ j:Fin 4, Pull.cash j•(ballX (bornT i a (p (((Pull.steps j:ℕ):ℤ) • step i) w)) v-ballX (bornT i a (p ((-((Pull.steps j:ℕ):ℤ)) • step i) w)) v))
 have hG(i): Calm L (fun w x=>y w i x) k:=by
    apply Calm.grove _ _ (fun w j v=>_) (fun j _ =>?_); exact ((Calm.minus (ht i _) (ht i _)).maps (((Pull.cash j)) • (ContinuousLinearMap.id ℝ ℝ)))
 refine ((Calm.grove L univ y (fun i _=> hG i)).minus ((scent_calm o R Λ hp h a).boost)).near (fun w=>?_)
 refine Eventually.of_forall fun x=>?_ ; unfold dust ballX y elm Pull.dTap; simp only [p,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply,map_zsmul,wrap_step,zero_add,zero_sub];rfl

-- width calm ready: one initial + ALL x, a
lemma hatchX (G : Gauge)(k:ℕ):∃ a C:ℝ,0<a∧ 0 ≤ C∧∀ u,0≤u→u≤a→∀ j≤k,∀ f:Side,∀ x:Site f,∀ i b:Axis, cost (landW x) u 4 0 (leaf (ballX (born (G:=G) x i b)) 0 j) ≤ C ∧ cost (landW x) u 4 0 (leaf (bottom (mist (G:=G) x i)) 0 j) ≤ C:=by
 let W:=Σ f, Site f; let U(w:W):Side:= w.1
 let x(w:W):Site (U w):= w.2
 choose a V ha hv h using fun i b=> (brew (G:=G) (k:=k) x i b).super 4; choose p y hP hy H using fun i=> (rain_cost (G:=G) (k:=k) x i).super 4
 let v:=univ.inf' univ_nonempty fun i:Axis×Axis=>min (a i.1 i.2) (p i.1); have he:0<v:= (Finset.lt_inf'_iff _).mpr fun i _=> lt_min (ha ..) (hP _)
 let C:= ∑ i:Axis×Axis,(V i.1 i.2+y i.1); have hC:0≤C:= Finset.sum_nonneg fun i _=>add_nonneg (hv ..) (hy _)
 refine ⟨v,C,he,hC,fun u hu ht j hj f o i b=>?_⟩
 let k:W:=⟨f,o⟩; change cost _ _ _ _ (leaf (ballX (born (G:=G) (x k) i b)) _ _) ≤ _∧_
 have hB:u ≤ min (a i b) (p i):= ht.trans (inf'_le _ (mem_univ ((i,b):Axis×Axis)))
 have hz : V i b+y i ≤ C:= Finset.single_le_sum (s:=univ) (a:=(i,b)) (f:=fun t:Axis×Axis=> V t.1 t.2+y t.1) (fun i _=> add_nonneg (hv ..) (hy ..)) (mem_univ _)
 exact ⟨(h i b u hu (hB.trans (min_le_left ..)) j hj k).trans ((le_add_of_nonneg_right (hy i)).trans hz),(H i u hu (hB.trans (min_le_right ..)) j hj k).trans ((le_add_of_nonneg_left (hv i b)).trans hz)⟩
lemma hatchY (p:Clip)(G:Gauge)(μ C:ℝ)(hp:0<μ)(k:ℕ):∃ a A:ℝ,0<a ∧ 0 ≤ A∧∀ u,0≤u→u≤a→∀ j≤k,∀ f:Side,∀ x:Site f,∀ (Λ:ℝ)(R:PathData G), R.Bounds p μ C Λ→∀ b:Axis,cost (landW x) u 4 0 (leaf (ballX (dust p R b x)) 0 j)≤A:=by
 let W:= Σ f:Side, Site f× { v: PathData G× ℝ // v.fst.Bounds p μ C v.snd}
 let x(w:W):Site w.fst:=w.2.1
 let R(w:W):PathData G:= w.2.2.val.1; let Λ(w:W):ℝ:=w.2.2.val.2
 choose a V ha hv h using fun i:Axis=>(dust_pay x i R Λ hp (fun w=> (show (R w).Bounds p μ C (Λ w) from w.2.2.property)) (k:=k)).super 4
 let y:=univ.inf' univ_nonempty a; have he:0 < y:= (Finset.lt_inf'_iff _).mpr fun i _=> ha i
 let H:=∑ i:Axis,V i; refine ⟨y,H,he,(Finset.sum_nonneg fun i _=>hv i),fun u hu ht j hj f q a r he b=>?_⟩
 let w:W:=⟨f,q,⟨r,a⟩,he⟩
 exact (h b u hu (ht.trans (inf'_le _ (mem_univ _))) j hj w).trans (Finset.single_le_sum (fun i _=> hv i) (mem_univ b))
end YM.Trace.Perfect
