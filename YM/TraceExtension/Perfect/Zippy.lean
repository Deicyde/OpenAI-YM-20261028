import YM.TraceExtension.Perfect.Bora
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}{α C D:ℝ} (x:Site f)
variable {M V I:Type*}[AddCommGroup M][Module ℝ M] [AddCommGroup V][Module ℝ V]
def voteJ (F : Site f→ M):= ((Fintype.card (Site f):ℝ))⁻¹ • ∑ i,F i
lemma map_vote (F:Site f→ M)(L:M→ₗ[ℝ]V): L (voteJ F)= voteJ (L∘F):=by unfold voteJ; rw [map_smul,map_sum];rfl
lemma vote_mem (F:Site f→M)(A:Submodule ℝ M)(h:∀ i,F i∈ A): voteJ F∈A:= A.smul_mem _ (A.sum_mem (fun i _=>h i))
def gravy (f:Side): (Site f→M)→ₗ[ℝ] M := {
 toFun:=voteJ
 map_add':=fun a b=>by simp [voteJ,sum_add_distrib,smul_add]
 map_smul':=fun a b=>by simp only[voteJ,Pi.smul_apply,← smul_sum, RingHom.id_apply]; rw [smul_comm] }
lemma p_vote (F:Site f→I→V)(i:I): voteJ F i=voteJ fun j=>F j i:=map_vote F (LinearMap.proj i)
private def root_elm (i:Axis): (Site f→M)→ₗ[ℝ] (Site f→M) where
 toFun:=elm i
 map_add':=fun X Y=>by ext1 v; unfold elm Pull.dTap; simp only[Pi.add_apply, add_sub_add_comm,smul_add,Finset.sum_add_distrib]
 map_smul':=fun c X=>rate_elm X c i
lemma voted (o:Site f)(G':Site f→Acr G f→ℝ)(h:∀ i,ContDiffAt ℝ ω (G' i) 0) (x:ℝ)(d:ℕ→ℝ)(hd:∀ i,Estate o (G' i) x d): Estate o (voteJ G') x d :=by
 let q:ℝ:= Fintype.card (Site f); have hx:0<q:= by unfold q; positivity
 refine ⟨fun i hi hv=> ?_⟩; unfold voteJ; rw [cell_fee .., abs_of_pos (inv_pos.mpr hx)]; rotate_left
 · rw [show (∑ i, G' i)=fun x=>∑ i,G' i x from funext fun i=> Finset.sum_apply ..]; apply ContDiffAt.sum (f:=G') ?_
   intro t _; exact h t
 rw [inv_mul_le_iff₀ hx]; have hh: leaf (∑ i,G' i) 0 i=fun v=>∑ j, leaf (G' j) 0 i v:=by unfold leaf bank; rw [iteratedFDeriv_sum_apply (fun t _=> (h t).of_le le_top)]; funext v; rw [_root_.sum_apply]
 rw [hh]; exact (cost_sum ..).trans ((Finset.sum_le_sum (fun j _=> (hd j).values i hi hv)).trans_eq (by simp [q]))
lemma voted_tip (o:Site f)(G':Site f→Acr G f→ℝ)(h:∀ i,ContDiffAt ℝ ω (G' i) 0)(ε:ℝ)(s:ℕ)(K:Tit G→Tit G→ℝ)(ht:∀ i,Testify o (G' i) K s ε): Testify o (voteJ G') K s ε:=by
 let q:ℝ:= Fintype.card (Site f); have hx:0<q:= by unfold q; positivity
 have he: ContDiffAt ℝ ω (∑ i,G' i) 0:=by rw [show (∑ i, G' i)=fun x=>∑ i,G' i x from funext fun i=> Finset.sum_apply ..]; apply ContDiffAt.sum ?_; intro i _; exact h _
 refine ⟨fun i j hj=> ?_⟩; let A(t):ℝ:= iteratedFDeriv ℝ 2 (G' t) 0 ![ballad i o,ballad j o]
 unfold voteJ; rw [iteratedFDeriv_const_smul_apply]; rotate_left; · exact he.of_le le_top
 rw [iteratedFDeriv_sum_apply (fun i _=> (h i).of_le le_top), _root_.smul_apply,_root_.sum_apply]; change |q⁻¹*(∑ i,A i)-K i j|≤_
 rw [show q⁻¹*(∑ i,A i)-K i j=q⁻¹*∑ b,(A b-K i j) by rw[sum_sub_distrib,mul_sub,sum_const,card_univ,nsmul_eq_mul, inv_mul_cancel_left₀ hx.ne'],abs_mul,abs_of_nonneg (inv_nonneg.mpr hx.le),inv_mul_le_iff₀ hx]
 apply (Finset.abs_sum_le_sum_abs ..).trans; exact (Finset.sum_le_sum (s:=univ) (fun k _=>(ht k).bill i j hj)).trans_eq (by simp[q])

namespace Dart
structure March (Z:Dart G f): Prop where
 still (x:Site f) : gait x Z=Z
-- transport spine
variable (Z:Dart G f)
def sing : Dart G f where
 J:= fun i j=> voteJ fun x:Site f=>(gait x Z).J i j
 Y:= fun i=> voteJ fun x:Site f=>(gait x Z).Y i
 E:= fun i=> voteJ fun x: Site f=>(gait x Z).E i
 Q:= fun i=> voteJ fun x:Site f=>(gait x Z).Q i
 twist:= fun i j k=> voteJ fun x:Site f=>(gait x Z).twist i j k
private lemma swerve (j: Site f→ Peat G f): loopB (rj x) x (voteJ (fun k:Site f=>loopB (rj k) k j))= voteJ fun k:Site f=>loopB (rj k) k j:=by
 rw [map_vote]; unfold voteJ; congr 1
 have hx(k:Site f): loopB (rj x) x (loopB (rj k) k j) = loopB (rj (k+x)) (k+x) j:=by ext t p; change j (t-x-k) (ride k (ride x p))=j (t-(k+x)) _; rw[pace_add,sub_sub,add_comm x]
 simp only [Function.comp_apply,hx]; exact Equiv.sum_comp (paceV x) (fun i=>loopB (rj i) i j)
lemma singed : March Z.sing:=by
 refine ⟨fun a=>?_⟩; change _= _; unfold gait sing; congr 1
 · funext i j; exact swerve a _
 · funext i; dsimp only; let f:= Z.Y i; have hx(k:Site _): loopB (ry a) a (loopB (ry k) k f)=loopB (ry (k+a)) (k+a) f:=by
       funext v u; change rideC _ (rideC _ (f (v-a-k) (ride k (ride a u)))) = rideC _ (f (v-(k+a)) _)
       rw [pace_add,sub_sub, add_comm a,rideC_sum]; simp only [neg_add_rev]
   rw[map_vote]; unfold voteJ; congr 1; change (∑ i:_, loopB (ry a) a (loopB (ry i) i f))=_; simp_rw[hx]; exact Equiv.sum_comp (paceV a) (fun i=> loopB (ry i) i f)
 · funext i; exact swerve a _
 · funext i; exact swerve a _
 funext i j k; exact swerve a _
lemma gale (X:Site f→Dart G f)(h:∀ i,(X i).Sound R p)(Y:Dart G f)(hY:Y.J=fun i j=>voteJ (fun z=> (X z).J i j)) (hy:Y.Y=fun i=>voteJ fun z=> (X z).Y i)(he:Y.E=fun i=>voteJ fun z=>(X z).E i)(hq:Y.Q=fun i=>voteJ fun z=>(X z).Q i)(hk:Y.twist=fun i j k=>voteJ fun z=>(X z).twist i j k): Y.Sound R p:=by
   refine ⟨fun i j x=>?_,fun i x=>?_,fun i x=>?_,fun i x=> ?_,fun a b i j=>?_,?_,fun i j=>?_,fun i y=>?_⟩
   · simp only[hY,p_vote]; exact vote_mem _ _ (fun i=> (h i).heart ..)
   · simp only[hy,p_vote]; exact vote_mem _ _ (fun i=> (h i).palm ..)
   · simp only[he,p_vote]; exact vote_mem _ _ (fun i=>(h i).plum ..)
   · simp only[hq,p_vote]; exact vote_mem _ _ (fun i=> (h i).plumQ ..)
   · simp only[hk,p_vote]; exact vote_mem _ _ (fun i=>(h i).mint ..)
   · simp only[hY,hq,show ∀ i v, twig i (v: Site f→Peat G f)=sprig i v from fun _ _=>rfl,map_vote]; unfold voteJ
     rw [← Finset.smul_sum,← Finset.smul_sum,sum_comm]; nth_rw 2 [sum_comm]; congr 1; exact Finset.sum_congr rfl (fun i _=> (h i).hue)
   · simp only[hY,hk,show ∀ i v, twig i (v: Site f→ Peat G f)=sprig i v from fun _ _=>rfl,map_vote]; unfold voteJ
     rw [← Finset.smul_sum,sum_comm (s:=_) (t:=_)]
     rw [← smul_sub, ← Finset.sum_sub_distrib]; congr 1; exact Finset.sum_congr rfl fun w _=> (h w).tint i j
   let V (z):= (((∑ a:Axis, elm a ((X z).J a i))-(X z).E i) y, aroma p R ((X z).Y i y))
   have hF: voteJ V ∈ wing f G:= vote_mem V _ (fun z=> (h z).fin i y)
   apply (show (_:Peat G f × Peat G f)= voteJ V from Prod.ext ?_ ?_) ▸ hF
   · dsimp only; rw [he,hY]; dsimp only
     simp_rw [show ∀ z: Site f→Peat G f,∀ i:Axis,elm i z=root_elm i z from fun _ _=>rfl,map_vote]; rw [show (voteJ V).1=_ from map_vote V (LinearMap.fst ℝ (Peat G f) (Peat G f))]; unfold voteJ; rw [← Finset.smul_sum, ← smul_sub,Pi.smul_apply, sum_comm, ← sum_sub_distrib, Finset.sum_apply]; rfl
   dsimp only; rw [hy]; change sniff R p (voteJ (fun z=>(X z).Y i) y)=_; rw [p_vote,map_vote]; exact (map_vote V (LinearMap.snd ℝ (Peat G f) (Peat G f))).symm
lemma gull (hp:R.Bounds p α C D){v:ℝ}{P Q:ℕ→ℝ}{ε:ℝ}(h:Viz Z p R v P Q ε): Viz (sing Z) p R v P Q ε:=by
 let X(i):=gait i Z; have hx(i:Site f): Viz (X i) p R v P Q ε:= gait_viz i Z hp _ _ _ _ h
 have hu(Y:Site f→Site f→Peat G f)(A:ℕ→ℝ)(h:∀ i x,Y i x∈ loom G f)(he:∀ i x,Estate x (ballX (Y i x)) v A) x: Estate x (ballX (voteJ Y x)) v A:=by
    change Estate x (topF (voteJ Y x)) v A; rw [p_vote,map_vote]; exact voted _ _ (fun i=> (loom_read (h i x)).2.2) _ _ (fun i=>he i x)
 refine ⟨gale X (fun i=>(hx i).sound) _ rfl rfl rfl rfl rfl,fun i j x=> ?_,fun i x=> ?_,fun i x=>?_,fun i x=>?_,fun i j k x=>?_,fun i j x=>?_,fun i x=>?_⟩
 · exact hu _ _ (fun a b=> (hx a).sound.heart i j b) (fun a b=> (hx a).J i j b) _
 · change Estate x (follic (voteJ (fun a=>(X a).Y i) x)) v _; rw [p_vote,map_vote]; exact voted _ _ (fun a=> (rain_read ((hx a).sound.palm i x)).2.2.1) _ _ (fun a=>(hx a).Y i x)
 · exact hu _ _ (fun a b=> (hx a).sound.plum i b) (fun a b=>(hx a).E i b) _
 · exact hu _ _ (fun a b=> (hx a).sound.plumQ i b) (fun a b=> (hx a).plum i b) _
 · exact hu _ _ (fun a b=> (hx a).sound.mint i j k b) (fun a b=> (hx a).mint i j k b) _
 · change Testify x (topF (voteJ (fun a=>(X a).J i j) x)) _ _ _; rw [p_vote,map_vote]; exact voted_tip _ _ (fun a=> (loom_read ((hx a).sound.heart i j x)).2.2) ε _ _ (fun a=> (hx a).ox i j x)
 change Testify x (follic (voteJ (fun a=>(X a).Y i) x)) _ _ _; rw[p_vote,map_vote]; exact voted_tip _ _ (fun a=>(rain_read ((hx a).sound.palm i x)).2.2.1) ε _ _ (fun a=> (hx a).orb i x)

end Dart
end YM.Trace.Perfect
