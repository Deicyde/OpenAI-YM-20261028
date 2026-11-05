import YM.RG08.Aura.Swell

/-! # Exact infinite primitive, both ends gave identical abstractions by four-dimensional
 uniqueness; charge moving on center-to-y selective arm. -/
noncomputable section
namespace YM.RG08.Aura
open Function Lattice Laurent Pert.Bulk Forms Carrel Steam Rows RG Stationary Bloch Tack Anchor Spar Sedan Precision Finset Exterior Packets Ducat Filter
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {f:Form}{p τ:ℝ}{y:Cover}

def flip (f:Form):Form:=fun x i=> f (-x-step i) i
def bow (f:Form)(i:Axis)(x:Cover):ℝ:= -rim (flip f) i (-x)
lemma fade (h:fell f p τ y)(ht:0≤τ)(_hp:0 ≤ p): fell (flip f) (p*Real.exp τ) τ (-y):=by
 intro x i
 apply le_trans (b:=|flip f x i| * (Real.exp (τ*sep (-x-step i) y)*Real.exp τ)) (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
 · rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right (h _ i) (Real.exp_nonneg _)
 rw [←Real.exp_add];apply Real.exp_le_exp.mpr
 have hx:= sep_triangle (-x) (-x-step i) y
 have hh:sep x (-y)=sep (-x) y:=by rw [sep,sep,show -x-y= -(x- -y) from by abel,length_neg]
 rw [show sep (-x) (-x-step i)=1 by rw [sep,sub_sub_cancel,length_step]] at hx;rw [hh];nlinarith
lemma turn (hl:locked f):locked (flip f):=by
 intro x i j
 have ht:= hl (-x-step i-step j) i j
 rw [show -x-step i-step j+step i= -x-step j from by abel,sub_add_cancel] at ht
 have he(i j:Axis): -(x+step i)-step j= -x-step i-step j:=by abel
 unfold flip; rw [he,he,show -x-step j-step i= -x-step i-step j from by abel];linarith
lemma bow_turn (i j:Axis)(x:Cover)(h:fell f p τ y)(hl:locked f)(hp:0≤p)(hs:0<τ): bow f i (x+step j)-bow f i x=f x j:=by
 have ht:=rim_turn (i:=i) (turn hl) hs (mul_nonneg hp (Real.exp_nonneg _)) (fade h hs.le hp) (-(x+step j)) j
 rw [show -(x+step j)+step j= -x from by abel,flip,show -( -(x+step j))-step j=x from by abel] at ht; unfold bow;linarith

-- path independence pointwise without needing infinite-support all. Show equality forward/reverse along fixed i by limit along transverse x+n step b while staying on all closed columns. Explicit decay. b≠i structural.
private def tally(b:Bool)(i:Axis):Cover:=if b then step i else -step i
private lemma dual_size {i j:Axis}(he:i≠j)(b:Bool)(t m:ℕ) : Laurent.size (t • tally b i + m • step j:Cover)=t+m:=by
 unfold Laurent.size; have hh:=Finset.sum_subset (s₁:=({i,j}: Finset Axis)) (Finset.subset_univ _) (f:=fun a:Axis=>((t • tally b i+m • step j:Cover) a).natAbs) (by simp only [mem_insert,mem_singleton,not_or]; intro x _ h; cases b<;>simp [h.1,h.2,tally])
 rw [←hh,sum_pair he];cases b<;>simp [tally,he,Ne.symm he]
private lemma tar {x:Cover}{i j k:Axis}(he:i≠j)(h:fell f p τ y)(hs:0<τ)(hp:0≤p)(b:Bool)(t m:ℕ):
 |f (tooth i (x+t • tally b j) m) k| ≤ p*Real.exp (τ*sep x y)* (Real.exp (-τ))^t * (Real.exp (-τ))^m:=by
 let z:=tooth i (x+t • tally b j) m
 rw [← mul_le_mul_iff_left₀ (Real.exp_pos (τ*sep z y))]
 refine (h _ _).trans ?_
 rw [←Real.exp_nat_mul,← Real.exp_nat_mul,mul_assoc p,mul_assoc p,mul_assoc p,←Real.exp_add,←Real.exp_add,←Real.exp_add]
 apply le_mul_of_one_le_right hp; apply Real.one_le_exp
 have hx:= sep_triangle z y x
 rw [sep_comm y x,show sep z x=(t:ℝ)+(m:ℝ) from ?_] at hx
 · nlinarith
 unfold sep z tooth length; rw [show x+t • _ +m • _-x=t • tally b j+m • step i from by abel,dual_size (Ne.symm he)];exact Nat.cast_add ..

lemma terrace (x:Cover){i j:Axis}(he:i≠j)(h:fell f p τ y)(hs:0<τ)(hp:0≤p)(b:Bool):Tendsto (fun t:ℕ=>rim f i (x+t • tally b j)) atTop (𝓝 0):=by
 let a:=Real.exp (-τ); have ha:0 ≤ a :=Real.exp_nonneg _; have hA:a<1:=by unfold a;rw [Real.exp_lt_one_iff];linarith
 rw [tendsto_iff_norm_sub_tendsto_zero]
 refine squeeze_zero (fun _=>norm_nonneg _) (g:=fun t=>p*Real.exp (τ*sep x y)* a^t*(1-a)⁻¹) ?_ ?_
 · intro t;rw [sub_zero,rim, norm_neg];refine (norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using licensedRim (i:=i) _ i hs hp h)).trans ?_;simp only [Real.norm_eq_abs]
   rw [←tsum_geometric_of_lt_one ha hA,←tsum_mul_left]
   exact (licensedRim _ _ hs hp h).tsum_le_tsum (fun m=> tar he h hs hp b t m) ((hasSum_geometric_of_lt_one ha hA).summable.mul_left _)
 have hw:= ((tendsto_pow_atTop_nhds_zero_of_lt_one ha hA).const_mul (p*Real.exp (τ*sep x y))).mul_const ((1-a)⁻¹)
 simpa using hw
-- for bow x+t positive ⇒ rim opposite with -t in j. rewrite as backward using phi reflected transverse too; dual_size result need both signs in **perp**, prove variant with z tooth i at x - t step j, use replace lemma generalize tar to Bool independent. -/
lemma tux (x:Cover)(i:Axis)(h:fell f p τ y)(hl:locked f)(hp:0≤p)(hs:0<τ):rim f i x=bow f i x:=by
 obtain ⟨b,hb⟩:=exists_ne i
 have he (t:ℕ) : rim f i (x+t • step b) - bow f i (x+t • step b) = rim f i x - bow f i x:=by
    induction t with
    | zero=>simp
    | succ t hi=>rw [add_smul,one_smul, ← add_assoc, ← hi];
                 linarith only [bow_turn (f:=f) i b (x+t • step b) h hl hp hs, rim_turn (i:=i) (f:=f) hl hs hp h (x+t • step b) b]
 have ht:= terrace (i:=i) (-x) (Ne.symm hb) (fade h hs.le hp) hs (mul_nonneg hp (Real.exp_nonneg _)) false
 have hv:Tendsto (fun t:ℕ=>rim f i (x+t • step b)) atTop (𝓝 0):= terrace x (Ne.symm hb) h hs hp true
 have hf:=hv.sub ht.neg; have hk (t:ℕ) : -rim (flip f) i (-x+t • tally false b)=bow f i (x+t • step b):=by simp [bow,tally,add_comm]
 change Tendsto (fun t=>rim f i (x+t • step b)- -rim (flip f) i _) _ _ at hf;simp_rw [hk,he,neg_zero,sub_zero] at hf
 exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hf)
-- choose by sign with uniform norm. Need exact forward/reverse distances.
private lemma norm_sign (x:Cover)(i:Axis)(h:0≤x i)(t:ℕ):Laurent.size (tooth i x t) = t + Laurent.size x:=by
 unfold Laurent.size; rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i),←Finset.add_sum_erase _ (fun i=> (x i).natAbs) (Finset.mem_univ i)]
 rw [show (tooth i x t i)= (x i+(t:ℤ)) from by simp [tooth]]
 rw [Finset.sum_congr (g:=fun j:Axis=>(tooth i x t j).natAbs) (f:=fun j:Axis=>(x j).natAbs) (s₁:=univ.erase i) rfl (fun j hj=>by have hi: j≠i:= (mem_erase.mp hj).1; simp [tooth,hi])]
 omega
lemma away (x y:Cover)(i:Axis)(t:ℕ)(h:0≤x i-y i): sep (tooth i x t) y= t+sep x y:=by
 unfold sep tooth length; rw [show x+t • _-y= tooth i (x-y) t from by unfold tooth; abel, norm_sign _ _ h, Nat.cast_add]
lemma aboard (x y:Cover)(i:Axis)(t:ℕ)(h:x i≤y i):sep (x-t • (step i)) y=t+sep x y:=by rw [sep,←length_neg];rw [show -(x- t • step i-y) = tooth i (-x) t - -y from by unfold tooth;abel, ← sep,away (-x) (-y) _ _ (by change 0≤ -(x i)- -y i;omega), sep,show -x- -y = -(x-y) by abel,length_neg];rfl
lemma bow_terms (x:Cover)(i:Axis):bow f i x=∑' n:ℕ,f (x-(n+1) • step i) i:=by unfold bow rim; rw [neg_neg]; apply tsum_congr;intro n;unfold flip tooth;rw [add_smul, one_smul,neg_add_rev];rw [show (-(n • step i) + - -x - step i:Cover)= (x - (n • step i+step i)) by abel]
lemma charged (x:Cover)(i: Axis)(h:fell f p τ y)(hl:locked f)(hp:0≤p)(hs:0<τ):|rim f i x|≤ p* (1-Real.exp (-τ))⁻¹ *Real.exp (-τ*sep x y):=by
 let a:= Real.exp (-τ); have ha:0≤a:=Real.exp_nonneg _; have hx:a<1:=by unfold a;rw [Real.exp_lt_one_iff];linarith
 let b:= p*Real.exp (-τ*sep x y)
 have hb:∑' n:ℕ,b*a^n=p*(1-a)⁻¹*Real.exp (-τ*sep x y):=by rw [tsum_mul_left,tsum_geometric_of_lt_one ha hx];unfold b;ring
 have hA : Summable fun n:ℕ=>b*a^n:=(hasSum_geometric_of_lt_one ha hx).summable.mul_left _
 have ht (F:ℕ→ℝ)(h:∀ n,|F n| ≤ b*a^n): |∑' n,F n| ≤ p*(1-a)⁻¹*Real.exp (-τ*sep x y):=by
    have he:=hA.of_nonneg_of_le (fun n=>abs_nonneg (F n)) h
    have H : |∑' n,F n| ≤ ∑' n, |F n|:=by simpa only [Real.norm_eq_abs] using (norm_tsum_le_tsum_norm (f:=F) (by simpa only [Real.norm_eq_abs] using he))
    exact H.trans ((he.tsum_le_tsum h hA).trans_eq hb)
 have he (n:ℕ)(z:Cover)(hZ:n+sep x y ≤ sep z y): |f z i| ≤ b*a^n:=by
    rw [←mul_le_mul_iff_left₀ (Real.exp_pos (τ*sep z y))]
    apply (h z i).trans
    unfold b a;rw [← Real.exp_nat_mul,mul_assoc p,mul_assoc p,←Real.exp_add,←Real.exp_add]; apply le_mul_of_one_le_right hp;apply Real.one_le_exp; nlinarith
 rcases le_total (y i) (x i) with H|H
 · unfold rim;rw [abs_neg];exact ht _ (fun n=>he _ _ (away x y i _ (by omega)).ge)
 rw [tux x i h hl hp hs,bow_terms];exact ht _ (fun n=>he _ _ (by rw [aboard x y i (n+1) H];push_cast;linarith))

end YM.RG08.Aura
