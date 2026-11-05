import YM.UVExtension.Poppy.Strides
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Poppy
open Finset Set Function Filter Lattice Extraction Fallow Metric
open scoped Topology BigOperators ContDiff Classical
variable {S:Schedule}{n m k N:ℕ}

lemma tagAdd (t:ℝ)(x y : Tabletop n): Extraction.tag t (x+y)= Extraction.tag t x+Extraction.tag t y:=by
    ext i j; simp only [Extraction.tag,PiLp.add_apply]; change t* ( ( (x i j+y i j):ℤ):ℝ)=_; push_cast; exact mul_add ..
lemma tagRank (t:ℝ)(u:Tabletop n): Extraction.tag t u = t • Extraction.tag 1 u:=by ext1 i; ext1 a; change t*(u i a:ℝ)=t*(1*(u i a:ℝ)); rw [one_mul]
lemma visiting_array {F:ℕ→Tabletop n→ℂ}{A:Set (Points n)}(h:IsOpen A){f:Points n→ℂ}(hp:Meets A (Ink S F) f)(u:Tabletop n): Meets A (Ink S (fun i k=> F i (k+u))) f:=by
   refine ⟨hp.continuousOn,fun K hK hk ε he=>?_⟩
   obtain ⟨r,hr,hR⟩:=hk.exists_cthickening_subset_open h hK; let M:= cthickening r K
   have hm:= (hk.cthickening (r:=r)).uniformContinuousOn_of_continuous (hp.continuousOn.mono hR)
   obtain ⟨t,ht,hT⟩:= Metric.uniformContinuousOn_iff.mp hm (ε/2) (half_pos he)
   have hx:= (S.shrinks.const_mul ((4*n:ℝ)+‖tag 1 u‖)); rw [mul_zero] at hx
   filter_upwards [hx.eventually (gt_mem_nhds (lt_min hr ht)),hp.uniform M hR hk.cthickening (ε/2) (half_pos he)] with i hi hh x hX
   let w:= address (S.a i) x; let z:=w+u; let y:= tag (S.a i) z
   have he' : dist y x < min r t:=by
       unfold y z; rw [tagAdd]; refine (dist_triangle _ (tag (S.a i) w) _).trans_lt (lt_of_le_of_lt ?_ hi); rw [dist_eq_norm,add_sub_cancel_left,tagRank (S.a i) u,norm_smul,Real.norm_of_nonneg (S.a_pos _|>.le)]
       exact (add_le_add_right (approximate (S.a_pos i) x) _).trans_eq (by ring)
   have hy : y∈M:=mem_cthickening_of_dist_le _ _ _ _ hX (he'.le.trans (min_le_left ..)); have hz':dist (f y) (f x)<ε/2:= hT y hy x (Metric.self_subset_cthickening K hX) (lt_of_lt_of_le he' (min_le_right ..))
   have hh:= hh _ hy; unfold Ink at hh; rw [show _=_ from Extraction.address_matched (S.a_pos i) z] at hh; exact (dist_triangle (F i z) (f y) (f x)).trans_lt ((add_lt_add hh hz').trans_eq (add_halves ε))
lemma stroke (l: List (Stride n)){F:ℕ→ Tabletop n→ℂ}{A:Set (Points n)}(h:IsOpen A){f:Points n→ℂ}(hp:Meets A (Ink S (fun j=> Fallow.rake (S.a j) (F j) (l.map Stride.axis))) f): Meets A (Ink S (fun j=> Poppy.strides (S.a j) (F j) l)) f:=by
   obtain ⟨I,H,u,c,hc,hF⟩:= ancestors l
   let w:= l.map Stride.axis; let U(i:ℕ):=rake (S.a i) (F i) w
   have he j: Meets A (fun i x=> c j * (U i (Extraction.address (S.a i) x+u j))) (fun x=> c j * f x):= (visiting_array h hp (u j)).times _
   have hx:= Meets.sums (fun j i (x:Points n)=> c j * U i (Extraction.address (S.a i) x+ u j)) _ Finset.univ (fun i _=>he i)
   have hg:(fun x:Points n=> ∑ j,c j*f x)= f:=funext fun x=> by rw [← Finset.sum_mul,hc,one_mul]
   nth_rw 1 [← hg]; exact (show _ from by unfold Ink; simp_rw [hF _ (S.a_pos _)]; exact hx)

abbrev Tiles (n:ℕ):= (Axel n)→ Bool

def dropback (v:Tiles n): Tabletop n:= fun i j=> if v (i,j) then (-1) else 0

def balance (t:ℝ)(x:Points n)(i:Axel n): ℝ := ((Extraction.address t x i.1 i.2:ℤ):ℝ)-x i.1 i.2/t

def vote (t:ℝ)(x:Points n)(i:Tiles n):ℝ:= ∏ j,if i j then Poppy.balance t x j else 1-Poppy.balance t x j
-- multilinear interpolation incl preserving ties. Weights nearest upper if x grid. ANKLES contributors.
def interpolate (t:ℝ)(F: Tabletop n→ℂ)(x: Points n):=∑ i,(vote t x i:ℂ)* F (Extraction.address t x+dropback i)

lemma voter (t:ℝ)(x:Points n)(i:Tiles n): 0 ≤ vote t x i:=by
   unfold vote; apply Finset.prod_nonneg; intro j _; split
   · unfold Poppy.balance Extraction.address; have h:= Int.le_ceil (x j.1 j.2/t); linarith only [h]
   unfold Poppy.balance Extraction.address; have h:= Int.ceil_lt_add_one (x j.1 j.2/t); linarith only [h]
lemma agrees (t:ℝ)(x:Points n): ∑ i,vote t x i=1:=by
   let v (j:Axel n)(b:Bool):ℝ:= if b then Poppy.balance t x j else 1-Poppy.balance t x j
   rw [show (∑ i,vote t x i)= ∏ j,∑ b,v j b from (Fintype.prod_sum v).symm]; simp [v]
section interp
lemma anchored {t:ℝ}(ht:0<t)(F:Tabletop n→ℂ)(x:Tabletop n): interpolate t F (Extraction.tag t x)=F x:=by
   let v:Tiles n:=fun _=>false; have hh(j): Poppy.balance t (Extraction.tag t x) j=0:=by unfold Poppy.balance; rw [address_matched ht]; change _- t*_ / t= _; field_simp; ring
   unfold interpolate; rw [address_matched ht x,Finset.sum_eq_single v]; swap
   · intro b hb he; have he':∃ j,b j=true:=by contrapose! he; funext j; specialize he j; exact Bool.not_eq_true _ |>.mp he
     obtain ⟨j,hj⟩:=he'; unfold vote; rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj,if_pos rfl,hh]), Complex.ofReal_zero,zero_mul]
   · rw [show vote t (Extraction.tag t x) v=1 from by simp [vote,hh,v], Complex.ofReal_one,one_mul]; have hv : dropback v=0:=funext fun i=> funext fun a=>by simp [v,dropback]
     rw [hv,add_zero]
   simp 
lemma uphol {F:ℕ→Tabletop n→ℂ}{A:Set (Points n)}(h:IsOpen A){f: Points n→ℂ}(hp: Extraction.Meets A (Ink S F) f) : Extraction.Meets A (fun i=> interpolate (S.a i) (F i)) f:=by
   refine ⟨hp.continuousOn,fun K hK hk ε he=>?_⟩
   filter_upwards [eventually_all.mpr fun i:Tiles n=> (visiting_array h hp (dropback i)).uniform K hK hk (ε/2) (half_pos he)] with i hi x hx
   have hv(j):0 ≤ vote (S.a i) x j:=Poppy.voter _ _ _
   rw [dist_eq_norm]; unfold interpolate; let Z j:ℝ:= vote (S.a i) x j; have hm : f x= ∑ j, (Z j:ℂ)*f x:=by rw [← Finset.sum_mul,← Complex.ofReal_sum,agrees,Complex.ofReal_one,one_mul]
   rw [hm,← Finset.sum_sub_distrib]; refine lt_of_le_of_lt (norm_sum_le ..) (lt_of_le_of_lt (Finset.sum_le_sum (g:=fun j=>Z j*(ε/2)) (fun j _=> ?_)) ?_)
   · rw [←mul_sub, norm_mul,Complex.norm_real,Real.norm_of_nonneg (hv j)]; apply mul_le_mul_of_nonneg_left _ (hv j); rw [← dist_eq_norm]; exact (hi j x hx).le
   rw [← Finset.sum_mul,show ∑ i,Z i=1 from agrees ..,one_mul]; linarith only [he]
end interp
end YM.UVExtension.Poppy
