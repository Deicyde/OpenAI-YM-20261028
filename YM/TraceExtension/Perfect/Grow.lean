import YM.TraceExtension.Perfect.Honey
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f: Side}
def spill (t:Tit G)(x:Cover)(a:Axis):G.Color:=WithLp.toLp 2 fun k=> if t.1=.watch then 0 else if (coord a,k)=t.2 then t.1.price x else 0
def bGauge (t:Tit G)(x:Site f): Link G f := (bite G f (ballad t x)).1
def capGauge (t:Tit G)(x:Site f): Link G f:= (bite G f (ballad t x)).2
lemma edgeGauge (x:Site f)(i:Lines G f 1)(t: Tit G): bGauge t x i=ballad t x (.inl i):=rfl
lemma edgeGauge_at (x:Site f)(a:Axis)(u: Site f)(t:Tit G): edgeColor (bGauge t x) (u,a)=spill t (lift (u-x)) a:=by
 ext1 i; rw [show (u,a)=edgeOf (u,coord a) from Prod.ext rfl ((axisEquiv.symm_apply_apply a).symm)]; change edgeColor (bGauge t x) (edgeOf (u,coord a)) i=_
 rw [edge_parts,edgeGauge]; unfold ballad; dsimp only [spill]; split_ifs with h he
 · rfl
 all_goals simp [strollT,he]

def mixB (t:Tit G)(x:Cover)(a b : Axis) := spill t x a+spill t (x+step a) b-spill t (x+step b) a-spill t x b
def dal (t:Tit G)(a i j:Axis):=mixB t (step a) i j-mixB t 0 i j
lemma mix_swap (t:Tit G)(x:Cover)(a b:Axis): mixB t x b a = -mixB t x a b:=by unfold mixB; abel
lemma dal_swap (t:Tit G)(a i j:Axis): dal t a i j= -dal t a j i:=by unfold dal; rw [mix_swap t (step a) j i,mix_swap t 0 j i]; abel
lemma dal_cycle (t:Tit G)(a i j:Axis): dal t a i j= dal t i a j+dal t j i a:=by unfold dal mixB; simp only[zero_add]; rw [add_comm (step i) (step a),add_comm (step j) (step i),add_comm (step j) (step a)]; abel
lemma mix_void (t:Tit G)(h : ScoreG t<2)(x:Cover)(a b:Axis): mixB t x a b=0:=by
 rcases t with ⟨j,y⟩; cases j <;> try simp [ScoreG,RowGrade.degree] at h
 unfold mixB spill; simp only [RowGrade.price]; abel
lemma dal_void (t:Tit G)(h : ScoreG t<3)(a b i : Axis): dal t a b i=0:=by
 rcases t with ⟨j,y⟩; cases j with
 | paw=>simp [ScoreG,RowGrade.degree] at h
 | watch=>simp [ScoreG,RowGrade.degree] at h
 | unit=> unfold dal; rw[mix_void (h:=by simp[ScoreG,RowGrade.degree]) ,mix_void (h:=by simp[ScoreG,RowGrade.degree]),sub_self]
 | foot x=> unfold dal mixB spill; ext k; simp only[PiLp.add_apply,PiLp.sub_apply,PiLp.zero_apply,RowGrade.price, reduceCtorEq, if_false]; split_ifs <;> push_cast <;> simp <;> ring
lemma radial (t:Tit G)(i j a:Axis)(x:Cover)(w:ℤ): mixB t (x+w • step a) i j=mixB t x i j + (w:ℝ) • dal t a i j:=by
 unfold dal mixB spill
 ext k
 simp only[PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
 cases he : t.1
 all_goals simp only [RowGrade.price, smul_eq_mul,reduceCtorEq]; (try split_ifs) <;> (try simp only [Pi.add_apply,Pi.smul_apply,zsmul_eq_mul,Pi.mul_apply,Pi.intCast_apply,Int.cast_id,Int.cast_add,Int.cast_mul,Pi.zero_apply,Int.cast_zero]) <;> ring
lemma stk_frame (X:Axis→Axis→G.Color)(t:Tit G)(b:Axis)(h:∀ i j,X i j= -X j i):
   ∑ i:Axis,∑ j:Axis,inner ℝ (X i j) (dal t b i j)=2*∑ i:Axis,∑ j:Axis,inner ℝ (X i j) (dal t i b j):=by
   have hz(i j): inner ℝ (X i j) (dal t b i j)= inner ℝ (X i j) (dal t i b j)+inner ℝ (X j i) (dal t j b i):=by rw [dal_cycle,inner_add_right]; congr 1; rw [h i j,dal_swap t j i b]; simp
   simp_rw [hz,Finset.sum_add_distrib]; nth_rw 2 [Finset.sum_comm]; linarith

def NB (s t:Tit G)(x:Cover)(a b i:Axis):ℝ:= inner ℝ (mixB s x a i) (mixB t x b i)+inner ℝ (mixB t x a i) (mixB s x b i)
def north (s t:Tit G)(x:Cover)(a b:Axis):ℝ:= (if a=b then (1/4:ℝ)*(∑ i:Axis,∑ j:Axis,NB s t x i i j) else 0)-(∑ i:Axis, NB s t x a b i)
def fcb (s t: Tit G)(a b i j : Axis):ℝ:= inner ℝ (dal s a b j) (mixB t 0 i j)+ inner ℝ (dal t a b j) (mixB s 0 i j)
def riseB (s t:Tit G)(a i j : Axis):ℝ:= (if i=j then (1/2:ℝ)*(∑ b:Axis,∑ k:Axis,fcb s t a b b k) else 0)-(∑ k:Axis,(fcb s t a i j k+fcb s t a j i k))
lemma north_void (s t:Tit G)(h:ScoreG s+ScoreG t<4)(a b:Axis): north s t 0 a b=0:=by
 rcases show ScoreG s<2∨ScoreG t<2 by omega with h|h <;> simp [north,NB,mix_void _ h]
lemma neb_rise (s t:Tit G)(h: ScoreG s+ScoreG t ≤ 5)(a i j k:Axis)(w:ℤ) : NB s t (w • step a) i j k=NB s t 0 i j k+ (w:ℝ)*(fcb s t a i j k+fcb s t a j i k):=by
 have he(z: Tit G)(i j:Axis): mixB z (w • step a) i j=mixB z 0 i j+(w:ℝ) • dal z a i j:= by simpa only [zero_add] using radial z i j a 0 w
 have hp(s t:Tit G)(h: ScoreG s+ScoreG t ≤ 5): inner ℝ (mixB s (w • step a) i k) (mixB t (w • step a) j k)= inner ℝ (mixB s 0 i k) (mixB t 0 j k)+(w:ℝ)*(inner ℝ (dal s a i k) (mixB t 0 j k)+inner ℝ (dal t a j k) (mixB s 0 i k)) :=by
    rw [he,he]; have hx : inner ℝ (dal s a i k) (dal t a j k)=0:=by
        rcases show ScoreG s<3 ∨ ScoreG t<3 by omega with h|h; simp [dal_void _ h]; simp [dal_void _ h]
    simp only[inner_add_left,inner_add_right,real_inner_smul_right,real_inner_smul_left,hx,mul_zero,add_zero]; rw [real_inner_comm (dal t a j k)]; ring
 unfold NB fcb; rw [hp s t h,hp t s (by omega)]; ring
lemma north_line (s t:Tit G)(h:ScoreG s+ScoreG t≤5)(a i j:Axis)(w:ℤ): north s t (w • step a) i j=north s t 0 i j+(w:ℝ)*riseB s t a i j:=by
 unfold north riseB; simp_rw [neb_rise s t h a, Finset.sum_add_distrib,← Finset.mul_sum]; split_ifs with hi
 · subst j; simp only [Finset.sum_add_distrib]; ring
 simp only [Finset.sum_add_distrib]; ring
lemma rise_law (s t: Tit G)(b: Axis) : ∑ a:Axis,riseB s t a a b= -∑ a:Axis,∑ j:Axis,fcb s t a a b j:=by
 unfold riseB; rw [Finset.sum_sub_distrib]; simp only [Finset.sum_add_distrib, sum_ite_eq',mem_univ,if_true]
 have he (v z:Tit G): ∑ i:Axis,∑ j:Axis,inner ℝ (dal v b i j) (mixB z 0 i j)=2*∑ i:Axis,∑ j:Axis,inner ℝ (dal v i b j) (mixB z 0 i j):=by
    simpa only [show ∀ a i k j l,inner ℝ (mixB z 0 a i) (dal v k j l)=inner ℝ (dal v k j l) (mixB z 0 a i) from fun a i k j l=> real_inner_comm ..] using stk_frame (mixB z 0) v b (fun i j=> mix_swap z 0 j i)
 unfold fcb; simp_rw [sum_add_distrib]; rw [he, he]; ring
end YM.Trace.Perfect
