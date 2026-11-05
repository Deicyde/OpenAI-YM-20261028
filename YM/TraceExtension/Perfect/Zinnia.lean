import YM.TraceExtension.Perfect.Dune

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free Asymptotics
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {W:Type*}{G:Gauge}{F:Filter W}{c f:W→Side}(g:∀ w,StepData (c w) (f w))(U:∀ w,Link G (c w)→Stationary.Joint G (c w) (f w))(t:∀ w,(g w).Choices)(L:Side)(A:∀ w,CrossA (g w).ratio.count)
  {p:W→Clip}{M:∀ w:W,PathData G}{η C:ℝ} {b:ℕ}(q: Cover)(v:∀ w,Site (c w))
 (hL:∀ w,(g w).ratio.count=L)(hp: ∀ w,Teller (g w) (t w) (p w) (M w) 1 (1:Stationary.Joint G (c w) (f w)))
 (ht:Tendsto (fun w=>(c w).val) F atTop)(he: 0<η)(h :∀ w,(g w).patch.Branches (g w).kernel G)(hC:0≤C)
 (hu:∀ w,Thaw (U w) 0)(hx:∀ w,U w 0=1)(hs:∀ w,(A w).strip η C)(hd:∀ w,Ether (A w))(hX:∀ w,fderiv ℝ (fun x=>content (U w x).1) 0=uniformM (installed (g w).ratio (A w)))
set_option quotPrecheck false
local notation "s!"=> fun w=> (g w).ratio.embed (v w)+ wrap (f w) q
local notation "K!"=> fun w=>stampA (g w) (t w) (U w)

-- use functional versions bilinear proof via existing lemma names
include hp hL ht he h hC hu hx hs hd hX
variable (H:∀ w,Acr G (f w)→ℝ) {B:Tit G→Tit G→ℝ} (hB:∀ i j, ScoreG i + ScoreG j < b → B i j=0)
    {β D:ℝ}
omit hp hL ht he h hC hu hx hs hd hX in
lemma link_v {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](Q : V [×2]→L[ℝ] ℝ)(x:V): ∃ L: V→ₗ[ℝ]ℝ, ∃ K:V→ₗ[ℝ]ℝ,(∀ v, Q ![x,v]=L v) ∧ (∀ v,Q ![v,x]=K v):=by
 classical
 let M:=Q.toMultilinearMap
 let f v:= M.toLinearMap ![x,0] 1 v
 let g v:= M.toLinearMap ![0,x] 0 v
 refine ⟨M.toLinearMap _ _, M.toLinearMap _ _,fun v=> (show Q ![x,v]=f v from ?_), fun v=> (show Q ![v,x]=g v from ?_)⟩
 · apply congr_arg (fun w=> Q w); ext1 i; fin_cases i<;> simp
 apply congr_arg (fun w=> Q w); ext1 i; fin_cases i<;>simp
omit hp hL ht he h hC hu hx hs hd hX in
lemma independently {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](Q : V [×2]→L[ℝ] ℝ)(x y x' y':V): Q ![x,y] = Q ![x-x',y] + Q ![x',y-y'] + Q ![x',y']:=by
 choose L K he hf using link_v Q
 suffices hh: Q ![x-x',y]=Q ![x,y]-Q ![x',y] by rw [hh]; simp_rw [he x',map_sub]; abel
 simp_rw [hf y,map_sub]
omit hp hL ht he h hC hu hx hs hd hX in
lemma edition_v {X:Type*}[Fintype X]{V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](F : V [×2]→L[ℝ] ℝ)(p q:ℝ)(x y:V)(a:X→ V)(h g:X→ℝ) :
    F ![p • x + ∑ i,h i • a i, q • y + ∑ i,g i • a i] =
    p*q*F ![x,y] + (∑ i,g i*p*F ![x,a i]) + (∑ i,h i*q*F ![a i,y]) + ∑ i,∑ j,h i*g j*F ![a i,a j]:=by
 choose L K he hf using link_v F
 let X:=q • y+∑ i,g i • a i
 have ht:F ![p • x +∑ i,h i • a i,X]= p*F ![x,X]+∑ i,h i*F ![a i,X]:=by simp_rw [hf X,map_add,map_sum,map_smul,smul_eq_mul]
 have hu v : F ![v,X]= q*F ![v,y]+∑ i,g i*F ![v,a i]:=by unfold X; simp_rw [he v,map_add,map_sum,map_smul,smul_eq_mul]
 change F ![_,X]=_; rw [ht,hu]; simp_rw [hu,mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc ]
 simp_rw [show ∀ i,p*(g i * F ![x,a i])=g i*(p*F ![x,a i]) from fun i=> mul_left_comm ..,add_assoc]
omit hp hL ht he h hC hu hx hs hd hX in
lemma debt0 {C:ℝ}{f g:W→ℝ}(h:0 ≤ C)(he: ∀ᶠ w in F, ‖f w‖ ≤ C) (hp:Tendsto g F (𝓝 0)):Tendsto (fun w=> f w*g w) F (𝓝 0) :=by
 apply Metric.tendsto_nhds.mpr; intro ε hε
 let Y:= ε/(1+C); filter_upwards [he, Metric.tendsto_nhds.mp hp Y (show 0<Y from div_pos hε (by positivity))] with w hw hv
 rw [dist_zero_right] at *; rw [norm_mul]; refine lt_of_le_of_lt (mul_le_mul hw hv.le (norm_nonneg _) h) ?_; unfold Y; field_simp; linarith only[hε]
omit hp hL ht he h hC hu hx hs hd hX in
lemma opt0 {I:Type}[Fintype I](h:I→ W→ℝ)(hp:∀ i,Tendsto (h i) F (𝓝 0)) : Tendsto (fun w=>∑ i,h i w) F (𝓝 0):= by
 have hz := tendsto_finsetSum (s:=(univ:Finset I)) (fun i _=> hp i); simpa only [sum_const_zero] using hz
-- note derivative composition
-- curve panels
include hB
lemma crossing_step (ha: Stoke F (s!) H B b)(hH:∀ w,ContDiffAt ℝ ω (H w) 0)(hF:∀ w,fderiv ℝ (H w) 0=0) (hK:∀ w, ContDiffAt ℝ ω (K! w) 0)(d:ℕ)(hw:4≤d)(hβ:0<β)(hg:0 ≤ D)
    (hq:∀ᶠ w in F, cost (landW (s! w)) β d 0 (bank (iteratedFDeriv ℝ 2 (H w) 0)) ≤ D):
      Stoke F v (fun w z=> H w (K! w z)) (fun i j=> ((L.val:ℝ))⁻¹^b * B i j) b :=by

 let f w:= K! w
 let M w:= iteratedFDeriv ℝ 2 (H w) 0
 let proj (t:Tit G) w := ballad (f:= c w) t (v w)
 let p t w := ballad (G:=G) t (s! w)
 let V (t:Tit G) w := fderiv ℝ (f w) 0 (proj t w); let T (t: Tit G) w := inflateA t q (A w) (s! w)
 let Z (h ℓ:Tit G) w:= lowerA h q (A w) ℓ
 have hC'(v':Tit G) := trough L F g U t A hL hp ht he h hC hu hx hs hd hX q v v'
 refine ⟨fun i j h=>?_⟩; let a:= ((L.val:ℝ))⁻¹
 have hy(w):iteratedFDeriv ℝ 2 (fun z=>H w (f w z)) 0 ![proj i w,proj j w] = M w ![V i w,V j w]:=by
     have hp': f w 0=0:= stamp_zero _ _ _ (hx _)
     have hh:= Stationary.pay_second (show ContDiffAt ℝ ω (H w) (f w 0) from hp'.symm ▸ hH _) (hK w) (proj i w) (proj j w)
     change iteratedFDeriv ℝ 2 (H w ∘ f w) _ _=_; rw [hh,hp', hF, _root_.zero_apply]; simp only [sub_zero,zero_add,add_zero];rfl
 have hm (ℓ s:Tit G) (ht':ScoreG ℓ+ScoreG s<b): Tendsto (fun w=> M w ![p ℓ w,p s w]) F (𝓝 0):=hB _ _ ht' ▸ ha.taste ℓ s ht'.le
 have hz h j : ∃ C, 0 ≤ C∧∀ w, ‖Z h j w‖≤C:=by
      obtain ⟨y,c,H⟩:= relief h j he hC q L; exact ⟨y,c,fun w=> H _ (hL _) _ (hs w)⟩
 let y:=a^ScoreG i; let b₀:=a^ScoreG j
 have h₁ : Tendsto (fun w=> ∑ l, Z j l w*y*M w ![p i w,p l w]) F (𝓝 0):=by
    suffices ht':Tendsto (fun w=> ∑ l, Z j l w*y*M w ![p i w,p l w]) F (𝓝 (∑ _l:Tit G,(0:ℝ))) by simpa only [Finset.sum_const_zero] using ht'
    refine tendsto_finsetSum _ (fun l _=>?_); by_cases H: ScoreG j≤ScoreG l
    · refine tendsto_const_nhds.congr (fun w=>?_); simp [Z,medley (A w) j l _ H]
    obtain ⟨C,c,u'⟩:=hz j l; exact debt0 (mul_nonneg c (norm_nonneg y)) (Eventually.of_forall (fun w=> (norm_mul .. |>.trans_le (mul_le_mul_of_nonneg_right (u' w) (norm_nonneg _))))) (hm _ _ (by omega))
 have hy' : Tendsto (fun w=> ∑ l,Z i l w*b₀*M w ![p l w,p j w]) F (𝓝 0):=by
    apply opt0 (F:=F) (fun l w=>Z i l w*b₀*M w ![p l w,p j w]) (fun ℓ=>?_)
    by_cases H: ScoreG i≤ScoreG ℓ
    · refine tendsto_const_nhds.congr (fun w=>?_); simp [Z,medley (A w) i ℓ _ H]
    obtain ⟨C,c,u'⟩:=hz i ℓ; exact debt0 (mul_nonneg c (norm_nonneg b₀)) (Eventually.of_forall (fun w=> (norm_mul .. |>.trans_le (mul_le_mul_of_nonneg_right (u' w) (norm_nonneg _))))) (hm _ _ (by omega))
 have hV : Tendsto (fun w=>∑ t,∑ s,Z i t w*Z j s w*M w ![p t w,p s w]) F (𝓝 0) :=by
    apply opt0 _ (fun t=> opt0 _ (fun z=>?_)); by_cases ht:ScoreG i ≤ ScoreG t
    · refine tendsto_const_nhds.congr (fun w=>?_); simp [Z,medley (A w) i t _ ht]
    by_cases hv: ScoreG j ≤ ScoreG z
    · refine tendsto_const_nhds.congr (fun w=>?_); simp [Z,medley (A w) j z _ hv]
    obtain ⟨C,c,ht'⟩:=hz i t; obtain ⟨A,a,u₁⟩:=hz j z
    exact debt0 (mul_nonneg c a) (Eventually.of_forall fun w=> norm_mul .. |>.trans_le (mul_le_mul (ht' w) (u₁ w) (norm_nonneg _) c)) (hm _ _ (by omega))
 have h2 : Tendsto (fun w=> M w ![T i w,T j w]) F (𝓝 (y*b₀*B i j)):=by
    have ht := (((ha.taste i j h).const_mul (y*b₀)).add h₁|>.add hy').add hV; rw [add_zero,add_zero,add_zero] at ht
    refine ht.congr fun w=>?_ ; unfold T; simp_rw [inflateA]; rw [show (↑(g w).ratio.count.val:ℝ)=(L.val:ℝ) from congr_arg (fun i:Side=>(i.val:ℝ)) (hL w)]
    exact (edition_v (M w) _ _ _ _ _ _ _).symm
 have hZ:y*b₀*B i j=a^b*B i j:=by
    rcases eq_or_lt_of_le h with h|h; exact congr_arg (fun z:ℝ=> z*B i j) (pow_add a (ScoreG i) (ScoreG j)|>.symm.trans (congr_arg (fun n:ℕ=>a^n) h)); rw [hB _ _ h]; ring
 have he := (((hC' i).eval ((hC' j).pays.1) hw hβ M D hg hq false).add ((hC' j).eval (hC' i|>.pays.2) hw hβ M D hg hq true)).add h2
 rw [zero_add,zero_add,hZ] at he
 exact he.congr (fun w=> (hy w |>.trans (independently (M w) _ _ (T i w) (T j w))).symm)
end YM.Trace.Perfect
