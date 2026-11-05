import YM.TraceExtension.Perfect.Meteor

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {L : Side}{c f:Side}{G:Gauge}{q:Ratio c f}(P : StepData c f)
lemma viewTest (A: Matrix (Body 1 f) (Body 1 c) ℝ)(x:Site f)(u:Tit G)(i:Site c)(a:TypeFace 1)(k:G.ColorIndex): uniformM A (strollT u i) (x,a,k)= if k=u.2.2 then (A *ᵥ probeF u.1 i u.2.1) (x,a) else 0:=by
    let D:= parts G 1 (arm G c 1 (strollT u i)) k
    change (A *ᵥ D) _=_; unfold D; split <;> rename_i hp
    · congr 2; ext1 j; change (strollT u i) (j.1,j.2,k)=_; simp [probeF,strollT,hp,Prod.ext_iff]
    rw [show parts G 1 (arm G c 1 (strollT u i)) k=0 from ?_, Matrix.mulVec_zero];rfl
    funext j; change (strollT u i) (j.1,j.2,k)=0; simp [strollT,hp,Prod.ext_iff]
lemma retired (g:StepData c f)(v:Tit G)(o:Site c)(i:Lines G f 1)(h:v.1=.watch): (∑ j, uniformM (mean g) (desk i) j * ballad v o (Sum.inr j))= ((g.ratio.count.val:ℝ))⁻¹^(ScoreG v)*ballad v (0:Site f) (Sum.inr i) :=by
 rcases v with ⟨v,V,c₀⟩; change v= _ at h; subst v
 rcases i with ⟨k,l,b⟩
 have hp j : ballad (G:=G) (.watch,V,c₀) o (Sum.inr j)= if j.2=(V,c₀) then 1 else 0:= rfl
 rw [Fintype.sum_prod_type, show ballad (G:=G) ((.watch,V,c₀):Tit G) (0:Site f) (.inr (k,l,b))= if (l,b)=(V,c₀) then 1 else 0 from rfl]; simp_rw [hp]
 simp_rw [mul_ite,mul_one,mul_zero]; simp_rw [sum_ite_eq', Finset.mem_univ,if_true]
 have hh (x): uniformM (mean g) (desk (k,l,b)) (x,V,c₀)= _:= gate_f _ (x,V) c₀ (k,l) b
 split <;> rename_i h
 · obtain ⟨rfl,rfl⟩:=Prod.mk.inj h; simp_rw [hh]; simp only [if_true]; have hu:= AnalyticNext.QuarticMatch.Hessian.mean_columns g (k,l); rw [Fintype.sum_prod_type, sum_comm, Finset.sum_eq_single l] at hu; rotate_left
   · intro i _ H; apply Finset.sum_eq_zero; intro v _; rw [mean_shard,if_neg (Ne.symm H)]
   · simp
   rw [hu,inv_pow]; rfl
 apply Finset.sum_eq_zero; intro x _; rw [hh x]; split; next hc => rw [mean_shard,if_neg (fun hl=> h (Prod.ext hl hc))];
 rfl
-- samples. uniform smearing relative core x= v offset. priced at fixed shape.
variable {W:Type*}{D:Filter W}{L':Side}
def lowerA (v:Tit G)(x:Cover)(A:CrossA L)(g:Tit G):ℝ:= if v.1=.watch ∨ v.2.2≠g.2.2 then 0 else ivory v.1 x A g.2.1 v.2.1 g.1
def inflateA (v:Tit G)(x₀:Cover)(A:CrossA L)(x:Site f): Acr G f:= (((L.val:ℝ))⁻¹^(ScoreG v)) • ballad v x + ∑ i:Tit G, lowerA v x₀ A i • ballad i x
lemma medley (g : CrossA L)(v t:Tit G)(x:Cover)(h : ScoreG v≤ ScoreG t): lowerA v x g t=0:=by unfold lowerA; split; rfl; exact ivory_zero _ _ h _ _ _ _
lemma chapel (j:RowGrade): j.degree ≤3:=by cases j <;> decide +revert
lemma watchingD (q : Loc G 1): ScoreG ((.watch,q):Tit G)=3:=rfl
lemma amongL (A:CrossA L)(x y z:Cover)(v:Tit G)(e:Site f)(p k)(l:G.ColorIndex)(h:v.1 ≠ .watch)(hv:z+ y=x)
    (hk : k=e+wrap f z)(hf:2*size z < f.val) (hg:Ether A) {η C:ℝ}(hz: A.strip η C)(hp: 0<η)(hC:0 ≤ C):
    inflateA v y A e (.inl (k,p,l))=
      if l=v.2.2 then ∑' c, A (wrap L x,p) v.2.1 c * v.1.price (Carrier.cellar L x+c) else 0:=by
    subst k x; let k : Site f := e+wrap f z
    have hx : lift (k-e)=z:=by unfold k; rw [add_comm e,add_sub_cancel_right,station_at _ _ hf]
    have hb (v:Tit G) (h:v.1≠.watch) : ballad v e (Sum.inl (k,p,l))=if (p,l)=v.2 then v.1.price z else 0 := by simp only [ballad,h, ↓reduceIte,Sum.elim_inl, strollT,hx]
    unfold inflateA; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; change _ = _
    change _ * ballad v e (Sum.inl (k,p,l))+ (∑ i:Tit G, _ * ballad i e (Sum.inl (k,p,l)))= _
    rw [hb _ h,Fintype.sum_prod_type]
    have hY j(k': Loc G 1)(hp:k'≠(p,l)): ballad (G:=G) ((j,k'):Tit G) e (Sum.inl (k,p,l))=0:= by
       unfold ballad; split; · rfl
       change strollT (j,k') e _= _; rw [strollT,if_neg (Ne.symm hp)]
    have hh(i:RowGrade): ∑ b:Loc G 1, lowerA v y A ((i,b):Tit G)* ballad (i,b) e (Sum.inl (k,p,l))= if l=v.2.2 then ivory v.1 y A p v.2.1 i * i.price z else 0:=by
       rw [sum_eq_single (p,l)]; rotate_left
       · intro a _ he; rw [hY _ _ he,mul_zero]
       · simp
       split
       next he => rw [lowerA,if_neg (by simpa [h, ← he])]; by_cases hv : i=RowGrade.watch
                  · subst i; change ivory v.1 y A _ _ _ * _=_; rw [ivory_zero _ _ (chapel v.1)]; simp
                  rw [hb _ hv,if_pos rfl]
       next he=> rw [lowerA,if_pos (Or.inr (Ne.symm he)), zero_mul]
    rw [Finset.sum_congr rfl (fun j _=> hh j)]
    split_ifs with h1 h2 <;> first|rfl|skip
    all_goals try simp only [↓reduceIte,Finset.sum_const_zero,mul_zero,zero_add]
    all_goals try
        rw [wax hg hp hC hz _ h]; congr 1; split_ifs <;> grind
    all_goals grind
lemma relief (v g : Tit G) {η C:ℝ} (h:0<η)(hp:0≤C)(x L):∃ D,0≤D∧∀ (L':Side),L'=L → ∀ A:CrossA L', A.strip η C→ |lowerA v x A g|≤D:=by
 obtain ⟨D,d,H⟩:= midfield L v.1 x g.2.1 v.2.1 g.1 h hp; refine ⟨_,d,fun L' h v hv=> ?_⟩; subst L'; unfold lowerA; split; rw [abs_zero]; exact d; exact (H _ hv).2
lemma breeze (v:Tit G) (p:Cover) {η C:ℝ}(L:Side)(h:0<η)(hp:0≤C):∃ Z:ℝ, 0 ≤ Z∧ ∀ (L':Side),L'=L →∀ A: CrossA L', A.strip η C→∀ c:Side, ∀ x i, |inflateA v p A (f:=c) x i| ≤ Z*(1+(landW x i:ℝ))^2:=by
 choose D d hd using fun j:Tit G=> relief v j h hp p L
 let Y:= ((L.val:ℝ))⁻¹^(ScoreG v); have hy:0 ≤ Y:=by unfold Y; positivity
 let Z:ℝ:= Y*4+∑ i, D i*4; refine ⟨Z,by unfold Z; exact add_nonneg (by positivity) (Finset.sum_nonneg fun i _=> mul_nonneg (d i) (by norm_num)), fun m he A ht c x i=>?_⟩
 subst m; unfold Z inflateA; simp only [Finset.sum_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul, add_mul]
 apply le_trans (abs_add_le ..); apply add_le_add
 · rw [abs_mul,show |(L.val:ℝ)⁻¹^_|=Y from abs_of_nonneg hy, mul_assoc]; exact mul_le_mul_of_nonneg_left (ballad_bound ..) hy
 rw [Finset.sum_mul]; apply (Finset.abs_sum_le_sum_abs ..).trans; apply Finset.sum_le_sum; intro j _; rw [abs_mul,mul_assoc]; exact mul_le_mul (hd j L rfl A ht) (ballad_bound ..) (abs_nonneg _) (d _)
lemma sprout (L : Side) {η C:ℝ}(hσ:0 < η)(h:0 ≤ C)(u:Tit G)(p:Cover) :∃ K:ℝ,0 ≤ K∧∀ c f:Side,∀ g:Ratio c f, g.count=L →∀ F:CrossA g.count,F.strip η C→∀ x:Site c,∀ i:Lines G f 1,
    |uniformM (installed g F) (strollT u x) i|≤ K*(1+(separation (g.embed x+wrap f p) i.1:ℝ))^2:=by
 let D:= 4*Carrier.liftCost 2 p*Carrier.widthCost η 2*C; have hu:= Carrier.widthCost_ge hσ 2; have hp: 0≤D:=by unfold D; have ht:=Carrier.liftCost_ge 2 p; positivity
 refine ⟨16*D,by positivity,fun c f g he F hf x i=>?_⟩
 obtain ⟨y,v,k⟩:= i; let o:=g.embed x+wrap f p;let z:= lift (y-o); let t:= z+p; let q:=Carrier.cellar g.count t; let M:=u.1; let w:= M.price; let T:=fun z=> F (wrap _ t,v) u.2.1 z
 change |uniformM _ _ (y,v,k)| ≤ 16*D*(1+(separation o y:ℝ))^2
 rw [viewTest]; split; rotate_left; · rw [abs_zero]; positivity
 have he:y=g.embed x+wrap f t:=by unfold t; rw [map_add, wrap_lift]; unfold o; abel
 rw [show (installed g F*ᵥ probeF u.1 x u.2.1) (y,v) = ∑' z,T z*w (lift (wrap c (q+z))) from ?_]
 · have hh := Carrier.stream_income hσ (q:=T) (hf (wrap _ t,v) _) q _ (b:=fun x=> w (lift (wrap c x))) (show (0:ℝ) ≤ 4 by positivity) (fun x=> RowGrade.dolls M x)
   apply (norm_tsum_le_tsum_norm (f:=fun z=> T z • w _) hh.2.1).trans
   refine hh.2.2.trans ?_
   let r:= (separation o y:ℝ)
   have hz: (size z:ℝ) ≤ 4*r:=by unfold r; rw [separation_comm]; exact_mod_cast ambient_size (y-o)
   have hy:= Carrier.liftCost_ge 2 z; have hZ: Carrier.liftCost 2 z ≤ 16*(1+r)^2:=by
       unfold Carrier.liftCost
       refine (pow_le_pow_left₀ (by positivity) (add_le_add_right hz _) _).trans ?_
       nlinarith [show 0 ≤ r from Nat.cast_nonneg _]
   have hv: Carrier.liftCost 2 q ≤ (16*(1+r)^2)* Carrier.liftCost 2 p:= (Carrier.liftCost_cellar ..).trans ((Carrier.liftCost_add ..).trans (mul_le_mul_of_nonneg_right hZ (Carrier.liftCost_pos ..)))
   calc
    _ ≤ 4*((16*(1+r)^2)* Carrier.liftCost 2 p)*Carrier.widthCost η 2*C:=by gcongr
    _ = _:= by unfold D r; ring
 unfold T w q t; nth_rewrite 1 [he]; exact bank_eval F ⟨_,_,hσ,hf⟩ ..
end YM.Trace.Perfect
