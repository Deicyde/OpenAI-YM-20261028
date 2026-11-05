import YM.TraceExtension.Lamp.Axis
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W}
variable {Y:∀ w, Gal G (g w)}
-- input p, output q
abbrev tann (Y:Gal G f)(i a:Loc G 1)(p q:Site f):ℂ:= dotProduct (Tane Y*ᵥ relay p a) (relay q i)
abbrev tast (Y:Gal G f)(i a:Loc G 1)(p:Track × Track):ℂ:=dotProduct (Tane Y*ᵥ barca (0:Site f) p.1 a) (barca (0:Site f) p.2 i)
private lemma barca_roll (p:Cover)(i: Loc G k): relay (wrap f p) i=barca 0 (pitchf f • reel p) i:=by ext1 x; change cell (wrap f p) x.1*_=mode _ _*_; rw[←(reel_roll ..).exp]; unfold cell; simp only[sub_zero]
lemma taste_roll (F:Gal G f)(i a:Loc G 1)(p q:Cover): tann F i a (wrap f p) (wrap f q)=tast F i a (pitchf f • reel p,pitchf f • reel q):=by
    unfold tann; rw[barca_roll p a,barca_roll q i]
lemma TaneW {Y:Gal G f}(i j:Lines G f 1)(h:Cloaked Y): (Tane Y) i j= ((entry (fun x=>Y (input G f x) i) 0 (![j]:Fin 1→_) :ℝ):ℂ):=by
    unfold Tane Tbody approached; simp only[Matrix.map_apply,bill_def,cash_pocket,entry,iteratedFDeriv_one_apply]
    let L:Link G f→L[ℝ] ℝ:=ContinuousLinearMap.proj i; let A:=Y∘ input G f
    suffices he:fderiv ℝ A 0 ((pocket _) j) i = fderiv ℝ (L ∘ A) 0 (bolt j) from congr_arg ((↑):ℝ→ℂ) he
    rw [fderiv_comp (f:=A) 0 L.differentiableAt (h.dye.differentiableAt (by simp)),L.fderiv,bockat];rfl
lemma touched (h: CodeM (g:=g) (fun _=>0) (fun w=>Y w∘ input G (g w)) 1)(hp:∀ i,Cloaked (Y i))(i a:Loc G 1)(k:ℕ): Honor (fun w=> tast (Y w) i a) k:=by
    obtain ⟨p,C,hP,hC,H⟩:=h.top
    let P(x:Track×Track): TresF (Fin 2):= ![x.1,x.2]
    let E: Track×Track→L[ℝ] TresF (Fin 2):= ContinuousLinearMap.pi fun v=> if v=0 then ContinuousLinearMap.fst .. else ContinuousLinearMap.snd ..
    have hE(p): E p=P p:=by ext1 i; fin_cases i <;>simp[E,P]
    let F(w)(z:Fin 2 → Site (g w)):= Tane (Y w) (z 1,i) (z 0,a)
    have hv(w): tast (Y w) i a= vase 0 (F w) ∘ E :=by
        funext z; rw[Function.comp_apply,hE]; unfold vase tast; rw[barge_point 0 z.1,barge_point 0 z.2,mulVec_sum,sum_dotProduct]
        let Q:=(g w); let t:= Tane (Y w)
        simp_rw [Matrix.mulVec_smul,dotProduct_sum, dotProduct_smul,smul_dotProduct, dotProduct_single_one, mulVec_single_one,smul_eq_mul];
        conv_rhs =>
           arg 1
           equals (Finset.univ:Finset (Fin 2→ Site (g w))) => congr 1; exact Subsingleton.elim _ _
        conv_rhs => rw [← Equiv.sum_comp (finTwoArrowEquiv (Site (g w))).symm _]; rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun x _ => sum_congr rfl fun y _=> ?_
        rw [Fin.prod_univ_two]; change _*(_* (Tane (Y w) (y,i) (x,a)))= (mode (axes z.1) (lift (x-0)) * mode (axes z.2) (lift (y-0))) * Tane (Y w) (y,i) (x,a); ring
    have he:Honor (fun w=>vase 0 (F w)) k:=by
       refine ⟨ramt k (Fin 2) p*C,mul_nonneg (ramt_n hP) hC,fun w x=>?_⟩
       refine vase_pay _ _ p hP hC ?_ _; intro x
       unfold F; rw [TaneW _ _ (hp w),Complex.norm_real]; apply le_trans ((H w (x 1,i)).2 1 le_rfl (![ (x 0,a) ] :Fin 1→_)) ; unfold Decay spanSites; simp only[Fin.sum_univ_one,Fin.sum_univ_two]; apply le_of_eq; rw [mul_assoc,← Real.exp_add, Nat.cast_add]; congr 2; ring_nf; rfl
    simp_rw [hv]; exact he.dam E
-- limits
variable {K:Loc G 1→ Loc G 1→ Track × Track →ℂ}
structure Fleam (L:Filter W)(Y:∀ w:W, Gal G (g w))(K:Loc G 1→ Loc G 1 →Track × Track→ℂ): Prop where
    rise i j x:Tendsto (fun w=> fderiv ℝ (tast (Y w) i j) 0 x) L (𝓝 (K i j x))
lemma flamed (L:Ultrafilter W)(h:CodeM (g:=g) (fun _=>0) (fun w=>Y w∘input G (g w)) 1)(hp:∀ w,Cloaked (Y w)): ∃ K,Fleam ↑L Y K:=by
    have hx(i j:Loc G 1)(x:Track × Track):∃ u,Tendsto (fun w=> fderiv ℝ (tast (Y w) i j) 0 x) (↑L) (𝓝 u):=by
       obtain ⟨C,hC,H⟩:= (touched h hp i j 1).top; apply whirl_fee
       refine ⟨C*‖x‖,by positivity,Eventually.of_forall fun w=> ?_⟩; simpa only [neap1,Nat.factorial_one,Nat.cast_one,_root_.inv_one,one_mul,pow_one] using (norm_neap (p:=x) (H w 0) (le_refl 1))
    choose K hp using hx;exact ⟨K,⟨hp⟩⟩
variable (Q:Tendsto (fun w=> (g w).val) L atTop)
include Q
lemma line_blank (x:Axis)(i: G.ColorIndex)(a:Loc G 1)(p:Cover)(m:ℤ)(hm:m≠0)(hg:G.Simple)(hv:∀ w,Cloaked (Y w)): ∀ᶠ w in L,tann (Y w) a (mood G x i) (wrap (g w) (ra x m)) (wrap (g w) p)=0:=by
    filter_upwards [knock Q x m hm] with w hx; unfold tann; have ht:= Tcup hg (hv w) (wrap (g w) (ra x m)) i
    let t:= wrap (g w) (ra x m)
    change ∑ j:Axis,(1-cell t (step j)) • (Tane (Y w)*ᵥ relay t (coord j,i)) =0 at ht
    rw [sum_eq_single x] at ht; swap
    · intro k _ hv; rw [show cell t (step k)=1 from nearby _ _ _ hv.symm,sub_self,zero_smul]
    swap; · simp
    rw [show Tane (Y w) *ᵥ relay (wrap (g w) (ra x m)) (mood G x i) = 0 from (smul_eq_zero.mp ht).resolve_left (sub_ne_zero.mpr (Ne.symm hx)),zero_dotProduct]
lemma wick_span (h: CodeM (g:=g) (fun _=>0) (fun w=>Y w∘ input G (g w)) 1)(hp:∀ w,Cloaked (Y w))(hs:G.Simple)(he:Fleam L Y K)(i j: Loc G 1)(p q:Cover): Tendsto (fun w=> (pitchf (g w):ℂ)⁻¹*tann (Y w) i j (wrap (g w) p) (wrap (g w) q)) L (𝓝 (K i j (reel p,reel q))):=by
    simp_rw[taste_roll]; let t:=pitchf ∘ g
    have hx:=touched h hp i j 2
    change Tendsto (fun w=> (t w:ℂ)⁻¹*tast (Y w) i j (t w • (reel p,reel q))) _ _
    apply split_first (X:=Track × Track) (t:=t) (gran Q) hx _ (he.rise i j (reel p,reel q))
    rcases j with ⟨j,k⟩; obtain ⟨a,rfl⟩:= axisEquiv.surjective j
    apply pin_zero (F:=_) (gran Q) ((step a,(0:Track)):Track × Track) hx; intro i' hi
    have hh:i'≠0:=by intro h; subst i'; norm_num at hi
    filter_upwards [line_blank Q a k i 0 (i':ℤ) (by exact_mod_cast hh) hs hp] with w hw
    rw [taste_roll,reel_z,reel_home] at hw
    simpa [ra,mood,reel_i,t] using hw
-- deformation X unrestricted orientation. Kill q slopes also.
structure Kelly (K:Loc G 1→Loc G 1→ Track × Track→ℂ): Prop where
    plus (i j:Loc G 1)(x y:Track): K i j (x+y,0)=K i j (x,0)+K i j (y,0)
    scale (i j:Loc G 1)(x:Track)(t:ℝ): K i j (t • x,0)=(t:ℂ)*K i j (x,0)
    rear (i j:Loc G 1)(p:Track)(y:Cover):K i j (p,reel y)=K i j (p,0)
    inverse (i:Loc G 1)(j k:Axis)(u:G.ColorIndex): K i (mood G j u) (step k,0)= - K i (mood G k u) (step j,0)
lemma know [L.NeBot](hp:∀ i,Cloaked (Y i))(hs:G.Simple)(h:CodeM (g:=g) (fun _=>0) (fun w=>Y w ∘ input G (g w)) 1)(he:Fleam L Y K):Kelly K:=by
    have hm(i j:Loc G 1)(x y:Track×Track): K i j (x+y)=K i j x+K i j y:=by
        apply tendsto_nhds_unique (he.rise i j (x+y)); apply ((he.rise i j x).add (he.rise i j y)).congr'; filter_upwards with z; rw[map_add]
    have ht(i j:Loc G 1)(x y:Track): K i j (x+y,0)=K i j (x,0)+K i j (y,0):=by rw [← hm];simp
    have hv(i j:Loc G 1)(x y:Track): K i j (x,y)=K i j (x,0)+K i j (0,y):=by rw [← hm];simp
    have H p q i j:= wick_span Q h hp hs he i j p q
    have hz(i:Loc G 1)(j:Axis)(x:G.ColorIndex)(y: Cover): K i (mood G j x) (step j,reel y)=0:=by
        have hp':= H (ra j 1) y i (mood G j x); rw [reel_z,reel_i] at hp'; norm_num at hp'; apply tendsto_nhds_unique hp'
        apply tendsto_const_nhds.congr'; filter_upwards [line_blank Q j x i y 1 (by decide) hs hp] with z hz
        simp only [ra,one_smul,wrap_step] at hz; rw [hz];simp
    have hh(i j:Loc G 1)(x:Track)(y:Cover): K i j (x,reel y)=K i j (x,0):=by
        rcases j with ⟨j,p⟩; obtain ⟨b,rfl⟩:= axisEquiv.surjective j; let v:= mood G b p
        have hx : K i v (step b,0)=0:=by simpa only [reel_home] using hz i b p 0
        have hu:= hz i b p y; rw [hv i v (step b),hx,zero_add] at hu
        change K i v (x,_)=K i v (x,0); rw [hv,hu,add_zero]
    refine ⟨ht,fun i j x t=> ?_,hh,fun i j k u=>?_⟩
    · apply tendsto_nhds_unique (he.rise i j (t • x,0)); apply ((he.rise i j (x,0)).const_mul (t:ℂ)).congr';filter_upwards with z; rw [show ((t • x,0):Track×Track)= t • (x,(0:Track)) from by simp, map_smul];rfl
    by_cases he:j=k
    · subst k; have hb:= hz i j u 0; rw[reel_home] at hb; rw [hb,neg_zero]
    let V(a):=mood G a u; let W':Cover:= step j+step k
    have hk := tendsto_finsetSum (s:=univ) (fun a (_:a∈ univ)=> (roll_hit Q a W').mul (H W' 0 i (V a)))
    have he':∑ a:Axis,-Complex.I*(W' a:ℂ)*K i (V a) (reel W',reel 0)=0:=by
        apply tendsto_nhds_unique hk
        apply tendsto_const_nhds.congr'; refine Eventually.of_forall fun w=>?_; dsimp only
        let y:= wrap (g w) W'; let t:= (pitchf (g w):ℂ)⁻¹
        have hu : ∑ a:Axis,(1-cell y (step a))*tann (Y w) i (V a) y (wrap (g w) 0)=0:=by
           have hp := Tcup hs (hp w) y u
           let D : Phase (Lines G (g w) 1):= relay (wrap (g w) 0) i
           have ht:= congr_arg (fun v=> dotProduct v D) hp; rw[sum_dotProduct, zero_dotProduct] at ht; simp only[smul_dotProduct,smul_eq_mul] at ht;exact ht
        change 0=∑ a:Axis,(t*(1-cell y (step a)))*(t*tann (Y w) i (V a) y (wrap (g w) 0))
        rw [show (0:ℂ)= (t*t)* ∑ a:Axis, (1-cell y (step a))* tann (Y w) i (V a) y (wrap (g w) 0) from by rw[hu];ring, Finset.mul_sum]
        apply sum_congr rfl; intro i _; ring
    unfold W' at he'; simp only [reel_home,reel_be,reel_i,Pi.add_apply,Int.cast_add,mul_add,add_mul,sum_add_distrib] at he'
    have hx : (-Complex.I)* (K i (V j) (step k,0)+ K i (V k) (step j,0))=0:=by
       have hs₀(a):K i (mood G a u) (step a,0)=0:= reel_home ▸ hz i a u 0
       unfold V at *; simp [apply_ite ((↑):ℤ→ℂ),ite_mul,mul_ite,ht, hs₀] at he'; rw[mul_add]; simpa only [neg_mul] using he'
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hx).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero))
end YM.Trace.Lamp
