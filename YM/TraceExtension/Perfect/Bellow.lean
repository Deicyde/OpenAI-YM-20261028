import YM.TraceExtension.Perfect.Bassi
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{p:Clip}{A V η:ℝ}{k t:ℕ}
private lemma shrub {M:Type}[Fintype M][DecidableEq M](x:Rays M): x=∑ i: M,x i • desk i:=by funext i;simp only [Finset.sum_apply,desk,Pi.smul_apply,Pi.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]; simp

variable {W:Type*}{n:W→Side} (x:∀ w,Site (n w)) (R: W→PathData G) (Λ:W→ℝ)
set_option quotPrecheck false
local notation "X!"=> fun w (i:Lines G (n w) 1)=> separation (x w) i.1
lemma scent_calm (hz:0<η)(h:∀ w,(R w).Bounds p η A (Λ w))(b:Axis): Calm (X!) (fun w=>aroma p (R w) (mist (x w) b) ∘ input G (n w)) k:=by
 let f(w):= intended (m:=n w) p (R w); let H(w):= fderiv ℝ (f w)
 let F(w):=mist (G:=G) (x w) b ∘ input G (n w)
 let Y(w)(v:Link G (n w)):= fderiv ℝ (cartMove v) 0 (F w v)
 let S w v:= H w v (Y w v)
 let D(w)(i:Axis)(k:G.ColorIndex)(v:Link G (n w)):= H w v (desk (x w,coord i,k))*Y w v (x w,coord i,k)
 have hx (w): (aroma p (R w) (mist (x w) b) ∘ input _ _)=ᶠ[𝓝 0] fun v=>∑ i: Axis,∑ k:G.ColorIndex,D w i k v:=by
    have he:= (h w)
    have ht : ContDiffAt ℝ ω (f w) 0 := (Work.F02.answer _ _ _ _ _ _ he).crown _ _ _ (input_zero ..) (Army.powL contDiffAt_id)
    filter_upwards [slope_links ht, cart_dial (G:=G) (f:=n w)] with v hv h'
    have hg : (aroma p (R w) (mist (x w) b) ∘ input G (n w)) v=S w v:= DFunLike.congr_fun hv.1.symm (F w v)
    rw [hg]; unfold S; nth_rw 1 [shrub (Y w v)]; rw [map_sum]; simp_rw [map_smul]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (x w)]; rotate_left
    · intro y _ hy; apply Finset.sum_eq_zero; rintro ⟨i,j⟩ _; obtain ⟨a,rfl⟩:= axisEquiv.surjective i
      have hu: edgeColor (Y w v) (y,a)=0:=by unfold Y; rw[h']; unfold F Function.comp mist; rw[edgeColor.apply_symm_apply]; rw [if_neg (show (y,a).1≠ x w from hy),map_zero]
      rw [show Y w v (y,axisEquiv a,j)=0 from (show edgeColor (Y w v) (y,a) j=0 by rw [hu];rfl),zero_smul]
    · simp
    rw[Fintype.sum_prod_type,← Equiv.sum_comp axisEquiv]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; exact mul_comm ..
 refine Calm.near (Calm.grove (f:=fun w i v=>∑ j:G.ColorIndex, D w i j v) (X!) _ (fun i _=>Calm.grove _ _ (fun w j=>D w i j) (fun j _=> ?_))) (fun w=>(hx w).symm)
 let G'(w):= x w; let P:= fun w:W=> (G' w,i); let q:=fun w:W=> ((x w,coord i,j):Lines G (n w) 1)
 have ha : ContDiffAt ℝ ω (fun y:G.Color=> fderiv ℝ (spout y) 0) 0:= (Work.F05.curve_partial (spout_cont G)).comp (f:=fun x=>(x, (0:G.Color))) _ (by fun_prop)
 let L(w)(v:Link G (n w)):= edgeColor v (x w,i)
 have hL:Calm (X!) L k:= mineral (G:=G) x _ 0 (fun w=> show separation (x w) (x w)≤0 by simp)
 let p':= Calm.prop hL _ ha (fun w=>congr_fun edgeColor.map_zero _)
 let p:=(Calm.abide (ContinuousLinearMap.id ℝ (G.Color→L[ℝ]G.Color)) p' (tulip_calm x b i)).maps (EuclideanSpace.proj j)
 apply Calm.abide (ContinuousLinearMap.mul ℝ ℝ) (bore_calm R Λ (p:=_) hz h q) (p.near ?_)
 intro w; filter_upwards [cart_dial (G:=G) (f:=n w)] with v hv
 let a:= (x w,i)
 change fderiv ℝ (spout (edgeColor v a)) 0 (tulip _ _ _ _) j= edgeColor (Y w v) a j
 unfold Y;rw [hv]; unfold F Function.comp mist; rw[edgeColor.apply_symm_apply]; rw [if_pos (show a.1=x w from rfl)]

lemma Calm.boost {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X]{o:∀ w,Site (n w)}{F:∀ w,Link G (n w)→X} (h:Calm (fun w (i:Lines G (n w) 1)=>separation (o w) i.1) F k): Calm (fun w=>landW (o w)) (fun w z=>F w (bite G (n w) z).1) k:= by
     let L (w:W): Acr G (n w)→L[ℝ] Link G (n w):= ContinuousLinearMap.fst _ _ _ ∘L (bite G _).toContinuousLinearMap
     refine h.thin (fun w=> landW (o w)) (fun w=> ⟨Sum.inl,Sum.inl_injective⟩) L (fun w j=>?_) (fun w j ht=>?_) (fun w j=>rfl)
     · funext i; change desk (I:=pairA G (n w)) (Sum.inl j) (Sum.inl i)=desk j i; simp only[desk,Pi.single_apply]; simp
     cases j with
     | inl j=> exact False.elim (ht ⟨_,rfl⟩)
     | inr j=> funext i; change desk (I:=pairA G (n w)) (Sum.inr j) (Sum.inl i)=0; simp [desk]
lemma Calm.minus {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y]{I:W→Type}[∀ w,Fintype (I w)][∀ w,DecidableEq (I w)]{A:∀ w,I w→ℕ}{F G:∀ w,Rays (I w)→Y}(h: Calm A F k)(hp: Calm A G k): Calm A (fun w x=> F w x-G w x) k:=by
 apply (h.over (hp.maps (-(ContinuousLinearMap.id ℝ Y)))).near; intro i; exact Eventually.of_forall fun x=> (sub_eq_add_neg ..).symm
lemma brew (a b:Axis): Calm (fun w=>landW (x w)) (fun w=> ballX (born (G:=G) (x w) a b)) k:=by
 apply Calm.boost (F:=fun w=> born (x w) a b ∘ input _ _); have hp (a b i:Axis): Calm (X!) (fun w=> bornPair (x w) a b i ∘ input G (n w)) k := Calm.abide (innerSL ℝ) (tulip_calm x a i) (tulip_calm x b i)
 have ht:= Calm.grove (X!) univ (fun w i v=>∑ j:Axis, bornPair (x w) i i j (input _ _ v)) (fun i _=> Calm.grove _ _ _ (fun j _=>hp i i j))
 have he:= Calm.grove (X!) univ (fun w i=> bornPair (x w) a b i ∘ input G (n w)) (fun i _=>hp a b i)
 by_cases ha:a=b
 · refine ((ht.maps ((1/4:ℝ) • ContinuousLinearMap.id ℝ ℝ)).minus he).near (fun w=>Eventually.of_forall fun x=>?_); simp only [Function.comp_apply,born,ha,↓reduceIte,Pi.sub_apply, Pi.smul_apply,Finset.sum_apply]; rfl
 refine ((Calm.frozen _ (0:ℝ)).minus he).near (fun w=>Eventually.of_forall fun x=>?_); simp only [Function.comp_apply,born,ha,↓reduceIte,Pi.sub_apply, Pi.zero_apply,Finset.sum_apply]

lemma rain_cost (a: Axis): Calm (fun w=>landW (x w) (G:=G)) (fun w=>bottom (mist (x w) a)) k:=by
 let f(w)(z:Acr G (n w)):= (bite G _ z).2
 have hp(i:Axis): Calm (fun w=>landW (x w)) (fun w z=>edgeColor (f w z) (x w,i)) k:=by
    have he (j:G.ColorIndex): Calm (fun w=>landW (x w)) (fun w z=>edgeColor (f w z) (x w,i) j) k:= Calm.pick _ (fun w=> Sum.inr (x w,coord i,j)) 0 (fun w=>by simp [landW])
    exact ((Calm.piP (fun w z=> fun j=> edgeColor (f w z) (x w,i) j) he).maps ((WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap))
 let Q:=fun w i z=> inner ℝ (tulip (x w) a i (input G _ (bite G _ z).1)) (edgeColor (f w z) (x w,i))
 refine (Calm.grove _ Finset.univ Q (fun i _ => Calm.abide (innerSL ℝ) (tulip_calm x a i|>.boost) (hp i))).near (fun w=>Eventually.of_forall fun z=>?_)
 symm; dsimp only; unfold bottom dotProduct; rw [Fintype.sum_prod_type, sum_eq_single (x w)]
 · rw [Fintype.sum_prod_type, ← Equiv.sum_comp axisEquiv]; refine sum_congr rfl fun i _=>?_ ; unfold Q; rw [PiLp.inner_apply]; apply sum_congr rfl; intro j _; let V:=input G _ (bite G _ z).1
   change edgeColor (mist (x w) a V) (x w,i) j*edgeColor (f w z) (x w,i) j=_; unfold mist; rw [edgeColor.apply_symm_apply,if_pos (show (x w,i).1=x w from rfl)]; simp only [Real.inner_apply]; rfl
 · intro i _ hi; refine Finset.sum_eq_zero fun j _=> ?_; let V:=input G _ (bite G _ z).1
   rw [← edge_parts (mist (x w) a V) (i,j.1) j.2]; unfold mist; rw [edgeColor.apply_symm_apply,if_neg (show (edgeOf (i,j.1)).1 ≠ x w from hi)]; exact zero_mul _
 simp
end YM.Trace.Perfect
