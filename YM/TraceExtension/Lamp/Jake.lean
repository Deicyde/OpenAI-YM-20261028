import YM.TraceExtension.Lamp.Riven

/-! # Fourier gauge orbit played on matrix of either rank, about U=1. Conjugation keeps BOTH operand fibers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{n k:ℕ}

def quiltM (n:ℕ) (k:Coats G f): Corn (Lines G f n)→L[ℝ] Corn (Lines G f n):=
    let A:= arm G f n
    A.symm.toContinuousLinearMap ∘L (ContinuousLinearMap.pi fun x:Body n f=> (G.adjoint (k x.1)).toContinuousLinearMap ∘L ContinuousLinearMap.proj x) ∘L A.toContinuousLinearMap
def mailBox(n:ℕ)(k:Coats G f) := billsM (pocket _) (pocket _) (quiltM n k)
lemma armq (x:Body n f)(k:Coats G f)(i:Corn (Lines G f n)) :arm G f n (quiltM n k i) x = G.adjoint (k x.1) (arm G f n i x):=by simp [quiltM]
lemma quiltB (k: Coats G f): mailBox 1 k=trench k:=by
    apply testers; intro x y; rw [mailBox,bill_pay,Stationary.trench,bill_pay]; apply congr_arg; ext1 ⟨i,a,b⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective a; change arm G f 1 (quiltM 1 k y) (i,coord a) b= _; rw [armq]; exact congr_arg (fun x:G.Color=>x b) (armor_at k y (i,a)).symm
lemma quiltG(k:Coats G f): mailBox 0 k=troop k:=by
    apply testers; intro x y; rw [mailBox,bill_pay,troop,bill_pay]; apply congr_arg; ext1 ⟨i,a,b⟩; rw[vac_only a]; change arm G f 0 (quiltM 0 k y) (i,vac) b= _; rw [armq]; exact congr_arg (fun x:G.Color=>x b) (armorG_at k y i).symm
lemma quilt_o (k:Coats G f): Military (mailBox n k):=by apply military_intro; intro x y; rw [mailBox,bill_pay,bill_pay,dotSite,dotSite]; simp_rw [armq]; refine sum_congr rfl (fun i _=>?_); exact (show G.Color→ₗᵢ[ℝ] G.Color from ⟨G.adjoint _, G.norm_adjoint _⟩).inner_map_map ..
lemma quilt_g : mailBox n (1:Coats G f)=1:=by apply testers; intro x y; rw [mailBox,bill_pay,one_mulVec]; apply congr_arg; apply (arm G f n).injective; ext1 i; rw [armq,Pi.one_apply,G.adjoint_one]

abbrev jerk (G:Gauge)(f:Side)(n:ℕ):= mailBox n ∘ switchSite (m:=f) (G:=G)
def tuneV (k:G.ColorIndex):G.Color:= WithLp.toLp 2 (Pi.single k 1)
lemma quips (p:BaseSites G f)(i j:Lines G f n): jerk G f n p i j=
    if i.1=j.1 ∧ i.2.1=j.2.1 then (G.adjoint (G.lieExp (gaugeColor p i.1)) (tuneV j.2.2)) i.2.2 else 0:=by
    rcases i with ⟨i,a,u⟩; rcases j with ⟨j,b,v⟩; let Z:Corn (Lines G f n):= (pocket _) (j,b,v); let A:=arm G f n Z (i,a)
    have he:A=(if i=j ∧ a=b then tuneV v else (0:G.Color)):=by
       by_cases he:i=j ∧ a=b
       · obtain ⟨rfl,rfl⟩:= he; rw[if_pos ⟨rfl,rfl⟩]; ext x; change Z (i,a,x) = _; by_cases h:x=v<;> simp [h,tuneV,Z]
       rw[if_neg he]; ext x; change Z (i,a,x)=0; simp[Z,Pi.single_apply]; tauto
    change (mailBox n (switchSite p)) _ _=_; rw [mailBox,bill_def,cash_pocket]; change arm G f n (quiltM n (switchSite p) Z) (i,a) u= _; rw[armq,switch_color,show arm _ _ _ _ _ = A from rfl,he]; split<;> first| rfl| (rw [map_zero];rfl)
lemma adj_ag (a b:G.ColorIndex): ContDiffAt ℝ ω (fun u=> (G.adjoint (G.lieExp u) (tuneV a)) b) 0:=by
    -- use CLast
    let A:=tuneV a; let L:=EuclideanSpace.proj (𝕜:=ℝ) b
    have ht: ContDiffAt ℝ ω (fun u=> G.adjoint (G.lieExp u) A) 0:= by
        let f:=fun u=> G.conjugate (G.lieExp u) (G.colorMat A)
        exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=f) _ (((catexp G).mul contDiffAt_const).mul ((show G.Mat≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (catexp G)))
    exact L.contDiff.contDiffAt.comp _ ht
lemma memo_mailB: Memo (jerk G f n) 0:=by
    intro i j; simp_rw [quips]; split
    · let L: BaseSites G f →L[ℝ] G.Color:=ContinuousLinearMap.proj (R:=ℝ) i.1 ∘L gaugeColor.toContinuousLinearMap; exact ContDiffAt.comp 0 (f:=L) ((map_zero L).symm ▸ adj_ag j.2.2 i.2.2) L.contDiff.contDiffAt
    exact contDiffAt_const
lemma pear_sign (u:Phase (Lines G f 0)): (seat (jerk G f n) u)ᵀ= -seat (jerk G f n) u:=by
    let A:=jerk G f n
    have h0: A 0=1:=by unfold A jerk; rw[Function.comp_apply,switch_zero,quilt_g]
    have he(p:BaseSites G f): seat A (axes p)=_:= seating A p
    apply Leads.buys (p:=fun u=> (seat A u)ᵀ) (q:=fun u=> -seat A u) _ (seat_e A|>.neg) _ u
    pick_goal 2
    · intro x
      rw[seating]; let T:=directionM A 0 x; have hx:Tᵀ= -T:=by
          have he:=memo_mailB (G:=G) (f:=f) (n:=n); have hy:∀ x, (A x)ᵀ*A x=1:=fun x=> (quilt_o (switchSite x)).right
          apply eq_neg_of_add_eq_zero_left
          have hm := direction_prod (Memo.spot he) he x
          change directionM (fun x=> (A x)ᵀ*A x) 0 x=directionM (fun x=> (A x)ᵀ) 0 x*A 0+(A 0)ᵀ*T at hm
          rw[funext hy,direction_zero,h0,transpose_one,Matrix.mul_one,Matrix.one_mul] at hm; exact hm.symm
      rw[show directionM A 0 x=T from rfl, show (approached T)ᵀ=approached Tᵀ from rfl,hx,prom_negation]
    intro p q; dsimp only; rw[seat_e A p q,transpose_add,transpose_smul]
-- frequency output. need const r adjustment all n
lemma beat_once {I: Type}[Fintype I][DecidableEq I](F:Corn I→ℝ)(p:I→ℂ): beat F 0 1 ![p]=∑ i,p i*( (fderiv ℝ F 0 (bolt i):ℝ):ℂ):=by
    have ht(x:Corn I): beat F 0 1 ![axes x]=↑(fderiv ℝ F 0 x):=by
       rw [show ![axes x]= axes ∘ (![x]:Fin 1→_) from funext (fun i=>by fin_cases i; rfl),beat_real,iteratedFDeriv_one_apply]; rfl
    apply Leads.buys (p:=fun p=> beat F 0 1 ![p]) (q:=fun p=>∑ i,p i* _) _ _ _ p
    · intro i j; let g:= beat F 0 1; have hx(p:Phase I): (![p]:Fin 1→_)= Function.update (fun _=>0) 0 p:=by ext1 i;fin_cases i;simp
      dsimp only; rw [hx (axes i+_),hx (axes i),hx (axes j)];exact Leads.pulse _ _ _ _ _
    · intro i j; simp [add_mul,Finset.mul_sum, sum_add_distrib, mul_assoc]
    intro x; rw [ht]; have hx:x= ∑ i,x i • bolt i:=by ext1 i; simp[Finset.sum_apply,bolt,Pi.single_apply,mul_ite]
    conv_lhs=> rw [hx,map_sum]; simp only[map_smul]
    push_cast; simp [axes,smul_eq_mul]
lemma shocks (u: G.ColorIndex)(L:Loc G k)(p q:Site f):
    (seat (jerk G f k) (relay p (vac,u))) *ᵥ relay q L=∑ a:G.ColorIndex,(↑( (G.ad (tuneV u) (tuneV L.2)) a):ℂ) • relay (p+q) (L.1,a):=by
    let V(p:G.Color)(u:G.ColorIndex)(x:G.ColorIndex):ℝ:= (G.adjoint (G.lieExp p) (tuneV u)) x
    have hp(w:G.Color)(u v:G.ColorIndex): fderiv ℝ (fun p=> V p u v) 0 w= G.ad w (tuneV u) v:=by
        let L:= EuclideanSpace.proj (𝕜:=ℝ) v
        exact (Push.side _ ((adj_ag u v).differentiableAt (by simp)) w).unique (L.hasFDerivAt.comp_hasDerivAt 0 (color_pitch w (tuneV u)))
    have he (x:Site f)(i j:Loc G k)(y:Site f): seat (jerk G f k) (relay p (vac,u)) (x,i) (y,j)= if x=y∧i.1=j.1 then cell p x* (↑(G.ad (tuneV u) (tuneV j.2) i.2):ℂ) else 0:=by
       unfold seat art; rw [Matrix.of_apply,beat_once]; simp_rw[quips]; split_ifs with hx
       · let Q:BaseSites G f→L[ℝ]G.Color:= ContinuousLinearMap.proj x ∘L gaugeColor.toContinuousLinearMap
         have hh:= (adj_ag j.2 i.2).differentiableAt (by simp)
         let F:=fun z=>V z j.2 i.2
         change (∑ i':Lines G f 0, relay p (vac,u) i'*↑(fderiv ℝ (F ∘ Q) 0 (bolt i'))) =_
         rw[fderiv_comp _ (by rw[map_zero];exact hh) Q.differentiableAt,map_zero,Q.fderiv, sum_eq_single (x,vac,u)]; swap
         · intro i' _ h; obtain ⟨y',w'⟩:=i'; by_cases he : w'=(vac,u)
           · subst w'; have ht : gaugeColor (bolt (y',vac,u)) x=(0:G.Color):=by
                 have ht:y'≠x:=fun e=> h (by rw[e])
                 ext q;change bolt (y',vac,u) (x,vac,q)=0; simp [bolt,Pi.single_apply,ht.symm]
             rw [show ( (fderiv ℝ F 0) ∘L Q) (bolt (y',vac,u))=(0:ℝ) from (by change _ at ht; change fderiv ℝ F 0 (gaugeColor _ x)=_; rw[ht,map_zero])]; simp
           simp [relay,tune,he]
         swap; · simp
         have hu:gaugeColor (bolt (x,vac,u)) x=tuneV u:=by ext i; change bolt (x,vac,u) (x,vac,i)=_; by_cases h:i=u<;> simp [h,tuneV,bolt]
         rw [show (_ ∘L Q) (bolt (x,vac,u))=G.ad (tuneV u) (tuneV j.2) i.2 from ?_]; · simp [relay,tune]
         change fderiv ℝ F 0 (gaugeColor _ x)=_; rw[hu]; exact hp ..
       simp
    ext1 ⟨x,i⟩; simp only [Matrix.mulVec,dotProduct]; rw [Fintype.sum_prod_type, sum_eq_single x, sum_eq_single L];
    · simp_rw [he,Finset.sum_apply]; unfold relay tune; by_cases hh:i.1=L.1
      · rw [sum_eq_single i.2]; simp only[hh, Pi.single_eq_same,Pi.smul_apply,smul_eq_mul,mul_cell]; simp [Pi.single_apply,Prod.ext_iff,hh]; ring
        · intro j _ h; simp [Pi.single_apply,Prod.ext_iff,h.symm]
        simp
      simp [hh,Pi.single_apply,Prod.ext_iff]
    · intro i _ h; simp[relay,tune,h]
    · simp
    · intro j _ h; refine sum_eq_zero fun k _=>?_ ; rw[he,if_neg]; simp
      exact fun e=>h e.1.symm
    simp
end YM.Trace.Lamp
