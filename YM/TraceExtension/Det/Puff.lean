import YM.TraceExtension.Det.Hull
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k l m n r:ℕ}{α a b τ A C D:ℝ}
-- uniformity, index repeated
variable {W:Type*}{g:W→Side}
    {F H:∀ w,WildM G (g w) k m}{o:∀ w,Site (g w)}
structure Parked (F:∀ w,WildM G (g w) k m) (n:ℕ): Prop where
    top : ∃ a C,0 < a ∧ 0 ≤ C ∧ ∀ w:W, Park (F w) a C n
structure Pella (o:∀ w,Site (g w))(F:∀ w,WildM G (g w) k m)(n:ℕ):Prop where
    top : ∃ a C,0<a ∧ 0≤C ∧ ∀ w:W, PetW (o w) (F w) a C n
lemma Parked.spins (h:Parked F n): Parked (fun w z=> (F w z)ᵀ) n:=by
    obtain ⟨a,C,ha,hC,H⟩:=h.top
    exact ⟨_,_,show 0<a/(n+1:ℝ) by positivity,hC,fun i=> Park.spins (H i) ha.le hC⟩
lemma Parked.plus (h:Parked F n)(hp:Parked H n): Parked (F+H) n:=by
    obtain ⟨a,C,ha,hC,f⟩:=h.top; obtain ⟨b,D,hb,hD,g⟩:=hp.top; exact ⟨_,_,lt_min ha hb,add_nonneg hC hD,fun w=> ((f w).tiny (min_le_left ..) hC le_rfl le_rfl).plus ((g w).tiny (min_le_right ..) hD le_rfl le_rfl)⟩
lemma Pella.up (h:Pella o F n)(hp:Pella o H n): Pella o (F+H) n:=by
    obtain ⟨a,C,ha,hC,f⟩:=h.top;obtain ⟨b,D,hb,hD,g⟩:=hp.top; exact ⟨_,_,lt_min ha hb,add_nonneg hC hD, fun w=> ((f w).tiny (min_le_left ..) hC le_rfl le_rfl).inc ((g w).tiny (min_le_right ..) hD le_rfl le_rfl)⟩
lemma Pella.down (h:Pella o F n)(hp:Pella o H n): Pella o (F-H) n:=by
    obtain ⟨a,C,ha,hC,f⟩:=h.top;obtain ⟨b,D,hb,hD,g⟩:=hp.top; exact ⟨_,_,lt_min ha hb,add_nonneg hC hD, fun w=> ((f w).tiny (min_le_left ..) hC le_rfl le_rfl).dec ((g w).tiny (min_le_right ..) hD le_rfl le_rfl)⟩
lemma Pella.cash (h:Pella o F n)(c:ℝ): Pella o (c • F) n:=by obtain ⟨a,C,ha,hC,f⟩:=h.top; exact ⟨_,_,ha,mul_nonneg (abs_nonneg c) hC, fun w=> (f w).which _⟩
lemma Pella.swap (h:Pella o F n): Pella o (fun w z=> (F w z)ᵀ) n:=by obtain ⟨a,C,ha,hC,f⟩:=h.top; exact ⟨_,_,ha,hC,fun w=> (f w).spotV⟩
lemma Pella.rightM {H:∀ w,WildM G (g w) m l}(h:Pella o F n)(hp:Parked H n): Pella o (fun w z=> F w z * H w z) n:=by
    obtain ⟨a,C,ha,hC,f⟩:=h.top;obtain ⟨b,D,hb,hD,p⟩:=hp.top; let v:=min a b/(n+2:ℝ); have hz:0<v:=div_pos (lt_min ha hb) (by positivity)
    have ht:= count_pos hz; refine ⟨_,_,hz,?_,fun i=>PetW.cross_r ((f i).tiny (min_le_left ..) hC le_rfl le_rfl) ((p i).tiny (min_le_right ..) hD le_rfl le_rfl) (lt_min ha hb) hC hD⟩; unfold v at ht; positivity
lemma Pella.leftM {H:∀ w,WildM G (g w) l k}(h:Pella o F n)(hp:Parked H n): Pella o (fun w z=> H w z * F w z) n:=by
    have he:= (h.swap.rightM hp.spins).swap; simp only [transpose_mul,transpose_transpose] at he; exact he
lemma Pella.shee {F:∀ w,WildM G (g w) k k}(h:Pella o F n): Pella o (fun w z=>sy (F w z)) n:= ((h.up h.swap).cash (1/2))
lemma Parked.tada (h:Parked F n)(hp:l≤ n): Parked F l:=by obtain ⟨a,C,ha,hC,f⟩:=h.top; exact ⟨_,_,ha,hC,fun w=>(f w).tiny le_rfl hC le_rfl hp⟩
lemma Pella.tada (h:Pella o F n)(hp:l ≤ n): Pella o F l:=by obtain ⟨a,C,ha,hC,f⟩:=h.top; exact ⟨_,_,ha,hC,fun w=>(f w).tiny le_rfl hC le_rfl hp⟩
structure Pico (o:∀ w,Site (g w))(F:∀ w,Link G (g w)→ ℝ)(n:ℕ):Prop where
    top: ∃ a C,0<a ∧ 0≤ C ∧ ∀ w:W, Pet Prod.fst (o w) (F w) a C n
lemma Pella.trace {H:∀ w,WildM G (g w) k k}(h:Pella o H n): Pico o (fun w z=> (H w z).trace) n:=by
    obtain ⟨a,C,ha,hC,f⟩:=h.top; exact ⟨_,_,ha,mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (count_pos ha).le,fun w=>(f w).grade ha hC⟩
lemma Pico.minus {F H:∀ w,Link G (g w)→ ℝ}(h:Pico o F n)(hp:Pico o H n): Pico o (F-H) n:=by obtain ⟨a,C,ha,hC,f⟩:=h.top;obtain ⟨b,D,hb,hD,p⟩:=hp.top; exact ⟨_,_,lt_min ha hb,add_nonneg hC hD,fun i=> ((f i).tilt le_rfl (min_le_left ..) le_rfl).minus ((p i).tilt le_rfl (min_le_right ..) le_rfl)⟩
lemma Pico.multi {F:∀ w,Link G (g w)→ ℝ}(h:Pico o F n)(c:ℝ): Pico o (c • F) n:=by obtain ⟨a,C,ha,hC,f⟩:=h.top; exact ⟨_,_,ha,mul_nonneg (show 0≤ ‖(c • (ContinuousLinearMap.id ℝ ℝ))‖ from norm_nonneg _) hC,fun w=>Pet.monoL (f w) (c • ContinuousLinearMap.id ℝ ℝ)⟩
lemma Pico.put {L:Type*}{F:∀ w,Link G (g w)→ ℝ}(h:Pico o F n)(e:L→W) : Pico (fun i:L=>o (e i)) (fun i=>F (e i)) n:=by obtain ⟨a,C,ha,hC,f⟩:=h.top; exact ⟨_,_,ha,hC,fun i=>f _⟩
lemma Parked.put {L:Type*}(h:Parked F n)(e:L→W): Parked (fun i:L=>F (e i)) n:=by obtain ⟨a,C,ha,hC,f⟩:=h.top; exact ⟨_,_,ha,hC,fun i=>f _⟩
lemma Pella.put {L:Type*}(h:Pella o F n)(e:L→W): Pella (fun i:L=>o (e i)) (fun i=>F (e i)) n:=by obtain ⟨a,C,ha,hC,f⟩:=h.top;exact ⟨_,_,ha,hC,fun i=> f _⟩
structure CodeM (o:∀ w,Site (g w))(X:(w:W)→ Link G (g w)→ Link G (g w))(m:ℕ):Prop where
    top:∃ a C,0<a∧0≤C∧∀ w i,Pet Prod.fst (o w) (fun z=> X w z i) a (C*Decay a (o w) i.1) m

lemma CodeM.sub {X Y:(w:W)→ Link G (g w)→ Link G (g w)}(h:CodeM o X n)(hp:CodeM o Y n): CodeM o (X-Y) n:=by
    obtain ⟨a,C,ha,hC,f⟩:=h.top;obtain ⟨b,D,hb,hD,p⟩:=hp.top; let v:=min a b; refine ⟨v,C+D,lt_min ha hb,add_nonneg hC hD,fun w i=>?_⟩
    rw[add_mul]; exact ((f w i).tilt (mul_le_mul_of_nonneg_left (slough _ _ (min_le_left ..)) hC) (min_le_left ..) le_rfl).minus ((p w i).tilt (mul_le_mul_of_nonneg_left (slough _ _ (min_le_right ..)) hD) (min_le_right ..) le_rfl)
lemma CodeM.eval {X:(w:W)→ Link G (g w)→ Link G (g w)}(h:CodeM o X n)(c:ℝ): CodeM o (c • X) n:=by
    obtain ⟨a,C,ha,hC,f⟩:=h.top; let L : ℝ→L[ℝ]ℝ:=c • ContinuousLinearMap.id _ _
    refine ⟨_,_,ha,mul_nonneg (norm_nonneg L) hC,fun w i=>?_⟩; rw[mul_assoc];exact (f w i).monoL L

lemma juke_budget {H:∀ w,WildM G (g w) 0 1}(h:Pella o H n): CodeM o (fun w z=> trapw (H w z) (jeps (input G (g w) z))) n:=by
    obtain ⟨a,C,ha,hC,f⟩:=h.top
    obtain ⟨D,hD,h⟩:=jolt_p G n a ha.le; let b:=a/(n+2:ℝ); have hb:0 < b:=by unfold b;positivity
    have ht:b≤a:=div_le_self ha.le (by linarith[Nat.cast_nonneg (α:=ℝ) n]); let B:=2^(n:ℕ)*‖ContinuousLinearMap.mul ℝ ℝ‖* C*D; have hB:0 ≤ B:=by unfold B; positivity
    let F(i:ℕ):ℝ:= Fintype.card (Loc G i)*countCost b; have hF(i):0 ≤ F i:=mul_nonneg (Nat.cast_nonneg _) (count_pos hb|>.le)
    refine ⟨_,B*(F 0)*(F 1),hb,mul_nonneg (mul_nonneg hB (hF _)) (hF _),fun w k=>?_⟩
    let x:=o w
    let Z(i j)(z):= H w z j i * jeps (input G (g w) z) i j k
    have he(i:Lines G (g w) 1)(j:Lines G (g w) 0): Pet Prod.fst x (Z i j) b ((B*Decay b x k.1)*Decay b x i.1*Decay b x j.1) n:=by
       have hd:= h (g w) i j k
       have hC': 0≤ C * Decay a x j.1*Decay a x i.1:=mul_nonneg (mul_nonneg hC (decay_pos .. |>.le)) (decay_pos .. |>.le)
       have hD':0≤ D*Decay a k.1 j.1*Decay a k.1 i.1:=mul_nonneg (mul_nonneg hD (decay_pos ..|>.le)) (decay_pos ..|>.le)
       apply Pet.tilt (Pet.bins (ContinuousLinearMap.mul ℝ ℝ) ((f w j i).tilt le_rfl ht le_rfl) ((hd.tilt le_rfl ht le_rfl).switch hD' x hb.le) hC' (mul_nonneg hD' (Real.exp_pos _|>.le))) _ le_rfl le_rfl
       have hp: Decay a x i.1 * Decay a k.1 i.1 ≤ Decay b x i.1* Decay ((n+1:ℝ)*b) x k.1:=by -- pay both anchor shift and x i
          let p:ℝ:=(n+1:ℝ)*b; have ht : a=b+p:=by unfold p b; field_simp; ring
          have hz: Decay a x i.1=Decay b x i.1 *Decay p x i.1:=by unfold Decay; rw [ht];
                                                                    rw[← Real.exp_add]; congr 1; ring
          have hv:= slough i.1 k.1 (show p≤a by linarith); rw [decay_comm a k.1 i.1,hz,mul_assoc]; exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hv (decay_pos ..|>.le)).trans (decay_step (show 0≤p by unfold p; positivity) _ _ _)) (decay_pos ..|>.le)
       have hv : (Decay a x i.1*Decay a k.1 i.1)*Real.exp (b*n*separation x k.1) ≤ Decay b x k.1*Decay b x i.1:=by
           refine (mul_le_mul_of_nonneg_right hp (Real.exp_pos _|>.le)).trans_eq ?_; rw[mul_assoc,mul_comm (Decay b x i.1)];congr 1; unfold Decay; rw[← Real.exp_add]; congr 1; ring
       have hs: Decay a x j.1 * Decay a k.1 j.1 ≤ Decay b x j.1:= (mul_le_of_le_one_right (decay_pos .. |>.le) (decay_le ha.le ..)).trans (slough _ _ ht)
       change _ ≤ B*Decay b x k.1*Decay b x i.1*Decay b x j.1
       calc
        _ = B*(((Decay a x i.1*Decay a k.1 i.1)*Real.exp (b*n*separation x k.1))*(Decay a x j.1*Decay a k.1 j.1)):=by unfold B x; ring
        _ ≤ _:= by rw[mul_assoc (B*_),(mul_assoc B _ _)]; exact mul_le_mul_of_nonneg_left ((mul_le_mul hv hs (mul_nonneg (decay_pos ..|>.le) (decay_pos .. |>.le)) (mul_nonneg (decay_pos ..|>.le) (decay_pos ..|>.le))).trans_eq (mul_assoc ..)) hB
    have hv(i:(Lines G (g w) 1)): Pet Prod.fst x (fun z=>∑ j,Z i j z) b ((B*Decay b x k.1)*Decay b x i.1*F 0) n:=by
       apply Pet.weighted x (fun j _=> he i j); rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((pay_gate G (g w)).count _ hb x) (mul_nonneg (mul_nonneg hB (decay_pos ..|>.le)) (decay_pos ..|>.le))
    have hx : Pet Prod.fst x (fun z=>∑ i,∑ j,Z i j z) b (B*F 0*F 1*Decay b x k.1) n:=by
       apply Pet.weighted x (fun i _=> hv i); rw [← Finset.sum_mul,← Finset.mul_sum]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show ∑ i:Lines G (g w) 1,Decay b x i.1≤F 1 from (pay_gate G (g w)).count _ hb x) (mul_nonneg hB (decay_pos ..|>.le))) (hF _)).trans_eq;ring
    exact hx.grows (Eventually.of_forall fun z=> by unfold trapw; dsimp only; simp only [Finset.sum_apply]; rfl)
end YM.Trace.Det
