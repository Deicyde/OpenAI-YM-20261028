import YM.TraceExtension.Lamp.Fiddle

/-! # small impulse of w insert -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
variable {W:Type*}{g:W→Side}{H K:WickL G}{T:Reed G}{L:Filter W}{Y:Gal G f}(d i b a:Axis)(u v:G.ColorIndex)
abbrev pier (A: Matrix (Lines G f k) (Lines G f k) ℝ)(p q:Site f)(i a:Loc G k):ℂ:= dotProduct (relay q i) (approached A *ᵥ relay p a)
lemma pier_sub (F H: Matrix (Lines G f k) (Lines G f k) ℝ)(p q:Site f)(i a:Loc G k) : pier (F-H) p q i a=pier F p q i a-pier H p q i a:=by
    unfold pier; rw [show approached (F-H)= approached F- approached H from ?_,sub_mulVec,dotProduct_sub]; ext; simp[approached]
lemma pier_add (F H:Matrix (Lines G f k) (Lines G f k) ℝ)(p q:Site f)(i a:Loc G k): pier (F+H) p q i a=pier F p q i a+pier H p q i a:=by unfold pier;rw[prom_addition,add_mulVec,dotProduct_add]
lemma pier_cash (F:Matrix (Lines G f k) (Lines G f k) ℝ)(p q:Site f)(i a: Loc G k)(t:ℝ): pier (t • F) p q i a=(t:ℂ)*pier F p q i a:=by unfold pier; rw[prom_tone,smul_mulVec,dotProduct_smul];rfl
lemma pier_sy (F:Matrix (Lines G f k) (Lines G f k) ℝ)(p q:Site f)(i a: Loc G k): pier (sy F) p q i a=(1/2:ℂ)*(pier F p q i a+pier F q p a i):=by
    rw [sy,pier_cash,pier_add]; push_cast; congr 2; unfold pier; rw[show approached Fᵀ=(approached F)ᵀ from rfl,dotProduct_mulVec,vecMul_transpose,dotProduct_comm]
lemma tote_sum (i:Loc G k)(M:Lines G f k→ ℂ)(p:Site f): dotProduct (relay p i) M=∑ x:Site f,cell p x*M (x,i):=by unfold relay tune dotProduct; rw[Fintype.sum_prod_type];simp [Pi.single_apply,mul_ite,ite_mul]
lemma tide_dot (q:Site f)(i j:Loc G 1)(p:Site f)(hp:Y∈rains G f): pier (tidal Y 1) p q i j=tann Y i j p q:=by obtain ⟨h,h'⟩:=hp; unfold pier;rw[tide_tilt h h',dotProduct_comm]
lemma pulse_sum (F:Site f→ℂ): ∑ x:Site f, (((stampQ 0 (x+step b)-stampQ 0 x):ℝ):ℂ)*F x=F (-step b)-F 0:=by
    have ht(x:Site f): 0=x+step b ↔ x= - step b:=⟨fun e=>eq_neg_of_add_eq_zero_left e.symm,fun e=> by rw [e,neg_add_cancel]⟩
    push_cast; simp [stampQ,sub_mul, Finset.sum_sub_distrib,ht,apply_ite Complex.ofReal,ite_mul]
lemma pitch_teat (i j:Loc G k)(p q:Site f): pier (teat G (stampQ 0) b k) p q i j= if i=j then cell (p+q) (-(step b))-1 else 0:=by
    unfold pier; rw[tote_sum]; let Z:= relay p j
    have ht(x:Site f): (approached (teat G (stampQ 0) b k)*ᵥ Z) (x,i) = (((stampQ 0 (x+step b)-stampQ 0 x):ℝ):ℂ)* Z (x,i):=by
       unfold teat approached; rw[show (Matrix.map _ _) = diagonal (fun j:Lines G f k=> (((stampQ 0 (j.1+step b)-stampQ 0 j.1):ℝ):ℂ)) from ?_, Matrix.mulVec_diagonal]
       ext i j; by_cases h:i=j<;> simp [diagonal,h]
    change (∑ x, cell q x*(approached _*ᵥ Z) (x,i))=_; simp_rw[ht]; unfold Z relay tune; split_ifs with h
    · subst j; simp only [Pi.single_eq_same, mul_one]; rw[show (∑ x:Site f,_)=(∑ x:Site f, (((stampQ 0 (x+step b)-stampQ 0 x):ℝ):ℂ)*cell (p+q) x) from ?_,pulse_sum b (fun x=>cell _ x)]; simp
      apply Finset.sum_congr rfl; intro i _; rw[mul_cell]; ring
    simp [h]
lemma pickX (V:Phase (Lines G f 1))(x: Site f)(q:G.ColorIndex): (approached (mine G (stampQ 0) b)*ᵥ V) (x,vac,q)= (↑(stampQ 0 x):ℂ)*V (x,coord b,q):=by
    apply Leads.buys (p:=fun P=> (approached _ *ᵥ P) (x,vac,q)) (q:=fun P=> (↑(stampQ (0:Site f) x):ℂ)*P (x,coord b,q)) ?_ ?_ ?_ V
    · intro u v; dsimp only; rw[mulVec_add,mulVec_smul];rfl
    · intro u v; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
    intro u; rw [prom_vec]; change ((gaugeColor ((mine G (stampQ 0) b)*ᵥ u) x q:ℝ):ℂ) = _; rw [mined]; exact Complex.ofReal_mul ..
lemma mailX (V:Phase (Lines G f 0))(x:Site f)(a:G.ColorIndex): (approached (mail (1:Config G f))*ᵥ V) (x,coord b,a)=V (x,vac,a)-V (x+step b,vac,a):=by
    apply Leads.buys (p:=fun P=>(approached (mail (1:Config G f))*ᵥ P) (x,coord b,a)) (q:=fun P=> P (x,vac,a)-P (x+step b,vac,a)) ?_ ?_ ?_ V
    · intro u v;dsimp only;rw[mulVec_add,mulVec_smul];rfl
    · intro u v; simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring
    intro u;rw[prom_vec]; change ((edgeColor (mail (1:Config G f) *ᵥ u) (x,b) a:ℝ):ℂ)=_;rw[mailed,cant_at,Pi.one_apply,G.adjoint_one];exact Complex.ofReal_sub ..
lemma dealX (V:Phase (Lines G f 1))(x:Site f)(a:G.ColorIndex):
    (approached (deal G (stampQ 0) b)*ᵥ V) (x,coord i,a)= (((stampQ 0 (x+step i)-stampQ 0 x):ℝ):ℂ)* V (x,coord b,a):=by
    apply Leads.buys (p:=fun P=> (approached (deal G (stampQ (0:Site f)) b)*ᵥ P) (x,coord i,a)) (q:=fun P=> _ * P (x,coord b,a)) ?_ ?_ ?_ V
    · intro u v; dsimp only; rw[mulVec_add,mulVec_smul];rfl
    · intro u v; simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
    intro u;rw[prom_vec]; change ((edgeColor (deal G (stampQ 0) b *ᵥ u) (x,i) a:ℝ):ℂ)=_; rw[deal_apply]; exact Complex.ofReal_mul ..
lemma pickPier (p q:Site f): pier (mail (1:Config G f)*mine G (stampQ (0:Site f)) b) p q (mood G i u) (mood G a v)= if b=a ∧ u=v then 1-cell q (-step i) else 0:=by
    unfold pier mood; rw[tote_sum,prom_mul,← mulVec_mulVec]; simp_rw [mailX,pickX]; unfold relay tune
    split_ifs with h; next =>
       simp only [show ((coord b,u): Loc G 1)= (coord a,v) from Prod.ext (congr_arg coord h.1) h.2, Pi.single_eq_same,mul_one]; simp [mul_sub,Finset.sum_sub_distrib,stampQ,apply_ite Complex.ofReal,mul_ite,ite_mul,show ∀ x:Site f,0=x+step i ↔ x= -step i from fun x=>⟨fun e=>eq_neg_of_add_eq_zero_left e.symm, fun e=>by rw [e,neg_add_cancel]⟩]; rw[← cell_add,neg_add_cancel,cell_origin]
    next =>
       simp only [Pi.single_apply, Prod.mk.injEq,coord_iff,h, ↓reduceIte,mul_zero,sub_zero,Finset.sum_const_zero]
lemma packPier (p q:Site f) : pier (mine G (stampQ (0:Site f)) b*mail (1:Config G f)) p q (vac,u) (vac,v)=if u=v then 1-cell p (step b) else 0:=by
    unfold pier;rw[tote_sum,prom_mul,← mulVec_mulVec]; simp_rw [pickX,mailX]; by_cases h:u=v<;>simp [stampQ,h,relay,tune,mul_ite,ite_mul,apply_ite Complex.ofReal]
lemma dealP (p q:Site f) : pier (deal G (stampQ 0) b) p q (mood G i u) (mood G a v)= if b=a∧u=v then cell (p+q) (-step i)-1 else 0:=by
    unfold pier mood;rw[tote_sum];simp_rw [dealX]; unfold relay tune; split_ifs with h; next=>
       have hz: ((coord b,u): Loc G 1)= (coord a,v):= Prod.ext (congr_arg coord h.1) h.2
       simp only [hz, Pi.single_eq_same,mul_one]
       rw [show (∑ x:Site f,_)=(∑ x:Site f, (((stampQ 0 (x+step i)-stampQ 0 x):ℝ):ℂ)*cell (p+q) x) from ?_,pulse_sum i (fun x=>cell _ x)]; simp
       apply Finset.sum_congr rfl; intro b _; rw [mul_cell]; ring
    next=> simp only[Pi.single_apply,Prod.mk.injEq,coord_iff,h,↓reduceIte,mul_zero,Finset.sum_const_zero]
end YM.Trace.Lamp
