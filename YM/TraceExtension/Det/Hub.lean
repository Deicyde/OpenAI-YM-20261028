import YM.TraceExtension.Det.Kismet
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Inverse
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k l m n r:ℕ}{α a b τ A C D:ℝ}
variable {o:Site f}{F H:WildM G f k m}
lemma slough  (x y:Site f)(h:a ≤ b): Decay b x y≤Decay a x y:= Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg h) (Nat.cast_nonneg _))
lemma Park.tiny (h:Park F a C r)(ht:τ≤a)(hr:0≤C)(hv:C≤A)(hh:n ≤ r) : Park F τ A n:=fun i j=> (h i j).tilt (mul_le_mul hv (slough i.1 j.1 ht) (decay_pos .. |>.le) (hr.trans hv)) ht hh
lemma PetW.tiny (h:PetW o F a C r)(ht:τ≤a)(hr:0≤C)(hv:C ≤ A)(hh:n ≤ r): PetW o F τ A n:= by
    intro i j
    exact (h i j).tilt (mul_le_mul (mul_le_mul hv (slough _ _ ht) (decay_pos .. |>.le) (hr.trans hv)) (slough _ _ ht) (decay_pos ..|>.le) (mul_nonneg (hr.trans hv) (decay_pos ..|>.le))) ht hh
lemma Park.plus (h:Park F a C n)(hp:Park H a D n): Park (F+H) a (C+D) n:=by intro i j;rw[add_mul];exact (h i j).plus (hp i j)
lemma Park.spins (h:Park F a C n)(hv:0 ≤ a)(hc:0 ≤ C): Park (fun z=>(F z)ᵀ) (a/(n+1:ℝ)) C n:=by
    intro i j
    let b:= a/(n+1:ℝ); have hp: b ≤ a:= div_le_self hv (by simp); have he:0≤b:=by unfold b; positivity
    change Pet Prod.fst i.1 (fun z=> F z j i) b _ n
    apply (((h j i).tilt le_rfl hp le_rfl).switch (mul_nonneg hc (decay_pos .. |>.le)) i.1 he).tilt _ le_rfl le_rfl
    unfold b; rw [mul_assoc,decay_comm a,drain_fee]
lemma PetW.spotV (h:PetW o F a C n): PetW o (fun z=>(F z)ᵀ) a C n:=by intro i j; rw[mul_right_comm];exact h j i
lemma PetW.inc (h:PetW o F a C n)(hp:PetW o H a D n): PetW o (F+H) a (C+D) n:=by intro i j;rw[add_mul,add_mul];exact (h i j).plus (hp i j)
lemma PetW.dec (h:PetW o F a C n)(hp:PetW o H a D n): PetW o (F-H) a (C+D) n:=by intro i j;rw[add_mul,add_mul];exact (h i j).minus (hp i j)
lemma PetW.which (h:PetW o F a C n)(b:ℝ): PetW o (b • F) a (|b| *C) n:=by
    intro i j; refine ⟨(h i j|>.1).const_smul b,fun k hk q=>?_⟩; unfold entry; rw[show (fun z:Link G f=> (b • F) z i j)=b • (fun z:Link G f=> F z i j) from rfl,iteratedFDeriv_const_smul_apply ((h i j|>.1).of_le le_top)]; simp only[_root_.smul_apply,norm_smul, mul_assoc]; have hx := mul_le_mul_of_nonneg_left (h i j|>.2 k hk q) (abs_nonneg b); simp only[mul_assoc] at hx;exact hx
lemma pay_hike (a:ℝ)(M:ℕ)(hx:n+2≤M)(j k:Site f)(h:0 ≤ a):  -- weights loss 1/(n+3) on PARK product
    Decay (a*M) j k * Real.exp (a*n*separation j k) ≤ Decay a j k * Decay a j k:=by
    unfold Decay; rw [← Real.exp_add, ← Real.exp_add,Real.exp_le_exp]
    have hv := mul_le_mul_of_nonneg_left (show (n:ℝ)+2 ≤ M by exact_mod_cast hx) h
    have hh:=mul_le_mul_of_nonneg_right hv (show (0:ℝ)≤ separation j k by positivity); linarith
lemma Park.cross_w {H:WildM G f m l}(hf:Park F a C n)(hh:Park H a D n)(hv:0<a)(hx:0≤C)(hd:0≤D):
    let u:=a/((n:ℝ)+2); Park (fun z=> F z * H z) u (((2:ℝ)^n*‖ContinuousLinearMap.mul ℝ ℝ‖* C*D)* ((Fintype.card (Loc G m):ℝ)*countCost u)) n:=by
    intro u i j; have hp(n'):0≤ Decay a i.1 (Leg (r:=m) (G:=G) n'):=decay_pos ..|>.le
    have hu:0<u:=by unfold u; positivity
    have hs: u≤a:= div_le_self hv.le (by linarith[Nat.cast_nonneg (α:=ℝ) n])
    have ht(q:Lines G f m): Decay a i.1 q.1 * Real.exp (u*n*separation i.1 q.1) ≤ Decay u i.1 q.1 * Decay u i.1 q.1:= by
        apply le_trans (le_of_eq ?_) (pay_hike u (n:=n) (n+2) le_rfl _ _ hu.le); rw [show u*(((n+2:ℕ)):ℝ)=a by unfold u; push_cast; field_simp]
    let P(q: Lines G f m):ℝ:= ((2:ℝ)^n*‖ContinuousLinearMap.mul ℝ ℝ‖*(C*Decay a i.1 q.1)* (D*Decay u q.1 j.1*Real.exp (u*n*separation i.1 q.1)))
    let G'(t: Lines G f m)(x:Link G f):= F x i t* H x t j
    refine Pet.weighted i.1 (F:=G') (s:=univ) (D:=P) (fun k _=> ?_) ?_
    · exact Pet.bins (ContinuousLinearMap.mul ℝ ℝ) ((hf i k).tilt le_rfl hs le_rfl) ((hh.tiny hs hd le_rfl le_rfl k j).switch (mul_nonneg hd (decay_pos ..|>.le)) i.1 hu.le) (mul_nonneg hx (hp _)) (mul_nonneg (mul_nonneg hd (decay_pos ..|>.le)) (Real.exp_pos _ |>.le))
    let v:ℝ:=2^n*‖ContinuousLinearMap.mul ℝ ℝ‖*C*D; have h0:0 ≤ v:=by unfold v; positivity
    apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((pay_gate G f|>.count (Prod.fst : Lines G f m → Site f) hu i.1)) h0) (decay_pos u i.1 j.1 |>.le))
    rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_le_sum fun q _=>?_ ; unfold P; calc
     _ = v * ((Decay a i.1 q.1 * Real.exp (u*n*separation i.1 q.1))*Decay u q.1 j.1) := by unfold v;ring
     _ ≤ v*((Decay u i.1 q.1 * Decay u i.1 q.1)*Decay u q.1 j.1):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (ht q) (decay_pos .. |>.le)) h0
     _ ≤ _:= by change _ ≤ v*Decay u i.1 q.1*Decay u i.1 j.1; rw [mul_assoc (Decay u i.1 q.1), mul_assoc v]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (decay_step hu.le ..) (decay_pos .. |>.le)) h0
-- root ops * global
lemma PetW.cross_r {H:WildM G f m l}(hf:PetW o F a C n)(hh:Park H a D n)(hv:0<a)(hx:0≤C)(hd:0≤D):
    let u:=a/((n:ℝ)+2); PetW o (fun z=> F z * H z) u (((2:ℝ)^n*‖ContinuousLinearMap.mul ℝ ℝ‖* C*D)* ((Fintype.card (Loc G m):ℝ)*countCost u)) n:=by
    intro u i j; let E:= Decay (n:=f) u; have hu:0<u:=by unfold u; positivity
    have hs: u≤a:= div_le_self hv.le (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    have ht(q:Lines G f m): Decay a o q.1 * Real.exp (u*n*separation o q.1) ≤ E o q.1 * E o q.1:= by
        apply le_trans (le_of_eq ?_) (pay_hike u (n:=n) (n+2) le_rfl _ _ hu.le); rw [show u*(((n+2:ℕ)):ℝ)=a by unfold u; push_cast; field_simp]
    let P(q: Lines G f m):ℝ:= ((2:ℝ)^n*‖ContinuousLinearMap.mul ℝ ℝ‖*(C*E o i.1*Decay a o q.1)* (D* E q.1 j.1 *Real.exp (u*n*separation o q.1)))
    let G'(t: Lines G f m)(x:Link G f):= F x i t* H x t j
    have he:∀ x y: Site f,0 ≤ E x y:= fun _ _=> (decay_pos ..).le
    refine Pet.weighted o (F:=G') (s:=univ) (D:=P) (fun k _=> ?_) ?_
    · exact Pet.bins (ContinuousLinearMap.mul ℝ ℝ) ((hf i k).tilt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (slough _ _ hs) hx) (decay_pos ..|>.le)) hs le_rfl) ((hh.tiny hs hd le_rfl le_rfl k j).switch (mul_nonneg hd (he _ _)) o hu.le) (mul_nonneg (mul_nonneg hx (he _ _)) (decay_pos .. |>.le)) (mul_nonneg (mul_nonneg hd (he _ _)) (Real.exp_pos _ |>.le))
    let v:ℝ:=2^n*‖ContinuousLinearMap.mul ℝ ℝ‖*C*D; have h0:0 ≤ v:=by unfold v; positivity
    apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((pay_gate G f|>.count (Prod.fst : Lines G f m → Site f) hu o)) h0) (he o i.1)) (he o j.1))
    rw [Finset.mul_sum, Finset.sum_mul,Finset.sum_mul]; refine Finset.sum_le_sum fun q _=>?_ ; unfold P; calc
     _ = v * E o i.1 * ((Decay a o q.1 * Real.exp (u*n*separation o q.1))*E q.1 j.1) := by unfold v;ring
     _ ≤ v * E o i.1 *((E o q.1 * E o q.1)* E q.1 j.1):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (ht _) (he _ _)) (mul_nonneg h0 (he _ _))
     _ ≤ _:= by change _ ≤ v*E _ _*E _ _*E _ _; rw [mul_right_comm v (E o q.1) (E o i.1),mul_assoc (E o q.1), mul_assoc (v*E o i.1)]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (decay_step hu.le ..) (he o q.1)) (mul_nonneg h0 (he _ _))
lemma PetW.cross_l {H:WildM G f m l}(hf:Park F a C n)(hh:PetW o H a D n)(hv:0<a)(hx:0≤C)(hd:0≤D):
    let v:=a/(n+1:ℝ); let u:=v/(n+2:ℝ); PetW o (fun z=> F z * H z) u (((2:ℝ)^n*‖ContinuousLinearMap.mul ℝ ℝ‖* D*C)* ((Fintype.card (Loc G m):ℝ)*countCost u)) n:=by
    intro v u; have hp:v≤a:= div_le_self hv.le (by simp); have he:=((hh.tiny hp hd le_rfl le_rfl).spotV.cross_r (hf.spins hv.le hx) (show 0<v by unfold v; positivity) hd hx).spotV
    simp only[← transpose_mul,transpose_transpose] at he; exact he
lemma PetW.grade {V:WildM G f k k}(h:PetW o V a C m)(ha:0 < a)(hp:0≤C): Pet Prod.fst o (fun z=>(V z).trace) a (C*(Fintype.card (Loc G k))*countCost a) m:=by
    have ht(i): Pet Prod.fst o (fun z=> V z i i) a (C*Decay a o i.1) m:= (h i i).tilt (mul_le_of_le_one_right (mul_nonneg hp (decay_pos ..).le) (decay_le ha.le ..)) le_rfl le_rfl
    apply Pet.weighted (F:=fun i z=> V z i i) (s:=univ) (D:=fun i=> C*Decay a o i.1) o (fun i _=>ht i); rw [← mul_sum,mul_assoc]; exact mul_le_mul_of_nonneg_left ((pay_gate G f).count _ ha o) hp
open Next.SectorChange
lemma Park.fume (h:Park F a C n)(ha:0<a)(hc:0 ≤ C) : Schur.Pours (F 0) Prod.fst Prod.fst (a/2) ((max ((Fintype.card (Loc G k):ℝ)*countCost (a/2)) ((Fintype.card (Loc G m):ℝ)* countCost (a/2))) * C):=by
    apply Schur.pure ha hc (fun i j=> ?_) (fun i => (pay_gate _ f).count _ (half_pos ha) i) (fun i => (pay_gate _ f).count _ (half_pos ha) i)
    have hx:= (h i j|>.2) 0 (Nat.zero_le n) Fin.elim0; simp [entry,spanSites, Decay,iteratedFDeriv_zero_apply] at hx
    unfold Wisps.rate; rw[mul_comm,← le_div_iff₀ (Real.exp_pos _),div_eq_mul_inv]; rw[← Real.exp_neg];exact hx
lemma Park.hit (h:Park F a C (n+1))(ha:0<a)(hc:0 ≤ C)(i:Lines G f 1):
    let b:= a/(n+1:ℝ)/(2:ℝ)
    PetW i.1 (fun z=>directionM F z (bolt i)) b C n:=by
    intro b j k
    let u:=a/(n+1:ℝ); have hu: 0 ≤ u:=by unfold u; positivity
    have hp : u≤a:= div_le_self ha.le (by simp); have ht: b≤u:= div_le_self hu (by linarith)
    have hx:= ((h j k).halp i).tilt le_rfl hp le_rfl
    apply ((hx.switch ?_ i.1 hu).tilt ?_ ht le_rfl)
    · exact mul_nonneg (mul_nonneg hc (decay_pos ..|>.le)) (decay_pos ..|>.le)
    rw [decay_comm a j.1 i.1,mul_assoc (C*_)]
    rw [show Decay a i.1 j.1 * Real.exp (u*n*separation i.1 j.1)=_ from drain_fee a i.1 j.1 n]
    have hb: 0 ≤ b:= by unfold b; positivity
    have hh : Decay u i.1 j.1=Decay b i.1 j.1*Decay b i.1 j.1:=by unfold Decay b u; rw[← Real.exp_add]; congr 1; ring
    change C*Decay a j.1 k.1 * Decay u i.1 j.1 ≤ _
    rw[hh,mul_right_comm]; calc
     _ = (C*Decay b i.1 j.1)*(Decay b i.1 j.1*Decay a j.1 k.1) :=by ring
     _ ≤ _ := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (slough _ _ (ht.trans hp)) (decay_pos b i.1 j.1|>.le)).trans (decay_step hb i.1 j.1 k.1)) (mul_nonneg hc (decay_pos ..|>.le))
lemma hit_back {x y z: Site f}(hx:0≤a) (n:ℕ): let b:= a/((n:ℝ)+2); Decay a x z* Decay a x y*Real.exp (b*n*separation z x) ≤ Decay b z x*Decay b z y:=by
    intro b; have hb:0≤b:=by unfold b; positivity
    have ht : Decay a x z*Real.exp (b*n*separation z x) ≤ Decay b z x*Decay b z x:=by
        rw [decay_comm a]; apply le_trans (le_of_eq ?_) (pay_hike b (M:=n+2) le_rfl z x hb); rw [show b*(((n+2:ℕ)):ℝ)=a by unfold b; push_cast; field_simp]
    rw [mul_right_comm]; apply (mul_le_mul ht (slough x y (show b≤a from div_le_self hx (by linarith [Nat.cast_nonneg (α:=ℝ) n]))) (decay_pos ..|>.le) (mul_nonneg (decay_pos ..|>.le) (decay_pos ..|>.le))).trans; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (decay_step hb ..) (decay_pos ..|>.le)
lemma Park.lit (h:Park F (a/(n+2:ℝ)) C 0)(hp:∀ i:Lines G f 1, PetW i.1 (fun z=> directionM F z (bolt i)) a C n)(hc:0≤C)(ha:0<a): Park F (a/(n+2:ℝ)) C (n+1):=by
    intro i j; refine ⟨(h i j).1,fun k hk q=>?_⟩
    cases k with
    | zero=> exact (h i j).2 _ le_rfl _
    | succ k=>
       let v:= q (Fin.last k); let b:= a/(n+2:ℝ)
       rw [show spanSites Prod.fst i.1 q=spanSites Prod.fst i.1 (Fin.init q) + separation i.1 v.1 from by unfold spanSites; rw[Fin.sum_univ_castSucc];rfl]
       have ht : entry (fun z=> F z i j) 0 q=entry (fun z=> directionM F z (bolt v) i j) 0 (Fin.init q):= Eq.trans (congr_arg (fun q=> entry (fun z=> F z i j) 0 q) (Fin.snoc_init_self q).symm) (entry_d (h i j).1 _ v)
       rw [ht,Nat.cast_add]; let X:= directionM F
       have hv:= hp v i j; have he: b≤a:= div_le_self ha.le (by linarith[Nat.cast_nonneg (α:=ℝ) n]); apply le_trans (((hv.tilt le_rfl he le_rfl).switch (mul_nonneg (mul_nonneg hc (decay_pos .. |>.le)) (decay_pos .. |>.le)) i.1 (show 0≤b by unfold b; positivity)).2 k (by omega) (Fin.init q))
       have hx:= hit_back (x:=v.1) (y:=j.1) (z:=i.1) ha.le n; let W:= spanSites Prod.fst i.1 (Fin.init q)
       change C*Decay a v.1 i.1*Decay a v.1 j.1* Real.exp (b*n*separation i.1 v.1)*Real.exp (-b*W) ≤ _
       rw [mul_add (-(a/_)), Real.exp_add]; simp only[← mul_assoc]; rw [mul_right_comm (C*Decay b i.1 j.1) _ _]
       apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _|>.le)
       have hh:= mul_le_mul_of_nonneg_left hx hc; change C*(Decay a v.1 i.1*Decay a v.1 j.1*_ )≤ C*(Decay b i.1 v.1*Decay b i.1 j.1) at hh
       simp only [mul_comm (Decay b i.1 v.1) (Decay b i.1 j.1), ← mul_assoc] at hh; exact hh
lemma Park.inverse_house (G:Gauge)(k:ℕ)(ha:0<a)(hC:0≤C)(hp:0<τ):∃ v D:ℝ,0<v∧0≤D∧∀ (n':Side)(F:WildM G n' k k), Park F a C n → IsUnit (F 0).det → Schur.Gapped (F 0) τ → (F 0).IsSymm → Park (fun x=> (F x)⁻¹) v D n:=by
    induction n with
    | zero=>
       let X:ℝ:= (Fintype.card (Loc G k):ℝ)*countCost (a/2); have hx:0≤X:=mul_nonneg (by positivity) (count_pos (half_pos ha)|>.le)
       obtain ⟨v,P,hv,hp',hP,H⟩:= Schur.inverse_tilt (σ:=a/2) hp (mul_nonneg hx hC) (half_pos ha)
       refine ⟨v,P,hv,hP.le, fun g F hf hh he hk i j=> ?_⟩
       have hy : Memo F 0:=fun i j=>(hf i j).1
       refine ⟨Memo.flip hy hh.ne_zero i j,fun n hn q=>?_⟩; obtain rfl:n=0:=by omega
       simp only[entry,iteratedFDeriv_zero_apply,spanSites,sum_of_isEmpty,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one]
       have h' := hf.fume ha hC; rw[max_self] at h'
       have ht := H Prod.fst (F 0) h' he hk j i
       unfold Wisps.rate at ht; unfold Decay; rw[neg_mul, Real.exp_neg,← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _),mul_comm]; exact ht
    | succ n ih=>
       obtain ⟨v,D,hv,hD,H⟩:=ih
       let b:=a/(n+1:ℝ)/2; let t:= min b v; let r:= t/(n+2:ℝ); let z:=r/(n+1:ℝ); let u:= z/(n+2:ℝ); let S:=(u/(n+2:ℝ))
       have ht':0<t:= lt_min (by unfold b; positivity) hv; have hr:0<r:=by unfold r; positivity
       have hz:0 < z:=by unfold z; positivity
       have hu: 0<u:= by unfold u; positivity
       have hV:t ≤ v:= min_le_right ..
       have h: r ≤ t:= div_le_self ht'.le (by linarith[Nat.cast_nonneg (α:=ℝ) n]); have hS:S≤u:=div_le_self hu.le (by linarith[Nat.cast_nonneg (α:=ℝ) n]); have he:z≤r:=div_le_self hr.le (by simp);have hu':u≤z:=div_le_self hz.le (by linarith [Nat.cast_nonneg (α:=ℝ) n])
       let P(p q x:ℝ):=(2:ℝ)^n*‖ContinuousLinearMap.mul ℝ ℝ‖*p*q*((Fintype.card (Loc G k):ℝ)*countCost x); let c:=P C D r; let w:=P c D u
       have hh(p q x:ℝ)(hp:0≤p)(hq:0≤q)(hx:0<x): 0≤ P p q x:=by unfold P; have ht:= count_pos hx; positivity
       have hc: 0≤c:=hh _ _ _ hC hD hr; have hw:0≤w:=hh _ _ _ hc hD hu
       refine ⟨S,D+w,by unfold S; positivity,by positivity,fun g F hf hj hk hy=> ?_⟩
       let G':= fun x=> (F x)⁻¹; have hF:= H g F (hf.tiny le_rfl hC le_rfl (by omega)) hj hk hy
       have hp:Park G' t D n:= hF.tiny hV hD le_rfl le_rfl
       refine Park.lit (hF.tiny (hS.trans (hu'.trans (he.trans (h.trans hV)))) hD (le_add_of_nonneg_right hw) (Nat.zero_le _)) (a:=u) (fun i=> ?_) (by positivity) hu
       let U(z):=directionM F z (bolt i); have hx:PetW i.1 U t C n:= (hf.hit ha hC i).tiny (min_le_left ..) hC le_rfl le_rfl
       have hh': PetW i.1 (fun z=> G' z*(U z*G' z)) u w n:= PetW.cross_l (hp.tiny h hD le_rfl le_rfl) (hx.cross_r hp ht' hC hD) hr hD hc
       have hf' : Memo F 0:= fun i j=>(hf i j).1
       have H : (fun z=> directionM G' z (bolt i))=ᶠ[𝓝 0] (-1:ℝ) • (fun z=> G' z*(U z*G' z)):=by
           filter_upwards [eventually_memo hf',hf'.det_val.continuousAt.eventually_ne hj.ne_zero] with z hv hz
           have he' := direction_inverse hv hz (bolt i); unfold G' U; simp only [Pi.smul_apply,neg_smul,one_smul]; rw [← mul_assoc]; exact he'
       have hh:=hh'.which (-1); simp only[abs_neg,abs_one,one_mul] at hh
       intro x y; apply ((hh.tiny le_rfl hw (le_add_of_nonneg_left hD) le_rfl x y).grows ?_); filter_upwards [H] with z hz; exact congr_arg (fun F:Funds (Lines G g k)=>F x y) hz.symm
end YM.Trace.Det
