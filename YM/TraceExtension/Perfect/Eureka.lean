import YM.TraceExtension.Perfect.Ether

/-! # Reproduction replaces aliases before reading polynomial probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
open RowGrade
variable {L:Side}{A:CrossA L}{s C:ℝ}
-- homogeneous contact read expanded in stalks. relative fine origin v (cover displacement o→embedding center). argument X at origin. coordinates telescope only once.
private def atL (L:Side)(p x : Cover): E4:= ((L.val:ℝ))⁻¹ • (Place.seat p)+ Place.seat x

-- row-grade representative Q below, coefficient pointwise polynomial in z
private def straws (L:Side)(g:RowGrade)(p y:Cover)(t: RowGrade):ℝ:=
    let l a:= (atL L p y) a
    let K:=(L.val:ℝ)⁻¹
    match g with
    | unit | watch=>0
    | foot i=>if t=unit then l i else 0
    | paw i j=> (if t=unit then (l i+l j)^2 else 0)+
         (if t=foot i then K*2*(l i+l j) else 0)+(if t=foot j then K*2*(l i+l j) else 0)
lemma grains_zero (g t:RowGrade)(x y:Cover)(ht:g.degree≤t.degree): straws L g x y t=0:=by
 cases g <;> simp_rw [straws]
 case foot i=> split <;> rename_i he; · subst t; norm_num [degree] at ht
               · rfl
 case paw i j=>
    split_ifs <;> first|(subst t; norm_num [degree] at ht)|simp

lemma basket (g:RowGrade)(hp:g≠watch)(z p y):
    g.rich (((L.val:ℝ))⁻¹ • Place.seat (p+z)+Place.seat y)= (L.val:ℝ)⁻¹^(g.degree-1)*g.price z + ∑ t:RowGrade, straws L g p y t*t.price z:=by
 have he (i:Axis): (((L.val:ℝ))⁻¹ • Place.seat (p+z)+Place.seat y) i=(L.val:ℝ)⁻¹*(z i:ℝ)+(atL L p y) i:=by simp [atL,Place.seat];ring
 cases g with
 | unit=> simp [price,degree,rich,straws]
 | foot i=> simp only [rich];rw [he];simp [degree,price,straws]
 | paw i j=> simp only [rich,he, straws]; simp_rw [add_mul, Finset.sum_add_distrib, ite_mul]; simp [price,degree]; ring
 | watch=> exact (hp rfl).elim

-- fixed-stage point tents summability. choose powers margin.
private lemma next_grow (L:Side)(p:Cover): ∃ C:ℝ, 0 ≤ C ∧ ∀ z i, |(atL L p z) i| ≤ C*(1+(size z:ℝ)):=by
 let A:= ((L.val:ℝ))⁻¹ • Place.seat p
 have ha := norm_nonneg A
 refine ⟨‖A‖+1,by positivity,fun z i=>?_⟩
 change ‖(A+Place.seat z) i‖≤ _
 refine ((PiLp.norm_apply_le _ i).trans ((norm_add_le ..).trans (add_le_add_right (Carrier.shade_seat ..) _))).trans ?_; nlinarith [mul_nonneg ha (Nat.cast_nonneg (α:=ℝ) (size z))]
private lemma sunny (L:Side)(g:RowGrade)(p:Cover)(t):∃ D:ℝ, 0 ≤ D∧ ∀ z, ‖straws L g p z t‖ ≤ D*Carrier.liftCost 2 z:=by
 obtain ⟨C,hC,h⟩:= next_grow L p
 let S:= L.val; let K:=((L.val:ℝ))⁻¹; have hK :0 ≤ K:=by unfold K; positivity
 let D:= 4*C*C+8*K*C+C; have hD : 0 ≤ D:= by unfold D; positivity
 refine ⟨D,hD,fun z=>?_⟩
 let F i:= (atL L p z) i; let d :ℝ:=1+size z; have hd:1 ≤ d :=by unfold d; simp
 have hz:0 ≤ d:=by linarith
 have hp : 0 ≤ D*Carrier.liftCost 2 z:=mul_nonneg hD (Carrier.liftCost_pos ..)
 have H : C*d≤ C*d^2 := mul_le_mul_of_nonneg_left ((by nlinarith only [hd]:d≤ d^2)) hC
 cases g with
 | watch | unit=> rw [show straws L _ p z t=0 from rfl,norm_zero]; exact hp
 | foot i=>
            unfold straws; dsimp only; split
            · refine le_trans (h z i) (H.trans ?_); apply mul_le_mul_of_nonneg_right _ (sq_nonneg d); unfold D; exact le_add_of_nonneg_left (by positivity)
            rw [norm_zero]; exact hp
 | paw i j=>
     let p :ℝ:= F i+F j; have hs :|p| ≤ 2*C*d:=(abs_add_le ..).trans ((add_le_add (h z i) (h z j)).trans_eq (by unfold d; ring))
     set b:= K*2*p
     have ht: ‖b‖≤ 4*K*C*d^2:=by rw [show b=K*2*p from rfl,norm_mul,Real.norm_of_nonneg (show 0≤K*2 by positivity)]; refine (mul_le_mul_of_nonneg_left hs (show 0 ≤ K*2 by positivity)).trans ?_; nlinarith only [mul_le_mul_of_nonneg_left H hK]
     change ‖(if t=unit then p^2 else 0)+(if t=foot i then b else 0)+(if t=foot j then b else 0)‖≤D*d^2
     apply (norm_add_le ..).trans; apply (add_le_add_left (norm_add_le ..) _).trans
     have h (t : Prop)[Decidable t]: ‖if t then b else 0‖≤4*K*C*d^2:=by split; exact ht; rw [norm_zero]; exact (norm_nonneg _).trans ht
     refine (add_le_add (add_le_add (b:=4*C*C*d^2) ?_ (h _)) (h _)).trans ?_
     · split; rotate_left; · rw [norm_zero]; positivity
       rw [Real.norm_of_nonneg (sq_nonneg _),← sq_abs]; apply (pow_le_pow_left₀ (abs_nonneg _) hs 2).trans_eq; ring
     unfold D; nlinarith only [mul_nonneg hC (sq_nonneg d)]

def ivory (v:RowGrade)(x:Cover)(A:CrossA L)(i j:TypeFace 1)(t:RowGrade):=∑' z,A (0,i) j z* straws L v x z t
lemma ivory_zero (v t:RowGrade)(h:v.degree≤t.degree)(A:CrossA L)(x i j): ivory v x A i j t=0:=by simp [ivory,grains_zero v t _ _ h]
lemma midfield (L:Side)(v:RowGrade)(x:Cover)(i j:TypeFace 1)(t:RowGrade){η C:ℝ}(h:0<η)(hc:0≤C): ∃ D:ℝ,0 ≤ D∧∀ A:CrossA L,A.strip η C→ (HasSum (fun z=> A (0,i) j z* straws L v x z t) (ivory v x A i j t) ∧ |ivory v x A i j t| ≤ D):=by
 obtain ⟨M,y,H⟩:= sunny L v x t; let V:= Carrier.widthCost η 2; have hp :0≤ V:= zero_le_one.trans (Carrier.widthCost_ge h _)
 refine ⟨M*(V*C),by positivity,fun A hx=>?_⟩
 have ht:= Carrier.width_income h (hx (0,i) j) 2
 let f z:= A (0,i) j z* straws L v x z t; have hv z : ‖f z‖ ≤ M*(‖A (0,i) j z‖ * Carrier.liftCost 2 z) :=by unfold f; rw [norm_mul,mul_left_comm M]; exact mul_le_mul_of_nonneg_left (H z) (norm_nonneg _)
 have he : Summable fun z=> ‖f z‖:= (ht.2.1.mul_left M).of_nonneg_of_le (fun z=> norm_nonneg _) hv
 refine ⟨he.of_norm.hasSum, (norm_tsum_le_tsum_norm he).trans ((he.tsum_le_tsum hv (ht.2.1.mul_left M)).trans ?_)⟩
 rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left ht.2.2 y
lemma wax {A:CrossA L}{η C:ℝ}(hA: Ether A)(h:0<η)(hc:0≤C) (hp:A.strip η C) (v:RowGrade)(hz:v≠watch)(x p:Cover)(i j:TypeFace 1) :
   ∑' z,A (wrap L (x+p),i) j z * v.price (Carrier.cellar L (x+p)+z) =
     (if i=j then (L.val:ℝ)⁻¹^v.degree*v.price x else 0)+ ∑ t,ivory v p A i j t*t.price x:=by
 rw [hA.cell,show x+p=p+x by abel]; simp_rw [basket v hz,_root_.mul_add,Finset.mul_sum]
 have he(t):= midfield L v p i j t h hc
 choose M m H using he
 rw [Summable.tsum_add, Summable.tsum_finsetSum]; rotate_left
 · intro t h; simp_rw [← mul_assoc (A (0,i) j _)]; exact ((H t A hp).1.summable).mul_right _
 · exact ((hp (0,i) j).summable h.le).mul_right _
 · apply summable_sum; intro t h; simp_rw [← mul_assoc (A (0,i) j _)]; exact ((H t A hp).1.summable).mul_right _
 simp_rw [← mul_assoc,tsum_mul_right,hA.base,ivory]; split; next h=> cases v <;> simp [degree] <;> ring_nf <;> simp
 simp
end YM.Trace.Perfect
