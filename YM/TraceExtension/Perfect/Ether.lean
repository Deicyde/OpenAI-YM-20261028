import YM.TraceExtension.Perfect.Spurs
import YM.Planned.PRIMARY_INTEGRAL_295.Streets

/-!
# Pin Venus on row approximants
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {L : Side}
namespace RowGrade
def rich: RowGrade→ E4→ℝ
| unit,_=>1
| foot i,x=> x i
| paw i j,x=>(x i+x j)^2
| watch,_=>1
lemma riches (v:RowGrade)(x:Cover): v.rich (Place.seat x)=v.price x:=by cases v <;> rfl
lemma bounded (v:RowGrade)(x:Cover): ‖v.price x‖≤4* Carrier.liftCost 2 x:=by
 have hh(a): |(x a:ℝ)|≤size x:=calc
     _= ‖Place.seat x a‖:=rfl
     _ ≤ _:= (PiLp.norm_apply_le ..).trans (Carrier.shade_seat x)
 rw [Carrier.liftCost]; have ht:0≤(size x:ℝ):=Nat.cast_nonneg _
 cases v with
 | unit | watch=>simp [price]; nlinarith
 | foot a => exact (hh a).trans (by nlinarith)
 | paw i j=> unfold price; rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]; refine (pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le ..).trans (add_le_add (hh i) (hh j))) _).trans ?_; nlinarith
lemma dolls {n:Side}(v:RowGrade)(x:Cover): ‖v.price (lift (wrap n x))‖≤ 4*Carrier.liftCost 2 x:=by
    refine (bounded ..).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num)); unfold Carrier.liftCost; gcongr; unfold size; exact Finset.sum_le_sum fun i _=> Next.Free.below_wrap ..
end RowGrade

abbrev CrossA (L : Side):= Cross L (TypeFace 1) (TypeFace 1)
structure Ether (A : CrossA L):Prop where
    base i j : ∑' z, (A ((0:Site L),i) j z) = if i=j then ((L.val:ℝ))⁻¹ else 0
    cell x i j (v:RowGrade) :
       ∑' z, A (wrap L x,i) j z * v.price (Carrier.cellar L x+z) = ∑' z, A (0,i) j z * v.rich (((L.val:ℝ))⁻¹ • Place.seat x+Place.seat z)
lemma Ether.witty {j t:ℕ}(P : Flight j t)(k : ℝ)(hk:0 < k)(ht:4 ≤ t): Ether (Carrier.linesOf P k):=by
 let v := Carrier.linesOf P k
 refine ⟨fun i a=> ?_,fun x i a r=>?_⟩
 · obtain ⟨b,rfl⟩:= axisEquiv.surjective i; obtain ⟨i,rfl⟩:=axisEquiv.surjective a
   have he:= Carrier.origin_money k hk P ht (0:Cover) b i; simp only [Carrier.member,map_zero] at he; simp only [Equiv.apply_eq_iff_eq]; exact he
 have he := P.legal
 let S := ((P.L.val:ℝ))⁻¹ • Place.seat x
 obtain ⟨b,rfl⟩:=axisEquiv.surjective i;obtain ⟨c,rfl⟩:= axisEquiv.surjective a
 have h (w : Carrier.RouteProbe) (n:ℕ)(hn:n<j) : (∑' z, v (wrap P.L x,coord b) (coord c) z * (w (Place.seat (Carrier.cellar P.L x+z)))^n)=∑' z,v (0,coord b) (coord c) z*(w (S+Place.seat z))^n:=by
    have hu:= Carrier.pure_moment k hk P ht x b c w n hn; simpa only [mul_comm (_^_),Carrier.member,map_zero] using hu
 cases r with
 | unit | watch => have hp:=h 0 0 (by omega);simp only [pow_zero] at hp;exact hp
 | foot i=> have hp:=h (EuclideanSpace.proj (𝕜:=ℝ) i) 1 (by omega); simp only [pow_one] at hp; exact hp
 | paw i j=> exact h (EuclideanSpace.proj i+EuclideanSpace.proj j) 2 (by omega)

variable {c f:Side}{g:Ratio c f}
-- one site and polar (atomic row)
def probeF (v:RowGrade)(u:Site c)(b : TypeFace 1) : Body 1 c→ℝ := fun y=> if y.2=b then v.price (lift (y.1-u)) else 0

lemma bank_eval (A:CrossA g.count)(h:Whole A)(x:Cover)(v:RowGrade) (u:Site c)(b i:TypeFace 1):
   (installed g A*ᵥ probeF v u b) (g.embed u+wrap f x,i) =
     ∑' z, A (wrap g.count x,i) b z * v.price (lift (wrap c (Carrier.cellar g.count x+z))):=by
   obtain ⟨s,C,hs,h⟩:=h
   unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single b]; rotate_left
   · intro j _ he; apply Finset.sum_eq_zero; intro i _; simp [probeF,he]
   · simp
   simp_rw [Work.F08.installed_sift,Work.F08.moves_parent,Work.F08.moves_residue,g.embed_parent,g.residue_embed]
   have hp := (h (wrap g.count x,i) b).summable hs.le
   have hv: Work.F08.arrives (0:Site g.count) x = wrap g.count x:=by simp [Work.F08.arrives]
   rw [show (∑ i:Site c,_)=(∑ z:Site c,Work.F08.sift (A (wrap g.count x,i) b) c (u+wrap c (Carrier.cellar g.count x)) z * probeF v u b (z,b)) from ?_]
   · rw [Work.F08.sift_action ..]; rotate_left
     · exact hp
     apply tsum_congr; intro z; rw [map_add]; simp [probeF, lift,sub_eq_add_neg]; congr 3; abel_nf; simp
   simp_rw [hv]; rfl
end YM.Trace.Perfect
