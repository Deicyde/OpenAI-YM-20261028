import YM.RG08.Invert.Home
import YM.Planned.PRIMARY_INTEGRAL_295.Streets
/-!
 # Exact inversion on periods in stencil coordinates.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Invert
open Function Filter Lattice Wilson Exterior Precision Laurent Next.Free Next.Free.Flight RG RG.Supply Bloch Input Finset Matrix
open Planned.PrimaryIntegral295 Carrier
open scoped BigOperators Topology Real Classical Matrix
variable {G:Gauge}{i j k t r:ℕ}{L c f:Side}
-- T version on all two-form. Psi too using inherent series
private lemma slug_mask (p:Momentum)(a:ℕ)(v:Axis→ℂ): shineF p a * mask a v=mask a v*shineF p a := by unfold shineF; rw [mask_mul,mask_mul]; exact congr_arg (mask a) (funext fun _=>mul_comm ..)
lemma fountain (P:Flight i j)(k:ℝ)(h:0<k)(p:Momentum)(he:p ∈baseCube)(l:Site P.L): shineF (aliasAt p l) 2*alloy k P (-p) (-l)=alloy k P p l*shineF p 2:=by
   let q:=aliasAt p l; have hh:shineF p 2*pulse k P.land p=pulse k P.land p*shineF p 2:= by unfold pulse; rw [Matrix.smul_mul,Matrix.mul_smul,slug_mask]
   have ht: shineF q 2*vault k P.wing q=vault k P.wing q *shineF q 2:= by unfold vault; rw [Matrix.smul_mul,Matrix.mul_smul,slug_mask]
   have hu:= base_subset_realCube zone_pos he
   have hX:= prospect P k p h he l|>.2
   unfold alloy agile; rw [alias_reverse p P.odd,(heart_even _ h P.land hu).1,(heart_even _ h P.wing (alias_in_real zone_pos hu l P.odd)).2]
   change shineF q 2*(vault k P.wing q*_*_)= _
   rw [← Matrix.mul_assoc,← Matrix.mul_assoc,ht, Matrix.mul_assoc (vault k P.wing q) (shineF q 2),show shineF q 2*_= _ from hX]
   simp only [Matrix.mul_assoc, hh]; rfl
lemma stroll (P:Flight i j)(k:ℝ)(h:0<k)(hk:4≤j)(x y:Cover)(a b:TypeFace 2): localeV (P.psi k) x a b y=localeV (P.psi k) (pole a x) a b (pole b y):= coherent (status_quote k h P.legal hk) P _ (fun p hp l=>fountain P k h p hp l) x y a b
section finite
-- Finite row/cross intertwiners

def mate (L:Side)(r:ℕ)(x:Co L (TypeFace r)): Co L (TypeFace r):=(-x.1-wrap L (brim x.2), x.2)
lemma mate_back (L:Side)(r:ℕ) : Involutive (mate L r):= fun x=> by refine Prod.ext ?_ rfl; unfold mate; dsimp only; abel
def mates (L:Side)(r:ℕ): Equiv.Perm (Co L (TypeFace r)):= ⟨mate L r,mate L r,mate_back L r,mate_back L r⟩
lemma cover_mate (L:Side)(x:Cover)(a:TypeFace r): mates L r (wrap L x,a)=(wrap L (pole a x),a):= by
   change ((-wrap L x-_,_) : Co L _)=_; simp [pole]

def Twilight (A:Matrix (Body r f) (Body r c) ℝ):Prop:= ∀ a b,A a b=A (mate f r a) (mate c r b)
-- periodize exact
private lemma tunnel (g:Ratio c f)(W: Cross g.count (TypeFace r) (TypeFace k))(x y:Cover)(a:TypeFace r)(b:TypeFace k): installed g W (wrap f x,a) (wrap c y,b)=∑' i, if wrap c y= wrap c i then localeV W x a b i else 0:=by
   rw [installed, Matrix.submatrix_apply,Row.acts,Matrix.of_apply,split_co]; dsimp only; simp_rw [Streets.owner,Streets.residue]
   let z:=cellar g.count x
   rw [← (Equiv.addRight z).tsum_eq (fun i:Cover=>if (wrap c y)=wrap c i then localeV W x a b i else 0)]; apply tsum_congr; intro k
   rw [show Equiv.addRight z k=k+z from rfl,map_add, add_comm (wrap c k) (wrap c z)]; unfold localeV; rw [show k+z-cellar g.count x=k from add_sub_cancel_right ..]; rfl
lemma ToNight (g:Ratio c f){W:Cross g.count (TypeFace r) (TypeFace r)} (h:∀ x y a b, localeV W x a b y= localeV W (pole a x) a b (pole b y)): Twilight (installed g W):=by
   rintro ⟨x,a⟩ ⟨y,b⟩; obtain ⟨x,rfl⟩: ∃ z,wrap f z=x:=⟨lift x,wrap_lift _⟩; obtain ⟨y,rfl⟩: ∃ z,wrap c z=y:= ⟨lift y, wrap_lift _⟩
   change _=installed _ _ (mates f r (wrap f x,a)) (mates c r (wrap c y,b)); rw [cover_mate,cover_mate,tunnel,tunnel,← (twin b).tsum_eq (fun i:Cover=>if wrap c (pole b y) = wrap c i then localeV W (pole a x) a b i else 0)]; refine tsum_congr fun i=>?_ ; rw [tw_p,h x i a b]; have he : (wrap c (pole b y)=wrap c (pole b i)) ↔ (wrap c y=wrap c i):= by simp [pole]
   split_ifs with hx h' hh
   · rfl
   · exact False.elim (h' (he.mpr hx))
   · exact False.elim (hx (he.mp hh))
   rfl
lemma axial (P:Flight i j)(k:ℝ)(h:0<k)(hk:4≤j)(he:f.val=c.val*P.L.val): Twilight (installed (P.visitRatio he) (P.duo k).A0) ∧ Twilight (installed (P.visitRatio he) (P.duo k).T) ∧ Twilight (installed (P.visitRatio he) (P.psi k)):=
    ⟨ToNight _ (fun x y a b=> axisKeep P k h hk a b x y),ToNight _ (fun x y a b=> angleKeep P k h hk a b x y),ToNight _ (fun x y a b=> stroll P k h hk x y a b)⟩
-- diagonal metric
private lemma even_r (u:ℝ)(h:0<u)(hj:4≤j) (v:Train j) (A: Row (TypeFace 2) (TypeFace 2)) (F: Momentum → Matrix (TypeFace 2) (TypeFace 2) ℂ)(hx: Corresponds A F)(hP:∀ p∈baseCube,F (-p)=F p)(hh:∀ p a b,a≠b → F p a b=0): Twilight (A.acts L):=by
   have h(a b : TypeFace 2) (he: a≠b):A a b=0:= by refine RRead_injective (hx.safe a b) (by simp) (fun p hp=>?_); rw [show RRead _ _= _ from congr_fun (congr_fun (hx.echo p hp) a) b, hh p a b he]; simp [RRead,Laurent.read]
   have he(a: TypeFace 2): A a a=A a a∘ (Equiv.neg Cover):=by
      refine RRead_injective (hx.safe a a) ((Equiv.neg Cover).summable_iff.mpr (hx.safe a a)) (fun p hp=>?_)
      have H: RRead (A a a) (-p)= RRead (A a a) p:= by change A.read (-p) _ _= A.read p _ _; rw [hx.echo p hp,hx.echo (-p) (signed_base hp sigma),hP p hp]
      rw [← H]; unfold RRead Laurent.read; rw [← (Equiv.neg Cover).tsum_eq]; exact tsum_congr fun i=>by simp
   rintro ⟨x,a⟩ ⟨y,b⟩; unfold mate; dsimp only
   by_cases hp: a=b
   · subst b; unfold Row.acts; simp only [of_apply]; rw [← (Equiv.neg Cover).tsum_eq (fun i:Cover=> if -y-_= -x-wrap L (brim a)+wrap L i then A a a i else 0)]
     apply tsum_congr; intro i; rw [Equiv.neg_apply, map_neg]; have hz : (-y-wrap L (brim a) = -x-wrap L (brim a) + -(wrap L i))  ↔ y=x+wrap L i:= by
       constructor
       · intro H; apply neg_injective; change -y=-(x+wrap L i); rw [eq_add_of_sub_eq H]; abel
       rintro rfl; abel
     split_ifs with h h' hh
     · exact congr_fun (he a) i
     · exact False.elim (h' (hz.mpr h))
     · exact False.elim (h (hz.mp hh))
     rfl
   unfold Row.acts; simp only [of_apply]; simp [h a b hp] -- binder
lemma metrics (P:Train j)(k:ℝ)(L:Side)(h:0<k)(hp:4≤j): Twilight ((pink k P).acts L)∧ Twilight ((blue k P).acts L) := by
   refine ⟨even_r k h hp P _ (pulse k P) (heart_true k h hp P).1 (fun p hP=>(heart_even k h P (base_subset_realCube zone_pos hP)).1) ?_, even_r k h hp P _ (vault k P) (heart_true k h hp P).2 (fun p hP=>(heart_even k h P (base_subset_realCube zone_pos hP)).2) ?_⟩
   · intro p a b H; simp [pulse,mask,H]
   intro p a b H; simp [vault,mask,H]
end finite
end YM.RG08.Invert
