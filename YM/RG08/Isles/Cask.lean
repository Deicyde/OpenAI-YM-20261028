import YM.RG08.Isles.Survey
import YM.RG08.Forms.Coherent

/-!
# Independence of held anchor in periodization, on translation-homogeneous tensors
-/
noncomputable section
namespace YM.RG08.Isles
open Forms Pert.Bulk Packets Laurent Finset Function Lattice Filter Bloch
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I:Type}{n:ℕ}{P:Side}

def lantern (i:Fin n)(z:Tape n (Cove P I)):Set (Tape n (Market I)):= {x| x i=reach (z i) ∧ port P ∘ x = z}
def pour (F:Flake n (Market I))(i:Fin n)(z:Tape n (Cove P I)):=∑' x, (lantern i z).indicator F x

def scale (j:Fin n)(z:Tape n (Cove P I))(x:Tape n (Market I)):= (reach (z j)).1 - (x j).1
def recenter (j:Fin n)(z:Tape n (Cove P I))(x:Tape n (Market I)):=sway (scale j z x) x
variable {i j:Fin n}{z:Tape n (Cove P I)}{x:Tape n (Market I)}
lemma found (hx:x∈lantern i z)(k:Fin n):port P (x k)=z k:=congrFun ((Set.mem_setOf.mp hx).2) k
lemma scale_null (hx:x∈lantern i z):wrap P (scale j z x)=0:=by
 have he:=congr_arg Prod.fst (found hx j)
 change wrap P (x j).1=(z j).1 at he
 rw [scale,map_sub,reach,wrap_lift,he,sub_self]
lemma recentered (hx:x∈lantern i z): recenter j z x∈lantern j z:=by
 apply And.intro
 · have he:=congr_arg Prod.snd (found hx j)
   ext1
   · simp [recenter,sway,pass,scale]
   exact he
 funext k
 unfold recenter sway port pass
 dsimp only [comp_apply]; rw [map_add,scale_null hx,add_zero];exact found hx k
lemma return_trip (hx:x∈lantern i z) : recenter i z (recenter j z x)=x:=by
 unfold recenter;rw [sway_sway]
 have he:x i=reach (z i):=(Set.mem_setOf.mp hx).1
 rw [show scale i z (sway (scale j z x) x)+scale j z x=0 from ?_,sway_zero]
 unfold scale sway pass;dsimp only [comp_apply];rw [he];abel

def exchange (i j:Fin n)(z:Tape n (Cove P I)):↥(lantern i z) ≃ ↥(lantern j z):=⟨fun x=>⟨_,recentered x.property⟩,fun x=>⟨_,recentered x.property⟩,fun x=>Subtype.ext (return_trip x.property),fun x=>Subtype.ext (return_trip x.property)⟩

lemma pour_at (F:Flake n (Market I))(i:Fin n)(z:Tape n (Cove P I)) : pour F i z=∑' x:lantern i z,F x.val:= (_root_.tsum_subtype _ _).symm
lemma common {F:Flake n (Market I)}(h:Cohort F)(i j:Fin n)(z:Tape n (Cove P I)):pour F i z=pour F j z:=by rw [pour_at,pour_at,← (exchange i j z).tsum_eq];exact tsum_congr fun x=>(h (scale j z x.val) x.val).symm

end YM.RG08.Isles
