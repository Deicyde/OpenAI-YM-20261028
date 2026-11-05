import YM.RG08.Carrel.Noria

/-! # Period evaluation of registered translated templates. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Lattice Laurent Forms Pert.Bulk Isles Packets Glyph Filter Finset Function
open scoped BigOperators Topology Classical ENNReal
variable {I:Type}{n:ℕ}{P:Side}

def aisle (o:Site P) (x:Slide I n):Tape n (Cove P I):=fun i=>(wrap P (x i).1+o,(x i).2)
def rooted (z:Tape n (Cove P I)) : Set (Site P×Slide I n) := {x | aisle x.1 x.2=z}
private def A (i:Fin n)(z:Tape n (Cove P I))(x:↥(lantern i z)×Cover):Site P × Slide I n:=(wrap P x.2,sway (-x.2) x.1.val)
private def B (i:Fin n)(z:Tape n (Cove P I))(x:Site P × Slide I n) := (reach (z i)).1-(x.2 i).1

private lemma spiral (i:Fin n)(z:Tape n (Cove P I))(x:↑(rooted z)):
 wrap P (B i z x.val)=x.val.1:=by
 have hx:=congrArg (fun (v:Tape n (Cove P I))=> (v i).1) (show aisle _ _=z from x.property)
 change wrap P (x.val.2 i).1 + x.val.1=(z i).1 at hx
 rw [B,map_sub,reach,wrap_lift,←hx];abel

def reels (i:Fin n)(z:Tape n (Cove P I)) : ↥(lantern i z)×Cover≃↥(rooted z) where
 toFun x:=⟨A i z x,by
   change aisle _ _=z; funext k
   unfold aisle A sway pass; dsimp only [comp_apply];rw [map_add,map_neg]; simp only [neg_add_cancel_right]
   have he:=found x.1.property k
   simpa [port] using he⟩
 invFun x:=(⟨sway (B i z x.val) x.val.2,by
     have he(k): aisle x.val.1 x.val.2 k=z k:=congrFun (show _=z from x.property) k
     refine ⟨?_,?_⟩
     · unfold sway pass B; dsimp only [comp_apply]; rw [add_sub_cancel]
       exact Prod.ext rfl (congrArg (fun w : Cove P I => w.2) (he i))
     funext k;unfold port sway pass;dsimp only [comp_apply];rw [map_add,spiral i z x];exact he k⟩, B i z x.val)
 left_inv := by
    rintro ⟨⟨y,hy⟩,x⟩
    have hz: y i=reach (z i):=hy.1
    have he:B i z (A i z (⟨y,hy⟩,x))=x:=by unfold B A sway pass; dsimp only [comp_apply];rw [hz];abel
    -- don't rw dependent proofs
    apply Prod.ext
    · apply Subtype.ext;change sway (B i z _) (sway (-x) y)=y
      rw [he,sway_sway,add_neg_cancel,sway_zero]
    exact he
 right_inv:=by
    intro x;apply Subtype.ext;apply Prod.ext
    · exact spiral i z x
    change sway _ (sway (B i z x.val) x.val.2)=x.val.2
    rw [sway_sway,neg_add_cancel,sway_zero]

lemma caught (F:Flake n (Market I))(h:Summable F)(i:Fin n)(z:Tape n (Cove P I)):
    pour (grown F) i z = ∑' x: ↥(rooted z),F x.val.2:=by
 have hu:Injective (fun x:↥(rooted z)=>x.val.2):=by
    rintro x y hi
    change x.val.2 = y.val.2 at hi
    have hx:=spiral i z x;have hy:=spiral i z y
    apply Subtype.ext;apply Prod.ext ?_ hi;rw [←hx,←hy,B,B,hi]
 have hs:Summable (fun x:↥(rooted z)=>F x.val.2):=h.comp_injective hu
 have hb:=hs.comp_injective (reels i z).injective
 rw [pour_at, ← (reels i z).tsum_eq]
 exact hb.tsum_prod.symm

/-- Blueprint time enrollment at any translating attachment, all periods. -/
def built (F:Flake n (Market I))(z:Tape n (Cove P I)):=∑ o:Site P,∑' y:Slide I n,if aisle o y=z then F y else 0


lemma bought (F:Flake n (Market I))(h:Summable F)(i:Fin n)(z:Tape n (Cove P I)):
    pour (grown F) i z=built F z:=by
 have hs : Summable ((rooted z).indicator (fun x: Site P × Slide I n=> F x.2)):=by
    have he: Injective (fun x:↥(rooted z)=> x.val.2) :=by
      rintro x y Hi
      change x.val.2=y.val.2 at Hi; apply Subtype.ext;apply Prod.ext ?_ Hi;rw [←spiral i z x,←spiral i z y,B,B,Hi]
    exact (summable_subtype_iff_indicator.mp (h.comp_injective he : Summable (fun x:↥(rooted z)=>F x.val.2)))
 rw [caught F h i, show (∑' x:↑(rooted z),F x.val.2)= tsum ((rooted z).indicator fun x=>F x.2) from _root_.tsum_subtype (rooted z) (fun x=>F x.2), hs.tsum_prod,tsum_fintype]
 unfold built;apply Finset.sum_congr rfl; intro u _;apply tsum_congr; intro x;by_cases hx:aisle u x=z <;> simp [Set.indicator,rooted,hx]

/-- Evaluating at any tests B over a torus agrees with summing U at every origin on that torus,
transporting slots to wrapped lifts from there, with all absolute exchanges included. -/
abbrev Vert (P : Side)(I:Type):= Cove P I→ℝ
def per_use (x:Slide I n)(W:Vert P I)(o:Site P):=∏ i,W (aisle o x i)

def per_sum (F:Flake n (Market I))(W:Vert P I):=∑' x:Slide I n,F x*(∑ o:Site P,per_use x W o)
variable [Fintype I]
lemma purchased (F:Flake n (Market I))(h:Summable F)(i:Fin n)(W:Vert P I):
    ∑ z:Tape n (Cove P I), pour (grown F) i z*(∏ j,W (z j))=per_sum F W:=by
 let U(o:Site P)(z:Tape n (Cove P I))(x:Slide I n):=if aisle o x=z then F x else 0
 let Y(z:Tape n (Cove P I)):=∏ i,W (z i)
 have he(o z): Summable (U o z):=(h.indicator (s:={x|aisle o x=z})).congr (fun i=>by unfold U Set.indicator; by_cases hi:aisle o i=z <;> simp [hi])
 simp_rw [bought F h i,built,Finset.sum_mul]
 unfold per_sum;rw [Finset.sum_comm];
 let V(z:Tape n (Cove P I))(x:Slide I n):=∑ o:Site P,U o z x * Y z
 change (∑ o:Site P,∑ z:Tape n (Cove P I),(∑' x,U o z x)*Y z)=_
 have H:(∑ o:Site P,∑ z:Tape n (Cove P I),(∑' x,U o z x)*Y z)=∑' x:Slide I n,∑ o:Site P,∑ z:Tape n (Cove P I),U o z x*Y z:=by
    simp_rw [← tsum_mul_right]
    rw [Summable.tsum_finsetSum (fun o _=> summable_sum fun i _=> (he o i).mul_right (Y i))]
    simp_rw [Summable.tsum_finsetSum (fun (i:Tape n (Cove P I)) _=> (he _ i).mul_right (Y i))]
 rw [H];apply tsum_congr;intro x;dsimp only [U];simp only [ite_mul,zero_mul,Finset.sum_ite_eq,if_pos (mem_univ _),Finset.mul_sum];rfl
end YM.RG08.Carrel
