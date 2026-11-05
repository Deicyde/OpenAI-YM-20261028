import YM.TraceExtension.Pills.Quip
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{R M k:ℕ}
lemma eyed (X:Link G n)(x:Site n)(p:PlaqAxes)(c:G.ColorIndex) : eyeB X x p c= (X (x+step p.val.1, coord p.val.2,c)-X (x,coord p.val.2,c))-(X (x+step p.val.2, coord p.val.1,c)-X (x,coord p.val.1,c)):=by
    unfold eyeB Work.F03.faceCurl; rw[← Exterior.fundamental]; rw [Square.cochain_square];rfl
private def sAct (s:Signed)(p:Track): Cover →+ ℝ where
 toFun x:= tracks p (Place.seat (s.act x))
 map_add' x y:= by simp [mul_add,sum_add_distrib]
 map_zero' := by simp [Place.seat]
variable (s:Signed)(p:Track)(i:Axis)(a:G.ColorIndex)
private lemma gaze (h:2*R+4<n.val)(d:Axis)(b:G.ColorIndex): ∃ (A B:ℝ),∀ x:Cover,x∈ Lattice.box R→ orderTurn s (XR (n:=n) p i a k) (wrap n x,coord d,b)= A*(B+sAct s p x)^k :=by
    let y:= s.perm d; let e:= EuclideanSpace.basisFun G.ColorIndex ℝ a
    let C:ℝ:= (basis y i)*e b
    have he (x:Cover)(w:Site n)(h:lift w=x): XR (n:=n) p i a k (w,coord y,b)=C*(tracks p (Place.seat x)+p i/2)^k:=by
       unfold XR; change edgeColor (stepC _ _) (w,y) b=_; rw[stepC]; simp only [ContinuousLinearEquiv.apply_symm_apply,sub_zero,h, elimA, midV]; change ((basis y i)* _^k)*(e b)=_; unfold C; ring
    have hx (x:Cover)(hx:x∈Lattice.box R): s.act x∈ Lattice.box R:=box_covariant R s ▸ mem_image_of_mem s.act hx
    by_cases hh:s.flip d=true
    · refine ⟨-C,tracks p (Place.seat (-step y))+p i/2,fun x ht=>?_⟩
      change flipCoords (G:=G) (m:=n) s ℝ (XR p i a k) (wrap n x,coord d,b)=_; rw[flip_price]
      rw[if_pos hh]; let w:=s.act (wrap n x)-step y
      rw[he (s.act x+ -step y) w (lift_eq_iff.mpr ⟨by simp [w,sub_eq_add_neg],?_⟩),Place.seat_add,map_add]; rw [show sAct s p x = tracks p (Place.seat (s.act x)) from rfl]; ring
      intro j; obtain ⟨hb,hc⟩:= box_test.mp (hx x ht); specialize hb j;specialize hc j; simp only[Pi.add_apply, Pi.neg_apply,step_apply]; split <;> omega
    refine ⟨C,p i/2,fun x ht=>?_⟩
    change flipCoords (G:=G) (m:=n) s ℝ (XR p i a k) _=_; rw [flip_price,if_neg hh, he (s.act x) _ (lift_eq_iff.mpr ⟨by simp,?_⟩)]
    · rw [add_comm];rfl
    intro j; obtain ⟨hb,hc⟩:= box_test.mp (hx x ht); specialize hb j; specialize hc j; omega
structure RelativeP (V:Link G n)(R:ℕ):Prop where
   valid (p:PlaqAxes)(b:G.ColorIndex):∃ (f:Cover→+ ℝ)(c:ℝ),∀ x∈ Lattice.box R, eyeB V (wrap n x) p b=c+f x
lemma fibres (hn:2*R+6<n.val)(k:ℕ)(he:k≤2): RelativeP (n:=n) (orderTurn s (XR p i a k)) R:=by
    let V:= orderTurn s (XR (n:=n) p i a k)
    have hB (x: Cover)(hb:x∈Lattice.box R)(a:Axis): x∈Lattice.box (R+1) ∧ x+step a ∈ Lattice.box (R+1):=by simp only[box_test,Pi.add_apply,step_apply] at *; constructor <;> constructor <;> intro j <;> have h:= hb.1 j <;> have hy:=hb.2 j <;> (first|omega | (split <;> omega))
    have hx(d b:Axis)(t:G.ColorIndex): ∃ (f:Cover→+ℝ)(c:ℝ),∀ x∈Lattice.box R,V (wrap n x+step b,coord d,t)-V (wrap n x,coord d,t)=c+f x:=by
       obtain ⟨A,B,h⟩:=gaze (k:=k) s p i a (R:=R+1) (by omega) d t
       let g:= sAct s p; let Z:= g (step b)
       have hp(x:Cover)(hp:x∈Lattice.box R): V (wrap n x+step b,coord d,t)- V (wrap n x,coord d,t)=A*((B+g x+Z)^k-(B+g x)^k):=by
           rw[show wrap n x+step b=wrap n (x+step b) by simp]; change orderTurn s (XR (n:=n) p i a k) _- orderTurn s (XR (n:=n) p i a k) _=_; rw [h _ (hB _ hp _ |>.2),h _ (hB _ hp b|>.1),map_add]; unfold g Z; ring
       match k with
       | 0=> exact ⟨0,0,fun x hx=> by rw[hp x hx]; simp⟩
       | 1=> exact ⟨0,A*Z,fun x hx=>by rw [hp x hx]; simp⟩
       | 2=> exact ⟨((ContinuousLinearMap.mul ℝ ℝ) (2*A*Z)).toLinearMap.toAddMonoidHom.comp g,A*Z*(2*B+Z),fun x hx=> by rw[hp x hx]; change _= _+ 2*A*Z*g x; ring⟩
       | k+3=> omega
    refine ⟨fun p b=>?_⟩; obtain ⟨H,C,h⟩:=hx p.val.2 p.val.1 b;obtain ⟨L,T,hl⟩:=hx p.val.1 p.val.2 b; refine ⟨H-L,C-T,fun x hx=>?_⟩; rw [eyed, h x hx,hl x hx]; simp;ring
end YM.Trace.Pills
