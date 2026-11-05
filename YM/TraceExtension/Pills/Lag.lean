import YM.TraceExtension.Pills.Fibre
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{R M k:ℕ}{x:Site n}{I:Type}
def Stifle (V:Link G n)(r:ℕ):Prop:=∀ e: Lines G n 1,pdist e.1>r→V e=0
lemma stark {V:Link G n}(h:Stifle V R)(s:Signed) : Stifle (orderTurn s V) (R+1):=by
   rintro ⟨x,d,k⟩ hx; obtain ⟨d,rfl⟩:= axisEquiv.surjective d
   have hv : pdist (s.act x) = pdist x:=by
       have h : separation (affine s (0:Site n) x) (affine s (0:Site n) 0)=separation x 0:= Push.Local.turn_sep ..; simpa [affine,separation] using h
   have he:pdist (s.act x) >R+1:=hv.symm ▸ hx; have hp: pdist (s.act x-step (s.perm d)) >R:=by
        let z:Site n:=step (s.perm d); have ht:= pdist_triangle (s.act x-z) z; rw[sub_add_cancel] at ht; have hh:= pdist_step (n:=n) (s.perm d); change pdist z≤1 at hh; change _ < pdist (s.act x-z); omega
   change flipCoords s ℝ V (x,coord d,k)=_; rw[flip_price]; split; rw [h ⟨_,_,_⟩ hp,neg_zero]; exact h _ (Nat.lt_trans (Nat.lt_succ_self _) he)
lemma eye_small {V:Link G n}(h:Stifle V R)(i:PlaqAxes)(c:G.ColorIndex) (hv:eyeB V x i c≠0):pdist x ≤R+1:=by
   contrapose! hv
   have ht(a:Axis)(b:Axis):V (x+step a,coord b,c)=0:= h (x+step a,coord b,c) (show R < pdist (x+step a) from by
      have he:= pdist_triangle (x+step a) (- step a); have hx:= pdist_step (n:=n) a; rw [add_neg_cancel_right,pdist_neg] at he; omega)
   rw [eyed]; simp only [ht,h (x,_,c) (show R<pdist x by omega),sub_zero]
-- cover cumulative sums
lemma localeT (y:Cover)(h: Laurent.size y ≤ R)(hx: pdist x≤ M): lift x+y∈ Lattice.box (M+R):=by
   apply box_test.mpr; constructor <;> intro i <;> have hv:= le_trans (component_le x i) hx <;> have hh: (y i).natAbs ≤ R:= le_trans (single_le_sum (f:=fun i=>(y i).natAbs) (fun i _=>Nat.zero_le _) (mem_univ i)) h <;> simp only[Pi.add_apply] <;> omega
lemma pollinate (p:Wo G)(i j:Fin 2)(h:i≠j):Laurent.size ((p.leg j).offset-(p.leg i).offset) ≤ p.length:=by
    fin_cases i <;> fin_cases j <;> (try contradiction)
    · exact delta_size p
    change Laurent.size ((p.leg 0).offset-(p.leg 1).offset) ≤ _; rw [show _-(p.leg 1).offset= -Extra.Iteration.delta p from ?_,Laurent.size_neg]; exact delta_size _; unfold Extra.Iteration.delta; abel
def hush(L:Finset I)(P:I→Wo G):Prop:=
    ∀ a:Fin 2→ PlaqAxes,∀ b:Cards G, (∑ i∈L,charge (P i) a b)=0 ∧ ∀ z:Axis,(∑ i∈L, charge (P i) a b * (Extra.Iteration.delta (P i) z))=0
variable (L:Finset I)(P:I→Wo G)
lemma poll (f: Cover→+ℝ)(p:Cover): f p=∑ i,p i*f (step i):=by
    nth_rw 1 [show p=∑ i,(p i) • step i from ?_]; swap; · ext i;rw [Finset.sum_apply]; simp [step_apply,mul_ite]
    rw [map_sum]; refine sum_congr rfl fun i _=>?_ ; rw[map_zsmul]; simp
lemma hush_sum (h:hush L P)(f: Cover→+ℝ)(a: Fin 2→ PlaqAxes)(b:Cards G)(i j:Fin 2)(h₁:i≠j): (∑ k∈L,charge (P k) a b * f (((P k).leg j).offset-((P k).leg i).offset))=0:=by
    have hs(q:Cover→+ℝ): (∑ k∈L,charge (P k) a b * q (Extra.Iteration.delta (P k)))=0:=by
       simp_rw[poll q (Extra.Iteration.delta _),mul_sum]; rw [sum_comm]; apply sum_eq_zero fun x _=>?_; simp_rw[← mul_assoc,← Finset.sum_mul,(h a b).2 x,zero_mul]
    fin_cases i <;> fin_cases j <;> (try contradiction)
    · exact hs f
    let s (k):=Extra.Iteration.delta (P k); have he(k): ((P k).leg 0).offset-((P k).leg 1).offset= -s k:= by unfold s Extra.Iteration.delta; abel
    change (∑ k∈L,charge (P k) a b * f (((P k).leg 0).offset- ((P k).leg 1).offset))=_; simp_rw [he,map_neg,mul_neg,sum_neg_distrib]; rw [show (∑ k∈L,charge _ _ _ * f (s k))=_ from hs f, neg_zero]
end YM.Trace.Pills
