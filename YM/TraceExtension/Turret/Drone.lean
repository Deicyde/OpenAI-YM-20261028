import YM.TraceExtension.Turret.Mark
import YM.TraceExtension.Pi.Flux
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Turret
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Extra.Iteration
open Filch
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{k r:ℕ}{o x y:Site n}{p q C E D a v A B:ℝ}{Z:Dart G n}{R:PathData G}{s:Clip} {X Y:Sway G n}
open Pull

def boom (X:Sway G n)(b:Axis)(x:Site n):= ∑ a:Axis, elm a (X a b) x
lemma drum_dist (x:Site n)(a:Axis)(i:ℤ)(he:i.natAbs ≤4):separation x (x+i • step a) ≤ 4:=by
    have hp(p:ℕ): separation x (x+p • step a) ≤ p:=by
       induction p with
       | zero=>simp
       | succ i ih=> simpa only[succ_nsmul, ← add_assoc] using (separation_triangle x (x+i • step a) (x+i • step a+step a)).trans (Nat.add_le_add ih (Work.E03.sep_step _ _))
    by_cases h:0≤ i
    · rw [show i • (step a:Site n)=i.natAbs • step a from ?_]; exact le_trans (hp _) he
      rw [← Nat.cast_smul_eq_nsmul ℤ,show (i.natAbs:ℤ)=i by omega]
    rw [show i • (step a:Site n)= -(i.natAbs • step a) from ?_]; swap
    · rw [← Nat.cast_smul_eq_nsmul ℤ,show (i.natAbs:ℤ)= -i by omega, neg_smul,neg_neg]
    apply (le_trans ?_ (le_trans (hp _) he)); simp [separation]

def drumA(A:ℝ):= ∑ i:Fin 4,|cash i| *(A+A)
def droneD(B:ℝ):= drumA (Perfect.shelter 1 4 (4:ℕ) * B)
lemma draftA {F H:CrG G n} (h:Bond F H k r a A B p)(i:Axis)(ha:0 ≤ a)(hb:a≤1): Bond (elm i F) (elm i H) k (r+4) a (drumA A) (droneD B) p:=by
    refine ⟨fun x=>by rw [Dart.loop_elm,h.run x],fun x=>by rw [Dart.loop_elm,h.running x],fun x=>?_ ,fun x=>?_⟩
    · unfold drumA elm Pull.dTap; apply sparkle _ _ _ fun j _=>?_ ; let m:ℤ:=steps j; let y:Site n:=x+(0+m) • step i; let w:Site n:=x+(0-m) • step i
      have hw (b:Fin 4): steps b≤4:=by unfold steps; omega
      exact (((h.read y).up (hedge (drum_dist x i (0+m) (by simp[m,hw])) r) le_rfl).lapse ((h.read w).up (hedge (drum_dist x i (0-m) (by simp [m,hw])) r) le_rfl)).scale (cash j)
    unfold droneD drumA elm dTap; rw [← Finset.sum_sub_distrib]; apply sighed _ _ _ fun j _=>?_ ; have hv(t:ℤ)(he:t.natAbs≤4): Sigh (F (x+t • step i)-H (x+t • step i)) x a (Perfect.shelter 1 4 ↑(4:ℕ)*B):= (h.lid (x+t • step i)).lease (drum_dist _ _ _ he) ha hb
    rw[← smul_sub,sub_sub_sub_comm]; have hp (b:Fin 4):steps b ≤4:=by unfold steps; omega
    exact ((hv (0+steps j) (by simp only[zero_add]; simpa using hp j)).lapse (hv (0-(steps j:ℤ)) (by simp[hp]))).scale _
lemma swell (h:∀ i j,Bond (X i j) (Y i j) k r a A B p)(hp:0 ≤ a)(hv:a≤1)(b:Axis): Bond (boom X b) (boom Y b) k (r+4) a (4*drumA A) (4*droneD B) p:=by
    let F(i):=elm i (X i b); let H(i):= elm i (Y i b); have h:= Bond.bondS F H univ _ _ (fun i _=>draftA (h i b) i hp hv)
    rw [show boom X b=∑ i,F i from funext fun x=>(Finset.sum_apply ..).symm, show boom Y b =∑ i,H i from funext fun x=> (Finset.sum_apply ..).symm]; simpa [Axis] using! h
lemma sky {b:Axis}(h:∀ i,Bounce (X i b)): boom X b 0= Kits.airT (fun i=> X i b 0):=by
    unfold boom Kits.airT; apply sum_congr rfl fun i _=>?_ ; rw [show (fun x=>rj x (X i b 0))= X i b from funext fun x=>(h i).trap x]
end YM.Trace.Turret
