import YM.TraceExtension.Turret.Storks
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Turret
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Extra.Iteration
open Filch
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{k r:ℕ}{o x y:Site n}{p q C E D a v:ℝ}
abbrev CrG(G:Gauge)(n:Side):= Site n→Peat G n
def sprout(o:Site n)(r:ℕ):=halo r {o}
lemma hedge (hv:separation o x ≤ k)(r:ℕ) : sprout x r ⊆ sprout o (r+k):=by
   intro v hv'; obtain ⟨b,hb,h⟩:= halo_spec.mp hv'; rw[mem_singleton.mp hb] at h
   exact halo_spec.mpr ⟨o,mem_singleton_self o,(separation_triangle o x v).trans (by omega)⟩
lemma sprout_mono(o:Site n){r k:ℕ}(he:r≤k):sprout o r⊆sprout o k:= fun z hz=> by
   obtain ⟨b,hb,h⟩:=halo_spec.mp hz; exact halo_spec.mpr ⟨b,hb,h.trans he⟩
lemma sprout_translation(o x:Site n)(r:ℕ): (sprout o r).image (· + x) ⊆ sprout (o+x) r:=by
    intro z hz; obtain ⟨q,h,rfl⟩:=mem_image.mp hz; obtain ⟨b,hb,h⟩:=halo_spec.mp h; rw[mem_singleton.mp hb] at h; exact halo_spec.mpr ⟨_,mem_singleton_self _,by unfold separation; rw[add_sub_add_right_eq_sub]; exact h⟩
def Bounce (F:CrG G n):Prop:=∀ x:Site n,Dart.loopB (rj x) x F=F
lemma Bounce.trap {F:CrG G n} (h:Bounce F)(x:Site n) : rj x (F 0)=F x:=by
    have hp:= congr_fun (h x) x; simpa only[Dart.loopB,LinearMap.coe_mk,AddHom.coe_mk,sub_self] using hp
lemma Bounce.take {F:CrG G n} (h:Bounce F)(x y:Site n) : rj y (F x)=F (x+y):=by
    have hp := congr_fun (h y) (x+y); simpa only[Dart.loopB,LinearMap.coe_mk,AddHom.coe_mk,add_sub_cancel_right] using hp
structure Bond (F H: CrG G n)(k r:ℕ)(A B C D:ℝ):Prop where
    run : Bounce F
    running:Bounce H
    read (x:Site n):Splendor (H x) (sprout x r) k B D
    lid(x:Site n): Sigh (F x - H x) x A C
namespace Bond
variable {F H J L:CrG G n} {A A' B B':ℝ}
protected lemma zero (hp:0 ≤ A)(hq:0 ≤B): Bond (0:CrG G n) 0 k r p A B C:=by refine ⟨fun _=>map_zero _,fun _=>map_zero _,fun _=>spark_zero hp,fun x=>?_⟩; change Sigh (0-0) _ _ _; rw[sub_self]; exact sigh_zero hq
lemma lapse (h:Bond F H k r p A B C)(hv: Bond J L k r p A' B' C): Bond (F-J) (H-L) k r p (A+A') (B+B') C:=by
    refine ⟨fun x=> by rw [map_sub,h.run x,hv.run x],fun x=> by rw [map_sub,h.running x,hv.running x],fun x=> (h.read x).lapse (hv.read x),fun x=>?_⟩; rw [show (F-J) x-(H-L) x=F x-H x - (J x - L x) by simp only[Pi.sub_apply]; abel]; exact (h.lid x).lapse (hv.lid x)
lemma plus (h:Bond F H k r p A B C)(hv: Bond J L k r p A' B' C): Bond (F+J) (H+L) k r p (A+A') (B+B') C:=by
    refine ⟨fun x=> by rw [map_add,h.run x,hv.run x],fun x=>by rw[map_add,h.running x,hv.running x],fun x=> (h.read x).plus (hv.read x),fun x=>?_⟩; rw [show (F+J) x-(H+L) x=F x-H x + (J x-L x) by simp only [Pi.add_apply]; abel]; exact (h.lid x).plus (hv.lid x)
lemma bondS {V:Type}(F H: V→ CrG G n)(s:Finset V)(C₁ C₂: V→ℝ)(h:∀ i∈s,Bond (F i) (H i) k r p (C₁ i) (C₂ i) A): Bond (∑ i∈s,F i) (∑ i∈s,H i) k r p (∑ i∈s,C₁ i) (∑ i∈s,C₂ i) A:=by induction s using Finset.induction with
 | empty=>simp only [sum_empty]; exact Bond.zero le_rfl le_rfl
 | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,sum_insert hi,sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma top (h:Bond F H k r p A B C)(hv:A ≤ A')(he:B ≤ B'){r':ℕ}(hp:r ≤ r'):Bond F H k r' p A' B' C:= ⟨h.run,h.running,fun x=>(h.read x).up (sprout_mono _ hp) hv,fun x=> (h.lid x).up he⟩
lemma suffix (d:Axis)(h:Bond F H k r a A B C)(ha:0≤ a)(hb:a≤1): Bond (twig d F) (twig d H) k (r+1) a (A+A) (Perfect.shelter 1 4 1 *B+B) C:=by
    refine ⟨fun x=>by rw [Dart.loop_twig,h.run x],fun x=> by rw[Dart.loop_twig,h.running x],fun x=>?_ ,fun x=> ?_⟩
    · have he:= (h.read (x+step d)).up (hedge (Work.E03.sep_step x d) r) le_rfl; exact he.lapse ((h.read x).up (sprout_mono _ (Nat.le_succ r)) le_rfl)
    have hv:= (h.lid (x+step d)).lease (Work.E03.sep_step x d) ha hb; unfold twig; rw[sub_sub_sub_comm]; simpa only[Nat.cast_one] using hv.lapse (h.lid x)
end Bond

def frost (Z:CrG G n)(r:ℕ): CrG G n:=fun x=> rj x (lakesC 0 r (Z 0))
def BurstG(G:Gauge)(k r:ℕ)(a A D B C:ℝ):Prop:= ∀ (n:Side)(F:CrG G n),Bounce F→ F 0∈loom G n → Estate 0 (ballX (F 0)) a (fun _=>A)→ Bond F (frost F r) k (4*(r+1+1)) (a/100) B C D
lemma greet(G:Gauge)(k:ℕ)(D:ℝ)(hd:0 ≤ D):∃ Z:ℕ→ℝ,∃ M:ℝ,∃ Q:ℕ,MarksP Z ∧ 0 ≤ M ∧ ∀ (r:ℕ)(a A:ℝ),0 < a→ a ≤ 1 → 0≤ A→ BurstG G k r a A D (Z r*A) (M*momentPrice Q (a/4)*Real.exp (-(a/4)*r)*A):=by
    obtain ⟨Z,hZ,H⟩:= Turret.entire G k D hd; obtain ⟨M,Q,hM,h⟩:= Filch.dew G
    refine ⟨Z,M,Q,hZ,hM,fun r a A ha hp hv n F he hF hA=>?_⟩; let T:=F 0; let Y:= lakesC 0 r T; let R:=4*(r+1+1); let c:=M*momentPrice Q (a/4)*Real.exp (-(a/4)*r)*A
    have hr:Y∈loom G n:=lake_lo _ _ hF
    have hy:Sigh (T-Y) 0 (a/100) c:= ⟨(loom _ _).sub_mem hF hr,(h n 0 r a A ha hp hv).1 _ hF hA⟩
    have hT: Splendor Y (sprout 0 R) k (Z r*A) D:= ⟨hr, J_take 0 r T,fun g U=> C_swept _ _ hF U g,fun U=> J_warm 0 r _ _ (incrementA U 0) _,fun V _ _ W x hp=> (H V n 0 A a r W x hp hv ha.le).1 T hF hA⟩
    refine ⟨he,fun x=>?_,fun x=> hT.trill ?_,fun x=>?_⟩
    · funext y p; change Y (ride (y-x) (ride x p))=Y _; rw [pace_add,sub_add_cancel]
    · simpa only [zero_add] using sprout_translation 0 x R
    rw [← he.trap x]; have h:= hy.trill x; rw[map_sub,zero_add] at h; exact h
end YM.Trace.Turret
