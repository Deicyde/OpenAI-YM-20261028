import YM.TraceExtension.Atlas.Prong
import YM.TraceExtension.Atlas.Fault
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge}{C:Family G}
local notation "F₀"=> Bel C.book
open LoomX
variable {H:(Bel C.book).Hierarchy}

variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E]
variable (bar:E→ₛₗ[starRingEnd ℂ] E) (sw:Signed→Module.End ℂ E)
def Wool : Submodule ℝ (Mat E) where
   carrier:={x| (∀ i,x (bar i)=bar (x i))∧∀ s i,x (sw s i)=sw s (x i)}
   add_mem':=fun {i j} ⟨hi,hx⟩ ⟨hu,hv⟩=> by
      refine ⟨?_,?_⟩
      · intro x; simp only [_root_.add_apply,hi,hu,map_add]
      intro s x; simp only [_root_.add_apply,hx,hv,map_add]
   smul_mem':=fun c i ⟨h,hx⟩=> by
      refine ⟨?_,?_⟩
      · intro v; change c • i (bar v)=bar (c • i v); rw[h, RCLike.real_smul_eq_coe_smul (K:=ℂ), RCLike.real_smul_eq_coe_smul (K:=ℂ), (bar).map_smulₛₗ]; simp
      intro s v; change c • i (sw s v)=sw s (c • i v); rw[hx]; exact ((sw s).restrictScalars ℝ|>.map_smul c _).symm
   zero_mem':=⟨fun v=> ( (bar).map_zero).symm, fun s v=> ((sw s).map_zero).symm⟩
def Threads {G:Gauge}{L:Register G}{T:Table L}(H:T.Hierarchy):= Wool (E:=↥(Active T)) (starA H) (swingA H)
lemma th_star(f: Threads H)(i): f.val (starA H i)=starA H (f.val i):=f.property.1 i
lemma th_swing(f: Threads H)(s i):f.val (swingA H s i)=swingA H s (f.val i):= f.property.2 ..
lemma th_prod {v w:Mat (Active (F₀))}(h:v∈ Threads H)(hh:w∈Threads H):v*w ∈ Threads H:=by
   obtain ⟨ha,hA⟩:= h; obtain ⟨ht,hT⟩:=hh; refine ⟨?_,?_⟩
   · intro i;change v (w _) = starA H (v (w i)); rw[ht, ha]
   intro s i;change v (w _) = swingA H s (v (w i)); rw [hT,hA]
lemma th_one:(1:Mat (Active (F₀)))∈ Threads H:=⟨fun _=>rfl,fun _ _=>rfl⟩
section
variable {I E: Type*} [Fintype I][NormedAddCommGroup E][NormedSpace ℂ E]
lemma page_agrees (A B: Bi E) (L:I→E)(h:∀ v:E, ∃ x:I→ℂ,v=∑ i,x i • L i)(hh:∀ i j,A (L i) (L j)=B (L i) (L j)):A=B:=by
   ext1 i;ext1 j; obtain ⟨p,hp⟩:=h i; obtain ⟨q,hq⟩:=h j; nth_rw 1 [hp,hq]
   -- when i=j as terms? distinct variables. use rw all.
   rw [hp,hq]; simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,hh]
lemma bi_surj [FiniteDimensional ℂ E] (P:Bi E)(hx:Injective P): Bijective P:=by
   let u:= P.toLinearMap
   refine ⟨hx,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=u) ?_).1 hx⟩
   rw [show Module.finrank ℂ (E →L[ℂ] ℂ) = Module.finrank ℂ (E →ₗ[ℂ] ℂ) from (LinearMap.toContinuousLinearMap.symm.finrank_eq)]
   exact (Subspace.dual_finrank_eq ..).symm
end

private lemma freezing {I:Type*}[Fintype I] (P:I→E)(h:∀ v:E, ∃ f:I→ℂ,v=∑ i,f i • P i)(A: Bi E)(X: Wool bar sw)
    (hc:∀ i j,A i j=A j i)(hA:∀ s x y,A (sw s x) (sw s y)=A x y)
    (hq:∀ i j,(∃ (s:Signed)(c:ℂ), c*c=1∧sw s (P i)=c • P i∧sw s (P j)=(-c) • P j) ∨
      ∃ (s:Signed)(c:ℂ), c*c=1∧sw s (P i)=c • P j∧sw s (P j)=c • P i) (v w): A (X.val v) w=A v (X.val w):=by
   let U : Bi E:= pullBi A X.val 1; let K : Bi E:=pullBi A 1 X.val
   have he : U=K:=by
      apply page_agrees U K P h; intro p q
      rcases hq p q with ⟨s,c,hc,hp,hq⟩|⟨s,c,hc,hp,hq⟩
      · let V:= sw s; let i:=P p;let j:=P q
        have hx(x y : E)(hz:V x=c • x)(hu: V y=(-c) • y): A x y=0:=by
            have hh:= hA s x y; rw [hz, hu,A.map_smul,_root_.smul_apply,map_smul,smul_eq_mul,smul_eq_mul, ← mul_assoc, mul_neg, hc] at hh; rw [neg_one_mul] at hh; linear_combination -(1/2:ℂ)*hh
        have hm : U i j=0:=hx _ _ (by change V (X.val i)=_; rw[← show X.val (V i)=_ from X.property.2 ..,hp,map_smul];rfl) hq
        exact hm.trans (hx _ (X.val j) hp (by rw [← show X.val (V j)=_ from X.property.2 ..,hq,map_smul])).symm
      have hm:= hA s (X.val (P p)) (P q); rw [← X.property.2,hq,hp, X.val.map_smul,A.map_smul,_root_.smul_apply,map_smul,smul_eq_mul,smul_eq_mul, ← mul_assoc,hc,one_mul] at hm; exact hm.symm.trans (‹∀ i j,A i j=A j i› _ _)
   exact congr_arg (fun f:Bi E=> f v w) he

lemma solve_u [FiniteDimensional ℂ E](P:Bi E)(he:Bijective P)(h:∀ i j, P (bar i) (bar j)=star (P i j))(hr:∀ s i j,P (sw s i) (sw s j)=P i j)
    (hs:Surjective bar)(hs':∀ s,Surjective (sw s)) (T:Bi E)(hx:∀ i j,T (bar i) (bar j)=star (T i j))(ht:∀ s i j,T (sw s i) (sw s j)=T i j): ∃ X:Wool bar sw,∀ i j,T i j=P (X.val i) j:=by
    let K:= LinearEquiv.ofBijective P.toLinearMap he; let V:= LinearMap.toContinuousLinearMap (K.symm.toLinearMap.comp T.toLinearMap); have hP(i j):P (V i) j=T i j:=congr_arg (fun f:E→L[ℂ] ℂ=> f j) (K.apply_symm_apply _)
    refine ⟨⟨V,?_,?_⟩,fun i j=>(hP i j).symm⟩
    · intro i; apply he.1; ext1 j; obtain ⟨x,rfl⟩:= hs j; rw[h,hP,hP,hx]
    intro s i; apply he.1; ext1 j; obtain ⟨x,rfl⟩:= hs' s j; rw [hr,hP,hP,ht]

section
variable {L:Register G}{T:Table L}{H:T.Hierarchy}
lemma knitter {I:Type*}[Fintype I] (B: I→ Active T)(ht:∀ v:Active T, ∃ u: I→ℂ,v=∑ i,u i • B i)(he:∀ i j,(∃ (s:Signed)(c:ℂ), c*c=1∧swingA H s (B i)=c • B i∧swingA H s (B j)=(-c) • B j) ∨
      ∃ (s:Signed)(c:ℂ), c*c=1∧swingA H s (B i)=c • B j∧swingA H s (B j)=c • B i)(A:laceC H)(X:Threads H)(v w): A.val (X.val v) w=A.val v (X.val w):= by
    exact freezing (E:=↥(Active T)) (starA H) (swingA H) B ht A.val X A.property.1 A.property.2.2 he v w
lemma knit_all(P : laceC H)(ht:Bijective P.val)(A : laceC H): ∃ X:Threads H,∀ v w,A.val v w=P.val (X.val v) w:=by
   refine solve_u (E:=↥(Active T)) (starA H) (swingA H) P.val ht P.property.2.1 P.property.2.2 ?_ ?_ A.val A.property.2.1 A.property.2.2
   · exact fun x=> ⟨_,star_invol H x⟩
   intro s x; let y:= swingA H s⁻¹ x; refine ⟨y,?_⟩; unfold y; rw[← swing_mul,mul_inv_cancel]; exact Subtype.ext (by rw [swing_act,Table.mirror_one])
end
variable (h:G.Simple)
include h
set_option maxHeartbeats 900000 in
set_option maxRecDepth 2000 in
lemma weave_self (A:laceC H)(X: Threads H) (v w): A.val (X.val v) w=A.val v (X.val w):=by
    exact knitter _ (page_basis (C:=C) h) (paired (H:=H)) A X v w

lemma loom_bij:Bijective (scannerX H 1).val:=by
    apply bi_surj; intro i j hj; by_contra hn; let v:=i-j; have he:v ≠ 0:= sub_ne_zero.mpr hn; have hp:= positive_turn (H:=H) h v he; have hh:(scannerX H 1).val v=0:=by unfold v; rw[map_sub,hj,sub_self]
    rw[lace_sym _ _ _,hh] at hp; exact (lt_self_iff_false _).mp hp
set_option maxHeartbeats 900000 in
set_option maxRecDepth 2000 in
lemma solveT (A : laceC H): ∃ X:Threads H,∀ v w, A.val v w=(scannerX H 1).val (X.val v) w:=by
   exact knit_all _ (loom_bij h) A
end YM.Trace.Pilot
