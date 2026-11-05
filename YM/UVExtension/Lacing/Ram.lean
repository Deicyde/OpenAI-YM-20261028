import YM.UVExtension.Lacing.Frames
/-!
 # Graph-step architecture. at every complex coordinate its inputs under Motion may be OTHER values of the parameter.
 Hence require *family* per motion. cone delivered, eq genuine. Strong stability even without complex orientation equations.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet RoutesF Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n n':Side}{d:ℕ} {F:Frame G d}{p P :BudgetPoint}{H:Hol G}
local notation "R"=> RoutesF F n n' p P H
local notation "E"=> Cow G n' p d H
local notation "B"=> Cow G n P d H
local notation "Lc"=> Bucket F P H n
set_option quotPrecheck false
variable (L:Motion→RoutesF F n n' p P H)(Y Y':Motion→(F.Coeff→ₗ[ℂ] Cow G n' p d H))(hn:2≤ n.val)
abbrev Cush (W:Type)[AddCommGroup W] [Module ℂ W]:= F.Coeff→ₗ[ℂ] W -- norm type unbound

def sell (i:Tally F):= rooms n F H P (aisleN (code _) i)
       (Eyelet.cap n F H P i.1 hn ((L i.1).rain (Y i.1 (Size.axis F i.2)) (some i.2)))
section chips
variable {χ:Type}[NormedAddCommGroup χ] [NormedSpace ℂ χ]
variable {Ω ι:Type} [NormedAddCommGroup Ω][NormedSpace ℂ Ω][FiniteDimensional ℂ Ω][Fintype ι]
def beadZ (f:Ω→ₗ[ℂ] (ι→ℂ))(l:ι→χ): Ω→L[ℂ] χ:= ({
 toFun x:= ∑ i:ι,f x i • l i
 map_add':=fun x y=> by simp only [map_add,Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul':=fun x y=> by simp only [map_smul, Pi.smul_apply, smul_smul,RingHom.id_apply, Finset.smul_sum]; rfl } : Ω→ₗ[ℂ] χ).toContinuousLinearMap
lemma beadV (f:Ω→ₗ[ℂ] (ι→ℂ))(l:ι→χ)(x:Ω): beadZ f l x=∑ i:ι,f x i • l i:= rfl

def bead (F:Frame G d)(l:Tally F→χ): F.Coeff→L[ℂ] χ:= beadZ (chips F) l
lemma bead_eq (F:Frame G d)(l:Tally F→χ)(x:F.Coeff): bead F l x=∑ i:Tally F,chips F x i • l i:= beadV (chips F) l x
end chips
def major: F.Coeff→L[ℂ] F.Coeff:= bead F (fun i=>(sell L Y hn i).1)
def minor: F.Coeff→L[ℂ] (Cow G n P d H) := bead F (fun i=>(sell L Y hn i).2)
local notation "a'"=> major L Y hn
local notation "b'"=> minor L Y hn
local notation "F1"=> F.Coeff
variable {u v c w :ℝ} {r:Side}{T:Heading F} (h:∀ i, Tips (L i) r T u v)

set_option maxRecDepth 4608 in
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
lemma pieces (x:F1) : major L Y hn x = ∑ i, chips F x i • (sell L Y hn i).1 ∧ minor L Y hn x= ∑ i:Tally F,chips F x i • (sell L Y hn i).2:=by
   unfold major minor; rw [bead_eq,bead_eq]; exact ⟨rfl,rfl⟩
include h
set_option synthInstance.maxHeartbeats 100000
lemma sailC (hc:0 ≤ c)(hp:∀ i x,‖Y i x‖ ≤ c*F.coeffSize (F.core x))(x:F1) : F.coeffSize (major L Y hn x-T.leads r x) ≤ (u+2*u*c)*orbitCost F*F.coeffSize (F.core x) ∧ ‖minor L Y hn x‖ ≤ (v+2*u*c)*orbitCost F * F.coeffSize (F.core (vowel F r x)):=by
    let J:= Size.axis F; let g:= T.leads r
    let C (u:F.Coeff):=F.coeffSize (F.core u); let D (u:F.Coeff):=F.coeffSize (vowel F r (F.core u))
    have hu:0 ≤ u:=(h (1,false)).counts.calm; let t:=u+2*u*c
    have he : 0≤ t:=by unfold t; positivity
    let A i:= sell L Y hn i; have hv(i:Tally F): F.coeffSize ((A i).1 - Motion.patch F i.1 (g (J i.2))) ≤ t*C (J i.2)∧ ‖(A i).2‖ ≤ (v+2*u*c)* D (J i.2):=by
       let x:= J i.2; let y:= Y i.1 x; have hh:‖y‖ ≤ c*C x:=hp i.1 x
       have hZ : c*C x ≤ c*D x:= mul_le_mul_of_nonneg_left (size_vowel F r (F.core x)).1 hc; have hS:= Tips.strum i.1 y hn (h i.1) i.2
       refine ⟨?_ ,?_⟩
       · calc _ ≤ u*C x+ (2*u)*‖y‖:=hS.1
              _ ≤ u*C x+ (2*u)*(c*C x):=add_le_add_right (mul_le_mul_of_nonneg_left hh (by positivity)) _
              _ = _ := by unfold t x;ring
       calc _ ≤ _:= Tips.deal (Eyelet.cap n F H P i.1 hn ((L i.1).rain y (some i.2))) _
            _ ≤ _:= hS.2
            _ ≤ v*D x+(2*u)*(c*D x):=add_le_add_right (mul_le_mul_of_nonneg_left (hh.trans hZ) (by positivity)) _
            _ = _:= by unfold x;ring
    rw [(pieces L Y hn x).1,(pieces L Y hn x).2]; constructor
    · change F.coeffSize ((∑ i:Tally F,chips F x i • (A i).1) - g x) ≤ t * orbitCost F * C x
      rw [show g x= repaint F (fun i=>g (Size.axis F i)) x from (repaint_same F g (fun x m => (T.coheres r m x).symm) x).symm, repaint, ←Finset.sum_sub_distrib]; simp_rw [← smul_sub]
      apply le_trans (Size.finite ..)
      simp_rw [Size.smul]
      refine le_trans (Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (hv i).1 (norm_nonneg (chips F x i)))) ?_
      simp_rw [mul_left_comm _ t,← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left (core_tab F x) he).trans_eq (mul_assoc ..).symm
    rw [core_vowel]; have he :0 ≤ v:= (h (1,false)).wing
    apply (norm_sum_le ..).trans; simp_rw [norm_smul]; exact le_trans (Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (hv i).2 (norm_nonneg _)) (residual_bill F r _ (by positivity) x)
end YM.UVExtension.Lacing
