import YM.Planned.PRIMARY_INTEGRAL_295.Mirage
/-!
# Numerical vacancy of the no-hole PreGram cone in dark K

Within actual height radius charged.Y.c Dict. No asserting outside
is used except Literal TRep.Expected. Keeps name at one seat. Uses fderiv
fallback consistency only where not legally calling station, real eqs earned
in separate Clinic receipt. No relying on plog outside authorized coords. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Largo
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice RG Wilson Pressure Labels Source Extra.Histories
open Warehouse Precision Exterior Tree Carrier Bloch Next.Free Progress.StationaryScenes Bazaars Launch Shapes
open Next.Foundations Vintage Spurs 
open Villa Floor Glints Fizz Fizz.Gush   Cabins  Little Density Little.Core Push.Uniform Honey  Night Mirage
open Next.Fluctuations Work.E03 Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {r:ℕ} {n c f : Side} {S:StepData c f}
variable (K:Core G S)(V W:Config G c)

lemma steeps (s:Signed)(e:Acres f G)(q:Site c) (hr:r+1 < separation (affine s 0 q) (chair S e)) (t:ℝ):
   AgreeNear S.ratio.parent q r (owl K s V (t • Pi.single e 1)) (owl K s V 0) := by
   intro i hi
   have hp : sendEdge s 0 i≠e.1:=by
      intro hp; have hv:=Mowing.wanders (S:=S) s q i; rw [hp] at hv; unfold chair at hr; omega
   let v:Temps G f:=t • Pi.single e 1
   let p:=sendEdge s 0 i
   have hc : upload K V v p=upload K V 0 p := by
      unfold upload increment; rw [Bosom.count_root, Bosom.count_root]; split
      · rfl
      have he (j:G.ColorIndex) : (sendEdge s 0 i,j)≠e:=fun H=>hp (congr_arg Prod.fst H)
      congr! 3; unfold v; simp [p,he]
   unfold owl pull Lattice.Step.read; split
   · change (upload K V _ p)⁻¹= (upload K V _ p)⁻¹; rw [hc]
   exact hc

lemma unready (i:Seats G c f)(e:Acres f G)(hb:S.patch.Branches S.kernel G)
    (h:budget S.patch K.R < separation (origin S i) (chair S e)): dowel K V i e=0:=by
    let s:= i.1.1; let p:= i.1.2.elim (fun i=>S.ratio.parent i.1.1) Prod.fst; let z:=affine s 0 p
    have he : z=shade S i.1:=by
       obtain ⟨⟨s,a|b⟩,i⟩:=i
       · change affine s 0 (S.ratio.parent a.1.1) = S.ratio.parent (affine s 0 a.1.1); simp [affine,S.ratio.parent_signed S.patch.odd_side]
       rfl
    have hs : ∀ t:ℝ, logs K i.1 V (t • Pi.single e 1)=logs K i.1 V 0:=by
       intro t; let R:=K.R; let D:=R+ 10+predReach S.patch
       let W(t:ℝ):=owl K s V (t • Pi.single e 1); let H:= owl K s V 0
       have hy : AgreeNear S.ratio.parent p D (W t) H:= steeps (r:=D) K V s e p (by rw [show affine s 0 p=_ from he]; unfold D R; unfold origin budget at h; omega) t
       obtain ⟨⟨l,i|i⟩,j⟩:= i
       · change crease K s V i _ = crease K s V i 0;
         have hx := Mirage.crease_eq K H H (W t) H i.1 (fun _ _=>rfl) (hy.shrink (by change separation p p +_≤_; unfold D R; simp; omega))
         unfold crease; split
         · exact tsum_congr hx.2
         exact hx.1
       have hh:= prediction_near_eq hb _ _ (Push.SectorMeasure.Oriented.choice s K.k) i (hy.shrink (by change separation p p+ _ ≤ _; rw [separation_self]; unfold D; omega))
       change gruel K s V i _=gruel K s V i _; unfold gruel corn; rw [show S.prediction (owl K s V (t • _)) _ i= _ from hh]
    unfold dowel keel; rw [Matrix.of_apply,Mowing.evades _ _ hs]; simp

lemma courts (a b:Acres f G)(hb:S.patch.Branches S.kernel G)
      (hc : AgreeNear id (chair S a) (2*budget S.patch K.R) V W): dark K V a b = dark K W a b ∧ foams K V a = foams K W a:=by
   let D:= budget S.patch K.R
   have hp (i:Seats G c f) : (dowel K V i a * dowel K V i b = dowel K W i a * dowel K W i b) ∧
       dowel K V i a * F₀ K V i = dowel K W i a * F₀ K W i:=by
       by_cases h:D<separation (origin S i) (chair S a)
       · rw [unready K V i a hb h, unready K W i a hb h]; simp
       have hk : separation (chair S a) (shade S i.1) ≤D:=by rw [separation_comm]; exact Nat.le_of_not_gt h
       obtain ⟨h1,h2⟩:= readers K V W i.1 hb (hc.shrink (by change _ +D ≤2*D; omega))
       have he : dowel K V i=dowel K W i:=by ext u; unfold dowel keel; rw [Matrix.of_apply,Matrix.of_apply,funext h2]
       rw [he]; simp [F₀,h1]
   constructor
   · simpa [dark,Matrix.mul_apply] using Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _=>(hp i).1)
   exact Finset.sum_congr rfl (fun i _=>(hp i).2)

lemma melts (a b:Acres f G)(hb:S.patch.Branches S.kernel G)(h: 2*budget S.patch K.R < separation (chair S a) (chair S b)): dark K V a b=0:=by
   let D:=budget S.patch K.R; have hm : a≠b:=fun hh'=>by rw [hh',separation_self] at h; omega
   unfold dark Core.fires; rw [Matrix.add_apply,Matrix.diagonal_apply,if_neg hm, add_zero, Matrix.mul_apply]
   apply Finset.sum_eq_zero; intro i _; change dowel K V i a*dowel K V i b=0
   by_cases hx:D<separation (origin S i) (chair S a)
   · rw [unready K V i a hb hx,zero_mul]
   rw [unready K V i b hb ?_,mul_zero]
   have he:= separation_triangle (chair S a) (origin S i) (chair S b); rw [separation_comm _ (origin S i)] at he; unfold D at *; omega
end YM.Planned.PrimaryIntegral295.Largo
