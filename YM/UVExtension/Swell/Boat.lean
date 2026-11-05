import YM.UVExtension.Swell.Barge
/-! arbitrary real origins price, no interpolation or estimates on family.R in meetings. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Swell
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {Q:Factor A} (S: Uses Q hG) {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w} {t:ℕ→ℕ}(L:Cellar S t R)
    (N n m k d:ℕ) {a z:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
local notation "T"=> A.B.a.S
local notation "P"=> A.B.a.budget m
local notation "W₀"=> A.B.a.clock.forcedAllowance m
local notation "R0"=> desk a ha
local notation "ℍ"=> Row a
variable (H: Fin k→ Type) [∀ j,Fintype (H j)]
set_option quotPrecheck false
local notation "𝔸"=> (i:Fin k) → H i
lemma sailsList {B D:Type}[NormedAddCommGroup B][NormedSpace ℂ B](T0:Opening D B){k:ℕ}{F:Fin k→ D→ℂ}{y:Fin k→ℝ}(g:Finset (Fin k))(hf:∀ i∈g,Sail T0 (F i) (y i))(hp:∀ i,0≤y i): Sail T0 (fun j=>∏ i∈g,F i j) (∏ i∈g,y i):=by
   induction g using Finset.induction_on with
   | empty=> simpa using! Sail.const («T»:=T0) 1
   | insert i g hi ih=> simp_rw [Finset.prod_insert hi]; exact (hf _ (Finset.mem_insert_self ..)).mult (ih (fun i hx=>hf i (Finset.mem_insert_of_mem hx))) (hp i)
variable {o:Side} (O : Fin k→ Site o)
lemma tasteC (R:Rep G o)(F:Config G o→ℂ)(c:ℂ): Hearth.tasting R (fun x=> c* F x) = c* Hearth.tasting R F:=by
   unfold Hearth.tasting; simp_rw [mul_left_comm _ c (F _),integral_const_mul]; rw [mul_left_comm]
lemma tastes {ι:Type}(R:Rep G o){α C Λ u v:ℝ} (hr:R.Lawful α C Λ u v) (K:Finset ι)(F:ι→ Config G o→ℂ)(hp:∀ i∈K,Envelope (F i)): Hearth.tasting R (∑ i∈K,F i)= ∑ i∈K,Hearth.tasting R (F i):=by
    induction K using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty, Hearth.tasting,Pi.zero_apply,mul_zero,integral_zero]
    | insert i s hi ih=>
       have hf j (hj:j∈s): Envelope (F j):=hp j (Finset.mem_insert_of_mem hj)
       rw [Finset.sum_insert hi, Finset.sum_insert hi]; have hh : Envelope (∑ i∈s,F i):=by
           exact (show (fun U=> ∑ i∈s,F i U)=(∑ i∈s,F i) from funext fun U=> (Finset.sum_apply ..).symm) ▸ Envelope.sumC _ _ hf
       rw [Pier.combine _ hr (hp i (Finset.mem_insert_self ..)) hh,ih hf]
lemma atlasC (f:(i:Fin k)→H i→ Config G o→ℂ)(g:(i:Fin k)→H i→ℂ): cargo k O (fun i=> ∑ j, g i j • f i j)=∑ s:𝔸, (∏ i,g i (s i)) • cargo k O (fun i=> f i (s i)):=by
    funext U; unfold cargo; simp_rw [Finset.sum_apply, Pi.smul_apply,smul_eq_mul]; simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib]
variable {H}
local notation "Z"=> ball (0:ℂ) a
local notation "n₀"=> A.B.a.S.side m n
open Cellar
def reward (A:Levels G)(k:ℕ)(r:Fin k→ℕ)(u d:ℝ)(m:ℕ):= u*((Real.exp ((A.budget m).supportExponent))^(1+∑ i,((r i)+(r i)+1)^4)*d* Real.exp ((1+∑ i,(box (r i)).card:ℕ):ℝ))

variable (hm:m≤N)(r: Fin k→ℕ)(K:(i:Fin k)→H i→ Config G (A.B.a.S.side m n)→ℂ)(F:(i:Fin k)→ H i→Row a→ℂ) (x y:(i:Fin k)→H i→ℝ) (hx:∀ i j,Sail (desk a ha) (F i j) (x i j))
    (hf:∀ i j,Interior (GridApprox.window 0 (r i)) (K i j))(hy:∀ i j V, ‖K i j V‖ ≤ y i j)
    (O':Fin k→ Site (A.B.a.S.side m n)) (hX:Harbour (desk a ha) k (A.B.a.budget m) (fun b:Row a=> S.realBeat b.val N n m) z)(hz:0≤z)
include hf hy hm hp hX hz
lemma scaled (e: 𝔸): Sail (desk a ha) (fun d:Row a=> Hearth.tasting (S.realBeat d.val N n m) (cargo k O' (fun i=> K i (e i)))) (reward A.B.a k r z (∏ i,y i (e i)) m) :=by
    let Q:= garment k O' r; let f:=cargo k O' (fun i=> K i (e i)); let t:= ∏ i,y i (e i); have ht :∀ U,‖f U‖≤t:=by intro U; unfold f cargo t; rw [norm_prod]; exact Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> hy i (e i) _)
    have hF:= loaded k O' r (fun i=>K i (e i)) (fun i=> hf i (e i))
    obtain ⟨hi,hq,h⟩:= lengths k O' r (P).B ((P).B_pos)
    have he: W₀≤1:=Real.exp_le_one_iff.mpr (by change -((A.B.a.clock.monitor m)^((1:ℝ)/5))≤_; exact neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _|>.le) _)) -- replace
    refine (insertP S N n m k ha hp hm Q hi f hF.localSites hF.gauge hF.borel ht hX hz).mono ?_; unfold reward
    apply mul_le_mul_of_nonneg_left _ hz
    refine mul_le_mul (mul_le_mul_of_nonneg_right ?_ ((norm_nonneg _).trans (ht 1))) (Real.exp_monotone ?_) (Real.exp_pos _).le (mul_nonneg (by positivity) ((norm_nonneg _).trans (ht 1)))
    · unfold Copse.worth; rw [← Real.exp_nat_mul]; apply Real.exp_monotone; rw [mul_comm]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hq) (P).exponent_pos.le
    exact (mul_le_of_le_one_right (Nat.cast_nonneg _) he).trans (Nat.cast_le.mpr h)
set_option quotPrecheck false
local notation "X0"=> fun i=> S.realBeat i N n m
include hx
lemma paces: Sail (desk a ha) (fun b:Row a=> Hearth.tasting (S.realBeat b.val N n m) (cargo k O' (fun i=>∑ j, F i j b • K i j))) (∑ e:𝔸,(∏ i,x i (e i))* reward A.B.a k r z (∏ i,y i (e i)) m) :=by
   let f (b:Row a) (e:𝔸):= ∏ i,F i (e i) b; let Z' (e:𝔸):= cargo k O' (fun i=> K i (e i)); let u(e:𝔸):= ∏ i,x i (e i)
   let b0:Row a:=⟨0,abs_zero.trans_lt ha⟩; have hh(i j): 0 ≤ x i j:= (norm_nonneg _).trans ((hx i j).within b0); have hr :∀ b:Row a,Hearth.tasting (S.realBeat b.val N n m) (cargo k O' (fun i=>∑ j,F i j b • K i j))=∑ e:𝔸,f b e * Hearth.tasting (S.realBeat b.val N n m) (Z' e):=by
       intro b; let g(i:Fin k)(j:H i):= F i j b; have hk (i: Fin k):∀ j:H i,g i j= F i j b:= fun _=>rfl; have he(e:𝔸): Envelope (f b e • Z' e):= GridApprox.cylinder_env ((loaded k O' r (fun i=> K i (e i)) (fun i=> hf i (e i))).scale _) -- cylinder namespace
       have hh: cargo k O' (fun i=> ∑ j,F i j b • K i j)=∑ e:𝔸,f b e • Z' e := atlasC k H O' K (fun i j=> F i j b); rw [hh,tastes (S.realBeat b.val N n m) (liveR S N n m (roseK S ha hp b) hm) _ _ (fun i _=> he i)]; exact Finset.sum_congr rfl (fun i _=> tasteC (X0 b.val) _ _)
   simp_rw [hr]; refine Sail.list _ (fun e _=>?_); exact (sailsList R0 Finset.univ (fun i _=> hx i (e i)) (fun i=>hh i (e i))).mult (scaled S N n m k ha hp hm r K y hf hy O' hX hz e) (Finset.prod_nonneg fun i _=> hh i (e i))
include hX
end YM.UVExtension.Swell
