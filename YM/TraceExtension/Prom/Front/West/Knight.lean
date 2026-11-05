import YM.MergeProof.West.Knight
import YM.TraceExtension.Prom.Front.West.Dart
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Gust
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {C : Family G} {ι κ χ μ V : Type} [Fintype V] [DecidableEq V]
variable [Fintype ι] [Fintype κ]
variable {N k d p m : ℕ} {q : BudgetPoint} {ζ : V→Site n} {τ : ℝ}

variable (m i : ℕ){d:Fin (m+1) → ℕ} (Y : Points (m+1)) (s : ℝ) (hN : k≤N) (v : (i:Fin (m+1))→ C.label (d i))
variable {Q : Rep G (C.side k p)} {B : Neat (C.side k p)→Burst G (C.side k p) (C.path.rep N p k).p.threshold}
variable {X : Keepat (C.side k p)} {w : Fin (m+1) → Config G (C.side k p)→ℂ} {c : Fin (m+1)→ℝ}

section
variable (A : ι → SourceAt G (seatsSky C s Y hN p)) (L : κ → Lifted G (seatsSky C s Y hN p) (C.path.rep N p k).p.threshold)
variable (h : C.Makes) (hp : ∀ i,C.ref (d i) ≤ k) (ht : ∀ j,Ticket (v j) i k N p Q.p X (w j) (c j))

def readyHXSky (j : ListensSky C s (v:=m+1) hN p) := openW (v j.2) i (handSky C s hN p j) (fpSky C s hN p j) j (ht j.2) (ζ:=seatsSky C s Y hN p)
def readyNearXSky (j : ListensSky C s (v:=m+1) hN p) := Rshot (v j.2) i h (hp j.2) hN (handSky C s hN p j) (fpSky C s hN p j) j (ht j.2) (ζ:=seatsSky C s Y hN p)
def readyWideXSky (j : ListensSky C s (v:=m+1) hN p × Keepat (C.side k p)) :=
    docket i (v j.1.2) h (hp j.1.2) hN j.1 (fpSky C s hN p j.1) (handSky C s hN p j.1) j.2 (ζ:=seatsSky C s Y hN p)
def readyStrXSky (H : Q.p.threshold≤(C.path.rep N p k).p.threshold) (j : ListensSky C s (v:=m+1) hN p) :=
    Ember (v j.2) i h (hp j.2) hN (handSky C s hN p j) (fpSky C s hN p j) j (ht j.2) H (ζ:=seatsSky C s Y hN p)

def standXSky (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold) := Sum.elim (readyStrXSky m i Y s hN v h hp ht ℓ)
    (fun i' => dash (C.path.rep N p k).p Q.p (Sum.elim A (readyWideXSky m i Y s hN v h hp) i') ℓ)
def restedXSky := Sum.elim (readyNearXSky m i Y s hN v h hp ht) (Sum.elim A (readyWideXSky m i Y s hN v h hp))

lemma powerXSky (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold) (U : Config G (C.side k p)) :
    let P:= C.path.rep N p k; let S:= fun x:Fin (m+1)=> C.localSection (d x);let a:=P.p.threshold;let b:= Q.p.threshold
    let f:=fun x => pinHat C (d x) k
    let H:=Sum.elim (restedXSky m i Y s hN v A h hp ht) (readyHXSky m i Y s hN v ht);let L:= standXSky m i Y s hN v A h hp ht ℓ
    (∑ j,Poly.send (slot j) (dot (fpSky C s hN p j) (f j.2 * (pressXSky hN s v j).exponentialEntry 0 (S j.2) P (pullerSky C s Y hN p j U)))) + (∑ i,(A i).amount a U) = (∑ i,(H i).amount b U)+(∑ i, (L i).occ U):= by
  intro P S a b f H L
  let Z:=Sum.elim A (readyWideXSky m i Y s hN v h hp); let F (j:ListensSky C s (v:=m+1) hN p):=Poly.send (slot j) (dot (fpSky C s hN p j) (f j.2 * (pressXSky hN s v j).exponentialEntry 0 (S j.2) P (pullerSky C s Y hN p j U)))
  let X:=readyStrXSky m i Y s hN v h hp ht ℓ; let O:=readyHXSky m i Y s hN v ht; let B:=readyNearXSky m i Y s hN v h hp ht
  have he i u : (Z i).amount a u=(Z i).amount b u+(dash P.p Q.p (Z i) ℓ).occ u:= dash_amount ..
  rw [Fintype.sum_sum_type (f:= fun j=> (H j).amount b U),show (∑ i,(H (Sum.inl i)).amount b U)=_ from Fintype.sum_sum_type _, Fintype.sum_sum_type (f:= fun j=>(L j).occ U)]
  change _ = (((∑ i,(B i).amount b U)+(∑ i,(Z i).amount b U))+(∑ i,(O i).amount b U))+
      ((∑ i,(X i).occ U)+(∑ i,(dash P.p Q.p (Z i) ℓ).occ U))
  have hx : ∑ i,(Z i).amount b U + ∑ i,(dash P.p Q.p (Z i) ℓ).occ U= ∑ i,(Z i).amount a U:= by rw [←sum_add_distrib]; exact sum_congr rfl fun i _=> (he i U).symm
  let W := readyWideXSky (p:=p) m i Y s hN v h hp
  have hq : ∑ i,F i=∑ i,(O i).amount b U + (∑ i,(B i).amount b U)+ (∑ i,(X i).occ U)+(∑ i,(W i).amount a U):= by
    rw [Fintype.sum_prod_type (fun i=> (W i).amount a U), ← sum_add_distrib,← sum_add_distrib,← sum_add_distrib]; apply sum_congr rfl; intro x _
    unfold F; let V:= pullerSky C s Y hN p x U;let P':=v x.2
    let g:=fpSky C s hN p x
    change Poly.send _ (dot g (awakeFull C k N p (v x.2) V))=_
    rw [cost_ex _ h (hp x.2) hN i V,dot_add,send_plus]; exact congr_arg₂ (·+·) (snow ..) (portion i (v x.2) h (hp x.2) hN x g (handSky C s hN p x) U).symm
  have hz : ∑ i,(A i).amount a U+(∑ i,(W i).amount a U)= ∑ i,(Z i).amount a U:= (Fintype.sum_sum_type (fun i=> (Z i).amount a U)).symm
  change (∑ i,F i)+_= _; rw [hq];
  linear_combination (norm:=abel) hz-hx

omit [Fintype ι] in
lemma standModeXSky (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold) j : ((standXSky m i Y s hN v A h hp ht ℓ) j).fires.val.Nonempty := by
  rcases j with y|j
  · exact singleton_nonempty _
  exact (Sum.elim A (readyWideXSky (p:=p) m i Y s hN v h hp) j).chosen
set_option synthInstance.maxSize 512 in

lemma assembledXSky (F : Siren G (C.side k p) Q.p.threshold) (W : ValidX (C.side k p)→ Wickless G _ Q.p.threshold) {a b σ T Λ δ : ℝ} (ℓ : Q.p.threshold ≤ (C.path.rep N p k).p.threshold)
    (hp' : Bridges (C.path.rep N p k) Q a b σ T Λ δ F W (q:=Q.p)) U :
    fabricatedXSky Y hN s v B A L h hp U=dust Q (Sum.elim (restedXSky m i Y s hN v A h hp ht) (readyHXSky m i Y s hN v ht))
      (teat (Sum.elim (ensembleOXSky Y hN s v B h hp) L) (Sum.elim (fun i=> (W i).credit (seatsSky C s Y hN p)) (standXSky m i Y s hN v A h hp ht ℓ)) F) U := by
  exact charge_por (H₁:=ℓ) _ _ _ _ (hp'.predicts U) (standModeXSky m i Y s hN v A h hp ht ℓ) (powerXSky m i Y s hN v A h hp ht ℓ U)
end
end YM.Next.Rank.Edition
